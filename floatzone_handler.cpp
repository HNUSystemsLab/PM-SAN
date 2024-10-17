#define _GNU_SOURCE


// #include <iostream>
#include <signal.h>
#include <fenv.h>
#include <unistd.h>
#include <string.h>
// #include <csignal>
#include <immintrin.h>
#include <stdio.h>
#include <dlfcn.h>
#include <iostream>

#include <execinfo.h>
#define TARGET "run_base"

#define     RAX     0
#define     RCX     1
#define     RDX     2
#define     RBX     3
#define     RSP     4
#define     RBP     5
#define     RSI     6
#define     RDI     7
#define     R8      8
#define     R9      9
#define     R10     10
#define     R11     11
#define     R12     12
#define     R13     13
#define     R14     14
#define     R15     15
#define     RNONE   16


#define REDZONE_SIZE 16 // bytes
#define REDZONE_JUMP (REDZONE_SIZE/sizeof(float))

#define FAULT_ERROR_CODE  1

#define FLOAT_MAGIC_POISON_PRE        (0x8b8b8b89U)
#define FLOAT_MAGIC_POISON_PRE_BYTE   (0x89U)
#define FLOAT_MAGIC_POISON            (0x8b8b8b8bU)
#define FLOAT_MAGIC_POISON_BYTE       (0x8bU)
//0x0b8b8b8a
#define FLOAT_MAGIC_ADD             ((float)(5.375081e-32))


#define SURVIVE_EXCEPTIONS 0
#define COUNT_EXCEPTIONS 0
#define AVOID_FALSE 0



const int regs_map[16] = {
    /* RAX = 0  */[RAX] = REG_RAX,
    /* RCX = 1  */[RCX] = REG_RCX,
    /* RDX = 2  */[RDX] = REG_RDX,
    /* RBX = 3  */[RBX] = REG_RBX,
    /* RSP = 4  */[RSP] = REG_RSP,
    /* RBP = 5  */[RBP] = REG_RBP,
    /* RSI = 6  */[RSI] = REG_RSI,
    /* RDI = 7  */[RDI] = REG_RDI,
    /* R8  = 8  */[R8 ] = REG_R8,
    /* R9  = 9  */[R9 ] = REG_R9,
    /* R10 = 10 */[R10] = REG_R10,
    /* R11 = 11 */[R11] = REG_R11,
    /* R12 = 12 */[R12] = REG_R12,
    /* R13 = 13 */[R13] = REG_R13,
    /* R14 = 14 */[R14] = REG_R14,
    /* R15 = 15 */[R15] = REG_R15
};


#define     NOTSUPP    {-1U, -1U, -1U}
const unsigned int lut_modrm[4][16][3] =
{
    {//Mod 00
        {RAX, 0, 0}, {RCX, 0, 0}, {RDX, 0, 0}, {RBX, 0, 0}, {RSP, 1, 0}, NOTSUPP,    {RSI, 0, 0}, {RDI, 0, 0}, {R8, 0, 0}, {R9, 0, 0}, {R10, 0, 0}, {R11, 0, 0}, {R12, 1, 0}, NOTSUPP,   {R14, 0, 0}, {R15, 0, 0},
    },

    {//Mod 01
        {RAX, 0, 1}, {RCX, 0, 1}, {RDX, 0, 1}, {RBX, 0, 1}, {RSP, 1, 1}, {RBP, 0, 1}, {RSI, 0, 1}, {RDI, 0, 1}, {R8, 0, 1}, {R9, 0, 1}, {R10, 0, 1}, {R11, 0, 1}, {R12, 1, 1}, {R13, 0, 1}, {R14, 0, 1}, {R15, 0, 1},
    },

    {//Mod 10
        {RAX, 0, 4}, {RCX, 0, 4}, {RDX, 0, 4}, {RBX, 0, 4}, {RSP, 1, 4}, {RBP, 0, 4}, {RSI, 0, 4}, {RDI, 0, 4}, {R8, 0, 4}, {R9, 0, 4}, {R10, 0, 4}, {R11, 0, 4}, {R12, 1, 4}, {R13, 0, 4}, {R14, 0, 4}, {R15, 0, 4},
    },

    {//Mod 11
        NOTSUPP,    NOTSUPP,    NOTSUPP,    NOTSUPP,    NOTSUPP,    NOTSUPP,    NOTSUPP,    NOTSUPP,     NOTSUPP,    NOTSUPP,    NOTSUPP,    NOTSUPP,    NOTSUPP,    NOTSUPP,    NOTSUPP,    NOTSUPP,
    },
};
const int scales[4] = {1,2,4,8};



void* get_fault_addr(uint8_t *op, int *op_len, ucontext_t *uc)
{

    uint32_t rex_x, rex_r, rex_b, modrm, mod, reg, rm, scale, index, base, sib, pos;
    int32_t offset;
    uint8_t *ptr;

    //Verify VEX instruction
    if (op[0] != 0xc5 && op[0] != 0xc4) goto get_fault_addr_error;

    base  = 0;
    index = 0;
    scale = 0;
    offset = 0;

    // vex 2 bytes
    if (op[0] == 0xc5) {
        if(op[2] != 0x58) goto get_fault_addr_error;
        rex_r = 1^((op[1]>>7)&1);
        rex_x = 0;
        rex_b = 0;
        pos = 3;    //point to modrm
    }

    // rex 3 bytes
    if (op[0] == 0xc4) {
        if(op[3] != 0x58) goto get_fault_addr_error;
        rex_r = 1^((op[1]>>7)&1);
        rex_x = 1^((op[1]>>6)&1);
        rex_b = 1^((op[1]>>5)&1);
        pos = 4;    //point to modrm
    }

    //mod/rm decode
    modrm = op[pos];
    mod = (modrm>>6)&0x3;
    reg = (rex_r<<3) | ((modrm>>3)&0x7);
    rm  = (rex_b<<3) | (modrm&0x7);
    base = rm;
    pos++;

    //Check for supported mod/rm
    if (lut_modrm[mod][rm][0] == -1U) goto get_fault_addr_error;

    //If SIB
    if(lut_modrm[mod][rm][1]) {
        sib = op[pos];
        scale = scales[(sib>>6) & 0x3];
        index = (rex_x<<3) | ((sib>>3)&0x7);
        base  = (rex_b<<3) | ((sib>>0)&0x7);
        //cursed SIB encoding
        if(mod != 0){
            if (index == RSP) index = RNONE;
        } else {
            if((index == RSP) && (base == RBP || base == R13)) goto get_fault_addr_error;
            if (index == RSP) index = RNONE;
            if (base == RBP || base == R13) {
                base = RNONE;
            }
        }
        pos++;
    }

    //Offset
    if(lut_modrm[mod][rm][2] == 1) {
        offset = (int8_t)op[pos];
        pos++;
    }
    if(lut_modrm[mod][rm][2] == 4) {
        offset = (int32_t)(((op[pos+0]&0xff) << 0) |
                ((op[pos+1]&0xff) << 8) |
                ((op[pos+2]&0xff) << 16) |
                ((op[pos+3]&0xff) << 24));
        pos += 4;
    }

get_fault_addr_success:
    ptr = NULL;
    *op_len = pos;
    if (base != RNONE) ptr += uc->uc_mcontext.gregs[regs_map[base]];
    if (index != RNONE) ptr += uc->uc_mcontext.gregs[regs_map[index]]*scale;
    ptr += offset;
    return (void *) ptr;

get_fault_addr_error:
    *op_len = 0;
    return NULL;
}



void sig_handler(int signumber){
  printf("get output sigFPE !\n");
  exit(0);
}

// oid handler(int sig, siginfo_t* si, void* vcontext)
void my_fpehandler(int sig, siginfo_t* si, void* vcontext){
  ucontext_t *uct = (ucontext_t*)vcontext;
  uint8_t* fault_rip = (uint8_t*)si->si_addr;
  printf("get output from action hdnler\n");
  int op_len;
  void **buf = (void**)malloc(128*sizeof(void *));
  int ret = backtrace(buf, 128);
  char **names = backtrace_symbols(buf, ret);
  void* rip_addr = get_fault_addr(fault_rip, &op_len, uct);
  if(rip_addr == NULL){
    printf("unknown crash happened!\n");
    exit(1);
  }
  uint8_t* fault_ptr = (uint8_t*) rip_addr;
  uint8_t* ptr;
  uint32_t* fault_32output = (uint32_t*)fault_ptr;
  printf("shit we got float zone output is %x\n", fault_32output[0]);
    //Probably useless
    if( (*(uint32_t *)fault_ptr) != FLOAT_MAGIC_POISON && 
        (*(uint32_t *)fault_ptr) != FLOAT_MAGIC_POISON_PRE)
         goto false_positive;
    else
      ptr = fault_ptr;

    // New Improved Addition: if the fault value is 0x8b8b8b89, we should scan right to confirm a redzone
    // not left, since the 89 has to mark the start of a redzone (this way we avoid reading a prepended underflow zone)
#if AVOID_FALSE == 1
    if(*((uint32_t *)fault_ptr) == FLOAT_MAGIC_POISON_PRE){ // i = {0,1,2,3} == {89 8b 8b 8b}
        int found = 0;
        for(int i = 4; i < REDZONE_SIZE; i++){
            if(*(ptr+i) != FLOAT_MAGIC_POISON_BYTE){
                // the right of a 0x898b8b8b8b is not a redzone (no 8b)
#if COUNT_EXCEPTIONS == 1
                except_cnt_vaddss_skip++;
#endif
                goto false_positive;
            }
        }
    }
    else {
        //Let's go left until we find something that is not 8b
        //if it is 89 -> true positive, or false positive containing 89 8b 8b 8b 8b ...
        //if it is not 89 false positive
        //also make sure we have at least 15 8b on the right

        int found = 0;
        while(*ptr == FLOAT_MAGIC_POISON_BYTE) { 
            ptr--;
            found++;
        }

        //Now ptr pointing to something that is not 8b
        if(*ptr == FLOAT_MAGIC_POISON_PRE_BYTE) {
            //Ok we need 15 8b on the right from current ptr
            for(int i = 1; i < REDZONE_SIZE; i++) {
                if (*(ptr+i) != FLOAT_MAGIC_POISON_BYTE) {
#if COUNT_EXCEPTIONS == 1
                    except_cnt_vaddss_skip++;
#endif
                    goto false_positive;
                }
            }
        } else {
#if COUNT_EXCEPTIONS == 1
            except_cnt_vaddss_skip++;
#endif
            goto false_positive;
        }
    }
#endif    
    
    
    // fault
#if COUNT_EXCEPTIONS == 1
    except_cnt_vaddss_rz++;
#endif

#if SURVIVE_EXCEPTIONS == 0
    fprintf(stderr, "\n!!!! [FLOATZONE] Fault addr = %p !!!!\n", rip_addr);

    for(int i=-64; i<64; i+=4) {
        fprintf(stderr, "%p: %02x %02x %02x %02x ", &fault_ptr[i], fault_ptr[i], fault_ptr[i+1], fault_ptr[i+2], fault_ptr[i+3]);
        if((void *)&fault_ptr[i] == rip_addr) fprintf(stderr, " <-----");
        fprintf(stderr, "\n");
    }
    fprintf(stderr, "\n");


    fprintf(stderr, "Fault RIP = %p\nBacktrace:\n", (void*)si->si_addr);
    for(int i=2; i<ret; i++) {
        fprintf(stderr, " - [%d] %s\n", i-2, names[i]);
    }

#if FUZZ_MODE == 1
    abort();
#else
    exit(FAULT_ERROR_CODE);
#endif
#endif

false_positive:
    // abort();
    uct->uc_mcontext.gregs[REG_RIP] += op_len;

  //   for(int i=0; i<16; i++) {
  //     if(memcmp(&uct->uc_mcontext.fpregs->_xmm[i], &redzone_s, REDZONE_SIZE) == 0) {
  //         memset(&uct->uc_mcontext.fpregs->_xmm[i], 0, REDZONE_SIZE);
  //     }
  // }

  return;
}

typedef int (*main_t)(int, char, char);
typedef int (*libc_start_main_t)(main_t main, int argc, char** ubp_av,
    void (*init)(void), void (*fini)(void), void (*rtld_fini)(void), void* stack_end);
extern "C" int __libc_start_main(main_t main, int argc, char** ubp_av, void (*init)(void), void (*fini)(void), void (*rtld_fini)(void), void* stack_end){
  libc_start_main_t my_libc = (libc_start_main_t)dlsym(RTLD_NEXT, "__libc_start_main");


  // if(strstr(ubp_av[0], TARGET)){
    int pid = getpid();
    printf("ubpav is %s \n", ubp_av[0]);
    printf("pid is %d\n", pid);
    printf("handler start before main function!\n");
    _MM_SET_FLUSH_ZERO_MODE(_MM_FLUSH_ZERO_ON);
    struct sigaction my_act;
    memset(&my_act, 0, sizeof(struct sigaction));
    my_act.sa_flags = SA_SIGINFO;
    my_act.sa_sigaction = my_fpehandler;
    sigaction(SIGFPE, &my_act, NULL);

  // } 
  
  return my_libc(main, argc, ubp_av, init, fini, rtld_fini, stack_end);
}

// int main(int argc, char* argv[]){

//   //init for floatzone

//   struct sigaction fzaction;
//   char* params[1];
//   memset(&fzaction, 0 ,sizeof(struct sigaction));
//   signal(SIGABRT, sig_handler);
//   if(vfork() == 0)
//   {
//       // _MM_SET_FLUSH_ZERO_MODE(_MM_FLUSH_ZERO_ON);

//   // register signal handler
//   // ___sigaction(SIGFPE, &fzaction, NULL);

//         // enable FP underflow exceptions
//     abort();
//     params[0] = "./output";
//     // // feenableexcept(FE_UNDERFLOW);
//     execvp(params[0], (char**)params);
//   }


//   //execute real program here




//   return 0;
// }