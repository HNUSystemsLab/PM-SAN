#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include <iostream>
#include <string>
#include <vector>
#include <unordered_map>
// #define OUTPUT_ADDRESS
// #define FLOATZONE
#define FILE_ADDRESS
// #define MUTEX
// void access_output(void* ptr, size_t size){
//   std::cout<<"access ptr is "<<ptr << "size is "<<size<<std::endl;
// }

using namespace llvm;

static std::string global_addr("start_address");
static std::string global_end("end_address");
static std::string target_func("_TraceMemory");
static std::string global_base("global_addr_");//this is used for filter function automaticaly
static std::string global_fileptr_base("file_pointer_");
static std::string global_counter_base("func_counter_");
static std::string global_lock_base("my_mutex_");
static std::string pmem_pmdk("pmemobj_create");
//TODO detail logic for mmap and pmemobj_create
static std::string pmem_nopmdk("mmapppp");
static std::string memcpy_func("memcpy");


std::string filter_file[2] = {
  "/home/cwk/cwk/noname/llvm_try/filterpmem",
  "/home/cwk/cwk/noname/llvm_try/filterdram"
};



static size_t freed_value = 0xfdfdfdfdfdfdfdfd;
static uint32_t freed_32value = 0xfdfdfdfd;
static uint16_t freed_16value = 0xfdfd;
static uint8_t freed_8value = 0xfd;
static size_t red_value = 0xfafafafafafafafa;
static uint32_t red_32value = 0xfafafafa;
static uint16_t red_16value = 0xfafa;
static uint8_t red_8value = 0xfa;
static uint32_t red_floatvalue = 0x0b8b8b8aULL;
static int init_value = 123456;
static int create_value = 654321;

// #define PO_1

enum trace_args{
  memaddress,
  acess_len,
  ls_flag,
  func_name,
  lineofcode,
  inst_offset,
  tag_ptr
};

//configurable filter function
std::vector<std::string> filter_function;
namespace {
struct MemoryTrace : public llvm::PassInfoMixin<MemoryTrace> {
  void initGlobaladdress(llvm::Module& M, std::string global_name, int ptr_flag=0, int array_case=40){
    auto &ctx = M.getContext();
                           
    if(ptr_flag == 1)
    {
      M.getOrInsertGlobal(global_name, Type::getInt8PtrTy(ctx));
      GlobalVariable *namedGlobal = M.getNamedGlobal(global_name);
      namedGlobal->setLinkage(GlobalValue::LinkOnceAnyLinkage);
      namedGlobal->setInitializer(llvm::ConstantPointerNull::get(PointerType::getUnqual(Type::getInt8Ty(ctx))));
    }
    else if(ptr_flag == 2)
    {
      M.getOrInsertGlobal(global_name, llvm::ArrayType::get(Type::getInt8Ty(ctx), array_case));
      GlobalVariable *namedGlobal = M.getNamedGlobal(global_name);
      namedGlobal->setLinkage(GlobalValue::LinkOnceAnyLinkage);
      llvm::Constant* con_0 = llvm::ConstantInt::get(llvm::Type::getInt8Ty(ctx), 0);
      std::vector<llvm::Constant*> init_vec;
      for(int i=0; i<array_case; i++)
        init_vec.push_back(con_0);
      llvm::Constant* const_array = llvm::ConstantArray::get(llvm::ArrayType::get(Type::getInt8Ty(ctx), array_case), init_vec);
      namedGlobal->setInitializer(const_array);
    }
    else if(ptr_flag == 32)
    {
      M.getOrInsertGlobal(global_name, Type::getInt32Ty(ctx));
      GlobalVariable *namedGlobal = M.getNamedGlobal(global_name);
      namedGlobal->setLinkage(GlobalValue::LinkOnceAnyLinkage);
      namedGlobal->setInitializer(llvm::ConstantInt::get(Type::getInt32Ty(ctx), 0));
    }
    else
    {
      M.getOrInsertGlobal(global_name, Type::getInt64Ty(ctx));
      GlobalVariable *namedGlobal = M.getNamedGlobal(global_name);
      namedGlobal->setLinkage(GlobalValue::LinkOnceAnyLinkage);
      namedGlobal->setInitializer(llvm::ConstantInt::get(Type::getInt64Ty(ctx), 0));
    }
  }



  void addGlobalFileOpen(llvm::Module& M, llvm::Function &victim_func, IRBuilder<> &builder, int pmem_flag=0){ //IRBuilder<> &builder
    auto &ctx = M.getContext();
    errs()<<"add file open function now!" << "\n";
    std::vector<Type*> param4file{PointerType::getUnqual(Type::getInt8Ty(ctx)),
                                  PointerType::getUnqual(Type::getInt8Ty(ctx))};
    FunctionType* fopenty = FunctionType::get(PointerType::getUnqual(Type::getInt8Ty(ctx)), param4file, false);
    FunctionCallee fopen = M.getOrInsertFunction("fopen", fopenty);
    // function origin type: FILE* fopen(const char* path, const char* mode);
    
    llvm::Value* Fopenfilename = builder.CreateGlobalStringPtr(filter_file[pmem_flag]);
    llvm::Value* Fopenmodename = builder.CreateGlobalStringPtr("r+");
    auto this_fileptr = global_fileptr_base + std::to_string(pmem_flag);
    GlobalVariable* glb_ptr = M.getNamedGlobal(this_fileptr);
    llvm::Value* Fopenreturn = builder.CreateCall(fopen, {Fopenfilename, Fopenmodename});
    builder.CreateStore(Fopenreturn, glb_ptr);
  

    //add global mutex
  }


  //output function 
  //output 2 file function
  void CreateFprintfCall(IRBuilder<> &builder, Function* func, Module& M, Value* const_value, int pmem_flag){
    //fprintf(file_pointer, "%s\n", function_name);
    LLVMContext &ctx = M.getContext();
                                      //
    std::vector<Type*> param4fprintf{Type::getInt8PtrTy(ctx), Type::getInt8PtrTy(ctx), Type::getInt8PtrTy(ctx),
                                       Type::getInt32Ty(ctx), func->getArg(ls_flag)->getType(), func->getArg(acess_len)->getType(),
                                       func->getArg(memaddress)->getType()};
    Type* return_type = Type::getInt32Ty(ctx);
    FunctionType* fprintfunc = FunctionType::get(return_type, param4fprintf, false);
    FunctionCallee fc_fprintf = M.getOrInsertFunction("fprintf", fprintfunc);

    auto global_fileptr = global_fileptr_base + std::to_string(pmem_flag);
    GlobalVariable* file_ptr = M.getNamedGlobal(global_fileptr);
    LoadInst* ptr_load = builder.CreateLoad(Type::getInt8PtrTy(ctx), file_ptr);
    builder.CreateCall(fc_fprintf, {ptr_load, const_value, func->getArg(func_name), func->getArg(inst_offset), func->getArg(ls_flag), 
                                      func->getArg(acess_len), func->getArg(memaddress)});
    GlobalVariable* file_counter = M.getNamedGlobal(global_counter_base + std::to_string(pmem_flag));
    LoadInst* counter_load = builder.CreateLoad(Type::getInt64Ty(ctx), file_counter);
    Value* counter_add1 = builder.CreateAdd(counter_load, builder.getInt64(1));
    builder.CreateStore(counter_add1, file_counter);

  }

  void CreatePrintfCall(IRBuilder<> &builder, Function *func, Module& M, Value* const_value){
    LLVMContext &ctx = M.getContext();
    // printf("load from %p address value %lx, global value is %lx, func name is %s\n", address);
    //change printf function to fprintf
    std::vector<Type*> param4output{Type::getInt8PtrTy(ctx), Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx), Type::getInt64Ty(ctx), Type::getInt8PtrTy(ctx), Type::getInt32Ty(ctx)};
    Type* output_type = Type::getVoidTy(ctx);
    FunctionType* add_func = FunctionType::get(output_type, param4output, false);
    FunctionCallee fc_printf = M.getOrInsertFunction("printf", add_func);
    
    GlobalVariable* global_value = M.getNamedGlobal(global_addr);
    LoadInst* load_global =  builder.CreateLoad(Type::getInt64Ty(ctx), global_value);
    builder.CreateCall(fc_printf, {const_value, func->getArg(memaddress), func->getArg(acess_len), load_global, func->getArg(func_name), func->getArg(inst_offset)});
  }


  Value* filterMainLogic(llvm::Module& M, IRBuilder<> &builder, Function* trace_func, int pmem_flag){
    LLVMContext &ctx = M.getContext();
    std::vector<Type*> fgets_args{
      Type::getInt8PtrTy(ctx), Type::getInt32Ty(ctx), Type::getInt8PtrTy(ctx)
    };
    FunctionType* fgets_type = FunctionType::get(Type::getInt8PtrTy(ctx), fgets_args, false);
    FunctionCallee fgets_func = M.getOrInsertFunction("fgets", fgets_type);


    std::vector<Type*> strcmp_args{
      Type::getInt8PtrTy(ctx), Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx)
    };
    FunctionType* strcmp_type = FunctionType::get(Type::getInt32Ty(ctx), strcmp_args, false);
    FunctionCallee strcmp_func = M.getOrInsertFunction("memcmp", strcmp_type);
    // builder.SetInsertPoint(entry);
    //strtok used to figure the \n problem
    std::vector<Type*> strtok_args{
      Type::getInt8PtrTy(ctx), Type::getInt8PtrTy(ctx)
    };
    FunctionType* strtok_type = FunctionType::get(Type::getInt8PtrTy(ctx), strtok_args, false);
    FunctionCallee strtok_func = M.getOrInsertFunction("strtok", strtok_type);

    FunctionType* strlen_type = FunctionType::get(Type::getInt64Ty(ctx), 
                                  {PointerType::getUnqual(Type::getInt8Ty(ctx))}, false);
    FunctionCallee strlen_func = M.getOrInsertFunction("strlen", strlen_type);

    // Constant* line_control = ConstantDataArray::getString(ctx, "\n");
    // Constant* line_var = M.getOrInsertGlobal("line_ptr", line_control->getType());
    // dyn_cast<GlobalVariable>(line_var)->setInitializer(line_control);
    // Value* line_value = builder.CreatePointerCast(line_var, strtok_args[1], "line_name ");
    auto line_value = builder.CreateGlobalStringPtr("\n");
    //fgets first
    auto global_fileptr = global_fileptr_base + std::to_string(pmem_flag);
    GlobalVariable* file_ptr = M.getNamedGlobal(global_fileptr);
    LoadInst* load_ptr = builder.CreateLoad(Type::getInt8PtrTy(ctx), file_ptr);

    auto array_type_char = llvm::ArrayType::get(Type::getInt8Ty(ctx), 1000);
    auto array_char = builder.CreateAlloca(array_type_char);
    //get element ptr
    auto ptr_char = //Builder.CreateInBoundsGEP(array_type_char, array_char, Builder.getInt64(0), Builder.getInt64(0));
                    builder.CreateConstInBoundsGEP2_64(array_type_char, array_char, 0, 0);

    //char2 is used for snprintf buffer
    auto array_char2 = builder.CreateAlloca(array_type_char);
    auto ptr_char2 = builder.CreateConstInBoundsGEP2_64(array_type_char, array_char2, 0, 0);
    std::vector<Type*> memset_args{
      Type::getInt8PtrTy(ctx), Type::getInt32Ty(ctx), Type::getInt64Ty(ctx)};
    FunctionType* memset_type = FunctionType::get(Type::getInt8PtrTy(ctx), memset_args, false);
    FunctionCallee memset_func = M.getOrInsertFunction("memset", memset_type);
    builder.CreateCall(memset_func, {ptr_char, builder.getInt32(0), builder.getInt64(1000)});
    builder.CreateCall(memset_func, {ptr_char2, builder.getInt32(0), builder.getInt64(1000)});

    builder.CreateCall(fgets_func, {ptr_char, builder.getInt32(1000), load_ptr});
    builder.CreateCall(strtok_func, {ptr_char, line_value});

    //connect arg3 and arg5 as the %s-%d format 
    //snprintf(buffer, len, format, arg1, arg2...)
    std::vector<Type*> snprintf_args{
      PointerType::getUnqual(Type::getInt8Ty(ctx)), Type::getInt64Ty(ctx),
      PointerType::getUnqual(Type::getInt8Ty(ctx)), PointerType::getUnqual(Type::getInt8Ty(ctx)),
      Type::getInt32Ty(ctx), trace_func->getArg(2)->getType(), trace_func->getArg(1)->getType(),
      trace_func->getArg(0)->getType()};
    FunctionType* snprintf_type = FunctionType::get(Type::getInt32Ty(ctx), snprintf_args, false);
    FunctionCallee snprintf_func = M.getOrInsertFunction("snprintf", snprintf_type);
    //call snprintf to generate %s-%d format
    if(snprintf_func)
    {
      auto str_againw2 = builder.CreateGlobalStringPtr("%s-%d-%d-%ld-%p");
      // auto str_again = builder.CreateGlobalString("%s-%d-%d-%ld-%p");
      builder.CreateCall(snprintf_func, {ptr_char2, builder.getInt64(1000), str_againw2, trace_func->getArg(3), 
                                          trace_func->getArg(5), trace_func->getArg(2), trace_func->getArg(1), trace_func->getArg(0)});
    }
    else
      errs()<<"not found snprintf"<<"\n";
    auto line_len = builder.CreateCall(strlen_func, {ptr_char});
    Value* line_sub = builder.CreateSub(line_len, builder.getInt64(12));
    
#ifdef OUTPUT_ADDRESS
    std::vector<Type*> param4printf{Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx), Type::getInt64Ty(ctx)};
    Type* return_type = Type::getVoidTy(ctx);
    FunctionType* print_func = FunctionType::get(return_type, param4printf, false);
    FunctionCallee fc_printf = M.getOrInsertFunction("printf", print_func);
    Constant* output_global = ConstantDataArray::getString(ctx, "output from global %ld-%ld\n");
    Constant* output_var = M.getOrInsertGlobal("output_global", output_global->getType());
    dyn_cast<GlobalVariable>(output_var)->setInitializer(output_global);
    Value* str_ptr = builder.CreatePointerCast(output_var, param4printf[0], "loopstrPtr");
    builder.CreateCall(fc_printf, {str_ptr, line_len, line_sub});
#endif



    Value* strcmp_return = builder.CreateCall(strcmp_func, {ptr_char, ptr_char2, line_sub});
    Value* cmp_str = builder.CreateICmpEQ(strcmp_return, builder.getInt32(0));


    // std::vector<Type*> printf_args{
    //   Type::getInt8PtrTy(ctx), Type::getInt8PtrTy(ctx), Type::getInt8PtrTy(ctx), Type::getInt32Ty(ctx) 
    // };
    // auto return_type = Type::getVoidTy(ctx);
    // FunctionType* print_func = FunctionType::get(return_type, printf_args, false);
    // FunctionCallee fc_printf = M.getOrInsertFunction("printf", print_func);
    // Constant* loop_str = ConstantDataArray::getString(ctx, "output file filter: %s %s %d\n");
    // Constant* loop_var = M.getOrInsertGlobal("check_ptr", loop_str->getType());
    // dyn_cast<GlobalVariable>(loop_var)->setInitializer(loop_str);
    // Value* str_ptr = builder.CreatePointerCast(loop_var, printf_args[0], "checkstrPtr");
    // builder.CreateCall(fc_printf, {str_ptr, ptr_char, trace_func->getArg(3), strcmp_return});


    return cmp_str;
  }

  // void create_fileblock(llvm::Module& M, Function* trace_func){
  //   LLVMContext &ctx = M.getConte
  // }

  void tryFileFilter(llvm::Module& M, Function* trace_func, llvm::BasicBlock *entry, llvm::BasicBlock *end, Value* const_value, int pmem_flag){
    //handle the duplicate function 
    LLVMContext &ctx = M.getContext();
    IRBuilder<> Builder(ctx);
    llvm::BasicBlock* f_entry = llvm::BasicBlock::Create(ctx, "file_entry", trace_func);
    llvm::BasicBlock* fseek_block = llvm::BasicBlock::Create(ctx, "fseek_begin", trace_func);
    llvm::BasicBlock* for_main = llvm::BasicBlock::Create(ctx, "fscan_main", trace_func);
    llvm::BasicBlock* for_out = llvm::BasicBlock::Create(ctx, "fscan_out", trace_func);
    llvm::BasicBlock* else_branch = llvm::BasicBlock::Create(ctx, "duplicate_if", trace_func);
    // llvm::BasicBlock* if_branch = llvm::BasicBlock::Create(ctx, "duplicate_else", trace_func);
    llvm::BasicBlock* for_iter = llvm::BasicBlock::Create(ctx, "for_iter", trace_func);
    //init param
    Builder.SetInsertPoint(entry);
    //pthread_mutex_lock , lock the file operation
    
    // auto ptr_test = Builder.CreateConstInBoundsGEP2_64(stupid_array, trace_func->getArg(6), 0, ci_int);
#ifdef FILE_ADDRESS
    auto mutex_array = llvm::ArrayType::get(Type::getInt8Ty(ctx), 40);
    // Builder.CreateInBoundsGEP(mutex_array, array_glb, indices);
    
    std::vector<Type*> mutex_arg{PointerType::getUnqual(Type::getInt8Ty(ctx))};
    FunctionType* mutex_type  = FunctionType::get(Type::getInt32Ty(ctx), mutex_arg, false);
    FunctionCallee mutex_func = M.getOrInsertFunction("pthread_mutex_lock", mutex_type);
    GlobalVariable* mutex_t = M.getNamedGlobal(global_lock_base + std::to_string(pmem_flag));
    auto ptr_mutex = Builder.CreateConstInBoundsGEP2_64(mutex_array, mutex_t, 0, 0);
    Builder.CreateCall(mutex_func, {ptr_mutex});

    //fast check path, without read file
    Value* index = trace_func->getArg(tag_ptr);
    auto index_value = Builder.CreateLoad(Type::getInt8Ty(ctx), index);
    Value* tag_compare = Builder.CreateICmpEQ(index_value, Builder.getInt8(0));
#ifdef OUTPUT_ADDRESS
    auto index_printf = Builder.CreateLoad(Type::getInt64Ty(ctx), index);
    std::vector<Type*> param4pt{Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx)};
    Type* return_type = Type::getVoidTy(ctx);
    FunctionType* print_func = FunctionType::get(return_type, param4pt, false);
    FunctionCallee fn_pf = M.getOrInsertFunction("printf", print_func);
    Constant* output_global = ConstantDataArray::getString(ctx, "output value is %lx\n");
    Constant* output_var = M.getOrInsertGlobal("output_global", output_global->getType());
    dyn_cast<GlobalVariable>(output_var)->setInitializer(output_global);
    Value* str_ptr = Builder.CreatePointerCast(output_var, param4pt[0], "loopstrPtr");
    Builder.CreateCall(fn_pf, {str_ptr, index_printf});
#endif

    Builder.CreateCondBr(tag_compare, f_entry, end);

#endif
    Builder.SetInsertPoint(f_entry);
    Builder.CreateStore(Builder.getInt8(1), trace_func->getArg(tag_ptr));
    std::vector<Type*> fseek_args{
      Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx), Type::getInt32Ty(ctx) 
    };
    FunctionType* fseek_type = FunctionType::get(Type::getInt32Ty(ctx), fseek_args, false);
    FunctionCallee fseek_func = M.getOrInsertFunction("fseek", fseek_type);
    Value* param1 = Builder.getInt64(0);
    Value* param2 = Builder.getInt32(0);
    auto global_fileptr = global_fileptr_base + std::to_string(pmem_flag);
    GlobalVariable* file_ptr = M.getNamedGlobal(global_fileptr);
    LoadInst* load_ptr = Builder.CreateLoad(Type::getInt8PtrTy(ctx), file_ptr);
    GlobalVariable* file_counter = M.getNamedGlobal(global_counter_base + std::to_string(pmem_flag));
    LoadInst* load_counter = Builder.CreateLoad(Type::getInt64Ty(ctx), file_counter);
    Value* flag = Builder.CreateAlloca(Type::getInt32Ty(ctx));
    Builder.CreateStore(Builder.getInt32(0), flag);
    Value* iter = Builder.CreateAlloca(Type::getInt64Ty(ctx));
    Builder.CreateStore(Builder.getInt64(0), iter);
    Builder.CreateCall(fseek_func, {load_ptr, Builder.getInt64(0), Builder.getInt32(0)});
    Builder.CreateBr(fseek_block);

    //enter the loop
    Builder.SetInsertPoint(fseek_block);
    Value* iter_value = Builder.CreateLoad(Type::getInt64Ty(ctx), iter);
    //compare the iter value and counter value
    Value* cmp_counter = Builder.CreateICmpUGT(load_counter, iter_value);
    Builder.CreateCondBr(cmp_counter, for_main, for_out);
    //inside loop, check duplicate
    Builder.SetInsertPoint(for_main);
    //TODO add check code (fget, strcmp) fuck the world!!!!!! 
    Value* cmp_result = filterMainLogic(M, Builder, trace_func, pmem_flag);
    Builder.CreateCondBr(cmp_result, else_branch, for_iter); //equal means duplicate, else means not duplicate
  

    // auto array_ptr = 
    Builder.SetInsertPoint(for_iter);
    Value* iter_1 = Builder.CreateAdd(Builder.CreateLoad(Type::getInt64Ty(ctx), iter), Builder.getInt64(1));
    Builder.CreateStore(iter_1, iter);
    Builder.CreateBr(fseek_block);


    //check the flag and do the fprintf operation
    Builder.SetInsertPoint(for_out);
    // Value* cmp_flag = Builder.CreateICmpEQ(Builder.CreateLoad(Type::getInt64Ty(ctx), flag), Builder.getInt64(1));
    CreateFprintfCall(Builder, trace_func, M, const_value, pmem_flag);
    // Builder.CreateStore(Builder.getInt32(1), load_tag);
    //pthread_mutex_unlock, unlock the file for other thread to write
    Builder.CreateBr(end);

    //else, return directly
    Builder.SetInsertPoint(else_branch);
    Builder.CreateBr(end);

#ifdef FILE_ADDRESS
    Builder.SetInsertPoint(end);
    FunctionCallee unlock_mutex = M.getOrInsertFunction("pthread_mutex_unlock", mutex_type);
    Builder.CreateCall(unlock_mutex, {ptr_mutex});
#endif

  }
  // Value* CastValue(){

  // }


  void CreateCheckLogic(llvm::Module &M, Function* trace_func, llvm::BasicBlock *end,
                           llvm::BasicBlock *start, llvm::Value* address){
    //real check memory addres logic
    LLVMContext &ctx = M.getContext();
    IRBuilder<> Builder(ctx);
    llvm::BasicBlock* for_main = llvm::BasicBlock::Create(ctx, "for_main", trace_func);
    llvm::BasicBlock* for_begin = llvm::BasicBlock::Create(ctx, "for_start", trace_func);
#ifdef FLOATZONE

#else
    llvm::BasicBlock* if_condition2 = llvm::BasicBlock::Create(ctx, "if_2", trace_func);
    llvm::BasicBlock* output_error = llvm::BasicBlock::Create(ctx, "output_error", trace_func);
#endif
    llvm::BasicBlock* incres_iter = llvm::BasicBlock::Create(ctx, "increse", trace_func);
    Builder.SetInsertPoint(start);
    Value* iter = Builder.CreateAlloca(Type::getInt64Ty(ctx));//i
    Builder.CreateStore(Builder.getInt64(0), iter);
    Value* access_len = trace_func->getArg(1);//len
    Value* address_temp = Builder.CreateAlloca(Type::getInt64Ty(ctx));
    Builder.CreateStore(address, address_temp);
    Builder.CreateBr(for_begin);
    Builder.SetInsertPoint(for_begin);
    Value* iter_value = Builder.CreateLoad(Type::getInt64Ty(ctx), iter);
    Value* cmp_result = Builder.CreateICmpUGT(access_len, iter_value); // i<len
    Builder.CreateCondBr(cmp_result, for_main, end);
    //main loop
    Builder.SetInsertPoint(for_main);
    //address plus offset
    //load address
    //cmp value with default value
    //return
    // std::cout<<"this is main loop call"<<std::endl; 3,933,528 1,073,741,824
    Value* address_intptr = Builder.CreateIntToPtr(Builder.CreateLoad(Type::getInt64Ty(ctx), address_temp), Type::getInt32PtrTy(ctx));
    // Value* address_ptr = Builder.CreateIntToPtr(address, Type::getInt64PtrTy(ctx));
    // Value* origin_value = Builder.CreateLoad(Type::getInt8PtrTy(ctx), address_ptr);
    // Value* value2print;
    // bool should_convert = origin_value->getType()->isPointerTy();
    // if(should_convert)
    //   value2print = Builder.CreatePtrToInt(origin_value, Type::getInt64Ty(ctx), "castto64");
    // else
    //   value2print = Builder.CreateIntCast(origin_value, Type::getInt64Ty(ctx), false, "castto64");
#ifdef PO_1
    Value* posiend_1 = Builder.CreateLoad(Type::getInt8Ty(ctx), address_intptr);
#else
    Value* posiend_4 = Builder.CreateLoad(Type::getInt32Ty(ctx), address_intptr);
#endif


    // Value* posiend = Builder.CreateLoad(Type::getInt64Ty(ctx), address_ptr);
    // Value* load2int = Builder.CreatePtrToInt(load2int, Type::getInt64Ty(ctx));
    //TODO change check process from ICMP to FLOAT_ADD (Done already)

#ifdef FLOATZONE

    Type* floatType = llvm::Type::getFloatTy(ctx);
    Type* floatPtrType = PointerType::get(floatType, 0);
    //get posien value in float type
    Value* posien_float = Builder.CreateBitOrPointerCast(address_intptr, floatPtrType);
    //get token value in float type
    //use consant int and cast ptr

    // Value* int_constant = Builder.getInt32(0x0b8b8b8a);
    // Value* float_constant = Builder.CreateBitOrPointerCast(int_constant, floatPtrType);

    const fltSemantics & floatSem = floatType->getFltSemantics();
    APFloat addV(floatSem, APInt(32, /*magic value*/  0x0b8b8b8a));
    Value *addVal = ConstantFP::get(floatType, addV);

    

    //
    InlineAsm* test_IA = InlineAsm::get(
                       FunctionType::get(llvm::Type::getVoidTy(ctx),
                       {floatPtrType, floatType}, false),
                       StringRef("vaddss $0, $1, %xmm15"),
                       StringRef("p,v,~{xmm15},~{dirflag},~{fpsr},~{flags}"),
                       true,
                       false,
                       InlineAsm::AD_ATT,
                       false);



    
    std::vector<Value*> param4vadd = {posien_float, addVal};
    Builder.CreateCall(test_IA, param4vadd);


    //add printf 
#ifdef OUTPUT_ADDRESS
    Value* float_watch = Builder.CreateAlloca(Type::getFloatTy(ctx));
    Builder.CreateStore(Builder.CreateLoad(Type::getInt32Ty(ctx), posien_float), float_watch);
    std::vector<Type*> param4vaddp{Type::getInt8PtrTy(ctx), Type::getInt32Ty(ctx), Type::getInt32PtrTy(ctx), Type::getInt32Ty(ctx)};
    Type* return_vaddt = Type::getVoidTy(ctx);
    FunctionType* print_funcv = FunctionType::get(return_vaddt, param4vaddp, false);
    FunctionCallee funcv_printf = M.getOrInsertFunction("printf", print_funcv);
    // auto sb_float_shit = Builder.CreateLoad(floatType, posien_float);
    Constant* funcv_str = ConstantDataArray::getString(ctx, " float is %lx, addresult %lx result is %lx\n");
    Constant* funcv_Var = M.getOrInsertGlobal("funcv_str", funcv_str->getType());
    dyn_cast<GlobalVariable>(funcv_Var)->setInitializer(funcv_str);
    Value* funcv_ptr = Builder.CreatePointerCast(funcv_Var, param4vaddp[0], "vaddsStrPtr");
    Builder.CreateCall(funcv_printf, {funcv_ptr, Builder.CreateLoad(Type::getInt32Ty(ctx), float_watch),
                        address_intptr, posiend_4});
#endif

#else
    //finish printf

#ifdef PO_1
    Value* check_result = Builder.CreateICmpEQ(posiend_1, Builder.getInt8(freed_8value));
#else
    Value* check_result = Builder.CreateICmpEQ(posiend_4, Builder.getInt32(freed_32value));
#endif
    // Value* check_result = Builder.CreateICmpEQ(posiend, Builder.getInt64(freed_value));
    Builder.CreateCondBr(check_result, output_error, if_condition2);// output_error, incres_iter);
    Builder.SetInsertPoint(if_condition2);
#ifdef PO_1
    Value* if_result2 = Builder.CreateICmpEQ(posiend_1, Builder.getInt8(red_8value));
#else
    Value* if_result2 = Builder.CreateICmpEQ(posiend_4, Builder.getInt32(red_32value));
#endif
    // Value* if_result2 = Builder.CreateICmpEQ(posiend, Builder.getInt64(red_value));
    Builder.CreateCondBr(if_result2, output_error, incres_iter);
    Builder.SetInsertPoint(output_error);
    std::vector<Type*> param4printf{Type::getInt8PtrTy(ctx), PointerType::getUnqual(Type::getInt8Ty(ctx)),
                                    Type::getInt64Ty(ctx), Type::getInt32Ty(ctx)};
    Type* return_type = Type::getVoidTy(ctx);
    FunctionType* print_func = FunctionType::get(return_type, param4printf, false);
    FunctionCallee fc_printf = M.getOrInsertFunction("printf", print_func);
    //get ptr global string
    auto str_ptr = Builder.CreateGlobalStringPtr("memory bug detected in func %s line %ld value is %lx\n");
    Builder.CreateCall(fc_printf, {str_ptr, trace_func->getArg(func_name), trace_func->getArg(4), posiend_4});

    FunctionType* abort_func = FunctionType::get(return_type, true);
    FunctionCallee fc_abort = M.getOrInsertFunction("abort", abort_func);
    // Builder.CreateCall(fc_abort);
    
#endif
    Builder.CreateBr(incres_iter);


    //move to next 4 bytes
    Builder.SetInsertPoint(incres_iter);
    //add iter value first
#ifdef PO_1
    Value* iter_11 = Builder.CreateAdd(Builder.CreateLoad(Type::getInt64Ty(ctx), iter), Builder.getInt64(1));
    Value* iter_address = Builder.CreateAdd(Builder.CreateLoad(Type::getInt64Ty(ctx), address_temp), Builder.getInt64(1));
    Builder.CreateStore(iter_11, iter);
#else
    Value* iter_14 = Builder.CreateAdd(Builder.CreateLoad(Type::getInt64Ty(ctx), iter), Builder.getInt64(4));
    Value* iter_address = Builder.CreateAdd(Builder.CreateLoad(Type::getInt64Ty(ctx), address_temp), Builder.getInt64(4)); 

    Builder.CreateStore(iter_14, iter);
#endif  
    //Then add address value with same step
   

    Builder.CreateStore(iter_address, address_temp);
    Builder.CreateBr(for_begin);//jmp back
    // llvm::BasicBlock *for_loop

  }


  void CreateFunction(llvm::Module& M){
    LLVMContext &ctx = M.getContext();
    // Value* arg1 = llvm::Type::getInt8PtrTy(ctx);
    // Value* arg2 = llvm::Type::getInt64Ty(ctx);
    //params: load/store_address, access_len, load/store_flag, function_name, lineofcode, inst_offset, tag_ptr
    std::vector<Type*> params{Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx), Type::getInt32Ty(ctx), 
                              Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx), Type::getInt32Ty(ctx),
                              PointerType::getUnqual(Type::getInt8Ty(ctx))};
    Type* rettype = Type::getVoidTy(ctx);
    FunctionType* cre_func = FunctionType::get(rettype, params, false);
    FunctionCallee fcl = M.getOrInsertFunction(target_func.c_str(), cre_func);
    Function *TraceMemoryFunction = dyn_cast<llvm::Function>(fcl.getCallee());
    TraceMemoryFunction->setLinkage(GlobalValue::LinkOnceODRLinkage);
    GlobalVariable* glb = M.getNamedGlobal(global_addr);
    GlobalVariable* glb_end = M.getNamedGlobal(global_end);
    llvm::BasicBlock *before_init = llvm::BasicBlock::Create(ctx, "before_start", TraceMemoryFunction);
    llvm::BasicBlock *BB = llvm::BasicBlock::Create(ctx, "entry", TraceMemoryFunction);
    llvm::BasicBlock* filter_branch = llvm::BasicBlock::Create(ctx, "filter", TraceMemoryFunction);
    llvm::BasicBlock* for_branch = llvm::BasicBlock::Create(ctx, "for_loop", TraceMemoryFunction);
#ifdef FILE_ADDRESS
    llvm::BasicBlock* file_branch = llvm::BasicBlock::Create(ctx, "file_branch", TraceMemoryFunction);
    llvm::BasicBlock* dram_branch = llvm::BasicBlock::Create(ctx, "dram_branch", TraceMemoryFunction);
    llvm::BasicBlock* dram_unlock = llvm::BasicBlock::Create(ctx, "dram_unlock", TraceMemoryFunction);
#endif
   
#ifdef OUTPUT_ADDRESS
    llvm::BasicBlock* filter_branch2 = llvm::BasicBlock::Create(ctx, "filter2", TraceMemoryFunction);
    llvm::BasicBlock* filter_branch3 = llvm::BasicBlock::Create(ctx, "filter8", TraceMemoryFunction); 
    //different path for different funcall
    llvm::BasicBlock *load_branch = llvm::BasicBlock::Create(ctx, "loadcase", TraceMemoryFunction);
    llvm::BasicBlock *store_branch = llvm::BasicBlock::Create(ctx, "storecase", TraceMemoryFunction);
    llvm::BasicBlock *func_branch = llvm::BasicBlock::Create(ctx, "funccase", TraceMemoryFunction);
#endif
    llvm::BasicBlock *return_block = llvm::BasicBlock::Create(ctx, "returnfunc", TraceMemoryFunction);
    IRBuilder<> Builder(ctx);
    Value* str_ptr;

    Builder.SetInsertPoint(before_init);
    LoadInst* load_address = Builder.CreateLoad(Type::getInt64Ty(ctx), glb);
    Value* if_init = Builder.CreateICmpEQ(load_address, Builder.getInt64(0));
    Builder.CreateCondBr(if_init, return_block, BB);
    Builder.SetInsertPoint(BB);
    Value* orig_arg = TraceMemoryFunction->getArg(0);
    Value* cast_arg = Builder.CreatePtrToInt(orig_arg, Builder.getInt64Ty());
    Value* cmp_address = Builder.CreateICmpUGE(load_address, cast_arg);
    Builder.CreateCondBr(cmp_address, return_block, filter_branch);

    Builder.SetInsertPoint(filter_branch);
    LoadInst* load_end = Builder.CreateLoad(Type::getInt64Ty(ctx), glb_end);
    Value* cmp_len = Builder.CreateICmpULE(cast_arg, load_end);
#ifdef FILE_ADDRESS
    Builder.CreateCondBr(cmp_len, file_branch, dram_branch);
#else
    Builder.CreateCondBr(cmp_len, for_branch, return_block);
#endif


#ifdef FILE_ADDRESS
    //if address is valid, record message in static file
    Builder.SetInsertPoint(file_branch);
    //function_name-inst_offset-load_store_func_flag-access_len
    //TODO add access_addr

    // Constant *file_store_str = ConstantDataArray::getString(ctx, "%s-%d-%d-%ld-%p\n");
    // // Constant *file_store_str = ConstantDataArray::getString(ctx, "%s\n");
    // Constant *file_store = M.getOrInsertGlobal("file_store_str", file_store_str->getType());
    // dyn_cast<GlobalVariable>(file_store)->setInitializer(file_store_str);
    // Value* var_store_stupid = Builder.CreatePointerCast(file_store, Type::getInt8PtrTy(ctx), "FileValue");
    auto var_store_stupid = Builder.CreateGlobalStringPtr("%s-%d-%d-%ld-%p\n");
    tryFileFilter(M, TraceMemoryFunction, file_branch, for_branch, var_store_stupid, 0);

    // CreateFprintfCall(Builder, TraceMemoryFunction, M, var_store_stupid);
    // Builder.CreateBr(for_branch);


#endif
    //create forloop function
#ifdef OUTPUT_ADDRESS
    CreateCheckLogic(M, TraceMemoryFunction, filter_branch3, for_branch, cast_arg);
#else
    CreateCheckLogic(M, TraceMemoryFunction, return_block, for_branch, cast_arg);
#endif

#ifdef OUTPUT_ADDRESS
    Builder.SetInsertPoint(filter_branch3);
    //8 byte check, for Pmem behavior observation
    // Value* cmp_byte8 = Builder.CreateICmpUGE(Builder.getInt64(8), TraceMemoryFunction->getArg(1));
    // Builder.CreateCondBr(cmp_byte8, filter_branch2, return_block);

    // Builder.SetInsertPoint(filter_branch2);
    //here add check logic

    // LoadInst* load_value = Builder.CreateLoad(Type::getInt64Ty(ctx), orig_arg);
    //for loop to check whole len


    //1 for load, 0 for store, 2 for function call
    Value* cmp_result = Builder.CreateICmpNE(TraceMemoryFunction->getArg(2), Builder.getInt32(0));
    Builder.CreateCondBr(cmp_result, filter_branch2, store_branch);
    Builder.SetInsertPoint(filter_branch2);
    Value* cmp_result2 = Builder.CreateICmpNE(TraceMemoryFunction->getArg(2), Builder.getInt32(1));
    Builder.CreateCondBr(cmp_result2, func_branch, load_branch);

    Builder.SetInsertPoint(load_branch);
    //load case
    //add const str
    Constant *load_str = ConstantDataArray::getString(ctx, "load from %p address len is %ld, global value is %lx, output from func %s line %ld\n");
    Constant *Var_load = M.getOrInsertGlobal("load_str", load_str->getType());
    dyn_cast<GlobalVariable>(Var_load)->setInitializer(load_str);
    str_ptr = Builder.CreatePointerCast(Var_load, Type::getInt8PtrTy(ctx), "Strptr");
    //jmp to output case
  
    CreatePrintfCall(Builder, TraceMemoryFunction, M, str_ptr);
    Builder.CreateBr(return_block);


    Builder.SetInsertPoint(store_branch);
    //store case
     //add const str
    Constant *store_str = ConstantDataArray::getString(ctx, "store to %p address len is %ld, global value is %lx, output from func %s line %ld\n");
    Constant *Var_store = M.getOrInsertGlobal("store_str", store_str->getType());
    dyn_cast<GlobalVariable>(Var_store)->setInitializer(store_str);
    str_ptr = Builder.CreatePointerCast(Var_store, Type::getInt8PtrTy(ctx), "Strptr");
    //jmp to output case

    CreatePrintfCall(Builder, TraceMemoryFunction, M, str_ptr);
    Builder.CreateBr(return_block);




    Builder.SetInsertPoint(func_branch);
     //funcall case
    Constant *funccall_str = ConstantDataArray::getString(ctx, "funccall to %p address len is %ld, global value is %lx, output from func %s line %ld\n");
    Constant *Var_funccall = M.getOrInsertGlobal("funccall_str", funccall_str->getType());
    dyn_cast<GlobalVariable>(Var_funccall)->setInitializer(funccall_str);
    str_ptr = Builder.CreatePointerCast(Var_funccall, Type::getInt8PtrTy(ctx), "Strptr");
    //jmp to output case
    CreatePrintfCall(Builder, TraceMemoryFunction, M, str_ptr);
    Builder.CreateBr(return_block);

// #ifdef FILE_ADDRESS
//     Constant *file_store_str = ConstantDataArray::getString(ctx, "%s\n");
//     Constant *file_store = M.getOrInsertGlobal("file_store_str", file_store_str->getType());
//     dyn_cast<GlobalVariable>(file_store)->setInitializer(file_store_str);
//     Value* var_store_stupid = Builder.CreatePointerCast(file_store, Type::getInt8PtrTy(ctx), "FileValue");
//     CreateFprintfCall(Builder, TraceMemoryFunction, M, var_store_stupid);
// #endif

#endif
    //TODO add file operation for DRAM case
#ifdef FILE_ADDRESS
    //if dram ptr is 0, return directly.

    tryFileFilter(M, TraceMemoryFunction, dram_branch, dram_unlock, var_store_stupid, 1);
    Builder.SetInsertPoint(dram_unlock);
    Builder.CreateBr(return_block);
#endif
    

    Builder.SetInsertPoint(return_block);
    
    // CreatePrintfCall(Builder, TraceMemoryFunction, M, str_ptr);
    Builder.CreateRetVoid();
  }




  inline Value* setGlobalptr(IRBuilder<> &builder, std::string glb_tag, Type* ty, llvm::Module &M){
    auto ptr_inst = builder.CreateAlloca(PointerType::getUnqual(ty));
    GlobalVariable* tag_variable = M.getGlobalVariable(glb_tag);
    builder.CreateStore(tag_variable, ptr_inst);
    return ptr_inst;
  }

  void instrumentFuncall(llvm::Module &M, Instruction &I, size_t operation_flag, int inst_offset, int func_flag=false, int inst_count=100, int tag_offset=0){
    //use operation flag to distinguish l/s and mem_func call
    LLVMContext &ctx = M.getContext();
    const DataLayout *dl = &M.getDataLayout();
    //get memtrace func first
    //params: load/store_address, access_len, load/store_flag, function_name_ptr, lineofcode, inst_offset, tag_ptr, tag_offset
    std::vector<Type*> traceargs{
      PointerType::getUnqual(Type::getInt8Ty(ctx)), Type::getInt64Ty(ctx), Type::getInt32Ty(ctx), 
      PointerType::getUnqual(Type::getInt8Ty(ctx)), Type::getInt64Ty(ctx), Type::getInt32Ty(ctx),
      PointerType::getUnqual(Type::getInt8Ty(ctx))
    };

    FunctionType* tracememtype = FunctionType::get(Type::getVoidTy(ctx), traceargs, false);
    FunctionCallee TraceMemory = M.getOrInsertFunction(target_func, tracememtype);
    Function* fn_name = I.getFunction();
    IRBuilder<> Builder(&I);
    Value* func_name;
    Value* func_array;
    StringRef func_name_ref = fn_name->getName(); //func_name_ref is used for printf param
    std::string global_tail = std::to_string(operation_flag);
    std::string global_store = global_base + global_tail;
#ifndef MUTEX

    //global tag is used to track whther inst has been marked yet.
    std::string global_tag = global_base + func_name_ref.data();
#endif
    //first search for exist
    Constant* valStr = M.getNamedGlobal(global_store.c_str());
    // bool found_global;
    if(valStr == nullptr)
    {
      //if not exist, than create new one
      // found_global = false;
      Value* shitStr = Builder.CreateGlobalString(func_name_ref, global_store.c_str());
      func_name = Builder.CreatePointerCast(shitStr, Type::getInt8PtrTy(ctx), "fncp");
      initGlobaladdress(M, global_tag, 2, inst_count);
    }
    else
    {
      //TODO add use global string logic
      func_name = Builder.CreatePointerCast(valStr, traceargs[3], "exist_value_ptr");
      // found_global = true;
      // errs()<<"global founded! "<<"\n";
    }
    // Value* func_name = Builder.CreateGlobalString(func_name_ref, "func_name_ref");
    GlobalVariable* inst_array_t = M.getNamedGlobal(global_tag);
    auto array_t = llvm::ArrayType::get(Type::getInt8Ty(ctx), inst_count);
    func_array = Builder.CreateConstInBoundsGEP2_64(array_t, inst_array_t, 0 ,tag_offset);
    Value* ptr = nullptr;
    Value* op_flag;
    Value* real_size;
    CallInst* memfunc_call;
    //value only avalible after the inst.
    // Value* value2print;
    // Value* cast64;
    size_t access_size = 0;
    if(llvm::LoadInst* load = dyn_cast<llvm::LoadInst>(&I))
    {
      ptr = load->getPointerOperand();
      auto ty = load->getType();
      access_size = dl->getTypeAllocSize(ty);
      op_flag = Builder.getInt32(1);
      real_size = Builder.getInt64(access_size);
      // value2print = &I;
    }
      
    else if(llvm::StoreInst* store = dyn_cast<llvm::StoreInst>(&I))
    {
      ptr = store->getPointerOperand();
      auto ty = store->getValueOperand()->getType();
      access_size = dl->getTypeAllocSize(ty);
      op_flag = Builder.getInt32(0);
      real_size = Builder.getInt64(access_size);
      // value2print = store->getOperand(0);
    }
    else
    {
      if(func_flag)
      {
        op_flag = Builder.getInt32(2);
        memfunc_call = dyn_cast<CallInst>(&I);
        ptr = memfunc_call->getArgOperand(0);
        if(func_flag == 12)
          real_size = memfunc_call->getArgOperand(1);
        else
          real_size = memfunc_call->getArgOperand(2);
      }
      else
      {
        errs()<<"unknown instruction !!!"<<"\n";
        return;
      }
      
    }
    // size_t access_size = 0;
    // Type* ty = ptr->getType();
    // bool should_cast = value2print->getType()->isPointerTy();
    // if(should_cast)
    //   cast64 = Builder.CreatePtrToInt(value2print, traceargs[3], "cast64");
    // else
    //   cast64 = Builder.CreateIntCast(value2print, traceargs[3], false, "cast64");

    // if(auto *ptrty = dyn_cast<PointerType>(ty))
    // {
    //   //change this to llvm 16 version
    //   // ty = ptrty->getPointerElementType();
    //   // access_size = dl->getTypeAllocSize(ty);
    //   // access_size = dl->getTypeStoreSize(ty);
    //   access_size = 4;
    // }
    // real_size = Builder.getInt64(access_size);

    // if(!found_global)
    //   Builder.CreateCall(TraceMemory, {ptr, real_size,  op_flag, func_name});
    // else
    const DebugLoc & line_output = I.getDebugLoc();
    size_t line_code = 0;
    if(line_output)
    {
      line_code = line_output.getLine();
      // real_size = Builder.getInt64(line_loc);
    }
    auto lc_arg = Builder.getInt64(line_code);
    auto offset_arg = Builder.getInt32(inst_offset);
    auto tag_arg = Builder.getInt32(tag_offset);
    Builder.CreateCall(TraceMemory, {ptr, real_size, op_flag, func_name, lc_arg, offset_arg, func_array});
    if(func_flag == 1)// maybe 1 extra check for sorce address
    {
      Value* src_ptr = memfunc_call->getArgOperand(1);
      op_flag = Builder.getInt32(3);
      Builder.CreateCall(TraceMemory, {src_ptr, real_size, op_flag, func_name, lc_arg, offset_arg, func_array});
    }
    // else if(func_flag == 12)
    // {
    //   Value* src_ptr = memfunc_call->getArgOperand(3);
    //   op_flag = Builder.getInt32(4);
    //   Builder.CreateCall(TraceMemory, {src_ptr, real_size, op_flag, func_name, lc_arg, offset_arg, func_array});


    // }
    // if(func_name_ref == "main" && this_line)
    // {
    //   auto line_loc = this_line.getLine();
    //   auto linescope = this_line.getScope();
    //   errs()<<func_name_ref<<"line loc : "<<line_loc<<" "<<linescope<<"\n";
    // }
    // Builder.CreateLoad(Type::getInt8Ty(ctx), memaddress);
  }

  void operateGlobal(llvm::Module&M, Function &F, Instruction &I, CallInst* func_called, int len_param = 2){
    // auto args0 = F.arg_begin();
    // args0->
    auto func_call = func_called;
    Value* func_return = func_call;
    // Value* func_arg0 = func_call->getArgOperand(0);
    Value* pmem_len = func_call->getArgOperand(len_param);
    Value* func_operand = func_call->getCalledOperand();
    LLVMContext &ctx = M.getContext();
    IRBuilder<> builder(I.getNextNonDebugInstruction());
    GlobalVariable* glb = M.getNamedGlobal(global_addr); 
    // LoadInst* load_global =  builder.CreateLoad(Type::getInt64Ty(ctx), glb);

    Value* get_function = func_call->getCalledFunction();
    Value* arg2value = builder.CreateBitCast(func_call, builder.getInt8PtrTy());
    Value* arg2int = builder.CreatePtrToInt(arg2value, builder.getInt64Ty());
    errs() << "output value is "<< func_return<<" \n";
    errs() << "output arg0 is "<< get_function<<" \n";
    errs() << "output args called is "<< func_operand << "\n";
    // Value* normal_value_return = builder.CreatePtrToInt(func_return, builder.getInt64Ty());
    // errs()<<"norm al return "<<normal_value_return <<" \n";
    builder.CreateStore(arg2int, glb);

    GlobalVariable* glb_end = M.getNamedGlobal(global_end);
    LoadInst* load_previous = builder.CreateLoad(Type::getInt64Ty(ctx), glb);
    Value* add_result = builder.CreateAdd(load_previous, pmem_len);
    builder.CreateStore(add_result, glb_end);
    Function* old_func = I.getFunction();
    // addGlobalFileOpen(M,  *(old_func), builder);
    //create add and store end address
   
    // LoadInst* load_after = builder.CreateLoad(Type::getInt64Ty(ctx), glb);
    // std::vector<Type*> param4printf{Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx)};
    // Type* return_type = Type::getVoidTy(ctx);
    // FunctionType* print_func = FunctionType::get(return_type, param4printf, false);
    // FunctionCallee fc_printf = M.getOrInsertFunction("printf", print_func);
    // Constant* output_global = ConstantDataArray::getString(ctx, "output from global %lx\n");
    // Constant* output_var = M.getOrInsertGlobal("output_global", output_global->getType());
    // dyn_cast<GlobalVariable>(output_var)->setInitializer(output_global);
    // Value* str_ptr = builder.CreatePointerCast(output_var, param4printf[0], "loopstrPtr");
    // builder.CreateCall(fc_printf, {str_ptr, load_after});

    //add enable FPE function call (used for floatzone)
#ifdef FLOATZONE
    std::vector<Type*> param4floate{Type::getInt32Ty(ctx)};
    Type* float_rtype = Type::getInt32Ty(ctx);
    FunctionType* float_init = FunctionType::get(float_rtype, param4floate, false);
    FunctionCallee fennable = M.getOrInsertFunction("feenableexcept", float_init);
    if(fennable)
      builder.CreateCall(fennable, {builder.getInt32(0x10)});
    else
      errs()<<"fail to add float init function"<<"\n";
#endif
    //call pthread init to init lock 
    std::vector<Type*> param4pthread{PointerType::getUnqual(Type::getInt8Ty(ctx)), PointerType::getUnqual(Type::getInt8Ty(ctx))};
    Type* pthread_rtype = Type::getInt32Ty(ctx);
    FunctionType* pthread_init = FunctionType::get(pthread_rtype, param4pthread, false);
    FunctionCallee ptd_init = M.getOrInsertFunction("pthread_mutex_init", pthread_init);
    if(ptd_init)
    {
      for(int i=0; i<2; i++)
      {
        auto array_type_char = llvm::ArrayType::get(Type::getInt8Ty(ctx), 40);
        GlobalVariable* glb_lock = M.getGlobalVariable(global_lock_base + std::to_string(i));
        auto ptr_char = builder.CreateConstInBoundsGEP2_64(array_type_char, glb_lock, 0, 0);
        Value* stupid_null = builder.getInt64(0);
        Value* null_ptr = builder.CreateBitCast(stupid_null, PointerType::getUnqual(Type::getInt8Ty(ctx)));
        builder.CreateCall(ptd_init, {ptr_char, null_ptr});
      }

    }
    else
      errs()<<"fail to init pthread mutext init "<<"\n";


  }



  void operateGlobalInvoke(llvm::Module&M, Function &F, Instruction &I, InvokeInst* func_call){
    // auto args0 = F.arg_begin();
    // args0->
    // Value* func_return = func_call;
    Value* func_arg0 = func_call->getArgOperand(0);
    Value* pmem_len = func_call->getArgOperand(2);
    Value* arg2value;
    Value* arg2int;
    // Value* func_operand = func_call->getCalledOperand();
    LLVMContext &ctx = M.getContext();
    //invoke call need to choose the normal jmp target for IRBuilder
    BasicBlock* bb = func_call->getNormalDest();
    auto II = bb->getFirstNonPHI();
    IRBuilder<> builder(II);

    addGlobalFileOpen(M, F, builder);
    addGlobalFileOpen(M, F, builder, 1);
    // int iter_times = 10;
    // for(int i=0; i<iter_times; i++)
    // {
    //   II = II->getNextNonDebugInstruction(); 
    //   errs()<<"error is "<<II<<"\n";
    // }
    // builder.SetInsertPoint(II->getNextNonDebugInstruction());
    GlobalVariable* glb = M.getNamedGlobal(global_addr);


    arg2value = builder.CreateBitCast(func_call, builder.getInt8PtrTy());
    arg2int = builder.CreatePtrToInt(arg2value, builder.getInt64Ty());
    // errs() << "output value is "<< func_return<<" \n";
    // errs() << "output arg0 is "<< get_function<<" \n";
    // errs() << "output invoke args called is "<< func_operand << "\n";
    // Value* normal_value_return = builder.CreatePtrToInt(func_return, builder.getInt64Ty());
    // errs()<<"norm al return "<<normal_value_return <<" \n";
    builder.CreateStore(arg2int, glb);

    GlobalVariable* glb_end = M.getNamedGlobal(global_end);
    LoadInst* load_previous = builder.CreateLoad(Type::getInt64Ty(ctx), glb);
    Value* add_result = builder.CreateAdd(load_previous, pmem_len);
    builder.CreateStore(add_result, glb_end);
    //create add and store end address


  }


  struct debug_iter{
    Instruction* _II;
    Function* _FF;
    int _offset;
    int func_flag;//used for wrapped memaccess
    int _offset2;
  };  

  //in this pass, we need to filter all non-concern function
  //in this pass
	llvm::PreservedAnalyses run(llvm::Module &M,
				llvm::ModuleAnalysisManager &) {
		errs() << "In here\n\n";
    bool init_flag = false;
    bool init_file_flag = false;
    Function* main_func;
    std::vector<Instruction*> del_vec;
    std::unordered_map<std::string, int> function_id;
    std::unordered_map<std::string, int> function_inst_count;
    size_t global_offset = 1;

    Instruction* invoke_inst = nullptr;
    InvokeInst* invoke_func = nullptr;
    Function* invoke_fn = nullptr;
    
    
   
    std::vector<debug_iter> debug_vec;
    
    // initGlobaladdress(M, global_addr);
    // initGlobaladdress(M, global_end);
    // initGlobaladdress(M, global_fileptr, 1);
    //insert ls into vector before everything
    //TODO add check logic for memcpy function


    
    for(auto &F: M)
    {
      int offset_ls = 0;
      int offset_array = 0;
      for(auto &B : F)
      {
        for(auto &I : B)
        {
          offset_ls++;
          if(I.getOpcode() == Instruction::Load || I.getOpcode() == Instruction::Store)
          {
            debug_iter di1;
            di1._II = &I;
            di1._FF = &F;
            di1._offset = offset_ls;
            di1._offset2 = offset_array;
            di1.func_flag = false;
            debug_vec.push_back(di1);
            offset_array++;
          }
          else if(CallInst* func_call = dyn_cast<CallInst>(&I))
          {
            auto memfn = func_call->getCalledFunction();
            if(memfn != NULL)
            {
              StringRef memfn_name = memfn->getName();
              debug_iter di1;
              di1._II = &I;
              di1._FF = &F;
              di1._offset = offset_ls;
              if(memfn_name == "llvm.memcpy.p0.p0.i64" || memfn_name == "llvm.memmove.p0.p0.i64" 
                  || memfn_name == "strncpy" || memfn_name == "strncat" || memfn_name == "snprintf")
              {
#ifdef OUTPUT_ADDRESS
                const DebugLoc& line_memcpy = I.getDebugLoc();
                size_t line_out = 0;
                if(line_memcpy)
                  line_out = line_memcpy.getLine();
                errs()<<"yes we got output from "<<line_out<<"\n";
#endif
               
                di1.func_flag = true;
                if(memfn_name == "snprintf")
                  di1.func_flag = 12;
                di1._offset2 = offset_array;
                debug_vec.push_back(di1);
                offset_array += 2;
              }
              else if(memfn_name == "llvm.memset.p0.i64")
              {
                di1.func_flag = 10;
                di1._offset2 = offset_array;
                debug_vec.push_back(di1);
                offset_array += 2;
              }
            }
          }
        }
      }
      std::string func_name(F.getName().data());
      function_inst_count[func_name] = offset_array;
    }


    initGlobaladdress(M, global_addr);
    initGlobaladdress(M, global_end);
    for(int i=0; i<2; i++)
    {
      initGlobaladdress(M, global_counter_base + std::to_string(i));
      initGlobaladdress(M, global_fileptr_base + std::to_string(i), 1);
      initGlobaladdress(M, global_lock_base + std::to_string(i), 2);
    }
    
    CreateFunction(M);
    
    for(auto &F: M)
    {
      int offset_ls = 0;
      if(F.getName() == "main")
      {

        std::string func_name(F.getName().data());
        function_id[func_name] = global_offset++;
        Function* main_func = &F;
        std::cout<<"found main func here "<<std::endl;
        for(auto &B : *(main_func)){
          for(auto &I : B){
            // if(!init_file_flag)
            // {
            //   initGlobaladdress(M, global_fileptr, 1);
            //   IRBuilder<> builder(I.getNextNonDebugInstruction());
            //   addGlobalFileOpen(M, F, builder);
            //   init_file_flag = true;
            // }
            if(CallInst* func_call = dyn_cast<CallInst>(&I))
            {
              // if(!init_flag)
              {
                Function* fn = func_call->getCalledFunction();
                if(fn != NULL)
                {
                  StringRef fn_name = fn->getName();
                  // operateGlobal(M, *(fn), I);
                  if(fn_name == pmem_pmdk.c_str())
                  {
                    errs() << "output func is " << fn_name << "arg0 is "<< func_call->getArgOperand(0) << "\n";
                    init_flag = true;
                    // Value* return_value = func_call;
                    // errs() << " value is "<<return_value<<"\n";

                    IRBuilder<> builder(&I);
                    addGlobalFileOpen(M, F, builder, 0);
                    addGlobalFileOpen(M, F, builder, 1);
                    // CreateFunction(M);
   
                    // addGlobalFileOpen(M, *(fn));
                    operateGlobal(M, *(fn), I, func_call);
                  }
                  else if(fn_name == pmem_nopmdk.c_str())
                  {
                    errs() <<"output func is "<<fn_name <<"arg0 is "<< func_call->getArgOperand(0) <<"\n";
                    auto if_created_func = M.getFunction("_TraceMemory");
                    if(!if_created_func)
                    {
                      errs() <<"find mmap and init use mmap parameter!"<<"\n";
                      init_flag = true;
                      //mmap size arg is arg(1)
                      operateGlobal(M, *(fn), I, func_call, 1);
                    }
                  }
                }
              }
            }
          }
        }
      }
      else if(F.getName() == "_TraceMemory")
        continue;
      else //normal function 
      {
        // errs() <<"output func "<<F.getName()<<"\n";
        std::string str_name(F.getName().data());
        function_id[str_name] = global_offset++;
        for(auto &B : F)
        {
          for(auto &I : B)
          {
            if(!init_flag)
            {
              
              if(CallInst* func_call = dyn_cast<CallInst>(&I))
              {
                Function* fn = func_call->getCalledFunction();
                if(fn != NULL)
                {
                  StringRef fnc_name = fn->getName();
                  
                  if(fnc_name == pmem_pmdk.c_str())
                  {
                    errs() << "output func in call func " << fnc_name << "arg0 is "<< func_call->getArgOperand(0) << "\n";
                    init_flag = true;
                    // Value* return_value = func_call;
                    // errs() << " value is "<<return_value<<"\n";
                    IRBuilder<> builder(I.getNextNonDebugInstruction());
                    addGlobalFileOpen(M, F, builder);
                    addGlobalFileOpen(M, F, builder, 1);
                    // addGlobalFileOpen(M, *(fn));
                    operateGlobal(M, *(fn), I, func_call);
                  }
                  else if(fnc_name == pmem_nopmdk.c_str())
                  {
                    errs() <<"output func is "<<fnc_name <<"arg0 is "<< func_call->getArgOperand(0) <<"\n";
                    auto if_created_func = M.getFunction("_TraceMemory");
                    if(!if_created_func)
                    {
                      errs() <<"find mmap and init use mmap parameter! but not in main!!!"<<"\n";
                      init_flag = true;
                      IRBuilder<> builder(I.getNextNonDebugInstruction());
                      addGlobalFileOpen(M, F, builder);
                      addGlobalFileOpen(M, F, builder, 1);
                      //mmap size arg is arg(1)
                      operateGlobal(M, *(fn), I, func_call, 1);
                    }
                  }
                }
              }
              else if(InvokeInst* func_invoke = dyn_cast<InvokeInst>(&I))
              {
                Function* fn = func_invoke->getCalledFunction();
                invoke_fn = fn;
                invoke_func = func_invoke;
                if(fn != NULL)
                {
                  StringRef fnc_name = fn->getName();
                  // errs() << "output func is " << fnc_name << "\n";
                  if(fnc_name == pmem_pmdk.c_str())
                  {
                    errs() << "output func in invoke func " << fnc_name << " arg0 is "<< func_invoke->getArgOperand(2) << "\n";
                    init_flag = true;
                    
                    // Value* return_value = func_call;
                    // errs() << " value is "<<return_value<<"\n";
                    invoke_inst = &I;
                  }//pm_init_function
                }//fn!=NULL
              }//invoke case
            }//init flag
          }// I : B
        }// B : F
      }//not trace nor main
    }// F : M
    //handle invoke init pmemobj last
    for(auto iter : debug_vec)
    {
      // StringRef func_name = iter._FF->getName();
      // errs() << "now executing func "<<  func_name << "\n";
      StringRef func_aname = iter._FF->getName();
      size_t test_value = function_id[func_aname.data()];
      if(test_value !=  0)
      {
        //init global address for inst tag
        //tag_value; funcname_instoffset
        instrumentFuncall(M, *(iter._II), test_value, iter._offset, iter.func_flag, function_inst_count[func_aname.data()], iter._offset2);

      }
      else
      {
        errs()<<"not found function named "<<func_aname << "\n";

      }
      // iter->eraseFromParent();
    }




    if(invoke_inst != nullptr)
    { 

      operateGlobalInvoke(M, *(invoke_fn), *(invoke_inst), invoke_func);
      errs()<<"operate invoke finish!"<<"\n";
    }

    return llvm::PreservedAnalyses::none();
		// return llvm::PreservedAnalyses::all();
	}

};
} // namespace





llvm::PassPluginLibraryInfo getMemoryTracePluginInfo() {
	return {LLVM_PLUGIN_API_VERSION, "MemoryTrace", LLVM_VERSION_STRING,
		[](PassBuilder &PB) {
			PB.registerPipelineParsingCallback(
				[](StringRef Name, ModulePassManager &MPM,
				ArrayRef<PassBuilder::PipelineElement>) {
					if (Name == "memory-trace") {
						MPM.addPass(MemoryTrace());
						return true;
					}

					return false;
				}
			);
		}};
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  printf("optimizing use second pass!\n");
  return getMemoryTracePluginInfo();
}