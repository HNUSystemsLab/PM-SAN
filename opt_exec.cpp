#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <fstream>
#include <iostream>
#include <string>
#include <dirent.h>

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;

char* cc_params[8];              /* Parameters passed to the real CC  */
static int  cc_par_cnt = 1;         /* Param count, including argv0      */

/* Copy argv to cc_params, making the necessary edits. */
// opt -load-pass-plugin /home/cwk/cwk/noname/llvm_try/llvmhello.so -passes=memory-trace *.ll -S -o modified_*.ll


static char** target_files;
static int target_opt_count = 0;


static void edit_params(const char* path, const char* ir_file) {
  // cc_params = (char**)calloc((argc + 128), sizeof(char*));
  cc_params[0] = "opt";
  // cc_params[cc_par_cnt++] = "-ldl";
  cc_params[cc_par_cnt++] = "-load-pass-plugin";
  cc_params[cc_par_cnt++] = "/home/cwk/cwk/noname/llvm_try/llvmhello.so";
  cc_params[cc_par_cnt++] = "-passes=memory-trace";
  char path_ir[100]="";
  sprintf(path_ir, "%s/%s", path, ir_file);
  memcpy(cc_params[cc_par_cnt], path_ir, 100);
  cc_par_cnt++;
  // cc_params[cc_par_cnt++] = path_ir;
  cc_params[cc_par_cnt++] = "-S";
  cc_params[cc_par_cnt++] = "-o";
  char output_ir[100] ="";
  sprintf(output_ir, "%s/modified_%s", path, ir_file);
  // std::cout<<"path ir is "<<path_ir<<std::endl;
  // std::cout<<"output ir is " << output_ir<<std::endl;
  memcpy(cc_params[cc_par_cnt], output_ir, 100);
  // cc_par_cnt++;
  // cc_params[cc_par_cnt++] = output_ir;

  cc_par_cnt = 1;
  // cc_params[cc_par_cnt++] = "/opt/rezzan/rezzan.so";

  // while (--argc) {
  //   char* cur = *(++argv);
  //   cc_params[cc_par_cnt++] = cur;
  // }
  // cc_params[cc_par_cnt] = NULL;
}



void scan_file(const char* path){
  DIR* dir = opendir(path);
  if(dir == NULL)
  {
    std::cout<<"dir not exist"<<std::endl;
    return;
  }
  struct dirent* dirptr = NULL;
  while((dirptr = readdir(dir)) != nullptr)
  {
    if(strcmp(dirptr->d_name, ".") !=0 && strcmp(dirptr->d_name, "..") !=0)
    {
      std::string file_name(dirptr->d_name);
      std::string last_name;
      // std::string last_name = file_name.substr(file_name.find_last_of("." + 1));
      int last_pos = file_name.find_last_of('.');
      if(last_pos>0)
      {
        last_name = file_name.substr(last_pos);
        if(strcmp(last_name.data(), ".ll") == 0)
        {
          //collect such file to opt
          char output_ir[50] = "";
          sprintf(output_ir, "modified_%s",  file_name.data());
          std::cout << "d_ino: " << dirptr->d_ino << " d_off: " << dirptr->d_off << " d_name: " << dirptr->d_name <<" "<< output_ir << std::endl;
          edit_params(path, file_name.c_str());
          for(int i=0; i<8; i++)
            printf("exe output is %s\n", cc_params[i]);
          if(fork() == 0)
          {
            int result = execvp(cc_params[0], (char**)cc_params);
            std::cout<<" output result is "<<result<<std::endl;
          } 
            
          // char* shabi[2];
          // shabi[0] = "opt";
          // shabi[1] = "opt -load-pass-plugin /home/cwk/cwk/noname/llvm_try/llvmhello.so -passes=memory-trace ./ART/N16.ll -S -o ./ART/modifiedfuck_N16.ll";
          // int result = execvp(shabi[0], (char**)shabi);
          
        }
      }
    }
  }
  closedir(dir);
}





/* Main entry point */

int main(int argc, char** argv) {

  cc_params[4] = (char*)malloc(100);
  memset(cc_params[4], 0, 100);
  cc_params[7] = (char*)malloc(100);
  memset(cc_params[7], 0 ,100);
  // for(int i=0; i<cc_par_cnt; i++)
  //   printf("exe output is %s\n", cc_params[i]);
  scan_file(argv[1]);
  // edit_params(argv[1], argv[1]);
  // execvp(cc_params[0], (char**)cc_params);
  return 0;
}
