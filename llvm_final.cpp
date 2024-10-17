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
#include <fstream>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>

//this pass is used for long-run sanitize check.

using namespace llvm;

static std::string global_addr("start_address");
static std::string global_end("end_address");
static std::string target_func("_TraceMemory");
static std::string slow_func("_Traceslow");
static std::string global_base("global_addr_");
static std::string pmem_pmdk("pmemobj_create");
static std::string pmem_nopmdk("mmap");
const char* filter_pmem = "/home/cwk/cwk/noname/llvm_try/filterpmem";
const char* filter_dram = "/home/cwk/cwk/noname/llvm_try/filterdram";
static size_t freed_value = 0xfdfdfdfdfdfdfdfd;
static size_t red_value = 0xfafafafafafafafa;
static uint32_t free4_value = 0xfdfdfdfd;
static uint32_t red4_value = 0xfafafafa;
static uint32_t red_floatvalue =  0x0b8b8b8aULL;
size_t trace_count = 0;
// #define OUTPUT_ADDRESS
// #define FLOATZONE
// #define CONFIRM_ADDRESS
// #define CHECKMERGE
//configurable filter function
//pair:first for inst offset, second for mem_funcall parameter pos


struct stupid_st{
  int _op_flag;
  int _op_len;
  size_t _op_address;
  int _inst_offset;
  int master;//merge_main inst or not
  bool merged = false;
};

std::unordered_map<std::string, std::unordered_set<size_t>> filter_function;
std::unordered_map<std::string, std::vector<struct stupid_st>> stupid_map;
std::unordered_map<std::string, std::unordered_set<size_t>> dram_function;


namespace {
struct MemoryTrace : public llvm::PassInfoMixin<MemoryTrace> {
  void initGlobaladdress(llvm::Module& M, std::string global_name){
    auto &ctx = M.getContext();
    M.getOrInsertGlobal(global_name, Type::getInt64Ty(ctx));
                              // PointerType::getUnqual(Type::getInt8Ty(ctx)));

    GlobalVariable *namedGlobal = M.getNamedGlobal(global_name);
    namedGlobal->setLinkage(GlobalValue::LinkOnceAnyLinkage);
    namedGlobal->setInitializer(llvm::ConstantInt::get(Type::getInt64Ty(ctx), 114514));
  }



  //output function 
  void CreatePrintfCall(IRBuilder<> &builder, Function *func, Module& M, Value* const_value){
    LLVMContext &ctx = M.getContext();
    // printf("helloworld from address %lx\n", address);
    std::vector<Type*> param4output{Type::getInt8PtrTy(ctx), Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx), Type::getInt64Ty(ctx),
                                    PointerType::getUnqual(Type::getInt8Ty(ctx)), Type::getInt64Ty(ctx)};
    
    Type* output_type = Type::getVoidTy(ctx);
    FunctionType* add_func = FunctionType::get(output_type, param4output, false);
    FunctionCallee fc_printf = M.getOrInsertFunction("printf", add_func);
    
    // Constant *store_str = ConstantDataArray::getString(ctx, "store from %p address value %lx, global value is %lx\n");
   
    // Constant *storeVar = M.getOrInsertGlobal("stroe_str", store_str->getType());
    
    // dyn_cast<Globalvariable>(stroeVar)->setInitializer(store_str);
    //choose different path to output different value
    // Value* strptr;
    //load case
    // strptr = builder.CreatePointerCast(loadVar, param4output[0], "loadStrPtr");

    //store case
    // strptr = builder.CreatePointerCast(storeVar, param4output[0], "loadStrPtr");
    GlobalVariable* global_value = M.getNamedGlobal(global_addr);
    LoadInst* load_global =  builder.CreateLoad(Type::getInt64Ty(ctx), global_value);
    builder.CreateCall(fc_printf, {const_value, func->getArg(0), func->getArg(1), load_global, func->getArg(3), func->getArg(4)});

  }




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
    //increment i
    //test output for loop
    Value* address_intptr = Builder.CreateIntToPtr(Builder.CreateLoad(Type::getInt64Ty(ctx), address_temp), PointerType::getUnqual(Type::getInt32Ty(ctx)));
    // Value* origin_value = Builder.CreateLoad(Type::getInt8PtrTy(ctx), address_ptr);
    // Value* value2print;
    // bool should_convert = origin_value->getType()->isPointerTy();
    // if(should_convert)
    //   value2print = Builder.CreatePtrToInt(origin_value, Type::getInt64Ty(ctx), "castto64");
    // else
    //   value2print = Builder.CreateIntCast(origin_value, Type::getInt64Ty(ctx), false, "castto64");
   

#ifdef FLOATZONE
    Value* posiend_4 = Builder.CreateLoad(Type::getInt32Ty(ctx), address_intptr);
    Type* floatType = llvm::Type::getFloatTy(ctx);
    Type* floatPtrType = PointerType::get(floatType, 0);
    Value* posien_float = Builder.CreateBitOrPointerCast(address, floatPtrType);
    //following codes are copied from floatzone 
    const fltSemantics & floatSem = floatType->getFltSemantics();
    APFloat addV(floatSem, APInt(32, /*magic value*/  0x0b8b8b8a));
    Value *addVal = ConstantFP::get(floatType, addV);

    

    //
    InlineAsm* test_IA =  InlineAsm::get(
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
    Builder.CreateBr(incres_iter);


#else
    Value* posiend = Builder.CreateLoad(Type::getInt32Ty(ctx), address_intptr);
    // Value* load2int = Builder.CreatePtrToInt(load2int, Type::getInt64Ty(ctx));
    Value* check_result = Builder.CreateICmpEQ(posiend, Builder.getInt32(free4_value));
    Builder.CreateCondBr(check_result, output_error, if_condition2);// output_error, incres_iter);
    Builder.SetInsertPoint(if_condition2);
    Value* if_result2 = Builder.CreateICmpEQ(posiend, Builder.getInt32(red4_value));
    Builder.CreateCondBr(if_result2, output_error, incres_iter);
    Builder.SetInsertPoint(output_error);
    //TODO add function name, add function line of codes, get these from function args;
    std::vector<Type*> param4printf{Type::getInt8PtrTy(ctx), Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx)};
    Type* return_type = Type::getVoidTy(ctx);
    FunctionType* print_func = FunctionType::get(return_type, param4printf, false);
    FunctionCallee fc_printf = M.getOrInsertFunction("printf", print_func);
    // Constant* loop_str = ConstantDataArray::getString(ctx, "mem error from function %s, line %ld\n");
    // // Constant* loop_str = ConstantDataArray::getString(ctx, "output from for loop %ld\n");
    // Constant* loop_var = M.getOrInsertGlobal("loop_str", loop_str->getType());
    // dyn_cast<GlobalVariable>(loop_var)->setInitializer(loop_str);
    // Value* str_ptr = Builder.CreatePointerCast(loop_var, param4printf[0], "loopstrPtr");
    auto str_ptr = Builder.CreateGlobalStringPtr("mem error from function %s, line %ld\n");
    // Builder.CreateCall(fc_printf, {str_ptr, trace_func->getArg(3), trace_func->getArg(4)});
    Builder.CreateBr(incres_iter);

    //TODO: change to 4 byte check (done already)

    //move to next 4 bytes
#endif
    Builder.SetInsertPoint(incres_iter);
    Value* iter_1 = Builder.CreateAdd(Builder.CreateLoad(Type::getInt64Ty(ctx), iter), Builder.getInt64(4));//i+=4
    Value* iter_addr = Builder.CreateAdd(Builder.CreateLoad(Type::getInt64Ty(ctx), address_temp), Builder.getInt64(4));//addr+=4
    
    Builder.CreateStore(iter_1, iter);
    Builder.CreateStore(iter_addr, address_temp);
    Builder.CreateBr(for_begin);//jmp back
    
    // llvm::BasicBlock *for_loop

  }


  //normal check, used for those un-tagged function
  void CreateSlowFunction(llvm::Module& M){
    LLVMContext &ctx = M.getContext();
    //void output_memory(void* address, size_t global_addres, int flag);
    //void tracememory(void* target_address, size_t acccess_flag, size_t access_sz, char* function_name, size_t loc)
    std::vector<Type*> params{Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx), Type::getInt32Ty(ctx), Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx)};
    Type* rettype = Type::getVoidTy(ctx);
    FunctionType* cre_func = FunctionType::get(rettype, params, false);
    FunctionCallee fcl = M.getOrInsertFunction(slow_func.c_str(), cre_func);
    Function *TraceMemoryFunction = dyn_cast<llvm::Function>(fcl.getCallee());
    TraceMemoryFunction->setLinkage(GlobalValue::LinkOnceODRLinkage);
    GlobalVariable* glb = M.getNamedGlobal(global_addr);
    GlobalVariable* glb_end = M.getNamedGlobal(global_end);
    llvm::BasicBlock *BB = llvm::BasicBlock::Create(ctx, "entry", TraceMemoryFunction);
    //if we can't decide whether L/S inst is PMem related or not, we need extra cmp operation in CONFIRM_ADDRESS
    llvm::BasicBlock* filter_branch = llvm::BasicBlock::Create(ctx, "filter", TraceMemoryFunction);
    llvm::BasicBlock *invalid_block = llvm::BasicBlock::Create(ctx, "invlidadd", TraceMemoryFunction);
    llvm::BasicBlock* for_branch = llvm::BasicBlock::Create(ctx, "for_loop", TraceMemoryFunction);
#ifdef OUTPUT_ADDRESS
    llvm::BasicBlock* filter_branch2 = llvm::BasicBlock::Create(ctx, "filter2", TraceMemoryFunction); 
    llvm::BasicBlock* filter_branch3 = llvm::BasicBlock::Create(ctx, "filter3", TraceMemoryFunction);
    //different branch for different funcall
    llvm::BasicBlock *load_branch = llvm::BasicBlock::Create(ctx, "loadcase", TraceMemoryFunction);
    llvm::BasicBlock *store_branch = llvm::BasicBlock::Create(ctx, "storecase", TraceMemoryFunction);
    llvm::BasicBlock *funccall_branch = llvm::BasicBlock::Create(ctx, "funccase", TraceMemoryFunction);
#endif

    llvm::BasicBlock *return_block = llvm::BasicBlock::Create(ctx, "returnfunc", TraceMemoryFunction);
    IRBuilder<> Builder(ctx);
    Value* str_ptr;
    Builder.SetInsertPoint(BB);
    Value* orig_arg = TraceMemoryFunction->getArg(0);
    Value* cast_arg = Builder.CreatePtrToInt(orig_arg, Builder.getInt64Ty());
    // compare the address with original value (should be removed if fine-grid filter pmem is set)
    LoadInst* load_address = Builder.CreateLoad(Type::getInt64Ty(ctx), glb);
   
    Value* cmp_address = Builder.CreateICmpUGE(load_address, cast_arg);
    // Builder.CreateCondBr(cmp_address, return_block, filter_branch);
    Builder.CreateCondBr(cmp_address, invalid_block, filter_branch);
    Builder.SetInsertPoint(filter_branch);
    //add printf call shit we get error!!

    //TODO remove the following 3 lines, since we can be sure the address is definate in PMem with filter file
    LoadInst* load_end = Builder.CreateLoad(Type::getInt64Ty(ctx), glb_end);
    Value* cmp_len = Builder.CreateICmpULE(cast_arg, load_end);
    //  Builder.CreateCondBr(cmp_len, for_branch, return_block);
    Builder.CreateCondBr(cmp_len, for_branch, invalid_block);
    //create forloop function
#ifdef OUTPUT_ADDRESS
    CreateCheckLogic(M, TraceMemoryFunction, filter_branch2, for_branch, cast_arg);
#else
    CreateCheckLogic(M, TraceMemoryFunction, return_block, for_branch, cast_arg);
#endif

#ifdef OUTPUT_ADDRESS

    Builder.SetInsertPoint(filter_branch2);
    //here add check logic
    
    // LoadInst* load_value = Builder.CreateLoad(Type::getInt64Ty(ctx), orig_arg);
    //for loop to check whole len 

    Value* cmp_result = Builder.CreateICmpNE(TraceMemoryFunction->getArg(2), Builder.getInt32(0));
    Builder.CreateCondBr(cmp_result, filter_branch3, store_branch);
    Builder.SetInsertPoint(filter_branch3);
    Value* cmp_result3 = Builder.CreateICmpNE(TraceMemoryFunction->getArg(2), Builder.getInt32(1));
    Builder.CreateCondBr(cmp_result3, funccall_branch, load_branch);

    Builder.SetInsertPoint(load_branch);
    //load case
    str_ptr = Builder.CreateGlobalStringPtr("load from %p address len %lx, global value is 0x%lx, func is %s, inst_offset is %ld\n");
    CreatePrintfCall(Builder, TraceMemoryFunction, M, str_ptr);
    Builder.CreateBr(return_block);

    Builder.SetInsertPoint(store_branch);
    //store case
    auto str_ptr2 = Builder.CreateGlobalStringPtr("store to %p address len %lx, global value is 0x%lx, func is %s, inst_offset is %ld\n");
    CreatePrintfCall(Builder, TraceMemoryFunction, M, str_ptr2);
    Builder.CreateBr(return_block);

    Builder.SetInsertPoint(funccall_branch);
    // str_ptr = Builder.CreatePointerCast(Var_func, PointerType::getUnqual(Type::getInt8Ty(ctx)), "Strptr");
    auto str_ptr3 = Builder.CreateGlobalStringPtr("funccall to %p address len %lx, global valutope is 0x%lx, func is %s, inst_offset is %ld\n");
    CreatePrintfCall(Builder, TraceMemoryFunction, M, str_ptr3);
    Builder.CreateBr(return_block);
#endif

    Builder.SetInsertPoint(invalid_block);
#ifdef OUTPUT_ADDRESS
    auto debug_ptr = Builder.CreateGlobalStringPtr("damn we get invlid %p address value %lx, global value %lx, func is %s, line is %ld\n");
    CreatePrintfCall(Builder, TraceMemoryFunction, M, debug_ptr);
#endif
    Builder.CreateBr(return_block);
    
    Builder.SetInsertPoint(return_block);
    // CreatePrintfCall(Builder, TraceMemoryFunction, M, str_ptr);
    Builder.CreateRetVoid();

  }

  //fast check, used for those tagged instructions, no need to divide address
  void CreateFastFunction(llvm::Module& M){
    LLVMContext &ctx = M.getContext();
    //void output_memory(void* address, size_t global_addres, int flag);
    //void tracememory(void* target_address, size_t acccess_flag, size_t access_sz, char* function_name, size_t loc)
    std::vector<Type*> params{Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx), Type::getInt32Ty(ctx), Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx)};
    Type* rettype = Type::getVoidTy(ctx);
    FunctionType* cre_func = FunctionType::get(rettype, params, false);
    FunctionCallee fcl = M.getOrInsertFunction(target_func.c_str(), cre_func);
    Function *TraceMemoryFunction = dyn_cast<llvm::Function>(fcl.getCallee());
    TraceMemoryFunction->setLinkage(GlobalValue::LinkOnceODRLinkage);
    GlobalVariable* glb = M.getNamedGlobal(global_addr);
    GlobalVariable* glb_end = M.getNamedGlobal(global_end);
    llvm::BasicBlock *BB = llvm::BasicBlock::Create(ctx, "entry", TraceMemoryFunction);
#ifdef CONFIRM_ADDRESS
    //if we can't decide whether L/S inst is PMem related or not, we need extra cmp operation in CONFIRM_ADDRESS
    llvm::BasicBlock* filter_branch = llvm::BasicBlock::Create(ctx, "filter", TraceMemoryFunction);
    llvm::BasicBlock *invalid_block = llvm::BasicBlock::Create(ctx, "invlidadd", TraceMemoryFunction);
#endif
    llvm::BasicBlock* for_branch = llvm::BasicBlock::Create(ctx, "for_loop", TraceMemoryFunction);
#ifdef OUTPUT_ADDRESS
    llvm::BasicBlock* filter_branch2 = llvm::BasicBlock::Create(ctx, "filter2", TraceMemoryFunction); 
    llvm::BasicBlock* filter_branch3 = llvm::BasicBlock::Create(ctx, "filter3", TraceMemoryFunction);
    //different branch for different funcall
    llvm::BasicBlock *load_branch = llvm::BasicBlock::Create(ctx, "loadcase", TraceMemoryFunction);
    llvm::BasicBlock *store_branch = llvm::BasicBlock::Create(ctx, "storecase", TraceMemoryFunction);
    llvm::BasicBlock *funccall_branch = llvm::BasicBlock::Create(ctx, "funccase", TraceMemoryFunction);
#endif

    llvm::BasicBlock *return_block = llvm::BasicBlock::Create(ctx, "returnfunc", TraceMemoryFunction);
    IRBuilder<> Builder(ctx);
    Value* str_ptr;
    Builder.SetInsertPoint(BB);
    Value* orig_arg = TraceMemoryFunction->getArg(0);
    Value* cast_arg = Builder.CreatePtrToInt(orig_arg, Builder.getInt64Ty());
#ifdef CONFIRM_ADDRESS
    // compare the address with original value (should be removed if fine-grid filter pmem is set)
    LoadInst* load_address = Builder.CreateLoad(Type::getInt64Ty(ctx), glb);
   
    Value* cmp_address = Builder.CreateICmpUGE(load_address, cast_arg);
    // Builder.CreateCondBr(cmp_address, return_block, filter_branch);
    Builder.CreateCondBr(cmp_address, invalid_block, filter_branch);
    Builder.SetInsertPoint(filter_branch);
    //add printf call shit we get error!!

    //TODO remove the following 3 lines, since we can be sure the address is definate in PMem with filter file
    LoadInst* load_end = Builder.CreateLoad(Type::getInt64Ty(ctx), glb_end);
    Value* cmp_len = Builder.CreateICmpULE(cast_arg, load_end);
    //  Builder.CreateCondBr(cmp_len, for_branch, return_block);
    Builder.CreateCondBr(cmp_len, for_branch, invalid_block);
#else
    Builder.CreateBr(for_branch);
#endif
    //create forloop function
#ifdef OUTPUT_ADDRESS
    CreateCheckLogic(M, TraceMemoryFunction, filter_branch2, for_branch, cast_arg);
#else
    CreateCheckLogic(M, TraceMemoryFunction, return_block, for_branch, cast_arg);
#endif

#ifdef OUTPUT_ADDRESS

    Builder.SetInsertPoint(filter_branch2);
    //here add check logic
    
    // LoadInst* load_value = Builder.CreateLoad(Type::getInt64Ty(ctx), orig_arg);
    //for loop to check whole len 

    Value* cmp_result = Builder.CreateICmpNE(TraceMemoryFunction->getArg(2), Builder.getInt32(0));
    Builder.CreateCondBr(cmp_result, filter_branch3, store_branch);
    Builder.SetInsertPoint(filter_branch3);
    Value* cmp_result3 = Builder.CreateICmpNE(TraceMemoryFunction->getArg(2), Builder.getInt32(1));
    Builder.CreateCondBr(cmp_result3, funccall_branch, load_branch);

    Builder.SetInsertPoint(load_branch);
    //load case
    //add const str
    // Constant *load_str = ConstantDataArray::getString(ctx, "load from %p address len %lx, global value is 0x%lx, func is %s, inst_offset is %ld\n");
    // Constant *Var_load = M.getOrInsertGlobal("load_str", load_str->getType());
    // dyn_cast<GlobalVariable>(Var_load)->setInitializer(load_str);
    // str_ptr = Builder.CreatePointerCast(Var_load, Type::getInt8PtrTy(ctx), "Strptr");

    str_ptr = Builder.CreateGlobalStringPtr("load from %p address len %lx, global value is 0x%lx, func is %s, inst_offset is %ld\n");
    CreatePrintfCall(Builder, TraceMemoryFunction, M, str_ptr);
    Builder.CreateBr(return_block);

    Builder.SetInsertPoint(store_branch);
    //store case
     //add const str
    // Constant *store_str = ConstantDataArray::getString(ctx, "store to %p address len %lx, global value is 0x%lx, func is %s, inst_offset is %ld\n");
    // Constant *Var_store = M.getOrInsertGlobal("stroe_str", store_str->getType());
    // dyn_cast<GlobalVariable>(Var_store)->setInitializer(store_str);
    // str_ptr = Builder.CreatePointerCast(Var_store, Type::getInt8PtrTy(ctx), "Strptr");
    auto str_ptr2 = Builder.CreateGlobalStringPtr("store to %p address len %lx, global value is 0x%lx, func is %s, inst_offset is %ld\n");
    CreatePrintfCall(Builder, TraceMemoryFunction, M, str_ptr2);
    Builder.CreateBr(return_block);

    Builder.SetInsertPoint(funccall_branch);
    //func call case
    // Constant *func_str = ConstantDataArray::getString(ctx, "funccall to %p address len %lx, global value is 0x%lx, func is %s, inst_offset is %ld\n");
    // Constant *Var_func = M.getOrInsertGlobal("func_str", func_str->getType());
    // dyn_cast<GlobalVariable>(Var_func)->setInitializer(func_str);
    // str_ptr = Builder.CreatePointerCast(Var_func, PointerType::getUnqual(Type::getInt8Ty(ctx)), "Strptr");
    auto str_ptr3 = Builder.CreateGlobalStringPtr("funccall to %p address len %lx, global value is 0x%lx, func is %s, inst_offset is %ld\n");
    CreatePrintfCall(Builder, TraceMemoryFunction, M, str_ptr3);
    Builder.CreateBr(return_block);
#endif

#ifdef CONFIRM_ADDRESS
    Builder.SetInsertPoint(invalid_block);
#ifdef OUTPUT_ADDRESS
    // Constant *debug_str = ConstantDataArray::getString(ctx, "damn we get invlid %p address value %lx, global value %lx, func is %s, line is %ld\n");
    // Constant *debug_store = M.getOrInsertGlobal("debug_str", debug_str->getType());
    // dyn_cast<GlobalVariable>(debug_store)->setInitializer(debug_str);
    // Value* debug_ptr = Builder.CreatePointerCast(debug_store, Type::getInt8PtrTy(ctx), "debugptr");
    auto debug_ptr = Builder.CreateGlobalStringPtr("damn we get invlid %p address value %lx, global value %lx, func is %s, line is %ld\n");
    CreatePrintfCall(Builder, TraceMemoryFunction, M, debug_ptr);
#endif
    Builder.CreateBr(return_block);
#endif
    
    Builder.SetInsertPoint(return_block);
    // CreatePrintfCall(Builder, TraceMemoryFunction, M, str_ptr);
    Builder.CreateRetVoid();
  }




  void instrumentFuncall(llvm::Module &M, Instruction &I, size_t operation_flag, size_t inst_offset, size_t merged_len=0){
   
    LLVMContext &ctx = M.getContext();
    const DataLayout *dl = &M.getDataLayout();
    //get memtrace func first
    //args1: l/s address (void*)
    //args2: l/s flag (size_t)
    //args3: l/s len (int)
    //args4: function_name (char*)
    //args5: line_of_code (size_t)
    std::vector<Type*> traceargs{
      PointerType::getUnqual(Type::getInt8Ty(ctx)), Type::getInt64Ty(ctx), Type::getInt32Ty(ctx),
      PointerType::getUnqual(Type::getInt8Ty(ctx)), Type::getInt64Ty(ctx)
    };

    FunctionType* tracememtype = FunctionType::get(Type::getVoidTy(ctx), traceargs, false);
    FunctionCallee TraceMemory;
    if(merged_len != 996996)
      TraceMemory = M.getOrInsertFunction(target_func, tracememtype);
    else
      TraceMemory = M.getOrInsertFunction(slow_func, tracememtype);
    Function* func_inst = I.getFunction();
    StringRef func_inst_ref = func_inst->getName();
    // Constant* valStr = M.getNamedGlobal()
    //in case of duplicate name, add 12345
    std::string str_name = global_base + func_inst_ref.data() + std::to_string(12345);
    Constant* valStr = M.getNamedGlobal(str_name.c_str());
    IRBuilder<> Builder(&I);
    Value* func_name;

    if(valStr == nullptr)
    {
      Value* newStr = Builder.CreateGlobalString(func_inst_ref, str_name.c_str());
      func_name = Builder.CreatePointerCast(newStr, Type::getInt8PtrTy(ctx), "funcname_ptr");
    }
    else
      func_name = Builder.CreatePointerCast(valStr, Type::getInt8PtrTy(ctx), "funcname_ptr");
    Value* ptr = nullptr;
    Value* op_flag;
    size_t access_sz = 0;
    Value* real_size;
    //value only avalible after the inst.
    // Value* value2print;
    // Value* cast64;
    if(llvm::LoadInst* load = dyn_cast<llvm::LoadInst>(&I))
    {
      ptr = load->getPointerOperand();
      op_flag = Builder.getInt32(1);
      auto ty = load->getType();
      access_sz = dl->getTypeAllocSize(ty);
      real_size = Builder.getInt64(access_sz);
      // value2print = &I;
    }
      
    else if(llvm::StoreInst* store = dyn_cast<llvm::StoreInst>(&I))
    {
      ptr = store->getPointerOperand();
      op_flag = Builder.getInt32(0);
      auto ty = store->getValueOperand()->getType();
      access_sz = dl->getTypeAllocSize(ty);
      real_size = Builder.getInt64(access_sz);
      // value2print = store->getOperand(0);
    }
  
    else
    {
      CallInst* memfunc_call = dyn_cast<CallInst>(&I);
      op_flag = Builder.getInt32(operation_flag);
      switch(operation_flag)
      {
        case 2:
          ptr = memfunc_call->getArgOperand(0);
          real_size = memfunc_call->getArgOperand(2);
          break;
        case 3:
          ptr = memfunc_call->getArgOperand(1);
          real_size = memfunc_call->getArgOperand(2);
          break;
        //other cases to scale
        default:
          printf("this is not a load/store or mem access function call!\n");
          return;
      }
    }
      
    // size_t access_size = 0;
    // bool should_cast = value2print->getType()->isPointerTy();
    // if(should_cast)
    //   cast64 = Builder.CreatePtrToInt(value2print, traceargs[3], "cast64");
    // else
    //   cast64 = Builder.CreateIntCast(value2print, traceargs[3], false, "cast64");

    // if(auto *ptrty = dyn_cast<PointerType>(ty))
    // {
    //   ty = ptrty->getPointerElementType();
    //   access_size = dl->getTypeAllocSize(ty);
    // }
    // ptr = Builder.CreateBitCast(ptr, Builder.getInt8PtrTy());
    const DebugLoc& line_output = I.getDebugLoc();
    size_t line_code = 0;
    if(line_output)
      line_code = line_output.getLine();
#ifndef OUTPUT_ADDRESS
    auto lc_arg = Builder.getInt64(line_code);
#else
    auto lc_arg = Builder.getInt64(inst_offset);
#endif
    if(merged_len != 0 && merged_len != 996996)
      real_size = Builder.getInt64(merged_len);
    
    Builder.CreateCall(TraceMemory, {ptr, real_size, op_flag, func_name, lc_arg});
    // Builder.CreateLoad(Type::getInt8Ty(ctx), memaddress);
  }


  void operateGlobal(llvm::Module&M, Function &F, Instruction &I, CallInst* func_called, int len_param=2){
    // auto args0 = F.arg_begin();
    // args0->
    auto func_call = func_called;
    Value* func_return = func_call;
    Value* func_arg0 = func_call->getArgOperand(0);
    Value* pmem_len = func_call->getArgOperand(len_param);
    Value* func_operand = func_call->getCalledOperand();
    LLVMContext &ctx = M.getContext();
    IRBuilder<> builder(I.getNextNode());
    GlobalVariable* glb = M.getNamedGlobal(global_addr);
    // LoadInst* load_global =  builder.CreateLoad(Type::getInt64Ty(ctx), glb);
    // LoadInst* load_arg = builder.CreateLoad(Type::getInt64Ty(ctx), args0);
    // Value* arg2value = builder.getInt64(func_arg0);
    // Value* arg2value = builder.CreateBitCast(func_arg0, builder.getInt8PtrTy());
    // Value* arg2return = builder.CreateBitCast(func_return, builder.getInt8PtrTy());
    // Value* normal_ptr = builder.CreatePointerCast(func_return,  PointerType::getUnqual(Type::getInt8Ty(ctx)));
    // Value* normal_value = builder.CreatePtrToInt(arg2value, builder.getInt64Ty());
    // LoadInst* load_normal = builder.CreateLoad(Type::getInt64Ty(ctx), normal_ptr);
    // Value* llvm_shit = func_call->getCalledValue();
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

    LoadInst* load_after = builder.CreateLoad(Type::getInt64Ty(ctx), glb);
    std::vector<Type*> param4printf{Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx)};
    Type* return_type = Type::getVoidTy(ctx);
    FunctionType* print_func = FunctionType::get(return_type, param4printf, false);
    FunctionCallee fc_printf = M.getOrInsertFunction("printf", print_func);
    auto str_ptr = builder.CreateGlobalStringPtr("output from global %lx\n");
    builder.CreateCall(fc_printf, {str_ptr, load_after});

    // add FPE init function for floatzone(also can be done in hooked _libc_start_main)
#ifdef FLOATZONE
    std::vector<Type*> param4floate{Type::getInt32Ty(ctx)};
    Type* float_rtype = Type::getInt32Ty(ctx);
    FunctionType* float_init = FunctionType::get(float_rtype, param4floate, false);
    FunctionCallee fennable = M.getOrInsertFunction("feenableexcept", float_init);
    if(fennable)
    {
      builder.CreateCall(fennable, {builder.getInt32(0x10)});
      errs()<<"feenableexcept add successfully"<<"\n";
    }  
    else
      errs()<<"fail to add float init function"<<"\n";
#endif
  }



  void operateGlobalInvoke(llvm::Module&M, Function &F, Instruction &I, InvokeInst* func_call){
    // auto args0 = F.arg_begin();
    // args0->
    Value* func_return = func_call;
    Value* func_arg0 = func_call->getArgOperand(0);
    Value* pmem_len = func_call->getArgOperand(2);
    Value* func_operand = func_call->getCalledOperand();
    LLVMContext &ctx = M.getContext();
    //invoke call need to choose the normal jmp target for IRBuilder
    BasicBlock* bb = func_call->getNormalDest();
    auto II = bb->getFirstNonPHI();
    IRBuilder<> builder(II);
    GlobalVariable* glb = M.getNamedGlobal(global_addr);
    // LoadInst* load_global =  builder.CreateLoad(Type::getInt64Ty(ctx), glb);
    // LoadInst* load_arg = builder.CreateLoad(Type::getInt64Ty(ctx), args0);
    // Value* arg2value = builder.getInt64(func_arg0);
    // Value* arg2value = builder.CreateBitCast(func_arg0, builder.getInt8PtrTy());
    // Value* arg2return = builder.CreateBitCast(func_return, builder.getInt8PtrTy());
    // Value* normal_ptr = builder.CreatePointerCast(func_return,  PointerType::getUnqual(Type::getInt8Ty(ctx)));
    // Value* normal_value = builder.CreatePtrToInt(arg2value, builder.getInt64Ty());
    // LoadInst* load_normal = builder.CreateLoad(Type::getInt64Ty(ctx), normal_ptr);
    // Value* llvm_shit = func_call->getCalledValue();
    // Value* get_function = func_call->getCalledFunction();
    Value* arg2value = builder.CreateBitCast(func_call, builder.getInt8PtrTy());
    Value* arg2int = builder.CreatePtrToInt(arg2value, builder.getInt64Ty());
    errs() << "output value is "<< func_return<<" \n";
    // errs() << "output arg0 is "<< get_function<<" \n";
    errs() << "output args called is "<< func_operand << "\n";
    // Value* normal_value_return = builder.CreatePtrToInt(func_return, builder.getInt64Ty());
    // errs()<<"norm al return "<<normal_value_return <<" \n";
    builder.CreateStore(arg2int, glb);

    GlobalVariable* glb_end = M.getNamedGlobal(global_end);
    LoadInst* load_previous = builder.CreateLoad(Type::getInt64Ty(ctx), glb);
    Value* add_result = builder.CreateAdd(load_previous, pmem_len);
    builder.CreateStore(add_result, glb_end);
    //create add and store end address

    // errs()<< "output from global "<<arg2value->getValue() <<"\n";
    // Value* glb_value = builder.CreatePointerCast(glb, Type::getInt64Ty(ctx), "start_address");
    
    // StoreInst* store_global = builder.CreateStore(arg2value, load_global);
    // LLVMContext &ctx = M.getContext();
    // // std::vector<Type*> getargs{Type::getInt8PtrTy(ctx), Type::getInt8PtrTy(ctx), Type::getInt64Ty(ctx), Type::getInt32Ty(ctx)};
    // // Function* pmem_func = M.getFunction("abort");
  }

  inline bool safe_function(Instruction* I){
    if(I == NULL)
      return false;
    switch (I->getOpcode())
    {
      case Instruction::Br:
        return false;
      case Instruction::CallBr:
        return false;
      case Instruction::Call:
        return false;
      default:
        return true;
    }
  }

  int check_merge(int inst_offset, std::vector<stupid_st> &sst){
    for(int i=0; i<sst.size(); i++)
    {
      if(sst[i]._inst_offset == inst_offset && sst[i].master == i)
      {
        if(sst[i].merged)
          return sst[i]._op_len;
        else
          return 0;
      }
      else if(sst[i]._inst_offset == inst_offset && sst[i].master != i)
      {
        std::cout<<"merged inst offset is "<<inst_offset<<" "<<sst[i].master<<std::endl;
        return -1;
      }
        
    }
    std::cout<<"not found this "<<inst_offset<<" instruction! "<<std::endl;
    return 0;
  }

	llvm::PreservedAnalyses run(llvm::Module &M,
				llvm::ModuleAnalysisManager &) {
		errs() << "In here\n\n";
    bool init_flag = false;
    Function* main_func;
    std::vector<Instruction*> del_vec;
    Instruction* invoke_inst = nullptr;
    InvokeInst* invoke_func = nullptr;
    Function* invoke_fn = nullptr;
    struct debug_iter{
      Instruction* _II;
      Function* _FF;
      int _offset;
      int is_memfunc;//used for conrim_address
      int _merge_flag=0;
    };  
    std::vector<debug_iter> debug_vec;
    std::vector<debug_iter> init_vec; //use this vec to simplify the init global address codes
    for(auto &F : M)
    {
      int inst_offset = 0;
      int block_offset=0;
      for(auto &B : F)
      {
        block_offset++;
        for(auto &I : B)
        {
          inst_offset++;
          if((I.getOpcode() == Instruction::Load || I.getOpcode() == Instruction::Store))
          {
            debug_iter di1;
            di1._II = &I;
            di1._FF = &F;
            di1._offset = inst_offset;
            di1.is_memfunc = 0;
            
            auto inext = I.getNextNode();
            if(safe_function(inext))
              di1._merge_flag = true;
            debug_vec.push_back(di1);
            // errs()<<"add function in shit shit "<<F.getName()<<"\n";
          }
          else if(CallInst* memfunc_call = dyn_cast<CallInst>(&I))
          {
            Function* fn = memfunc_call->getCalledFunction();
            if(fn != NULL)
            {
              StringRef fn_name = fn->getName();
              if((fn_name == "llvm.memcpy.p0.p0.i64" || fn_name == "llvm.memmove.p0.p0.i64") && filter_function[F.getName().data()].size() != 0 )
              {
                debug_iter di1;
                di1._II = &I;
                di1._FF = &F;
                di1._offset = inst_offset;
                di1.is_memfunc = 1;
                debug_vec.push_back(di1);
              }
            }
          }
        }
      }
    }


    initGlobaladdress(M, global_addr);
    initGlobaladdress(M, global_end);
    CreateFastFunction(M);
    CreateSlowFunction(M);
    //Find suitable place to add init and create function
    for(auto &F: M)
    {
      if(F.getName() == "main")
      {
        Function* main_func = &F;
        std::cout<<"found main func here "<<std::endl;
        for(auto &B : *(main_func))
        {
          for(auto &I : B)
          {
            if(CallInst* func_call = dyn_cast<CallInst>(&I))
            {
              if(!init_flag)
              {
                Function* fn = func_call->getCalledFunction();
                if(fn != NULL)
                {
                  StringRef fn_name = fn->getName();
                  // operateGlobal(M, *(fn), I);
                  if(fn_name == pmem_pmdk.c_str() || fn_name == pmem_nopmdk.c_str())
                  {
                    errs() << "output func is " << fn_name << "arg0 is "<< func_call->getArgOperand(0) << "\n";
                    init_flag = true;
                    // Value* return_value = func_call;
                    // errs() << " value is "<<return_value<<"\n";

                    if(fn_name == pmem_nopmdk.c_str())
                    {
                      errs()<<"find mmap use mmap parameter!"<<"\n";
                      operateGlobal(M, *(fn), I, func_call, 1);
                    }
                    else
                      operateGlobal(M, *(fn), I, func_call);
                  }
                }
              }
            }
          }
        }
      }
      // else if(F.getName() == "_TraceMemory")
      //   continue;
      // else if(F.getName() == "_Z9benchmarkNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEEi"  || F.getName() == "_ZN12inner_node_t13linear_searchEmb")
      // {
      //   errs() <<"output benchmark here"<<"\n";
      //   continue;
      // }
      else if(filter_function[F.getName().data()].size() != 0)
      {
        // errs() <<"pmem related function "<<F.getName()<<"\n";
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
                  if(fnc_name == pmem_pmdk.c_str() || fnc_name == pmem_nopmdk.c_str())
                  {
                    errs() << "output func in call func " << F.getName() << "arg0 is "<< func_call->getArgOperand(0) << "\n";
                    init_flag = true;
                    // Value* return_value = func_call;
                    // errs() << " value is "<<return_value<<"\n";
                    if(fnc_name == pmem_nopmdk.c_str())
                    {
                      errs()<<"find mmap use mmap parameter!"<<"\n";
                      operateGlobal(M, *(fn), I, func_call, 1);
                    }
                    else
                      operateGlobal(M, *(fn), I, func_call);
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
                    errs() << "output func in invoke func " << fnc_name << "arg0 is "<< func_invoke->getArgOperand(2) << "\n";
                    init_flag = true;
                    // Value* return_value = func_call;
                    // errs() << " value is "<<return_value<<"\n";
                    invoke_inst = &I;
                  }
                }
              }
            }
          }
        }
      }
      else
      {
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

                    errs() << "output func in call func in meaningless branch " << F.getName() << "arg0 is "<< func_call->getArgOperand(0) << "\n";
                    init_flag = true;
                    // Value* return_value = func_call;
                    // errs() << " value is "<<return_value<<"\n";
                    operateGlobal(M, *(fn), I, func_call);
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
                    errs() << "output func in invoke func in meaningless branch" << fnc_name << "arg0 is "<< func_invoke->getArgOperand(2) << "\n";
                    init_flag = true;
                    // Value* return_value = func_call;
                    // errs() << " value is "<<return_value<<"\n";
                    invoke_inst = &I;
                  }
                }
              }
            }
          }
        }
      }
    }

    //instrument 
    bool skip_flag = false;
    for(auto iter : debug_vec)
    {
      StringRef debug_vec_funcname = iter._FF->getName();
      auto shit_offset = iter._offset;
      auto this_map = filter_function[debug_vec_funcname.data()];
      auto that_map = dram_function[debug_vec_funcname.data()];

      //spercific instrument into function 
      //make a pair to find
      size_t query_value = (size_t)iter._offset;
      query_value = (query_value<<30);
  
      //0:load 1:store 2:memfunc_param0, 3:memfunc_param1, ...
      static const int border_file = 4;
      bool if_found = false;
      for(int hash_iter=0; hash_iter < border_file; hash_iter++)
      {
        // printf("shit origin value is %lx\n", query_value); !!!78物业！阿弥诺斯，阿弥诺斯，阿米诺丝诺丝诺丝 阿米阿米
        // add instruction comprision
        if(this_map.find(query_value) != this_map.end())
        {
          //encode neighbor node first:
          if_found = true;
          int merge_len = 0;
#ifdef CHECKMERGE
          // printf("instrument added in function offset is %d, flag is %lx, merge flag is %d\n", shit_offset, query_value, iter._merge_flag);
          
          //check if this check can merge
          //merge_len case: >0: merge to large len, =0: normal check, <0: be merged to other check, skip this one
          if(iter._merge_flag || skip_flag)
            merge_len = check_merge(iter._offset, stupid_map[debug_vec_funcname.data()]);
#endif
          if(merge_len >= 0)
          {
            if(merge_len > 0)
              skip_flag = true;
            instrumentFuncall(M, *(iter._II), hash_iter, shit_offset, merge_len);
            trace_count++;
          } 
          else
          {
            printf("one instruction %d is merged to larger one!\n", iter._offset);
            skip_flag = false;
          }
        }
        else if(that_map.find(query_value) != that_map.end())
          if_found = true;
        query_value++;
      }

      //instruction is not tracked in file, should be checked with full logic
      if(!if_found)
      {
        // printf("uncertain instruction, use full check instrument!\n");
        if(iter.is_memfunc)
        { 
          instrumentFuncall(M, *(iter._II), 2, 12345, 996996);
          instrumentFuncall(M, *(iter._II), 3, 12345, 996996);
        }
        else
          instrumentFuncall(M, *(iter._II), 0, 12345, 996996);
      }
       
    }
    //handle invoke init pmemobj last
    if(invoke_inst != nullptr)
    { 
      errs() << "invoke call, executig"  << "\n";
      operateGlobalInvoke(M, *(invoke_fn), *(invoke_inst), invoke_func);
    }

    debug_vec.clear();
    for(auto iter = filter_function.begin(); iter != filter_function.end(); iter++)
    {
      auto filter_set = iter->second;
      filter_set.clear();
    }
    filter_function.clear();
    stupid_map.clear();
    dram_function.clear();
    printf("output istrument funcall is %ld\n", trace_count);
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

//feel stupid to do this../
void merge_instruction(){
 for(auto iter = stupid_map.begin(); iter != stupid_map.end(); iter++)
 {

    std::vector<struct stupid_st> *this_vec = &iter->second;
    // ]= iter->second;
    //sort on inst_offset 
    std::sort(this_vec->begin(), this_vec->end(), [&](stupid_st s1, stupid_st s2){
      if(s1._inst_offset < s2._inst_offset)
        return true;
      return false;
    });
    for(int i=0; i<this_vec->size(); i++)
      this_vec->at(i).master = i;
    for(int i=0; i<this_vec->size() - 1; i++)
    {
      //only merge one step, only merge normal load-store instruction
      if(this_vec->at(i).master == i && this_vec->at(i)._op_flag < 2 && this_vec->at(i + 1)._op_flag < 2)
      {
        int j = i+1;
        stupid_st *prev, *next;
        if(this_vec->at(i)._op_address <= this_vec->at(j)._op_address){prev = &this_vec->at(i);next = &this_vec->at(j);}
        else{prev = &this_vec->at(j); next = &this_vec->at(i);}
        
        if(abs(this_vec->at(i)._inst_offset - this_vec->at(j)._inst_offset) <= 2 && 
            next->_op_address - prev->_op_address <= 16)
        {
          //change both instruction's message to merged value.
          auto prev_end = prev->_op_address + prev->_op_len;
          auto next_end = next->_op_address + next->_op_len;
          auto differ = next->_op_address - prev->_op_address;
          if(prev_end >= next->_op_address && prev_end <= next_end)
            prev->_op_len = differ + next->_op_len;
          //always set small inst_offset's instruction as master, so that bug can be detect at once.
          this_vec->at(j).master = this_vec->at(i).master;
          prev->merged = true;
          next->merged = true;
        }
      }
    }
  }
}

void file_operation(std::ifstream &if12, std::unordered_map<std::string, std::unordered_set<size_t>> &my_map, int merge_flag=0){
  char func_buffer[1000];
  while(if12.good())
  {
    if12>>func_buffer;
    std::string func_name = strtok(func_buffer, "-");
    std::string inst_offset = strtok(NULL, "-");
    std::string op_flag = strtok(NULL, "-");
    std::string op_len = strtok(NULL, "-");
    std::string op_address = strtok(NULL, "-");
    size_t hex_address = strtol(op_address.c_str(), NULL, 16);
    // printf("function, %s, offset %d, flag %d, len %d, address %lx\n", 
    //         func_buffer, std::stoi(inst_offset), std::stoi(op_flag), std::stoi(op_len), hex_address);
    // std::cout<<"real address: "<<op_address <<std::endl;
    //encode an key to contain offset, flag and access_len
    size_t hashed_value = std::stoull(inst_offset);
    size_t op_ull = std::stoull(op_flag);
    hashed_value = (hashed_value << 30) | op_ull;
    // printf("hash value is %lx\n", hashed_value);
    my_map[func_name].insert(hashed_value);
  #ifdef CHECKMERGE
    if(merge_flag)
    {
      struct stupid_st sst1;
      sst1._inst_offset = std::stoull(inst_offset);
      sst1._op_address = hex_address;
      sst1._op_flag = std::stoi(op_flag);
      sst1._op_len = std::stoi(op_len);
      stupid_map[func_name].push_back(sst1);
    }
  #endif
  }
  printf("finish read operation\n");

}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  printf("hello from plugn\n");
  std::ifstream if1(filter_pmem);
  std::ifstream if2(filter_dram);
  file_operation(if1, filter_function, 1);
  printf("hash size is %ld\n", filter_function.size());
  if1.close();
  //dram doesn't merge
  file_operation(if2, dram_function, 0);
  printf("hash size is %ld\n", dram_function.size());
#ifdef CHECKMERGE
  //scan file to get message, mark mergable instructions, 
  merge_instruction();
  for(auto iter = stupid_map.begin(); iter != stupid_map.end(); iter++)
  {
    auto this_vec = iter->second;
    for(int i=0; i<this_vec.size(); i++)
    {
        // std::cout<<"this vec "<<i<<" inst offset "<<this_vec[i]._inst_offset<<" "<<std::hex<<this_vec[i]._op_address<<" "<<this_vec[i].master<<" "<<this_vec[i]._op_len<<std::endl;
        printf("vec %d, inst_offset %d, op_address %lx, master %d, op_len %d, op_flag %d\n", i, this_vec[i]._inst_offset,
                this_vec[i]._op_address, this_vec[i].master, this_vec[i]._op_len, this_vec[i]._op_flag);
    }
  }
#endif 


  return getMemoryTracePluginInfo();
}