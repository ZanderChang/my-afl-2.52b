/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   Copyright 2015, 2016 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.

 */

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fstream>
#include <sstream>
#include <iomanip>
#include <map>
#include <assert.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Triple.h"
#include "llvm/ADT/Twine.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/IR/Function.h"

using namespace llvm;

std::ofstream PassLogFile; // Pass静态分析日志，目录地址从环境变量PASS_LOG_DIR中获取
#define PASS_LOG_DIR_DEFAULT "/tmp"

Function *SanCovTraceCmpFunction[4];
Function *SanCovTraceConstCmpFunction[4];
Function *SanCovTraceSwitchFunction;
Function *SanCovTraceStrcmpFunction;
Function *SanCovTracePC;
InlineAsm *EmptyAsm;

SanitizerCoverageOptions Options;
const DataLayout *DL;
LLVMContext *C;
Module *CurModule;

char *SanCovTraceCmp1 = "__sanitizer_cov_trace_cmp1";
char *SanCovTraceCmp2 = "__sanitizer_cov_trace_cmp2";
char *SanCovTraceCmp4 = "__sanitizer_cov_trace_cmp4";
char *SanCovTraceCmp8 = "__sanitizer_cov_trace_cmp8";
char *SanCovTraceConstCmp1 = "__sanitizer_cov_trace_const_cmp1";
char *SanCovTraceConstCmp2 = "__sanitizer_cov_trace_const_cmp2";
char *SanCovTraceConstCmp4 = "__sanitizer_cov_trace_const_cmp4";
char *SanCovTraceConstCmp8 = "__sanitizer_cov_trace_const_cmp8";
char *SanCovTraceSwitchName = "__sanitizer_cov_trace_switch";
char *SanCovTraceStrcmpName = "__sanitizer_cov_trace_strcmp";
char *SanCovTracePCName = "__sanitizer_cov_trace_pc";

// Data Type
Type *VoidTy;
Type *Int64Ty, *Int64PtrTy;
Type *Int32Ty;
Type *Int16Ty;
Type *Int8Ty;

// 
int64_t EmptyBasicBlockId = 0;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;
      bool runOnFunction(Function &F);

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}


char AFLCoverage::ID = 0;

void InjectTraceForCmp(ArrayRef<Instruction *> CmpTraceTargets)
{
    for (auto I : CmpTraceTargets)
    {
        if (ICmpInst *ICMP = dyn_cast<ICmpInst>(I))
        {
            IRBuilder<> IRB(ICMP);
            Value *A0 = ICMP->getOperand(0);
            Value *A1 = ICMP->getOperand(1);
            if (!A0->getType()->isIntegerTy())
                continue;
            uint64_t TypeSize = DL->getTypeStoreSizeInBits(A0->getType());
            int CallbackIdx = TypeSize == 8 ? 0 : TypeSize == 16 ? 1 : TypeSize == 32 ? 2 : TypeSize == 64 ? 3 : -1;
            if (CallbackIdx < 0)
                continue;
            // __sanitizer_cov_trace_cmp((type_size << 32) | predicate, A0, A1);
            auto CallbackFunc = SanCovTraceCmpFunction[CallbackIdx];
            bool FirstIsConst = isa<ConstantInt>(A0);
            bool SecondIsConst = isa<ConstantInt>(A1);
            // If both are const, then we don't need such a comparison.
            if (FirstIsConst && SecondIsConst)
                continue;
            // If only one is const, then make it the first callback argument.
            if (FirstIsConst || SecondIsConst)
            {
                CallbackFunc = SanCovTraceConstCmpFunction[CallbackIdx];
                if (SecondIsConst)
                    std::swap(A0, A1);
            }

            auto Ty = Type::getIntNTy(*C, TypeSize);
            IRB.CreateCall(CallbackFunc, {IRB.CreateIntCast(A0, Ty, true), IRB.CreateIntCast(A1, Ty, true)});
        }
    }
}

void InjectTraceForSwitch(ArrayRef<Instruction *> SwitchTraceTargets)
{
    for (auto I : SwitchTraceTargets)
    {
        if (SwitchInst *SI = dyn_cast<SwitchInst>(I))
        {
            IRBuilder<> IRB(I);
            SmallVector<Constant *, 16> Initializers;
            Value *Cond = SI->getCondition();
            if (Cond->getType()->getScalarSizeInBits() > Int64Ty->getScalarSizeInBits())
                continue;
            Initializers.push_back(ConstantInt::get(Int64Ty, SI->getNumCases()));
            Initializers.push_back(ConstantInt::get(Int64Ty, Cond->getType()->getScalarSizeInBits()));
            if (Cond->getType()->getScalarSizeInBits() < Int64Ty->getScalarSizeInBits())
            {
                Cond = IRB.CreateIntCast(Cond, Int64Ty, false);
            }

            for (auto It : SI->cases())
            {
                Constant *C = It.getCaseValue();
                if (C->getType()->getScalarSizeInBits() < Int64Ty->getScalarSizeInBits())
                {
                    C = ConstantExpr::getCast(CastInst::ZExt, It.getCaseValue(), Int64Ty);
                }
                Initializers.push_back(C);
            }
            std::sort(Initializers.begin() + 2, Initializers.end(),
                      [](const Constant *A, const Constant *B) { return cast<ConstantInt>(A)->getLimitedValue() < cast<ConstantInt>(B)->getLimitedValue(); });

            ArrayType *ArrayOfInt64Ty = ArrayType::get(Int64Ty, Initializers.size());
            GlobalVariable *GV = new GlobalVariable(
                *CurModule, ArrayOfInt64Ty, false, GlobalVariable::InternalLinkage,
                ConstantArray::get(ArrayOfInt64Ty, Initializers),
                "__sancov_gen_cov_switch_values");

            IRB.CreateCall(SanCovTraceSwitchFunction, {Cond, IRB.CreatePointerCast(GV, Int64PtrTy)});
        }
    }
}

std::vector<std::string> CmpCalls = {
    "strcmp", "strncmp", "strcasecmp", "strncasecmp", "memcmp"
};

bool IsCmpCall(std::string Name)
{
    for (std::vector<std::string>::size_type i = 0; i < CmpCalls.size(); i++)
    {
        if (Name.size() == CmpCalls[i].size() && Name.compare(0, CmpCalls[i].size(), CmpCalls[i]) == 0)
            return true;
    }
    return false;
}

/*
    string转为hex string
*/
std::string ToHex(const std::string& s)
{
    std::ostringstream ret;

    for (std::string::size_type i = 0; i < s.length(); ++i)
        ret << std::hex << std::setfill('0') << std::setw(2) << std::uppercase << (int)s[i];

    return ret.str();
}

void InjectTraceForStrcmp(ArrayRef<Instruction *> StrcmpTraceTargets)
{
    for (auto I : StrcmpTraceTargets)
    {
        IRBuilder<> IRB(I);

        if (CallInst *call_inst = dyn_cast<CallInst>(I))
        {
            
            // 动态获取待比较的字符串
            if (call_inst->getNumArgOperands() >= 2)
            {
                Value *V0 = call_inst->getArgOperand(0);
                Value *V1 = call_inst->getArgOperand(1);
                Value *V2 = ConstantInt::get(*C, APInt(64, 0, false));

                if (call_inst->getNumArgOperands() == 3)
                    V2 = call_inst->getArgOperand(2);

                IRB.CreateCall(SanCovTraceStrcmpFunction, {IRB.CreatePointerCast(V0, Int64PtrTy), IRB.CreatePointerCast(V1, Int64PtrTy), IRB.CreateIntCast(V2, Int64Ty, false)});
            }

            // 静态分析时提取const数据字符串
            std::vector<StringRef> tmp;
            for (size_t i = 0; i < call_inst->getNumArgOperands(); i++)
            {
                Value *ArgValue = call_inst->getArgOperand(i);

                ConstantExpr *ConstantArg = dyn_cast<ConstantExpr>(ArgValue);
                if (ConstantArg == nullptr) // not const data (user input?)
                    continue;

                GlobalVariable *GV = dyn_cast<GlobalVariable>(ConstantArg->getOperand(0));
                if (GV == nullptr || !GV->hasInitializer())
                    continue;
                ConstantDataArray *AR = dyn_cast<ConstantDataArray>(GV->getInitializer());
                if (AR == nullptr)
                    continue;
                StringRef data = AR->getRawDataValues();
                tmp.push_back(data);

                // ConstantArg->getOperand(0)->getType()->getTypeID() 15 PointerTyID
            }

            if (!tmp.empty())
            {
                PassLogFile << "[" << call_inst->getCalledFunction()->getName().str() << "] ";
                for (int i = 0; i < tmp.size() - 1; i++)
                    PassLogFile << "[" << ToHex(tmp[i].str()) << "] ";
                PassLogFile << "[" << ToHex(tmp[tmp.size() - 1].str()) << "]\n";
            }
        }
    }
}

void InjectCoverage(ArrayRef<BasicBlock *> BlocksToInstrument, std::map<BasicBlock*, std::string>& BlockToName)
{
    for (auto BB : BlocksToInstrument)
    {
        assert(BlockToName.count(BB) > 0);

        std::string BlockName = BlockToName[BB];
        Constant *ConstantName = ConstantDataArray::getString(*C, BlockName, true); // CDS
        GlobalVariable *GV = new GlobalVariable(*CurModule, ConstantName->getType(), true, GlobalVariable::InternalLinkage, ConstantName);

        BasicBlock::iterator IP = BB->getFirstInsertionPt();
        IRBuilder<> IRB(&*IP);
        IRB.CreateCall(SanCovTracePC, {IRB.CreatePointerCast(GV, Int64PtrTy)}); // gets the PC using GET_CALLER_PC.
        IRB.CreateCall(EmptyAsm, {}); // Avoids callback merge.
    }
}

bool isInvalidFunction(Function &F)
{
    // return F.empty() || F.getName().contains("__sanitizer_") || F.getLinkage() == GlobalValue::AvailableExternallyLinkage;
    return F.getName().contains("__sanitizer_") || F.getName().contains("llvm.");
    // return false;
}

bool AFLCoverage::runOnFunction(Function &F)
{
    if (isInvalidFunction(F))
        return false;
    
    // 获取函数在源代码中的所在行
    unsigned int LineNum = 0;
    DISubprogram* DISp = F.getSubprogram();
    if (DISp)
        LineNum = DISp->getLine();

    PassLogFile << "[F] " << F.getName().str() << " " << LineNum << "\n";

    SmallVector<Instruction *, 8> CmpTraceTargets;
    SmallVector<Instruction *, 8> SwitchTraceTargets;
    SmallVector<Instruction *, 8> StrcmpTraceTargets;
    SmallVector<BasicBlock *, 16> BlocksToInstrument;
    std::map<BasicBlock*, std::string> BlockToName;

    // bool isMain = F.getName().equals("main") ? true : false;

    for (auto &BB : F)
    {
        std::string BasicBlockName;
        if (BB.getName().empty()) // 防止Label为空
            BB.setName(Twine("emptyBB.").concat(Twine(EmptyBasicBlockId++)));

        // 静态分析时加上BasicBlock后续BasicBlock信息
        PassLogFile << "[BB] " << BB.getName().str();

        for (BasicBlock* Succ : successors(&BB))
        {
            if (Succ->getName().empty()) // 防止Label为空
                Succ->setName(Twine("emptyBB.").concat(Twine(EmptyBasicBlockId++)));
            PassLogFile << "|" << Succ->getName().str();
        }
        PassLogFile << "\n";

        BlocksToInstrument.push_back(&BB);

        // 构造BasicBlock全局唯一的名字
        // 所属模块|所属函数|该基本块
        BlockToName[&BB] = CurModule->getName().str() + "|" + F.getName().str() + "|" + BB.getName().str();

        for (auto &Inst : BB)
        {
            // 输出Inst源码位置信息和自身
            const DebugLoc & InstDebugInfo = Inst.getDebugLoc();
            unsigned int InstLine = 0;
            unsigned int InstCol = 0;

            if (InstDebugInfo)
            {
                InstLine = InstDebugInfo.getLine();
                InstCol = InstDebugInfo.getCol();
            }

            // std::string InstStr;
            // raw_string_ostream ss(InstStr);
            // ss << Inst;

            // PassLogFile << "[I] " << InstLine << "|" << InstCol << "|" << ss.str() << "\n";

            PassLogFile << "[I] " << InstLine << "|" << InstCol << "\n";

            if (isa<ICmpInst>(&Inst))
                CmpTraceTargets.push_back(&Inst);
            if (isa<SwitchInst>(&Inst))
                SwitchTraceTargets.push_back(&Inst);
            if (isa<CallInst>(&Inst))
            {
                CallInst *call_inst = dyn_cast<CallInst>(&Inst);
                Function *fn = call_inst->getCalledFunction();
                if (fn == NULL)
                {
                    Value *v = call_inst->getCalledValue();
                    fn = dyn_cast<Function>(v->stripPointerCasts());
                    if (fn == NULL)
                        continue;
                }

                if (isInvalidFunction(*fn))
                    continue;

                PassLogFile << "[BBC] " << fn->getName().str() << "\n";

                if (IsCmpCall(fn->getName()))
                    StrcmpTraceTargets.push_back(&Inst);
            }
        }
    }

    InjectCoverage(BlocksToInstrument, BlockToName);
    InjectTraceForCmp(CmpTraceTargets);
    InjectTraceForSwitch(SwitchTraceTargets);
    InjectTraceForStrcmp(StrcmpTraceTargets);

    return true;
}
/*
    环境变量 PASS_LOG_DIR 编译时日志文件输出地址
    编译过程中每个Modlue对应的输出文件为PASS_LOG_PATH/moduleName_log
    [F] 函数名 源代码所在行
    [BB] 基本块命名
    [I]
    [BBC] 基本块调用函数名
    [*cmp] strcmp类函数中的const字符串（hex形式）

    环境变量 RUNTIME_LOG_PATH 运行时日志文件输出地址
    运行过程中程序插桩输出文件为RUNTIME_LOG_PATH
    [PC] 基本块地址 基本块在IR中的名称
    [STRCMP] strcmp类函数的参数
    [CMP] cmp指令的2个值
    [SWITCH] switch指令的每个case的值
*/ 
bool AFLCoverage::runOnModule(Module &M)
{
    std::string moduleName = M.getName();
    auto i = moduleName.rfind('/', moduleName.length());
    if (i != std::string::npos)
    {
        moduleName = moduleName.substr(i + 1, moduleName.length() - i);
    }
    outs() << "[+] " << moduleName << "\n";

    char* PASS_LOG_DIR = getenv("PASS_LOG_DIR");
    struct stat info;
    std::string PASS_LOG_PATH;
    if (stat(PASS_LOG_DIR, &info) != 0)
    {
        outs() << "[+] Writing Pass Log into " << PASS_LOG_DIR_DEFAULT << "\n";
        PASS_LOG_PATH = PASS_LOG_DIR_DEFAULT;
    }
    else if (info.st_mode & S_IFDIR)
    {
        outs() << "[+] Writing Pass Log into " << PASS_LOG_DIR << "\n";
        PASS_LOG_PATH = PASS_LOG_DIR;
    }
    else
    {
        outs() << "[!] No Such DIR " << PASS_LOG_DIR << "\n";
        return false;
    }

    // if (PASS_LOG_PATH.back() == '/')
    //     PASS_LOG_PATH.pop_back();
    
    PASS_LOG_PATH += '/';
    PASS_LOG_PATH += moduleName;
    PASS_LOG_PATH += "_log";

    outs() << "[+] Writing into " << PASS_LOG_PATH << "\n";

    PassLogFile.open(PASS_LOG_PATH);

    if (!PassLogFile)
    {
        outs() << "[!] NO VALID PASS_LOG_PATH!\n";
        return false;
    }

    CurModule = &M;
    C = &(M.getContext());
    DL = &M.getDataLayout();
    Triple TargetTriple = Triple(M.getTargetTriple());

    //
    IRBuilder<> IRB(*C);
    VoidTy = Type::getVoidTy(*C);
    Int64Ty = IRB.getInt64Ty();
    Int64PtrTy = PointerType::getUnqual(IRB.getInt64Ty());
    Int32Ty = IRB.getInt32Ty();
    Int16Ty = IRB.getInt16Ty();
    Int8Ty = IRB.getInt8Ty();

    SanCovTraceCmpFunction[0] = checkSanitizerInterfaceFunction(M.getOrInsertFunction(SanCovTraceCmp1, VoidTy, Int8Ty, Int8Ty));
    SanCovTraceCmpFunction[1] = checkSanitizerInterfaceFunction(M.getOrInsertFunction(SanCovTraceCmp2, VoidTy, Int16Ty, Int16Ty));
    SanCovTraceCmpFunction[2] = checkSanitizerInterfaceFunction(M.getOrInsertFunction(SanCovTraceCmp4, VoidTy, Int32Ty, Int32Ty));
    SanCovTraceCmpFunction[3] = checkSanitizerInterfaceFunction(M.getOrInsertFunction(SanCovTraceCmp8, VoidTy, Int64Ty, Int64Ty));

    SanCovTraceConstCmpFunction[0] = checkSanitizerInterfaceFunction(M.getOrInsertFunction(SanCovTraceConstCmp1, VoidTy, Int8Ty, Int8Ty));
    SanCovTraceConstCmpFunction[1] = checkSanitizerInterfaceFunction(M.getOrInsertFunction(SanCovTraceConstCmp2, VoidTy, Int16Ty, Int16Ty));
    SanCovTraceConstCmpFunction[2] = checkSanitizerInterfaceFunction(M.getOrInsertFunction(SanCovTraceConstCmp4, VoidTy, Int32Ty, Int32Ty));
    SanCovTraceConstCmpFunction[3] = checkSanitizerInterfaceFunction(M.getOrInsertFunction(SanCovTraceConstCmp8, VoidTy, Int64Ty, Int64Ty));

    SanCovTraceSwitchFunction = checkSanitizerInterfaceFunction(M.getOrInsertFunction(SanCovTraceSwitchName, VoidTy, Int64Ty, Int64PtrTy));

    SanCovTraceStrcmpFunction = checkSanitizerInterfaceFunction(M.getOrInsertFunction(SanCovTraceStrcmpName, VoidTy, Int64PtrTy, Int64PtrTy, Int64Ty));

    SanCovTracePC = checkSanitizerInterfaceFunction(M.getOrInsertFunction(SanCovTracePCName, VoidTy, Int64PtrTy));

    // We insert an empty inline asm after cov callbacks to avoid callback merge.
    EmptyAsm = InlineAsm::get(FunctionType::get(IRB.getVoidTy(), false), StringRef(""), StringRef(""), /*hasSideEffects=*/true);

    // Make sure smaller parameters are zero-extended to i64 as required by the x86_64 ABI.
    if (TargetTriple.getArch() == Triple::x86_64)
    {
        for (int i = 0; i < 3; i++)
        {
            SanCovTraceCmpFunction[i]->addParamAttr(0, Attribute::ZExt);
            SanCovTraceCmpFunction[i]->addParamAttr(1, Attribute::ZExt);
            SanCovTraceConstCmpFunction[i]->addParamAttr(0, Attribute::ZExt);
            SanCovTraceConstCmpFunction[i]->addParamAttr(1, Attribute::ZExt);
        }
    }

    for (auto &F : M)
    {
        runOnFunction(F);
    }

    PassLogFile.close(); // 关闭该Module的输出文件

    return true;
}


// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
// clang -Xclang -load -Xclang build/skeleton/libCollectCMPPass.so test.c -o test
static void registerAFLPass(const PassManagerBuilder &, legacy::PassManagerBase &PM)
{
    PM.add(new AFLCoverage());
}
static RegisterStandardPasses RegisterAFLPass(PassManagerBuilder::EP_OptimizerLast, registerAFLPass);
static RegisterStandardPasses RegisterAFLPass0(PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);

// used for
// clang -c -emit-llvm test.c // .bc
// clang -S -emit-llvm test.c // .ll
// opt -load build/skeleton/libCollectCMPPass.so -CollectCMPPass test.bc/test.ll
// static RegisterPass<RegisterAFLPass> X("RegisterAFLPass", "RegisterAFLPass For CFG",
//                                       false /* Only looks at CFG */,
//                                       false /* Analysis Pass */);

// opt --dot-cfg test.ll
// dot -Tpng cfg.a.dot > cfg.a.png

// clang -emit-llvm -c -I/data2/zhangzheng1/tools/llvm-6.0/usr/local/include SanCovTraceCmp.cpp # SanCovTraceCmp.bc
// clang -emit-llvm -c test.c # test.bc
// llvm-link SanCovTraceCmp.bc test.bc -o main.bc
// clang++ -fPIC CollectCMP.cpp -o libCollectCMPPass.so `llvm-config --cxxflags` -shared
// opt -load libCollectCMPPass.so -CollectCMPPass main.bc -o final.bc
// lli final.bc
// llvm-dis final.bc # final.ll
// opt --dot-cfg final.ll
// dot -Tpng cfg.main.dot > cfg.main.png
// llc -filetype=obj final.bc # final.o
// clang final.o -o final

// PASS_LOG_DIR=/data2/zhangzheng1/codes/myUtilities/LLVMPass/llvm-pass-skeleton/PASS_LOG ~/zhangzheng1/codes/my-afl-2.52b/afl-2.52b/afl-clang-fast test.c -o test