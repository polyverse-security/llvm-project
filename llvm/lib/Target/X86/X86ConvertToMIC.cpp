//===- X86EvexToVex.cpp ---------------------------------------------------===//
// Convert code to be Move Independent
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// This file defines the pass that replaces instructions using
/// instruction pointer relative addressing modes with instruction sequences
/// taking into account that the code has been moved by a certain offset
/// w.r.t. original location. The offset is computed by a call to a 
/// fixed address generated in the function prolog and stored 
/// in a dedicated variable in the function's frame
//
//===----------------------------------------------------------------------===//

#include "MCTargetDesc/X86BaseInfo.h"
#include "MCTargetDesc/X86InstComments.h"
#include "X86.h"
#include "X86InstrInfo.h"
#include "X86Subtarget.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineOperand.h"
#include "llvm/MC/MCContext.h"
#include "llvm/MC/MCInstrDesc.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"

#include <cassert>
#include <cstdint>

using namespace llvm;

// Including the generated EVEX2VEX tables.
struct X86EvexToVexCompressTableEntry {
  uint16_t EvexOpcode;
  uint16_t VexOpcode;

  bool operator<(const X86EvexToVexCompressTableEntry &RHS) const {
    return EvexOpcode < RHS.EvexOpcode;
  }

  friend bool operator<(const X86EvexToVexCompressTableEntry &TE,
                        unsigned Opc) {
    return TE.EvexOpcode < Opc;
  }
};
#include "X86GenEVEX2VEXTables.inc"

#define CONVERTTOMIC_DESC "Convert to Movement Independent Code"
#define CONVERTTOMIC_NAME "x86-convert-to-mic"

#define DEBUG_TYPE CONVERTTOMIC_NAME

/// Returns true if two machine operands are identical and they are not
/// physical registers.
static inline bool isIdenticalOp(const MachineOperand &MO1,
                                 const MachineOperand &MO2);

/// Returns true if two address displacement operands are of the same
/// type and use the same symbol/index/address regardless of the offset.
static bool isSimilarDispOp(const MachineOperand &MO1,
                            const MachineOperand &MO2);

/// Returns true if the instruction is CALL.
static inline bool isCALL(const MachineInstr &MI) {
  unsigned Opcode = MI.getOpcode();
  return Opcode == X86::CALL16r || Opcode == X86::CALL32r ||
         Opcode == X86::CALL64r || Opcode == X86::CALL64pcrel32 ;
}

namespace {

/// A key based on instruction's memory operands.
class MemOpKey {
public:
  MemOpKey(const MachineOperand *Base, const MachineOperand *Scale,
           const MachineOperand *Index, const MachineOperand *Segment,
           const MachineOperand *Disp)
      : Disp(Disp) {
    Operands[0] = Base;
    Operands[1] = Scale;
    Operands[2] = Index;
    Operands[3] = Segment;
  }

  bool operator==(const MemOpKey &Other) const {
    // Addresses' bases, scales, indices and segments must be identical.
    for (int i = 0; i < 4; ++i)
      if (!isIdenticalOp(*Operands[i], *Other.Operands[i]))
        return false;

    // Addresses' displacements don't have to be exactly the same. It only
    // matters that they use the same symbol/index/address. Immediates' or
    // offsets' differences will be taken care of during instruction
    // substitution.
    return isSimilarDispOp(*Disp, *Other.Disp);
  }

  // Address' base, scale, index and segment operands.
  const MachineOperand *Operands[4];

  // Address' displacement operand.
  const MachineOperand *Disp;
};

class ConvertToMICPass : public MachineFunctionPass {

  using MemOpMap = DenseMap<MemOpKey, SmallVector<MachineInstr *, 16>>;
  void findCALLs(const MachineBasicBlock &MBB, MemOpMap &LEAs);

  /// For EVEX instructions that can be encoded using VEX encoding, replace
  /// them by the VEX encoding in order to reduce size.
  bool ConvertToMIC(MachineInstr &MI, llvm::MachineBasicBlock::iterator &MBBI) const;

public:
  static char ID;

  ConvertToMICPass() : MachineFunctionPass(ID) { }

  StringRef getPassName() const override { return CONVERTTOMIC_DESC; }

  /// Loop over all of the basic blocks, replacing EVEX instructions
  /// by equivalent VEX instructions when possible for reducing code size.
  bool runOnMachineFunction(MachineFunction &MF) override;

  // This pass runs after regalloc and doesn't support VReg operands.
  MachineFunctionProperties getRequiredProperties() const override {
    return MachineFunctionProperties().set(
        MachineFunctionProperties::Property::NoVRegs);
  }

private:
  /// Machine instruction info used throughout the class.
  const X86InstrInfo *TII = nullptr;
};

} // end anonymous namespace

char ConvertToMICPass::ID = 0;

bool ConvertToMICPass::runOnMachineFunction(MachineFunction &MF) {
  LLVM_DEBUG(dbgs() << "😁😁POLYVERSE😁😁 movable code - I am here!!!!: " << MF.getName() << "\n";);

  bool Changed = false;
  for (MachineBasicBlock &MBB : MF) {
    // Traverse the basic block.
    for (auto I = MBB.begin(), E = MBB.end(); I != E;) {
      MachineInstr &MI = *I++;
      if( !isCALL(MI) ) {
        // LLVM_DEBUG(dbgs() << "🥵🥵POLYVERSE🥵🥵 not a call 🥵🥵!!!!\n");
        continue;
      }
      LLVM_DEBUG(dbgs() << "🥵🥵POLYVERSE MI 🥵🥵: " << "\n"; MI.dump(););
      Changed |= ConvertToMIC(MI, I);
    }
  }
  return Changed;
}

static bool usesExtendedRegister(const MachineInstr &MI) {
  auto isHiRegIdx = [](unsigned Reg) {
    // Check for XMM register with indexes between 16 - 31.
    if (Reg >= X86::XMM16 && Reg <= X86::XMM31)
      return true;

    // Check for YMM register with indexes between 16 - 31.
    if (Reg >= X86::YMM16 && Reg <= X86::YMM31)
      return true;
    return false;
  };

  // Check that operands are not ZMM regs or
  // XMM/YMM regs with hi indexes between 16 - 31.
  for (const MachineOperand &MO : MI.explicit_operands()) {
    if (!MO.isReg())
      continue;

    Register Reg = MO.getReg();

    assert(!(Reg >= X86::ZMM0 && Reg <= X86::ZMM31) &&
           "ZMM instructions should not be in the EVEX->VEX tables");

    if (isHiRegIdx(Reg))
      return true;
  }

  return false;
}

// Do any custom cleanup needed to finalize the conversion.
static bool performCustomAdjustments(MachineInstr &MI, unsigned NewOpc) {
  (void)NewOpc;
  unsigned Opc = MI.getOpcode();
  switch (Opc) {
  case X86::VALIGNDZ128rri:
  case X86::VALIGNDZ128rmi:
  case X86::VALIGNQZ128rri:
  case X86::VALIGNQZ128rmi: {
    assert((NewOpc == X86::VPALIGNRrri || NewOpc == X86::VPALIGNRrmi) &&
           "Unexpected new opcode!");
    unsigned Scale = (Opc == X86::VALIGNQZ128rri ||
                      Opc == X86::VALIGNQZ128rmi) ? 8 : 4;
    MachineOperand &Imm = MI.getOperand(MI.getNumExplicitOperands()-1);
    Imm.setImm(Imm.getImm() * Scale);
    break;
  }
  case X86::VSHUFF32X4Z256rmi:
  case X86::VSHUFF32X4Z256rri:
  case X86::VSHUFF64X2Z256rmi:
  case X86::VSHUFF64X2Z256rri:
  case X86::VSHUFI32X4Z256rmi:
  case X86::VSHUFI32X4Z256rri:
  case X86::VSHUFI64X2Z256rmi:
  case X86::VSHUFI64X2Z256rri: {
    assert((NewOpc == X86::VPERM2F128rr || NewOpc == X86::VPERM2I128rr ||
            NewOpc == X86::VPERM2F128rm || NewOpc == X86::VPERM2I128rm) &&
           "Unexpected new opcode!");
    MachineOperand &Imm = MI.getOperand(MI.getNumExplicitOperands()-1);
    int64_t ImmVal = Imm.getImm();
    // Set bit 5, move bit 1 to bit 4, copy bit 0.
    Imm.setImm(0x20 | ((ImmVal & 2) << 3) | (ImmVal & 1));
    break;
  }
  case X86::VRNDSCALEPDZ128rri:
  case X86::VRNDSCALEPDZ128rmi:
  case X86::VRNDSCALEPSZ128rri:
  case X86::VRNDSCALEPSZ128rmi:
  case X86::VRNDSCALEPDZ256rri:
  case X86::VRNDSCALEPDZ256rmi:
  case X86::VRNDSCALEPSZ256rri:
  case X86::VRNDSCALEPSZ256rmi:
  case X86::VRNDSCALESDZr:
  case X86::VRNDSCALESDZm:
  case X86::VRNDSCALESSZr:
  case X86::VRNDSCALESSZm:
  case X86::VRNDSCALESDZr_Int:
  case X86::VRNDSCALESDZm_Int:
  case X86::VRNDSCALESSZr_Int:
  case X86::VRNDSCALESSZm_Int:
    const MachineOperand &Imm = MI.getOperand(MI.getNumExplicitOperands()-1);
    int64_t ImmVal = Imm.getImm();
    // Ensure that only bits 3:0 of the immediate are used.
    if ((ImmVal & 0xf) != ImmVal)
      return false;
    break;
  }

  return true;
}

// For EVEX instructions that can be encoded using VEX encoding
// replace them by the VEX encoding in order to reduce size.
bool ConvertToMICPass::ConvertToMIC(MachineInstr &MI, llvm::MachineBasicBlock::iterator &MBBI) const {
  // VEX format.
  // # of bytes: 0,2,3  1      1      0,1   0,1,2,4  0,1
  //  [Prefixes] [VEX]  OPCODE ModR/M [SIB] [DISP]  [IMM]
  //
  // EVEX format.
  //  # of bytes: 4    1      1      1      4       / 1         1
  //  [Prefixes]  EVEX Opcode ModR/M [SIB] [Disp32] / [Disp8*N] [Immediate]
  if( !isCALL(MI) )
    return false;
  LLVM_DEBUG(dbgs() << "😁😁POLYVERSE😁😁 got a CALL!!!!😁😁\n");

  auto MBB = MI.getParent();
  auto MF = MBB->getParent();
  llvm::MCContext &ctx = MF->getContext();
  auto TII = MF->getSubtarget<X86Subtarget>().getInstrInfo();
  MachineInstr *MovableMI =
      MBB->getParent()->CreateMachineInstr(TII->get(X86::NOOP), DebugLoc()); // TODO some meaningful instruction code

  auto symbol = ctx.createTempSymbol("POLYVERSE", true);
  MovableMI->setPreInstrSymbol(*MF, symbol); // MF->getPICBaseSymbol()

  LLVM_DEBUG(dbgs() << "😁😁POLYVERSE inserting MI 😁😁: " << "\n"; MovableMI->dump(););

  MBB->insert(MBBI, MovableMI);

  const MCInstrDesc &Desc = MI.getDesc();

  // Check for EVEX instructions only.
  if ((Desc.TSFlags & X86II::EncodingMask) != X86II::EVEX)
    return false;

  // Check for EVEX instructions with mask or broadcast as in these cases
  // the EVEX prefix is needed in order to carry this information
  // thus preventing the transformation to VEX encoding.
  if (Desc.TSFlags & (X86II::EVEX_K | X86II::EVEX_B))
    return false;

  // Check for EVEX instructions with L2 set. These instructions are 512-bits
  // and can't be converted to VEX.
  if (Desc.TSFlags & X86II::EVEX_L2)
    return false;

#ifndef NDEBUG
  // Make sure the tables are sorted.
  static std::atomic<bool> TableChecked(false);
  if (!TableChecked.load(std::memory_order_relaxed)) {
    assert(llvm::is_sorted(X86EvexToVex128CompressTable) &&
           "X86EvexToVex128CompressTable is not sorted!");
    assert(llvm::is_sorted(X86EvexToVex256CompressTable) &&
           "X86EvexToVex256CompressTable is not sorted!");
    TableChecked.store(true, std::memory_order_relaxed);
  }
#endif

  // Use the VEX.L bit to select the 128 or 256-bit table.
  ArrayRef<X86EvexToVexCompressTableEntry> Table =
    (Desc.TSFlags & X86II::VEX_L) ? makeArrayRef(X86EvexToVex256CompressTable)
                                  : makeArrayRef(X86EvexToVex128CompressTable);

  auto I = llvm::lower_bound(Table, MI.getOpcode());
  if (I == Table.end() || I->EvexOpcode != MI.getOpcode())
    return false;

  unsigned NewOpc = I->VexOpcode;

  if (usesExtendedRegister(MI))
    return false;

  if (!performCustomAdjustments(MI, NewOpc))
    return false;

  MI.setDesc(TII->get(NewOpc));
  MI.setAsmPrinterFlag(X86::AC_EVEX_2_VEX);
  return true;
}

INITIALIZE_PASS(ConvertToMICPass, CONVERTTOMIC_NAME, CONVERTTOMIC_DESC, false, false)

FunctionPass *llvm::createX86ConvertToMICInsts() {
  return new ConvertToMICPass();
}
