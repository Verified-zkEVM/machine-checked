/-
  DO NOT EDIT -- generated from catcrypt-compiler (see `Cases/CatCrypt/PROVENANCE.md`).

  `cswapPhys` of catcrypt-compiler's `RiscvBytesProof` (branch `rv64-g5-x25519`,
  `523dffe6`), encoded by its `encodeMBlock64`: 52 words. `prog` is their decoding by
  riscv-zkvm's own `decode` (`decode_ok`), the decoder `stepSp1` runs.
-/

import MachineChecked.RiscV.Image

set_option maxRecDepth 200000

namespace Cases.CatCrypt.Image.Cswap

open RiscvZkvm.Rv64

def len : Nat := 52

def words : List (BitVec 32) := [
  0x00050313#32,
  0x405003b3#32,
  0x00777e33#32,
  0x00757eb3#32,
  0x01d54eb3#32,
  0x01de6e33#32,
  0x000e0513#32,
  0x405003b3#32,
  0x00737e33#32,
  0x00777eb3#32,
  0x01d74eb3#32,
  0x01de6e33#32,
  0x000e0713#32,
  0x00058313#32,
  0x405003b3#32,
  0x0077fe33#32,
  0x0075feb3#32,
  0x01d5ceb3#32,
  0x01de6e33#32,
  0x000e0593#32,
  0x405003b3#32,
  0x00737e33#32,
  0x0077feb3#32,
  0x01d7ceb3#32,
  0x01de6e33#32,
  0x000e0793#32,
  0x00060313#32,
  0x405003b3#32,
  0x00787e33#32,
  0x00767eb3#32,
  0x01d64eb3#32,
  0x01de6e33#32,
  0x000e0613#32,
  0x405003b3#32,
  0x00737e33#32,
  0x00787eb3#32,
  0x01d84eb3#32,
  0x01de6e33#32,
  0x000e0813#32,
  0x00068313#32,
  0x405003b3#32,
  0x0078fe33#32,
  0x0076feb3#32,
  0x01d6ceb3#32,
  0x01de6e33#32,
  0x000e0693#32,
  0x405003b3#32,
  0x00737e33#32,
  0x0078feb3#32,
  0x01d8ceb3#32,
  0x01de6e33#32,
  0x000e0893#32]

def prog : List Instr := [
  RiscvZkvm.Rv64.Instr.ADDI (RiscvZkvm.Rv64.Reg.x6) (RiscvZkvm.Rv64.Reg.x10) 0x000#12,
  RiscvZkvm.Rv64.Instr.SUB (RiscvZkvm.Rv64.Reg.x7) (RiscvZkvm.Rv64.Reg.x0) (RiscvZkvm.Rv64.Reg.x5),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x14) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x10) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.XOR (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x10) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.OR (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.ADDI (RiscvZkvm.Rv64.Reg.x10) (RiscvZkvm.Rv64.Reg.x28) 0x000#12,
  RiscvZkvm.Rv64.Instr.SUB (RiscvZkvm.Rv64.Reg.x7) (RiscvZkvm.Rv64.Reg.x0) (RiscvZkvm.Rv64.Reg.x5),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x6) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x14) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.XOR (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x14) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.OR (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.ADDI (RiscvZkvm.Rv64.Reg.x14) (RiscvZkvm.Rv64.Reg.x28) 0x000#12,
  RiscvZkvm.Rv64.Instr.ADDI (RiscvZkvm.Rv64.Reg.x6) (RiscvZkvm.Rv64.Reg.x11) 0x000#12,
  RiscvZkvm.Rv64.Instr.SUB (RiscvZkvm.Rv64.Reg.x7) (RiscvZkvm.Rv64.Reg.x0) (RiscvZkvm.Rv64.Reg.x5),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x15) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x11) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.XOR (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x11) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.OR (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.ADDI (RiscvZkvm.Rv64.Reg.x11) (RiscvZkvm.Rv64.Reg.x28) 0x000#12,
  RiscvZkvm.Rv64.Instr.SUB (RiscvZkvm.Rv64.Reg.x7) (RiscvZkvm.Rv64.Reg.x0) (RiscvZkvm.Rv64.Reg.x5),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x6) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x15) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.XOR (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x15) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.OR (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.ADDI (RiscvZkvm.Rv64.Reg.x15) (RiscvZkvm.Rv64.Reg.x28) 0x000#12,
  RiscvZkvm.Rv64.Instr.ADDI (RiscvZkvm.Rv64.Reg.x6) (RiscvZkvm.Rv64.Reg.x12) 0x000#12,
  RiscvZkvm.Rv64.Instr.SUB (RiscvZkvm.Rv64.Reg.x7) (RiscvZkvm.Rv64.Reg.x0) (RiscvZkvm.Rv64.Reg.x5),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x16) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x12) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.XOR (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x12) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.OR (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.ADDI (RiscvZkvm.Rv64.Reg.x12) (RiscvZkvm.Rv64.Reg.x28) 0x000#12,
  RiscvZkvm.Rv64.Instr.SUB (RiscvZkvm.Rv64.Reg.x7) (RiscvZkvm.Rv64.Reg.x0) (RiscvZkvm.Rv64.Reg.x5),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x6) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x16) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.XOR (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x16) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.OR (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.ADDI (RiscvZkvm.Rv64.Reg.x16) (RiscvZkvm.Rv64.Reg.x28) 0x000#12,
  RiscvZkvm.Rv64.Instr.ADDI (RiscvZkvm.Rv64.Reg.x6) (RiscvZkvm.Rv64.Reg.x13) 0x000#12,
  RiscvZkvm.Rv64.Instr.SUB (RiscvZkvm.Rv64.Reg.x7) (RiscvZkvm.Rv64.Reg.x0) (RiscvZkvm.Rv64.Reg.x5),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x17) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x13) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.XOR (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x13) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.OR (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.ADDI (RiscvZkvm.Rv64.Reg.x13) (RiscvZkvm.Rv64.Reg.x28) 0x000#12,
  RiscvZkvm.Rv64.Instr.SUB (RiscvZkvm.Rv64.Reg.x7) (RiscvZkvm.Rv64.Reg.x0) (RiscvZkvm.Rv64.Reg.x5),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x6) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.AND (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x17) (RiscvZkvm.Rv64.Reg.x7),
  RiscvZkvm.Rv64.Instr.XOR (RiscvZkvm.Rv64.Reg.x29) (RiscvZkvm.Rv64.Reg.x17) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.OR (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x28) (RiscvZkvm.Rv64.Reg.x29),
  RiscvZkvm.Rv64.Instr.ADDI (RiscvZkvm.Rv64.Reg.x17) (RiscvZkvm.Rv64.Reg.x28) 0x000#12]

theorem decode_ok : MachineChecked.RiscV.decodeWords words = prog.map some := by decide +kernel

theorem prog_length : prog.length = len := rfl

end Cases.CatCrypt.Image.Cswap
