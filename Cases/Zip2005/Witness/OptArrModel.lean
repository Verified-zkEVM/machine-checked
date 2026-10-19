import Cases.Zip2005.Witness.ArrayBytes32Cells

/-! `Ok(Some([Bytes32; 32]))` as `next_element<[Bytes32; 32]>` writes it: the model `optArrW`. -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- Byte `p` of `Ok(Some(bytes))` over the 1024 input bytes from offset `r`. -/
def optArrByte (O W : List Word) (r p : Nat) : BitVec 8 :=
  if p = 0 then 0#8 else if p = 1 then 1#8 else if p < 1026 then inByte W r (p - 2)
  else extractByte O[p / 8]! (p % 8)

/-- `Ok(Some([Bytes32; 32]))` over `O` (129 words). -/
def optArrW (O W : List Word) (r : Nat) : List Word :=
  (List.range 129).map fun i => word8 (optArrByte O W r (8 * i)) (optArrByte O W r (8 * i + 1))
    (optArrByte O W r (8 * i + 2)) (optArrByte O W r (8 * i + 3)) (optArrByte O W r (8 * i + 4))
    (optArrByte O W r (8 * i + 5)) (optArrByte O W r (8 * i + 6)) (optArrByte O W r (8 * i + 7))

@[simp] theorem optArrW_length (O W : List Word) (r : Nat) : (optArrW O W r).length = 129 := by
  simp [optArrW]

theorem optArrW_getElem! (O W : List Word) (r i : Nat) (h : i < 129) :
    (optArrW O W r)[i]! = word8 (optArrByte O W r (8 * i)) (optArrByte O W r (8 * i + 1))
      (optArrByte O W r (8 * i + 2)) (optArrByte O W r (8 * i + 3)) (optArrByte O W r (8 * i + 4))
      (optArrByte O W r (8 * i + 5)) (optArrByte O W r (8 * i + 6)) (optArrByte O W r (8 * i + 7)) := by
  simp [optArrW, h]

attribute [byte_simp] optArrByte optArrW_getElem!
attribute [byte_pre ↓] optArrByte optArrW_getElem!

end Cases.Zip2005
