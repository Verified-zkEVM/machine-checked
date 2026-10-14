import Cases.Zip2005.Curve.FromBytesKit

/-!
# A decompression's flag from the branch on it

`FromBytesPost` leaves its `CtOption` flag `0` or `1`. The caller branches on the flag
zero-extended to a register. Whichever way the branch is phrased (`== 1`, `!= 1`, `!= 0`,
`== 0`), the arm that continues fixes the flag to `1`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

set_option autoImplicit false

theorem fb_flag {b0 b1 b2 b3 : Word} {x y : Nat} {f : BitVec 8} (h : FromBytesPost b0 b1 b2 b3 x y f) :
    f = 1#8 ∨ f = 0#8 := by
  rcases h with ⟨-, -, ⟨h, -⟩ | ⟨h, -⟩⟩
  · exact Or.inl h
  · exact Or.inr h

theorem fb_flag_ne1 {b0 b1 b2 b3 : Word} {x y : Nat} {f : BitVec 8} {v : Word}
    (h : FromBytesPost b0 b1 b2 b3 x y f) (hv : BitVec.zeroExtend 64 f = v) (hb : ¬(v != 1#64) = true) :
    f = 1#8 := by
  rcases fb_flag h with h1 | h0
  · exact h1
  · subst h0 hv; simp at hb

theorem fb_flag_beq1 {b0 b1 b2 b3 : Word} {x y : Nat} {f : BitVec 8} {v : Word}
    (h : FromBytesPost b0 b1 b2 b3 x y f) (hv : BitVec.zeroExtend 64 f = v) (hb : (v == 1#64) = true) :
    f = 1#8 := by
  rcases fb_flag h with h1 | h0
  · exact h1
  · subst h0 hv; simp at hb

theorem fb_flag_ne0 {b0 b1 b2 b3 : Word} {x y : Nat} {f : BitVec 8} {v : Word}
    (h : FromBytesPost b0 b1 b2 b3 x y f) (hv : BitVec.zeroExtend 64 f = v) (hb : (v != 0#64) = true) :
    f = 1#8 := by
  rcases fb_flag h with h1 | h0
  · exact h1
  · subst h0 hv; simp at hb

theorem fb_flag_nbeq0 {b0 b1 b2 b3 : Word} {x y : Nat} {f : BitVec 8} {v : Word}
    (h : FromBytesPost b0 b1 b2 b3 x y f) (hv : BitVec.zeroExtend 64 f = v) (hb : ¬(v == 0#64) = true) :
    f = 1#8 := by
  rcases fb_flag h with h1 | h0
  · exact h1
  · subst h0 hv; simp at hb

end Cases.Zip2005
