/-
  Cases.Zip2005.Runtime.Tlsf.Class

  The size classes of rlsf's TLSF, as the compiled code computes them (phase D4).

  A free block of size `s` is filed under the first-level class `flOf s = 58 - clz s` (the
  position of its top bit, less 5) and the second-level class `slOf s`, the six bits below
  the top bit (a rotate right by `57 - clz s`, masked). `alloc` searches from the class of
  its rounded request `r`, rounded *up* a second-level step when bits below the class are
  set (`flSearch`, `slSearch`). The code computes `clz` without a `clz` instruction: an
  or-shift cascade, a complement and a SWAR popcount.

  `search_ok` is what makes the search sound: every block filed at or above the search class
  is at least as large as the request. Arithmetic facts like it are decided by `bv_decide`.
-/

import Std.Tactic.BVDecide

namespace Cases.Zip2005.Runtime.Tlsf

/-- Leading zeros, the compiled way (`64` for zero, by the code's separate branch). -/
def clz (x : BitVec 64) : BitVec 64 :=
  if x = 0 then 64#64 else
  let a := x ||| (x >>> 1)
  let a := a ||| (a >>> 2)
  let a := a ||| (a >>> 4)
  let a := a ||| (a >>> 8)
  let a := a ||| (a >>> 16)
  let a := a ||| (a >>> 32)
  let a := ~~~a
  let a := a - ((a >>> 1) &&& 0x5555555555555555#64)
  let a := (a &&& 0x3333333333333333#64) + ((a >>> 2) &&& 0x3333333333333333#64)
  let a := (a + (a >>> 4)) &&& 0x0f0f0f0f0f0f0f0f#64
  (a * 0x0101010101010101#64) >>> 56

/-- `subw`: a 32-bit subtraction, sign-extended. -/
def subw (a b : BitVec 64) : BitVec 64 := ((a.truncate 32) - (b.truncate 32)).signExtend 64

/-- A rotate right, as `srl`/`subw`/`sll`/`or`. -/
def rotr (x s : BitVec 64) : BitVec 64 :=
  (x >>> (s &&& 63#64)) ||| (x <<< ((subw 0 s) &&& 63#64))

/-- The first- and second-level class a free block of size `s` is filed under. -/
def flOf (s : BitVec 64) : BitVec 64 := 0x3a#64 - clz s
def slOf (s : BitVec 64) : BitVec 64 := rotr s (subw 0x39#64 (clz s)) &&& 0x3f#64

/-- The search class for a rounded request `r`: rounded up past any lower bits. -/
def searchRaw (r : BitVec 64) : BitVec 64 :=
  let a0 := rotr r (subw 0x39#64 (clz r))
  (a0 &&& 0x3f#64) + (if a0.ult 0x80#64 then 0#64 else 1#64)
def flSearch (r : BitVec 64) : BitVec 64 := (searchRaw r >>> 6) - clz r + 0x3a#64
def slSearch (r : BitVec 64) : BitVec 64 := searchRaw r &&& 0x3f#64

/-- Block sizes and requests: whole granules (32 bytes), at least one, below `2^40`. -/
def SizeOk (s : BitVec 64) : Prop := 32#64 ≤ s ∧ s < 1#64 <<< 40

/-- **The search is sound**: a block filed at or above the search class fits the request. -/
theorem search_ok {s r : BitVec 64} (hs : SizeOk s) (hr : SizeOk r)
    (hc : flSearch r < flOf s ∨ (flSearch r = flOf s ∧ slSearch r ≤ slOf s)) : r ≤ s := by
  obtain ⟨hs, hs'⟩ := hs
  obtain ⟨hr, hr'⟩ := hr
  simp only [flSearch, slSearch, searchRaw, flOf, slOf, rotr, subw, clz] at *
  bv_decide

/-- Sound for any granule request, however large: no block below `2^40` is filed at or above
    the class of a larger request. -/
theorem search_ok' {s r : BitVec 64} (hs : SizeOk s) (hr : 32#64 ≤ r) (hr31 : r &&& 31#64 = 0#64)
    (hc : flSearch r < flOf s ∨ (flSearch r = flOf s ∧ slSearch r ≤ slOf s)) : r ≤ s := by
  obtain ⟨hs, hs'⟩ := hs
  simp only [flSearch, slSearch, searchRaw, flOf, slOf, rotr, subw, clz] at *
  bv_decide

/-- The search class of a request is a first-level class (below 60). -/
theorem flSearch_lt {r : BitVec 64} (hr : 32#64 ≤ r) : flSearch r < 60#64 := by
  simp only [flSearch, searchRaw, rotr, subw, clz] at *
  bv_decide

/-- Classes are in range: 64 first-level classes of 64 second-level ones. -/
theorem flOf_lt {s : BitVec 64} (hs : SizeOk s) : flOf s < 64#64 := by
  obtain ⟨hs, hs'⟩ := hs
  simp only [flOf, clz] at *
  bv_decide

theorem slOf_lt (s : BitVec 64) : slOf s < 64#64 := by
  simp only [slOf, rotr, subw, clz]
  bv_decide

end Cases.Zip2005.Runtime.Tlsf
