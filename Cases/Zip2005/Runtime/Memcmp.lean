/-
  Cases.Zip2005.Memcmp

  `memcmp(a, b, n)` on doubleword-aligned blocks of `n = 8k` bytes: the result
  is zero exactly when the blocks are equal. The function is proved once, at Lprog
  and for every length (`MemcmpLprog.safe`); here its bytes are read as the
  doublewords of two regions.
-/

import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Runtime.MemcmpLprog
import Cases.Zip2005.Image.F_7803f54c
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

/-- Byte `i` of a little-endian doubleword list. -/
def byteOf (xs : List Word) (i : Nat) : BitVec 8 := extractByte (xs[i / 8]!) (i % 8)

theorem word_eq_of_bytes (w w' : Word) (h : ∀ k, k < 8 → extractByte w k = extractByte w' k) :
    w = w' := by
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  have hk := h (n / 8) (by omega)
  have := congrArg (fun b : BitVec 8 => b.getLsbD (n % 8)) hk
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight] at this
  have e : n / 8 * 8 + n % 8 = n := by omega
  simpa [show n % 8 < 8 by omega, e] using this

/-- Two lists of `k` doublewords are equal when their `8k` bytes are. -/
theorem eq_of_bytes {xs ys : List Word} {k : Nat} (hx : xs.length = k) (hy : ys.length = k)
    (h : ∀ i, i < 8 * k → byteOf xs i = byteOf ys i) : xs = ys := by
  apply List.ext_getElem (hx.trans hy.symm)
  intro n h1 h2
  apply word_eq_of_bytes
  intro b hb
  have := h (8 * n + b) (by omega)
  simp only [byteOf, show (8 * n + b) / 8 = n by omega, show (8 * n + b) % 8 = b by omega,
    getElem!_pos xs n h1, getElem!_pos ys n h2] at this
  exact this

theorem fold8 {xs : List Word} (h : xs.length = 8) :
    [xs[0]!, xs[1]!, xs[2]!, xs[3]!, xs[4]!, xs[5]!, xs[6]!, xs[7]!] = xs := by
  match xs, h with
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem fold4 {xs : List Word} (h : xs.length = 4) : [xs[0]!, xs[1]!, xs[2]!, xs[3]!] = xs := by
  match xs, h with
  | [_, _, _, _], _ => rfl

theorem calleeSaved_not_clobbered : ∀ r ∈ calleeSavedRegs, r ∉ MemcmpLprog.clobbered := by decide

theorem regionOk_lt_two_pow {lo hi : Nat} {base : Word} {k : Nat}
    (h : RegionOk lo hi base k) : 8 * k < 2 ^ 64 := by
  have := h.inMem; unfold SP1_MAX_MEMORY at this; omega

/-- A byte of a well-placed region is a byte of its doublewords. -/
theorem getByte_region {lo hi : Nat} {base : Word} {k : Nat} (hok : RegionOk lo hi base k)
    {xs : List Word} (hxl : xs.length = k) {s : MachineState} (hx : Region base xs s) {i : Nat}
    (hi : i < 8 * k) : s.getByte (base + BitVec.ofNat 64 i) = byteOf xs i := by
  rw [getByte_cell hok (i := i / 8) (k := i % 8) (by omega) (by omega) s
    (by rw [show 8 * (i / 8) + i % 8 = i by omega]),
    hx (i / 8) (by omega)]
  rfl

/-- `memcmp(a, b, 8k)` on two blocks of `k` doublewords: zero exactly when they are equal. -/
theorem memcmp_blocks_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState)
    (ra a b : Word) (xs ys : List Word) (k : Nat) (hxl : xs.length = k) (hyl : ys.length = k)
    (hpc : s.pc = 0x7803f54c#64) (hcode : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a) (ha1 : s.getReg .x11 = b) (ha2 : s.getReg .x12 = BitVec.ofNat 64 (8 * k))
    (hx : Region a xs s) (hokx : RegionOk Ro.layout.textLo Ro.layout.textHi a k)
    (hy : Region b ys s) (hoky : RegionOk Ro.layout.textLo Ro.layout.textHi b k)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [] s t →
      (t.getReg .x10 = 0 ↔ xs = ys) →
      BitVec.signExtend 64 ((t.getReg .x10).truncate 32) = t.getReg .x10 → SafeN G n P t) :
    SafeN G n P s := by
  refine MemcmpLprog.safe s ra a b (8 * k) (regionOk_lt_two_pow hokx) hpc hcode hra ha0 ha1 ha2
    (fun i hi => by
      simpa [show 8 * (i / 8) + i % 8 = i by omega] using addrOk hokx (i := i / 8) (k := i % 8) (by omega) (by omega))
    (fun i hi => by
      simpa [show 8 * (i / 8) + i % 8 = i by omega] using addrOk hoky (i := i / 8) (k := i % 8) (by omega) (by omega))
    fun t hpc' hcode' hmem hkept hx10 hsx => ?_
  refine hk t (by rw [hpc', hra1]) (fun r hr => hkept r (calleeSaved_not_clobbered r hr)) hcode'
    (fun addr _ => hmem addr) ?_ hsx
  rw [hx10]
  constructor
  · intro h
    exact eq_of_bytes hxl hyl fun i hi => by
      rw [← getByte_region hokx hxl hx hi, ← getByte_region hoky hyl hy hi]; exact h i hi
  · intro h i hi
    subst h
    rw [getByte_region hokx hxl hx hi, getByte_region hoky hyl hy hi]

/-- `memcmp(a, b, 64)` on two blocks of eight doublewords: zero exactly when they are equal. -/
theorem memcmp8_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a b : Word) (xs ys : List Word)
    (hxl : xs.length = 8) (hyl : ys.length = 8)
    (hpc : s.pc = 0x7803f54c#64) (hcode : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (_hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a) (ha1 : s.getReg .x11 = b) (ha2 : s.getReg .x12 = 64#64)
    (hx : Region a xs s) (hokx : RegionOk Ro.layout.textLo Ro.layout.textHi a 8)
    (hy : Region b ys s) (hoky : RegionOk Ro.layout.textLo Ro.layout.textHi b 8)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [] s t →
      (t.getReg .x10 = 0 ↔ xs = ys) →
      BitVec.signExtend 64 ((t.getReg .x10).truncate 32) = t.getReg .x10 → SafeN G n P t) :
    SafeN G n P s :=
  memcmp_blocks_spec s ra a b xs ys 8 hxl hyl hpc hcode hra hra1 ha0 ha1 ha2 hx hokx hy hoky hk

/-- `memcmp(a, b, 32)` on two blocks of four doublewords: zero exactly when they are equal. -/
theorem memcmp4_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a b : Word) (xs ys : List Word)
    (hxl : xs.length = 4) (hyl : ys.length = 4)
    (hpc : s.pc = 0x7803f54c#64) (hcode : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (_hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a) (ha1 : s.getReg .x11 = b) (ha2 : s.getReg .x12 = 32#64)
    (hx : Region a xs s) (hokx : RegionOk Ro.layout.textLo Ro.layout.textHi a 4)
    (hy : Region b ys s) (hoky : RegionOk Ro.layout.textLo Ro.layout.textHi b 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [] s t →
      (t.getReg .x10 = 0 ↔ xs = ys) →
      BitVec.signExtend 64 ((t.getReg .x10).truncate 32) = t.getReg .x10 → SafeN G n P t) :
    SafeN G n P s :=
  memcmp_blocks_spec s ra a b xs ys 4 hxl hyl hpc hcode hra hra1 ha0 ha1 ha2 hx hokx hy hoky hk

end Cases.Zip2005
