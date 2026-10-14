import Cases.Zip2005.Sinsemilla.SinsemillaModel
import Cases.Zip2005.Sinsemilla.SinsemillaPack
import Cases.Zip2005.Field.FpRepr
import Cases.Zip2005.Sinsemilla.Lebs2ipK
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Sinsemilla.SinsemillaChunk
import Cases.Zip2005.Image.F_78021238
import Cases.Zip2005.Image.Ro

/-!
# The chunk loop of `CommitDomain::commit`, the `commit_ivk` instantiation (`0x78021238`)

The message `Vec<bool>` is 510 bytes; its region is stated as 65 words so that the executor
keeps it opaque (a 64-word region would be expanded into cells, and the loop's byte loads have
a symbolic index). (`hash_to_point_inner`, `0x7802135c` – `0x780214a4`)

One iteration: ten message bytes assembled into two words, `lebs2ip_k`, the table entry at
`0x78001968 + 64 m` taken out of Montgomery form by `pack`, `incomplete_add` twice, the result
copied back over the accumulator. The accumulator is nine words (tag, eight limbs).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
/-- The loop, by induction on the chunks left: from the loop head with `i` chunks folded and `n`
to go, to the exit with all `i + n` folded. `Bv` holds the message bytes (`0`/`1` over the first
`10 nc`), `T` the generator table. -/
theorem sinsemilla_loop_ivk {G : MachineState → Prop} {nb : Nat} {P : Prop} (sp bp : Word) (T Bv : List Word) (nc : Nat)
    (c : Word → Option Instr) (g3 g4 g8 g9 g18 : Word) (a0 : List Word)
    (hbounds : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = c → SafeN G nb P u)
    (hunwrap : ∀ u : MachineState, u.pc = 0x7803dc7c#64 → u.code = c → SafeN G nb P u)
    (hTl : T.length = 8192) (hBl : Bv.length = 65) (hnc : 10 * nc ≤ 512)
    (hbool : ∀ o, o < 10 * nc → byteAt Bv o = 0#64 ∨ byteAt Bv o = 1#64) :
    ∀ n i (t : MachineState) (acc : List Word) (len p : Word), i + n ≤ nc → 1 ≤ n →
      AccRep (sinFold T (some a0) (chunks Bv i)) acc →
      t.pc = 0x7802135c#64 → t.code = c →
      CodeAt F_78021238.base F_78021238.prog t →
      CodeAt F_780234cc.base F_780234cc.prog t → CodeAt F_780237dc.base F_780237dc.prog t →
      CodeAt F_78029468.base F_78029468.prog t →
      CodeAt F_780235e8.base F_780235e8.prog t → CodeAt F_7803f54c.base F_7803f54c.prog t →
      CodeAt F_78035f88.base F_78035f88.prog t → CodeAt F_780360e0.base F_780360e0.prog t →
      CodeAt F_7801bf3c.base F_7801bf3c.prog t → CodeAt F_7801b4d8.base F_7801b4d8.prog t →
      CodeWithin Ro.layout.textLo Ro.layout.textHi t → RoImage Ro.layout t →
      t.getReg .x2 = sp → StackOk Ro.layout 0x130 sp → sp.toNat + 0x3a0 ≤ 0x78000000 →
      t.getReg .x3 = g3 → t.getReg .x4 = g4 → t.getReg .x8 = g8 → t.getReg .x9 = g9 →
      t.getReg .x18 = g18 →
      t.getReg .x19 = sp + 0x178#64 → t.getReg .x20 = sp + 0x280#64 →
      t.getReg .x21 = len → len = BitVec.ofNat 64 (10 * n) →
      t.getReg .x22 = p → p = bp + BitVec.ofNat 64 (10 * i) →
      t.getReg .x23 = 9#64 → t.getReg .x24 = 0x3ff#64 → t.getReg .x25 = 0x78001968#64 →
      t.getReg .x26 = 1#64 →
      Region 0x78001968#64 T t → RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001968#64 8192 →
      Region bp Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi bp 65 →
      (∃ A : List Word, A.length = 9 ∧ Region (sp + 0x70#64) A t) → RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x70#64) 9 →
      Region (sp + 0x170#64) acc t → RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x170#64) 9 →
      (∃ C : List Word, C.length = 4 ∧ Region (sp + 0x1b8#64) C t) → RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x1b8#64) 4 →
      (∃ D : List Word, D.length = 4 ∧ Region (sp + 0x238#64) D t) → RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x238#64) 4 →
      (∃ E : List Word, E.length = 9 ∧ Region (sp + 0x278#64) E t) → RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x278#64) 9 →
      (∃ F : List Word, F.length = 9 ∧ Region (sp + 0x8#64) F t) → RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x8#64) 9 →
      Disjoint bp 65 (sp - 0x130#64) 126 →
      (∀ u (acc' : List Word), u.pc = 0x780214a4#64 → u.code = c →
        u.getReg .x2 = sp → u.getReg .x3 = g3 → u.getReg .x4 = g4 → u.getReg .x8 = g8 →
        u.getReg .x9 = g9 → u.getReg .x18 = g18 → u.getReg .x19 = sp + 0x178#64 →
        Unchanged [(sp - 0x130#64, 38), (sp + 0x70#64, 9), (sp + 0x170#64, 9), (sp + 0x1b8#64, 4),
          (sp + 0x238#64, 4), (sp + 0x278#64, 9), (sp + 0x8#64, 9)] t u →
        Region (sp + 0x170#64) acc' u → AccRep (sinFold T (some a0) (chunks Bv (i + n))) acc' →
        SafeN G nb P u) →
      SafeN G nb P t := by
  intro n
  induction n with
  | zero => intro i t acc _ _ _ hn; exact absurd hn (by omega)
  | succ n ih =>
    intro i t acc len p hin hn hrep hpc hc hcodeC hcodeL hcodeP hcodeT hcodeI hcodeCmp hcodeAA hcodeLR
      hcodeAdd hcodeM hcw hro hsp hstk hhi h3 h4 h8 h9 h18 h19 h20 h21 hlen h22 hp h23 h24 h25 h26
      hT hokT hB hokB hA' hokA hacc hokacc hC' hokC hD' hokD hE' hokE hF' hokF hdB hk
    subst hlen hp
    obtain ⟨A, hAl, hA⟩ := hA'
    obtain ⟨C, hCl, hC⟩ := hC'
    obtain ⟨D, hDl, hD⟩ := hD'
    obtain ⟨E, hEl, hE⟩ := hE'
    obtain ⟨F, hFl, hF⟩ := hF'
    have hal : acc.length = 9 := hrep.1
    have hin' : 10 * (i + (n + 1)) ≤ 512 := by omega
    have hlo := hstk.lo
    have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x130#64) 38 := hstk.frame 38 (by decide)
    have hu := Unchanged.refl [(sp - 0x130#64, 38), (sp + 0x70#64, 9), (sp + 0x170#64, 9), (sp + 0x1b8#64, 4),
      (sp + 0x238#64, 4), (sp + 0x278#64, 9), (sp + 0x8#64, 9)] t
    sym_exec [lebs2ip_k_spec, sinsemilla_pack_spec, incomplete_add_spec, memcpy72_spec, hbounds, hunwrap]
      stop [0x7802135c, 0x780214a4]
    all_goals
      -- the chunk value from the ten bytes
      have hi16 : 10 * i + 16 < 2 ^ 64 := by omega
      have idx : ∀ k, k < 16 → (BitVec.ofNat 64 (10 * i) + BitVec.ofNat 64 k).toNat = 10 * i + k := by
        intro k hk; rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
      have hm : (lebs2ipK v31 v9).toNat = chunkVal Bv i ∧ chunkVal Bv i ≤ 1023 := by
        rw [← v31_def, ← v30_def, ← v29_def, ← v28_def, ← v27_def, ← v26_def, ← v25_def, ← v24_def,
          ← v19_def, ← v18_def, ← v17_def, ← v16_def, ← v15_def, ← v14_def, ← v9_def, ← v8_def, ← v7_def,
          ← v5_def, ← v6_def, ← v10_def, ← v11_def, ← v12_def, ← v13_def, ← v20_def, ← v21_def,
          ← v22_def, ← v23_def]
        simp only [idx _ (by decide : 1 < 16), idx _ (by decide : 2 < 16), idx _ (by decide : 3 < 16),
          idx _ (by decide : 4 < 16), idx _ (by decide : 5 < 16), idx _ (by decide : 6 < 16),
          idx _ (by decide : 7 < 16), idx _ (by decide : 8 < 16), idx _ (by decide : 9 < 16)]
        exact lebs2ipK_chunk Bv i A[1]! (fun k hk => hbool _ (by omega))
      have hml : (lebs2ipK v31 v9).toNat ≤ 1023 := hm.1 ▸ hm.2
      -- the table entry
      have t0 : v45 = T[8 * chunkVal Bv i]! := by rw [← v45_def, tbl_idx0 _ hml, hm.1]
      have t1 : v46 = T[8 * chunkVal Bv i + 1]! := by rw [← v46_def, tbl_idx _ hml 8 (by decide) (by decide), hm.1]
      have t2 : v47 = T[8 * chunkVal Bv i + 2]! := by rw [← v47_def, tbl_idx _ hml 16 (by decide) (by decide), hm.1]
      have t3 : v48 = T[8 * chunkVal Bv i + 3]! := by rw [← v48_def, tbl_idx _ hml 24 (by decide) (by decide), hm.1]
      have t4 : v53 = T[8 * chunkVal Bv i + 4]! := by rw [← v53_def, tbl_idx _ hml 32 (by decide) (by decide), hm.1]
      have t5 : v54 = T[8 * chunkVal Bv i + 5]! := by rw [← v54_def, tbl_idx _ hml 40 (by decide) (by decide), hm.1]
      have t6 : v55 = T[8 * chunkVal Bv i + 6]! := by rw [← v55_def, tbl_idx _ hml 48 (by decide) (by decide), hm.1]
      have t7 : v56 = T[8 * chunkVal Bv i + 7]! := by rw [← v56_def, tbl_idx _ hml 56 (by decide) (by decide), hm.1]
      simp only [Nat.reduceMul, Nat.shiftRight_zero] at post73_6 post73_8 post79_6 post79_8
      have hS : [BitVec.ofNat 64 (leLimbsToNat [v45, v46, v47, v48] * Fp.rInv % Fp.p),
          BitVec.ofNat 64 ((leLimbsToNat [v45, v46, v47, v48] * Fp.rInv % Fp.p) >>> 64),
          BitVec.ofNat 64 ((leLimbsToNat [v45, v46, v47, v48] * Fp.rInv % Fp.p) >>> 128),
          BitVec.ofNat 64 ((leLimbsToNat [v45, v46, v47, v48] * Fp.rInv % Fp.p) >>> 192),
          BitVec.ofNat 64 (leLimbsToNat [v53, v54, v55, v56] * Fp.rInv % Fp.p),
          BitVec.ofNat 64 ((leLimbsToNat [v53, v54, v55, v56] * Fp.rInv % Fp.p) >>> 64),
          BitVec.ofNat 64 ((leLimbsToNat [v53, v54, v55, v56] * Fp.rInv % Fp.p) >>> 128),
          BitVec.ofNat 64 ((leLimbsToNat [v53, v54, v55, v56] * Fp.rInv % Fp.p) >>> 192)] =
          sEntryW T (chunkVal Bv i) := by
        rw [sEntryW, natToLeLimbs_cells4, natToLeLimbs_cells4, t0, t1, t2, t3, t4, t5, t6, t7]; rfl
      -- the accumulator step
      have hrep' := AccRep.step T _ acc (chunkVal Bv i) hrep _ _ _ _ _ _ _ _ hS post73_0 post73_1 post73_7
        post73_6 post73_8 post79_0 post79_1 post79_7 post79_6 post79_8
      rw [← sinFold_append, ← chunks_succ] at hrep'
      have hcodes := And.intro (codeAt_of_code_eq hcode hcodeC) (And.intro (codeAt_of_code_eq hcode hcodeL)
        (And.intro (codeAt_of_code_eq hcode hcodeP) (And.intro (codeAt_of_code_eq hcode hcodeT)
        (And.intro (codeAt_of_code_eq hcode hcodeI) (And.intro (codeAt_of_code_eq hcode hcodeCmp)
        (And.intro (codeAt_of_code_eq hcode hcodeAA) (And.intro (codeAt_of_code_eq hcode hcodeLR)
        (And.intro (codeAt_of_code_eq hcode hcodeAdd) (codeAt_of_code_eq hcode hcodeM)))))))))
      obtain ⟨hcode', hcodeL', hcodeP', hcodeT', hcodeI', hcodeCmp', hcodeAA', hcodeLR', hcodeAdd', hcodeM'⟩ := hcodes
      have hx21' : s_87.getReg .x21 = BitVec.ofNat 64 (10 * n) := by
        rw [hx21, ← v42_def]; exact x21_step n (by omega)
      have hx22' : s_87.getReg .x22 = bp + BitVec.ofNat 64 (10 * (i + 1)) := by
        rw [hx22, ← v41_def]; exact x22_step bp i
      have hc' : s_87.code = c := hcode.trans hc
    -- back to the head: `n ≥ 1` chunks left
    · have hn0 : n ≠ 0 := by
        intro h0; subst h0
        simp only [bne_iff_ne, ne_eq] at hbr86
        exact hbr86 (by rw [← v42_def]; exact x21_step 0 (by omega))
      refine ih (i + 1) s_87 _ _ _ (by omega) (by omega) hrep' hpc hc' hcode' hcodeL' hcodeP' hcodeT' hcodeI'
        hcodeCmp' hcodeAA' hcodeLR' hcodeAdd' hcodeM' hcw hro hx2 hstk hhi hx3 hx4 hx8 hx9 hx18 hx19 hx20
        hx21' rfl hx22' rfl hx23 hx24 hx25 hx26 hR0 hokT hR1 hokB ⟨_, by rfl, hR3⟩ hokA hR2 hokacc ⟨_, by rfl, hR4⟩ hokC
        ⟨_, by rfl, hR5⟩ hokD ⟨_, by rfl, hR6⟩ hokE ⟨_, by rfl, hR7⟩ hokF hdB ?_
      intro u acc'' hpc' hc'' h2' h3' h4' h8' h9' h18' h19' hun hreg hrep''
      refine hk u acc'' hpc' hc'' h2' h3' h4' h8' h9' h18' h19' (hunch.trans hun) hreg ?_
      rwa [show i + 1 + n = i + (n + 1) by omega] at hrep''
    -- the exit: this was the last chunk
    · have hn0 : n = 0 := by
        simp only [bne_iff_ne, ne_eq, not_not] at hbr86
        rw [← v42_def, x21_step n (by omega)] at hbr86
        exact ofNat_ten_eq_zero n (by omega) hbr86
      subst hn0
      exact hk s_87 _ hpc hc' hx2 hx3 hx4 hx8 hx9 hx18 hx19 hunch hR2 hrep'

end Cases.Zip2005
