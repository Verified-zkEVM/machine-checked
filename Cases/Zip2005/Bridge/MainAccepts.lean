import Cases.Zip2005.Bridge.Accepts
import Cases.Zip2005.Bridge.WitnessWords
import Cases.Zip2005.Bridge.InstanceWords

/-!
# `main`'s accepting path decodes its input

`guestAccepts_main` is the pure half of `main_spec`'s close. Its hypotheses are, verbatim, what
the symbolic execution of `main` leaves at the return: the two hint reads (`L`, `L1`, the hint
words laid over the read windows), the instance moved through its three `memcpy`s (`A27`, `A34`,
`A56`), the witness visitor's `Ok` disjunct over the struct `V` (`witW`, `witOkCond`) and segment
A1's facts over the struct's cells (`GuestW`, the tag bytes, the `negate` niche not taken). The
conclusion is the top-level theorem's: `GuestAccepts I`.
-/

namespace Cases.Zip2005.Top

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005
open Zcash.Circuits (Fq)

set_option autoImplicit false

theorem neg_bit (b : BitVec 8) (hb : b.toNat < 2) :
    (!(BitVec.zeroExtend 64 b &&& 1#64 == 0#64)) = (UInt8.ofBitVec b == 1) := by
  have h : b = 0#8 ∨ b = 1#8 := by
    have : b.toNat = 0 ∨ b.toNat = 1 := by omega
    rcases this with h | h
    · left; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
    · right; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
  rcases h with rfl | rfl <;> decide

theorem witO4_ge (W : List Word) : 1295 ≤ witO4 W := by
  unfold witO4 witO3 witO2 witO1 optLen
  split <;> split <;> split <;> omega

set_option maxHeartbeats 4000000 in
/-- **`main`'s accepting path decodes its input and satisfies the guest's statement.** -/
theorem guestAccepts_main (I : List (BitVec 8)) (L L1 : Word)
    (B B1 JL JL2 P15 P68 V VL WL O D27 D56 A27 A34 A56 : List Word)
    (hL : bytesToWordLE (List.take 8 I) = L) (hLI : 8 + L.toNat ≤ I.length) (hl128 : 128 ≤ L.toNat)
    (hB : hintWords (List.take L.toNat (List.drop 8 I)) = B) (hBp : P15 = overlay B JL)
    (hJL : JL.length = 175)
    (h27 : mcpyW D27 [(instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[2]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[3]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[4]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[5]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[6]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[7]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[8]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[9]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[10]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[11]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[12]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[13]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[14]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[15]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[16]!] 0 0 113 15 = A27)
    (h34 : mcpyW [(instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[0]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[1]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[2]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[3]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[4]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[5]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[6]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[7]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[8]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[9]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[10]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[11]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[12]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[13]!, (instW O ([P15[0]!, P15[1]!, P15[2]!, P15[3]!] ++ [P15[4]!, P15[5]!, P15[6]!, P15[7]!] ++ [P15[8]!, P15[9]!, P15[10]!, P15[11]!] ++ [P15[12]!, P15[13]!, P15[14]!, P15[15]!]))[14]!] [A27[0]!, A27[1]!, A27[2]!, A27[3]!, A27[4]!, A27[5]!, A27[6]!, A27[7]!, A27[8]!, A27[9]!, A27[10]!, A27[11]!, A27[12]!, A27[13]!, A27[14]!] 0 0 113 15 = A34)
    (h56 : mcpyW D56 [A34[0]!, A34[1]!, A34[2]!, A34[3]!, A34[4]!, A34[5]!, A34[6]!, A34[7]!, A34[8]!, A34[9]!, A34[10]!, A34[11]!, A34[12]!, A34[13]!, A34[14]!] 7 0 113 15 = A56)
    (hL1 : bytesToWordLE (List.take 8 (List.drop (8 + L.toNat) I)) = L1)
    (hLI1 : 8 + L1.toNat ≤ (List.drop (8 + L.toNat) I).length)
    (hB1 : hintWords (List.take L1.toNat (List.drop 8 (List.drop (8 + L.toNat) I))) = B1)
    (hBp1 : P68 = overlay B1 JL2) (hJL2 : JL2.length = 175)
    (hok : extractByte V[173]! 7 = 2#8 ∨ V = witW WL V ∧ witOkCond WL L1.toNat)
    (halq : leLimbsToNat [VL[128]!, VL[129]!, VL[130]!, VL[131]!] < Fq.q)
    (hG : GuestW [A56[3]!, A56[4]!, A56[5]!, A56[6]!] [A56[7]!, A56[8]!, A56[9]!, A56[10]!] [VL[132]!, VL[133]!, VL[134]!, VL[135]!] [VL[136]!, VL[137]!, VL[138]!, VL[139]!] [VL[140]!, VL[141]!, VL[142]!, VL[143]!] [VL[144]!, VL[145]!, VL[146]!, VL[147]!] [VL[148]!, VL[149]!, VL[150]!, VL[151]!] [VL[152]!, VL[153]!, VL[154]!, VL[155]!] [VL[156]!, VL[157]!, VL[158]!, VL[159]!] (natToLeLimbs 4 (Fq.mul (leLimbsToNat [VL[128]!, VL[129]!, VL[130]!, VL[131]!]) Fq.R2)) (skWord VL[161]! VL[162]!) (skWord VL[162]! VL[163]!) (skWord VL[163]! VL[164]!) (skWord VL[164]! VL[165]!) (BitVec.zeroExtend 64 (extractByte VL[173]! 7) &&& 1#64) VL[160]!)
    (hWLl : WL.length = 174) (hWL : ∀ i, i < 174 → WL[i]! = P68[i]!)
    (hVL : ∀ k, k < 174 → VL[k]! = V[k]!)
    (hsk : extractByte VL[161]! 4 ≠ 0#8) (hniche : extractByte VL[173]! 7 ≠ 2#8) :
    GuestAccepts I := by
  have hVLk := hVL
  rw [hVLk 128 (by decide), hVLk 129 (by decide), hVLk 130 (by decide), hVLk 131 (by decide), hVLk 132 (by decide), hVLk 133 (by decide), hVLk 134 (by decide), hVLk 135 (by decide), hVLk 136 (by decide), hVLk 137 (by decide), hVLk 138 (by decide), hVLk 139 (by decide), hVLk 140 (by decide), hVLk 141 (by decide), hVLk 142 (by decide), hVLk 143 (by decide), hVLk 144 (by decide), hVLk 145 (by decide), hVLk 146 (by decide), hVLk 147 (by decide), hVLk 148 (by decide), hVLk 149 (by decide), hVLk 150 (by decide), hVLk 151 (by decide), hVLk 152 (by decide), hVLk 153 (by decide), hVLk 154 (by decide), hVLk 155 (by decide), hVLk 156 (by decide), hVLk 157 (by decide), hVLk 158 (by decide), hVLk 159 (by decide), hVLk 160 (by decide), hVLk 161 (by decide), hVLk 162 (by decide), hVLk 163 (by decide), hVLk 164 (by decide), hVLk 165 (by decide), hVLk 173 (by decide)] at hG
  rw [hVLk 128 (by decide), hVLk 129 (by decide), hVLk 130 (by decide), hVLk 131 (by decide)] at halq
  rw [hVLk 161 (by decide)] at hsk
  rw [hVLk 173 (by decide)] at hniche
  rcases hok with h2 | ⟨hV, hokc⟩
  · exact absurd h2 hniche
  -- the records
  have hI1 : instRec I = inBytes (List.take L.toNat (List.drop 8 I)) := by
    unfold instRec; rw [record_inBytes I (by omega), hL]
  have h8 : 8 ≤ (List.drop (8 + L.toNat) I).length := by omega
  have hI2 : witRec I = inBytes (List.take L1.toNat (List.drop 8 (List.drop (8 + L.toNat) I))) := by
    unfold witRec; rw [record_inBytes I (by omega), hL]
    show (record (inBytes (List.drop (8 + L.toNat) I))).1 = _
    rw [record_inBytes _ h8, hL1]
  have hr1l : (List.take L.toNat (List.drop 8 I)).length = L.toNat := by simp; omega
  have hr2l : (List.take L1.toNat (List.drop 8 (List.drop (8 + L.toNat) I))).length = L1.toNat := by
    simp at hLI1 ⊢; omega
  -- the instance's words
  subst hBp hB
  obtain ⟨e32, e64⟩ := inst_words (List.take L.toNat (List.drop 8 I)) JL O D27 D56 A27 A34 A56 hJL
    (by omega) h27 h34 h56
  rw [e32, e64] at hG
  -- the witness's words
  have hW2 : WL = overlay (hintWords (List.take L1.toNat (List.drop 8 (List.drop (8 + L.toNat) I)))) (JL2.take 174) := by
    apply List.ext_getElem
    · rw [hWLl]; simp [overlay, hJL2]
    · intro i h1 h2
      rw [← getElem!_pos WL i h1, hWL i (by omega), ← getElem!_pos _ i h2, hBp1, ← hB1]
      have hi : i < 174 := by omega
      simp only [overlay, List.length_take, hJL2]
      rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_map,
        List.getElem_range, List.getElem_range]
      by_cases hb : i < (hintWords (List.take L1.toNat (List.drop 8 (List.drop (8 + L.toNat) I)))).length
      · simp only [hb, if_true]
      · simp only [hb, if_false]
        rw [getElem!_pos JL2 i (by omega), getElem!_pos (JL2.take 174) i (by simp; omega), List.getElem_take]
  rw [hW2] at hV hokc
  generalize List.take L1.toNat (List.drop 8 (List.drop (8 + L.toNat) I)) = r2 at hI2 hr2l hV hokc
  obtain ⟨hc0, -, -, hc4, hc5⟩ := hokc
  have hJ2 : 174 ≤ (JL2.take 174).length := by simp [hJL2]
  have hw4 := witO4_ge (overlay (hintWords r2) (JL2.take 174))
  have hw4' := witO4_le (overlay (hintWords r2) (JL2.take 174))
  have hr2 : 297 ≤ r2.length := by omega
  have hw5 : witO4 (overlay (hintWords r2) (JL2.take 174)) + 1 ≤ r2.length := by omega
  have hc : ∀ n : ℕ, V[n]! = (witW (overlay (hintWords r2) (JL2.take 174)) V)[n]! := fun n => by conv_lhs => rw [hV]
  rw [hc 161, witW_skTag r2 (JL2.take 174) V hJ2 hr2] at hsk
  rw [inByte_overlay r2 (JL2.take 174) 0 (by omega) (by omega)] at hc0
  have htag : r2[0]! = 1#8 := by
    have hne : r2[0]!.toNat ≠ 0 := fun h => hsk (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    apply BitVec.eq_of_toNat_eq; show r2[0]!.toNat = 1; omega
  have hs : inByte (overlay (hintWords r2) (JL2.take 174)) 0 0 = 1#8 := by
    rw [inByte_overlay r2 (JL2.take 174) 0 (by omega) (by omega)]; exact htag
  have hno := witO4_negOff r2 (JL2.take 174) hJ2 hs hw5
  have e132 : [V[132]!, V[133]!, V[134]!, V[135]!] = wordsAt r2 65 4 := by
    rw [hc 132, hc 133, hc 134, hc 135]
    exact witW_field r2 (JL2.take 174) V hJ2 hr2 htag 132 (by decide) (by decide)
  have e136 : [V[136]!, V[137]!, V[138]!, V[139]!] = wordsAt r2 97 4 := by
    rw [hc 136, hc 137, hc 138, hc 139]
    exact witW_field r2 (JL2.take 174) V hJ2 hr2 htag 136 (by decide) (by decide)
  have e140 : [V[140]!, V[141]!, V[142]!, V[143]!] = wordsAt r2 129 4 := by
    rw [hc 140, hc 141, hc 142, hc 143]
    exact witW_field r2 (JL2.take 174) V hJ2 hr2 htag 140 (by decide) (by decide)
  have e144 : [V[144]!, V[145]!, V[146]!, V[147]!] = wordsAt r2 161 4 := by
    rw [hc 144, hc 145, hc 146, hc 147]
    exact witW_field r2 (JL2.take 174) V hJ2 hr2 htag 144 (by decide) (by decide)
  have e148 : [V[148]!, V[149]!, V[150]!, V[151]!] = wordsAt r2 193 4 := by
    rw [hc 148, hc 149, hc 150, hc 151]
    exact witW_field r2 (JL2.take 174) V hJ2 hr2 htag 148 (by decide) (by decide)
  have e152 : [V[152]!, V[153]!, V[154]!, V[155]!] = wordsAt r2 225 4 := by
    rw [hc 152, hc 153, hc 154, hc 155]
    exact witW_field r2 (JL2.take 174) V hJ2 hr2 htag 152 (by decide) (by decide)
  have e156 : [V[156]!, V[157]!, V[158]!, V[159]!] = wordsAt r2 257 4 := by
    rw [hc 156, hc 157, hc 158, hc 159]
    exact witW_field r2 (JL2.take 174) V hJ2 hr2 htag 156 (by decide) (by decide)
  have e128 : [V[128]!, V[129]!, V[130]!, V[131]!] = wordsAt r2 33 4 := by
    rw [hc 128, hc 129, hc 130, hc 131]
    exact witW_field r2 (JL2.take 174) V hJ2 hr2 htag 128 (by decide) (by decide)
  have es0 : skWord V[161]! V[162]! = (wordsAt r2 1 4)[0]! := by
    rw [hc 161, hc 162]
    exact witW_sk r2 (JL2.take 174) V hJ2 hr2 htag 0 (by decide)
  have es1 : skWord V[162]! V[163]! = (wordsAt r2 1 4)[1]! := by
    rw [hc 162, hc 163]
    exact witW_sk r2 (JL2.take 174) V hJ2 hr2 htag 1 (by decide)
  have es2 : skWord V[163]! V[164]! = (wordsAt r2 1 4)[2]! := by
    rw [hc 163, hc 164]
    exact witW_sk r2 (JL2.take 174) V hJ2 hr2 htag 2 (by decide)
  have es3 : skWord V[164]! V[165]! = (wordsAt r2 1 4)[3]! := by
    rw [hc 164, hc 165]
    exact witW_sk r2 (JL2.take 174) V hJ2 hr2 htag 3 (by decide)
  have ev : V[160]! = (wordsAt r2 289 1)[0]! := by
    rw [hc 160]; exact witW_value r2 (JL2.take 174) V hJ2 hr2 htag
  have en : extractByte V[173]! 7 = r2[negOff (inBytes r2)]! := by
    rw [hc 173, witW_negate r2 (JL2.take 174) V hJ2 hw5, hno]
  rw [rd r2 (JL2.take 174) hJ2 _ 0 (by omega) (by omega), Nat.add_zero, hno] at hc4
  rw [e132, e136, e140, e144, e148, e152, e156, e128, es0, es1, es2, es3, ev, en] at hG
  refine guestAccepts_of I (List.take L.toNat (List.drop 8 I)) r2 _ _ hI1 hI2 (by omega) hr2
    (by rw [← hno]; omega) htag ?_ ?_ ?_ hG
  · exact fq_parse_val _ (by rw [← e128]; exact halq)
  · rw [inBytes_get r2 _ (by rw [← hno]; omega)]
    show (UInt8.ofBitVec _).toBitVec.toNat < 2
    rw [UInt8.toBitVec_ofBitVec]; exact hc4
  · rw [inBytes_get r2 _ (by rw [← hno]; omega)]
    exact neg_bit _ hc4

end Cases.Zip2005.Top
