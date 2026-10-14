/-
  Cases.Zip2005.Precompile.Prime -- `Sp1.pallasP` is prime, kernel-checked.

  A Pratt certificate: Lucas's theorem (`lucas_primality`, Mathlib) applied at
  each node, with the two exponentiation side conditions discharged by *the
  model's own* `Accel.powMod` evaluated by `decide` -- the kernel's GMP-backed
  `Nat` arithmetic -- and transported to `ZMod p` by `cast_powMod`. No
  `native_decide`, no new axiom.

  The factorisations and witnesses are those of CompElliptic's
  `PALLAS_BASE_is_prime` (`CompElliptic/Fields/Pasta.lean`, generated from
  PARI/GP factorisations of `p - 1`); the technique there is CompPoly's
  `PrattCertificate'`, which this reproduces with a Boolean checker instead so
  that nothing from the `spec/` package (a different toolchain) is imported.
-/

import Cases.Zip2005.Precompile.PowMod
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime
import Mathlib.Tactic.NormNum.Prime

namespace Cases.Zip2005.Precompile

open RiscvZkvm.Rv64

/-- One Lucas node, as a Boolean the kernel evaluates: `fs` lists the prime
    factorisation of `p - 1` as `(q, k)` pairs, and `a` is a witness of order
    `p - 1` modulo `p`. The primality of each `q` is a separate obligation
    (`prime_of_lucasCheck`'s `hfs`), so certificates nest. -/
def lucasCheck (p a : Nat) (fs : List (Nat × Nat)) : Bool :=
  decide (p < 2 ^ 512) && decide (2 ≤ p) &&
  ((fs.map fun qk => qk.1 ^ qk.2).prod == p - 1) &&
  (Accel.powMod a (p - 1) p == 1) &&
  fs.all fun qk => Accel.powMod a ((p - 1) / qk.1) p != 1

/-- Soundness of one Lucas node. -/
theorem prime_of_lucasCheck {p a : Nat} {fs : List (Nat × Nat)}
    (hfs : ∀ qk ∈ fs, qk.1.Prime) (h : lucasCheck p a fs = true) : p.Prime := by
  simp only [lucasCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨hlt, h2⟩, hprod⟩, hpow⟩, hnot⟩ := h
  refine lucas_primality p (a : ZMod p) ?_ ?_
  · rw [← cast_powMod (by omega), hpow, Nat.cast_one]
  · intro q hq hdvd
    rw [← hprod] at hdvd
    obtain ⟨d, hd, hqd⟩ := (Prime.dvd_prod_iff (Nat.prime_iff.mp hq)).mp hdvd
    obtain ⟨qk, hmem, rfl⟩ := List.mem_map.mp hd
    have hq' : q = qk.1 :=
      (Nat.prime_dvd_prime_iff_eq hq (hfs qk hmem)).mp (hq.dvd_of_dvd_pow hqd)
    subst hq'
    have hexp : (p - 1) / qk.1 < 2 ^ 512 := by
      have := Nat.div_le_self (p - 1) qk.1; omega
    rw [← cast_powMod hexp]
    intro heq
    have := (ZMod.natCast_eq_natCast_iff' _ 1 p).mp (heq.trans Nat.cast_one.symm)
    rw [Nat.mod_eq_of_lt (by rw [powMod_eq hexp]; exact Nat.mod_lt _ (by omega)),
      Nat.mod_eq_of_lt (by omega)] at this
    exact hnot qk hmem this

/-! ### The certificate tree for `p` -/

theorem prime_417677162933 : Nat.Prime 417677162933 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (59, 1), (1973, 1), (897019, 1)])
    (by
      intro qk h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h <;> subst h <;> norm_num)
    (by decide +kernel)

theorem prime_539204044132271846773 : Nat.Prime 539204044132271846773 :=
  prime_of_lucasCheck (a := 5)
    (fs := [(2, 2), (3, 5), (89, 1), (14923, 1), (417677162933, 1)])
    (by
      intro qk h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h <;> subst h <;>
        first | exact prime_417677162933 | norm_num)
    (by decide +kernel)

theorem prime_22160661629 : Nat.Prime 22160661629 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 2), (7, 1), (19, 1), (41655379, 1)])
    (by
      intro qk h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h <;> subst h <;> norm_num)
    (by decide +kernel)

theorem prime_325086459374267 : Nat.Prime 325086459374267 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (509, 1), (413527, 1), (772231, 1)])
    (by
      intro qk h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h <;> subst h <;> norm_num)
    (by decide +kernel)

theorem prime_8999194758858563409123804352480028797519453 :
    Nat.Prime 8999194758858563409123804352480028797519453 :=
  prime_of_lucasCheck (a := 2)
    (fs := [(2, 2), (3, 4), (11, 1), (2531, 1), (115603, 1), (1197907, 1),
      (22160661629, 1), (325086459374267, 1)])
    (by
      intro qk h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h | h <;> subst h <;>
        first | exact prime_22160661629 | exact prime_325086459374267 | norm_num)
    (by decide +kernel)

/-- **`Sp1.pallasP` is prime.** The Pallas base field is a field. -/
theorem pallasP_prime : Nat.Prime Sp1.pallasP :=
  prime_of_lucasCheck (a := 5)
    (fs := [(2, 32), (3, 1), (463, 1), (539204044132271846773, 1),
      (8999194758858563409123804352480028797519453, 1)])
    (by
      intro qk h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h <;> subst h <;>
        first
          | exact prime_539204044132271846773
          | exact prime_8999194758858563409123804352480028797519453
          | norm_num)
    (by decide +kernel)

instance fact_pallasP_prime : Fact (Nat.Prime Sp1.pallasP) := ⟨pallasP_prime⟩

end Cases.Zip2005.Precompile
