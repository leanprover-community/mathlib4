/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Fabrizio Barroero, Laura Capuano, Nirvana Coppola,
María Inés de Frutos Fernández, Sam van Gool, Silvain Rideau-Kikuchi, Amos Turchet,
Francesco Veneziano
-/

import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.NumberTheory.Padics.PadicNorm

/-!
# Ostrowski’s Theorem

The goal of this file is to prove Ostrowski’s Theorem which gives a list of all the nontrivial
absolute values on a number field up to equivalence. (TODO)

## References
* [K. Conrad, *Ostroski's Theorem for Q*][conradQ]
* [K. Conrad, *Ostroski for number fields*][conradnumbfield]
* [J. W. S. Cassels, *Local fields*][cassels1986local]


## Tags
ring_norm, ostrowski
-/

namespace Rat.MulRingNorm
open Int

variable {f g : MulRingNorm ℚ}

/-- Values of a multiplicative norm of the rationals coincide on ℕ if and only if they coincide
on ℤ. -/
lemma eq_on_Nat_iff_eq_on_Int : (∀ n : ℕ , f n = g n) ↔ (∀ n : ℤ , f n = g n) := by
  refine ⟨fun h z ↦ ?_, fun a n ↦ a n⟩
  obtain ⟨n , rfl | rfl⟩ := eq_nat_or_neg z <;>
  simp only [Int.cast_neg, Int.cast_natCast, map_neg_eq_map, h n]

/-- Values of a multiplicative norm of the rationals are determined by the values on the natural
numbers. -/
lemma eq_on_Nat_iff_eq : (∀ n : ℕ , f n = g n) ↔ f = g := by
  refine ⟨fun h ↦ ?_, fun h n ↦ congrFun (congrArg DFunLike.coe h) ↑n⟩
  ext z
  rw [← Rat.num_div_den z, map_div₀, map_div₀, h, eq_on_Nat_iff_eq_on_Int.mp h]

/-- The equivalence class of a multiplicative norm on the rationals is determined by its values on
the natural numbers. -/
lemma equiv_on_Nat_iff_equiv : (∃ c : ℝ, 0 < c ∧ (∀ n : ℕ , (f n)^c = g n)) ↔
    f.equiv g := by
    refine ⟨fun ⟨c, hc, h⟩ ↦ ⟨c, ⟨hc, ?_⟩⟩, fun ⟨c, hc, h⟩ ↦ ⟨c, ⟨hc, fun n ↦ by rw [← h]⟩⟩⟩
    ext x
    rw [← Rat.num_div_den x, map_div₀, map_div₀, Real.div_rpow (apply_nonneg f _)
      (apply_nonneg f _), h x.den, ← MulRingNorm.apply_natAbs_eq,← MulRingNorm.apply_natAbs_eq,
      h (natAbs x.num)]


/-- The p-adic norm on ℚ. -/
def mulRingNorm_padic (p : ℕ) [hp : Fact (Nat.Prime p)] : MulRingNorm ℚ :=
{ toFun     := λ x : ℚ => (padicNorm p x : ℝ),
  map_zero' := by simp only [padicNorm.zero, Rat.cast_zero]
  add_le'   := by simp only; norm_cast; exact fun r s => padicNorm.triangle_ineq r s
  neg'      := by simp only [eq_self_iff_true, forall_const, padicNorm.neg];
  eq_zero_of_map_eq_zero' := by simp only [Rat.cast_eq_zero]; apply padicNorm.zero_of_padicNorm_eq_zero
  map_one' := by simp only [ne_eq, one_ne_zero, not_false_eq_true, padicNorm.eq_zpow_of_nonzero,
    padicValRat.one, neg_zero, zpow_zero, Rat.cast_one]
  map_mul' := by simp only [padicNorm.mul, Rat.cast_mul, forall_const]
}

@[simp] lemma mul_ring_norm_eq_padic_norm (p : ℕ) [Fact (Nat.Prime p)] (r : ℚ) :
  mulRingNorm_padic p r = padicNorm p r := rfl

/-!
Throughout this file, `f` is an arbitrary absolute value.
-/
variable {f : MulRingNorm ℚ}

open Rat.MulRingNorm
section Nonarchimedean

-- ## Non-archimedean: step 1 define `p = smallest n s. t. 0 < |n| < 1`

/-- There exists a minimal positive integer with absolute value smaller than 1 -/
lemma p_exists (bdd: ∀ n : ℕ, f n ≤ 1) (hf_nontriv : f ≠ 1) : ∃ (p : ℕ), (0 < f p ∧ f p < 1) ∧
    ∀ (m : ℕ), 0 < f m ∧ f m < 1 → p ≤ m := by
  -- there is a positive integer with absolute value different from one
  have hn : ∃ (n : ℕ), n ≠ 0 ∧ f n ≠ 1 := by
    by_contra h
    apply hf_nontriv
    push_neg at h
    apply eq_on_Nat_iff_eq.1
    intro n
    by_cases hn0 : n=0
    · rw [hn0]
      simp only [CharP.cast_eq_zero, map_zero]
    · push_neg at hn0
      simp only [MulRingNorm.apply_one, Nat.cast_eq_zero, hn0, ↓reduceIte, h n hn0]
  obtain ⟨n, hn1, hn2⟩ := hn
  set P := {m : ℕ | 0 < f ↑m ∧ f ↑m < 1}
  have hPnonempty : Set.Nonempty P := by
    use n
    exact ⟨map_pos_of_ne_zero f (Nat.cast_ne_zero.mpr hn1), lt_of_le_of_ne (bdd n) hn2⟩
  use sInf P
  refine ⟨Nat.sInf_mem hPnonempty, ?_⟩
  intro m hm
  exact Nat.sInf_le hm

-- ## Non-archimedean case: Step 2. p is prime

variable (bdd: ∀ n : ℕ, f n ≤ 1)  (p : ℕ)  (hp0 : 0 < f p)  (hp1 : f p < 1)
  (hmin : ∀ (m : ℕ), 0 < f m ∧ f m < 1 → p ≤ m)

private lemma one_lt_of_ne_zero_one {a : ℕ} (ne_0 : a ≠ 0) (ne_1 : a ≠ 1) : 1 < a := by
  rcases a with _ | a
  · exact (ne_0 rfl).elim
  · rw [Nat.succ_ne_succ, ← pos_iff_ne_zero] at ne_1
    exact Nat.succ_lt_succ ne_1

 /-- The minimal positive integer with absolute value smaller than 1 is a prime number-/
lemma p_is_prime : (Prime p) := by
  rw [← Nat.irreducible_iff_prime]
  constructor
  · rw [Nat.isUnit_iff]
    intro p1
    simp only [p1, Nat.cast_one, map_one, lt_self_iff_false] at hp1
  · intro a b hab
    rw [Nat.isUnit_iff, Nat.isUnit_iff]
    by_contra con
    push_neg at con
    obtain ⟨a_neq_1, b_neq_1⟩ := con
    apply not_le_of_lt hp1
    rw [hab]
    simp only [Nat.cast_mul, map_mul]
    have neq_0 {a b : ℕ} (hab : p = a * b) : a ≠ 0 := by
      intro an0
      rw [an0, zero_mul] at hab
      rw [hab] at hp0
      rw_mod_cast [map_zero] at hp0
      simp only [lt_self_iff_false] at hp0
    have one_le_f (a b : ℕ) (hab : p = a * b) (one_lt_b : 1 < b) : 1 ≤ f a := by
      by_contra ca
      apply lt_of_not_ge at ca
      apply (@not_le_of_gt _ _ p a)
      · rw [hab, gt_iff_lt]
        exact lt_mul_of_one_lt_right ((pos_iff_ne_zero ).2 (neq_0 hab)) one_lt_b
      · apply hmin
        refine ⟨?_ ,ca⟩
        apply map_pos_of_ne_zero
        exact_mod_cast (neq_0 hab)
    have hba : p = b * a := by
      rw [mul_comm]
      exact hab
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_f a b hab (one_lt_of_ne_zero_one (neq_0 hba) b_neq_1)
    · exact one_le_f b a hba (one_lt_of_ne_zero_one (neq_0 hab) a_neq_1)

-- ## Step 3
/-- a natural number not divible by p has absolute value 1 -/
lemma not_divisible_norm_one (m : ℕ) (hpm : ¬ p ∣ m ) : f m = 1 := by
  rw [le_antisymm_iff]
  refine ⟨bdd m, ?_ ⟩
  by_contra hm
  apply lt_of_not_le at hm
  set M := (f p) ⊔ (f m) with hM
  set k := Nat.ceil (Real.logb  M (1/2)) + 1 with hk
  have hcopr : IsCoprime (p ^ k : ℤ) (m ^ k) := by
    apply IsCoprime.pow (Nat.Coprime.isCoprime _)
    rw [Nat.Prime.coprime_iff_not_dvd (Prime.nat_prime (p_is_prime p hp0 hp1 hmin))]
    exact_mod_cast hpm
  obtain ⟨a, b, bezout⟩ := hcopr
  have le_half x (hx0 : 0 < x) (hx1 : x < 1) (hxM : x ≤ M) : x ^ k < 1/2 := by
    calc
    x ^ k = x ^ (k : ℝ) := by norm_cast
    _ < x ^ Real.logb M (1 / 2) := by
      apply Real.rpow_lt_rpow_of_exponent_gt hx0 hx1
      rw [hk]
      apply lt_of_le_of_lt (Nat.le_ceil (Real.logb M (1/2)))
      norm_cast
      exact lt_add_one ⌈Real.logb M (1 / 2)⌉₊
    _ ≤ x ^ Real.logb x (1/2) := by
      apply Real.rpow_le_rpow_of_exponent_ge hx0 (le_of_lt hx1)
      simp only [← Real.log_div_log]
      ring_nf
      simp only [one_div, Real.log_inv, neg_mul, neg_le_neg_iff]
      rw [mul_le_mul_left (Real.log_pos one_lt_two)]
      rw [inv_le_inv_of_neg _ ((Real.log_neg_iff hx0).2 hx1)]
      · exact Real.log_le_log hx0 hxM
      · rw [Real.log_neg_iff]
        · rw [hM, sup_lt_iff]
          exact ⟨hp1, hm⟩
        · rw [hM, lt_sup_iff]
          left
          exact hp0
    _ = 1/2 := by
      rw [Real.rpow_logb hx0 (ne_of_lt hx1)]
      simp only [one_div, inv_pos, Nat.ofNat_pos]
  apply lt_irrefl (1 : ℝ)
  calc
    (1:ℝ) = f 1 := by rw [map_one]
    _ = f (a * p ^ k + b * m ^ k) := by
      rw_mod_cast [bezout]
      norm_cast
    _ ≤ f (a * p ^ k) + f (b * m ^ k) := f.add_le' (a * p ^ k) (b * m ^ k)
    _ ≤ 1 * (f p) ^ k + 1 * (f m) ^ k := by
      simp only [map_mul, map_pow, le_refl]
      gcongr
      all_goals rw [← MulRingNorm.apply_natAbs_eq]; apply bdd
    _ = (f p) ^ k + (f m) ^ k := by simp only [one_mul]
    _ < 1 := by
      rw [← add_halves (a:=1)]
      apply add_lt_add
      · apply le_half (f ↑p) hp0 hp1
        exact le_sup_left
      · apply le_half (f m) _ hm le_sup_right
        apply map_pos_of_ne_zero
        intro m0
        apply hpm
        rw_mod_cast [m0]
        exact dvd_zero p

-- ## Non-archimedean case: step 4

lemma abs_p_eq_p_minus_t : ∃ (t : ℝ), 0 < t ∧ f p = p ^ (-t) := by
  use - Real.logb p (f p)
  have pprime : Nat.Prime p := (Prime.nat_prime (p_is_prime p hp0 hp1 hmin))
  constructor
  · rw [Left.neg_pos_iff]
    apply Real.logb_neg _ hp0 hp1
    rw [Nat.one_lt_cast]
    exact Nat.Prime.one_lt pprime
  · rw [neg_neg]
    apply (Real.rpow_logb (by exact_mod_cast Nat.Prime.pos pprime) _ hp0).symm
    simp only [ne_eq, Nat.cast_eq_one,Nat.Prime.ne_one pprime, not_false_eq_true]

-- ## Non-archimedean case: end goal
/--
  If `f` is bounded and not trivial, then it is equivalent to a p-adic absolute value.
-/
theorem equiv_padic_of_bounded (bdd: ∀ n : ℕ, f n ≤ 1) (hf_nontriv : f ≠ 1) :
∃ p, ∃ (hp : Fact (Nat.Prime p)), MulRingNorm.equiv f (mulRingNorm_padic p) := by
  obtain ⟨p, hfp, hmin⟩ := p_exists bdd hf_nontriv
  have hprime : Prime p := p_is_prime p hfp.1 hfp.2 hmin
  use p
  have hprime_fact : Fact (Nat.Prime p) := fact_iff.2 (Prime.nat_prime hprime)
  use (hprime_fact)
  obtain ⟨t, h⟩ := abs_p_eq_p_minus_t p hfp.1 hfp.2 hmin
  rw [← equiv_on_Nat_iff_equiv]
  use (t⁻¹)
  refine ⟨by simp only [one_div, inv_pos, h.1], ?_ ⟩
  have oneovertnezero : t⁻¹ ≠ 0 := by
    simp only [ne_eq, inv_eq_zero]
    linarith [h.1]
  intro n
  by_cases hn : n=0
  · rw [hn]
    simp only [CharP.cast_eq_zero, map_zero, ne_eq, oneovertnezero, not_false_eq_true,
      Real.zero_rpow]
  · push_neg at hn
    rcases Nat.exists_eq_pow_mul_and_not_dvd hn p (Nat.Prime.ne_one (Prime.nat_prime hprime))
      with ⟨ e, m, hpm, hnpm⟩
    rw [hnpm]
    simp only [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, mul_ring_norm_eq_padic_norm,
      padicNorm.padicNorm_p_of_prime, Rat.cast_inv, Rat.cast_natCast, inv_pow]
    rw [not_divisible_norm_one bdd p hfp.1 hfp.2 m hpm, h.2]
    rw [← padicNorm.nat_eq_one_iff] at hpm
    rw [hpm]
    simp only [mul_one, Rat.cast_one]
    rw [← Real.rpow_natCast_mul (Real.rpow_nonneg (Nat.cast_nonneg p) _ ),
      ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm ↑e t⁻¹, ← mul_assoc]
    simp only [neg_mul]
    rw [mul_inv_cancel (by linarith only [h.1]), one_mul, Real.rpow_neg (Nat.cast_nonneg p),
      Real.rpow_natCast]

end Nonarchimedean

end Rat.MulRingNorm
