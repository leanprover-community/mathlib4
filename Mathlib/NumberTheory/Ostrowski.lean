/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Fabrizio Barroero, Laura Capuano, Nirvana Coppola,
María Inés de Frutos-Fernández, Sam van Gool, Silvain Rideau-Kikuchi, Amos Turchet,
Francesco Veneziano
-/

import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.NumberTheory.Padics.PadicNorm

/-!
# Ostrowski’s Theorem

Ostrowski's Theorem for the field `ℚ`: every absolute value on `ℚ` is equivalent to either a
`p`-adic absolute value or to the standard Archimedean (Euclidean) absolute value.

## TODO

Extend to arbitrary number fields.

## References

* [K. Conrad, *Ostrowski's Theorem for Q*][conradQ]
* [K. Conrad, *Ostrowski for number fields*][conradnumbfield]
* [J. W. S. Cassels, *Local fields*][cassels1986local]

## Tags

ring norm, ostrowski
-/

/- ## Preliminary lemmas on limits -/

open Filter Nat Real Topology

-- For any `C > 0`, the limit of `C ^ (1/k)` is 1 as `k → ∞`
private lemma tendsto_root_atTop_nhds_one {C : ℝ} (hC : 0 < C) :
    Tendsto (fun k : ℕ ↦ C ^ (k : ℝ)⁻¹) atTop (𝓝 1) := by
  convert_to Tendsto ((fun k ↦ C ^ k) ∘ (fun k : ℝ ↦ k⁻¹) ∘ (Nat.cast))
    atTop (𝓝 1)
  exact Tendsto.comp (Continuous.tendsto' (continuous_iff_continuousAt.2
    (fun a ↦ continuousAt_const_rpow hC.ne')) 0 1 (rpow_zero C))
    <| Tendsto.comp tendsto_inv_atTop_zero tendsto_natCast_atTop_atTop

--extends the lemma `tendsto_rpow_div` when the function has natural input
private lemma tendsto_nat_rpow_div :
    Tendsto (fun k : ℕ ↦ (k : ℝ) ^ (k : ℝ)⁻¹) atTop (𝓝 1) := by
  convert_to Tendsto ((fun k : ℝ ↦ k ^ k⁻¹) ∘ Nat.cast) atTop (𝓝 1)
  apply Tendsto.comp _ tendsto_natCast_atTop_atTop
  simp_rw [← one_div]
  exact tendsto_rpow_div

namespace Rat.MulRingNorm
open Int

variable {f g : MulRingNorm ℚ}

/-- Values of a multiplicative norm of the rationals coincide on ℕ if and only if they coincide
on `ℤ`. -/
lemma eq_on_nat_iff_eq_on_Int : (∀ n : ℕ , f n = g n) ↔ (∀ n : ℤ , f n = g n) := by
  refine ⟨fun h z ↦ ?_, fun a n ↦ a n⟩
  obtain ⟨n , rfl | rfl⟩ := eq_nat_or_neg z <;>
  simp only [Int.cast_neg, Int.cast_natCast, map_neg_eq_map, h n]

/-- Values of a multiplicative norm of the rationals are determined by the values on the natural
numbers. -/
lemma eq_on_nat_iff_eq : (∀ n : ℕ , f n = g n) ↔ f = g := by
  refine ⟨fun h ↦ ?_, fun h n ↦ congrFun (congrArg DFunLike.coe h) ↑n⟩
  ext z
  rw [← Rat.num_div_den z, map_div₀, map_div₀, h, eq_on_nat_iff_eq_on_Int.mp h]

/-- The equivalence class of a multiplicative norm on the rationals is determined by its values on
the natural numbers. -/
lemma equiv_on_nat_iff_equiv : (∃ c : ℝ, 0 < c ∧ (∀ n : ℕ , (f n) ^ c = g n)) ↔
    f.equiv g := by
    refine ⟨fun ⟨c, hc, h⟩ ↦ ⟨c, ⟨hc, ?_⟩⟩, fun ⟨c, hc, h⟩ ↦ ⟨c, ⟨hc, fun n ↦ by rw [← h]⟩⟩⟩
    ext x
    rw [← Rat.num_div_den x, map_div₀, map_div₀, div_rpow (by positivity) (by positivity), h x.den,
      ← MulRingNorm.apply_natAbs_eq,← MulRingNorm.apply_natAbs_eq, h (natAbs x.num)]

open Rat.MulRingNorm

section Non_archimedean

/-! ## Non-archimedean case

Every bounded absolute value is equivalent to a `p`-adic absolute value
-/

/-- The mulRingNorm corresponding to the p-adic norm on `ℚ`. -/
def mulRingNorm_padic (p : ℕ) [Fact p.Prime] : MulRingNorm ℚ :=
{ toFun     := fun x : ℚ ↦ (padicNorm p x : ℝ),
  map_zero' := by simp only [padicNorm.zero, Rat.cast_zero]
  add_le'   := by simp only; norm_cast; exact fun r s ↦ padicNorm.triangle_ineq r s
  neg'      := by simp only [forall_const, padicNorm.neg]
  eq_zero_of_map_eq_zero' := by
    simp only [Rat.cast_eq_zero]
    apply padicNorm.zero_of_padicNorm_eq_zero
  map_one' := by simp only [ne_eq, one_ne_zero, not_false_eq_true, padicNorm.eq_zpow_of_nonzero,
    padicValRat.one, neg_zero, zpow_zero, Rat.cast_one]
  map_mul' := by simp only [padicNorm.mul, Rat.cast_mul, forall_const]
}

@[simp] lemma mulRingNorm_eq_padic_norm (p : ℕ) [Fact p.Prime] (r : ℚ) :
  mulRingNorm_padic p r = padicNorm p r := rfl

-- ## Step 1: define `p = minimal n s. t. 0 < f n < 1`

variable (hf_nontriv : f ≠ 1) (bdd : ∀ n : ℕ, f n ≤ 1)

include hf_nontriv bdd in
/-- There exists a minimal positive integer with absolute value smaller than 1. -/
lemma exists_minimal_nat_zero_lt_mulRingNorm_lt_one : ∃ p : ℕ, (0 < f p ∧ f p < 1) ∧
    ∀ m : ℕ, 0 < f m ∧ f m < 1 → p ≤ m := by
  -- There is a positive integer with absolute value different from one.
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, n ≠ 0 ∧ f n ≠ 1 := by
    contrapose! hf_nontriv
    rw [← eq_on_nat_iff_eq]
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp only [Nat.cast_zero, map_zero]
    · simp only [MulRingNorm.apply_one, Nat.cast_eq_zero, hn0, ↓reduceIte, hf_nontriv n hn0]
  set P := {m : ℕ | 0 < f ↑m ∧ f ↑m < 1} -- p is going to be the minimum of this set.
  have hP : P.Nonempty :=
    ⟨n, map_pos_of_ne_zero f (Nat.cast_ne_zero.mpr hn1), lt_of_le_of_ne (bdd n) hn2⟩
  exact ⟨sInf P, Nat.sInf_mem hP, fun m hm ↦ Nat.sInf_le hm⟩

-- ## Step 2: p is prime

variable {p : ℕ} (hp0 : 0 < f p) (hp1 : f p < 1) (hmin : ∀ m : ℕ, 0 < f m ∧ f m < 1 → p ≤ m)

include hp0 hp1 hmin in
/-- The minimal positive integer with absolute value smaller than 1 is a prime number.-/
lemma is_prime_of_minimal_nat_zero_lt_mulRingNorm_lt_one : p.Prime := by
  rw [← Nat.irreducible_iff_nat_prime]
  constructor -- Two goals: p is not a unit and any product giving p must contain a unit.
  · rw [Nat.isUnit_iff]
    rintro rfl
    simp only [Nat.cast_one, map_one, lt_self_iff_false] at hp1
  · rintro a b rfl
    rw [Nat.isUnit_iff, Nat.isUnit_iff]
    by_contra! con
    obtain ⟨ha₁, hb₁⟩ := con
    obtain ⟨ha₀, hb₀⟩ : a ≠ 0 ∧ b ≠ 0 := by
      refine mul_ne_zero_iff.1 fun h ↦ ?_
      rwa [h, Nat.cast_zero, map_zero, lt_self_iff_false] at hp0
    have hap : a < a * b := lt_mul_of_one_lt_right (by omega) (by omega)
    have hbp : b < a * b := lt_mul_of_one_lt_left (by omega) (by omega)
    have ha :=
      le_of_not_lt <| not_and.1 ((hmin a).mt hap.not_le) (map_pos_of_ne_zero f (mod_cast ha₀))
    have hb :=
      le_of_not_lt <| not_and.1 ((hmin b).mt hbp.not_le) (map_pos_of_ne_zero f (mod_cast hb₀))
    rw [Nat.cast_mul, map_mul] at hp1
    exact ((one_le_mul_of_one_le_of_one_le ha hb).trans_lt hp1).false

-- ## Step 3: if p does not divide m, then f m = 1

open Real

include hp0 hp1 hmin bdd in
/-- A natural number not divible by `p` has absolute value 1. -/
lemma mulRingNorm_eq_one_of_not_dvd {m : ℕ} (hpm : ¬ p ∣ m) : f m = 1 := by
  apply le_antisymm (bdd m)
  by_contra! hm
  set M := f p ⊔ f m with hM
  set k := Nat.ceil (M.logb (1 / 2)) + 1 with hk
  obtain ⟨a, b, bezout⟩ : IsCoprime (p ^ k : ℤ) (m ^ k) := by
    apply IsCoprime.pow (Nat.Coprime.isCoprime _)
    exact (Nat.Prime.coprime_iff_not_dvd
      (is_prime_of_minimal_nat_zero_lt_mulRingNorm_lt_one hp0 hp1 hmin)).2 hpm
  have le_half {x} (hx0 : 0 < x) (hx1 : x < 1) (hxM : x ≤ M) : x ^ k < 1 / 2 := by
    calc
    x ^ k = x ^ (k : ℝ) := (rpow_natCast x k).symm
    _ < x ^ M.logb (1 / 2) := by
      apply rpow_lt_rpow_of_exponent_gt hx0 hx1
      rw [hk]
      push_cast
      exact lt_add_of_le_of_pos (Nat.le_ceil (M.logb (1 / 2))) zero_lt_one
    _ ≤ x ^ x.logb (1 / 2) := by
      apply rpow_le_rpow_of_exponent_ge hx0 (le_of_lt hx1)
      simp only [one_div, ← log_div_log, log_inv, neg_div, ← div_neg, hM]
      gcongr
      simp only [Left.neg_pos_iff]
      exact log_neg (lt_sup_iff.2 <| Or.inl hp0) (sup_lt_iff.2 ⟨hp1, hm⟩)
    _ = 1 / 2 := rpow_logb hx0 (ne_of_lt hx1) one_half_pos
  apply lt_irrefl (1 : ℝ)
  calc
  1 = f 1 := (map_one f).symm
  _ = f (a * p ^ k + b * m ^ k) := by rw_mod_cast [bezout]; norm_cast
  _ ≤ f (a * p ^ k) + f (b * m ^ k) := f.add_le' (a * p ^ k) (b * m ^ k)
  _ ≤ 1 * (f p) ^ k + 1 * (f m) ^ k := by
    simp only [map_mul, map_pow, le_refl]
    gcongr
    all_goals rw [← MulRingNorm.apply_natAbs_eq]; apply bdd
  _ = (f p) ^ k + (f m) ^ k := by simp only [one_mul]
  _ < 1 := by
    have hm₀ : 0 < f m :=
      map_pos_of_ne_zero _ <| Nat.cast_ne_zero.2 fun H ↦ hpm <| H ▸ dvd_zero p
    linarith only [le_half hp0 hp1 le_sup_left, le_half hm₀ hm le_sup_right]

-- ## Step 4: f p = p ^ (- t) for some positive real t

include hp0 hp1 hmin in
/-- The absolute value of `p` is `p ^ (-t)` for some positive real number `t`. -/
lemma exists_pos_mulRingNorm_eq_pow_neg : ∃ t : ℝ, 0 < t ∧ f p = p ^ (-t) := by
  have pprime := is_prime_of_minimal_nat_zero_lt_mulRingNorm_lt_one hp0 hp1 hmin
  refine ⟨- logb p (f p), Left.neg_pos_iff.2 <| logb_neg (mod_cast pprime.one_lt) hp0 hp1, ?_⟩
  rw [neg_neg]
  refine (rpow_logb (mod_cast pprime.pos) ?_ hp0).symm
  simp only [ne_eq, Nat.cast_eq_one,Nat.Prime.ne_one pprime, not_false_eq_true]

/-! ## Non-archimedean case: end goal -/

include hf_nontriv bdd in
/-- If `f` is bounded and not trivial, then it is equivalent to a p-adic absolute value. -/
theorem mulRingNorm_equiv_padic_of_bounded :
    ∃! p, ∃ (_ : Fact (p.Prime)), MulRingNorm.equiv f (mulRingNorm_padic p) := by
  obtain ⟨p, hfp, hmin⟩ := exists_minimal_nat_zero_lt_mulRingNorm_lt_one hf_nontriv bdd
  have hprime := is_prime_of_minimal_nat_zero_lt_mulRingNorm_lt_one hfp.1 hfp.2 hmin
  have hprime_fact : Fact (p.Prime) := ⟨hprime⟩
  obtain ⟨t, h⟩ := exists_pos_mulRingNorm_eq_pow_neg hfp.1 hfp.2 hmin
  simp_rw [← equiv_on_nat_iff_equiv]
  use p
  constructor -- 2 goals: MulRingNorm.equiv f (mulRingNorm_padic p) and p is unique.
  · use hprime_fact
    refine ⟨t⁻¹, by simp only [inv_pos, h.1], fun n ↦ ?_⟩
    have ht : t⁻¹ ≠ 0 := inv_ne_zero h.1.ne'
    rcases eq_or_ne n 0 with rfl | hn -- Separate cases n=0 and n ≠ 0
    · simp only [Nat.cast_zero, map_zero, ne_eq, ht, not_false_eq_true, zero_rpow]
    · /- Any natural number can be written as a power of p times a natural number not divisible
      by p  -/
      rcases Nat.exists_eq_pow_mul_and_not_dvd hn p hprime.ne_one with ⟨e, m, hpm, rfl⟩
      simp only [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, mulRingNorm_eq_padic_norm,
        padicNorm.padicNorm_p_of_prime, Rat.cast_inv, Rat.cast_natCast, inv_pow,
        mulRingNorm_eq_one_of_not_dvd bdd hfp.1 hfp.2 hmin hpm, h.2]
      rw [← padicNorm.nat_eq_one_iff] at hpm
      simp only [← rpow_natCast, p.cast_nonneg, ← rpow_mul, mul_one, ← rpow_neg, hpm, cast_one]
      congr
      field_simp [h.1.ne']
      ring
  · intro q ⟨hq_prime, h_equiv⟩
    by_contra! hne
    apply Prime.ne_one (Nat.Prime.prime (Fact.elim hq_prime))
    rw [ne_comm, ← Nat.coprime_primes hprime (Fact.elim hq_prime),
      Nat.Prime.coprime_iff_not_dvd hprime] at hne
    rcases h_equiv with ⟨c, _, h_eq⟩
    have h_eq' := h_eq q
    simp only [mulRingNorm_eq_one_of_not_dvd bdd hfp.1 hfp.2 hmin hne, one_rpow,
      mulRingNorm_eq_padic_norm, padicNorm.padicNorm_p_of_prime, cast_inv, cast_natCast, eq_comm,
      inv_eq_one] at h_eq'
    norm_cast at h_eq'

end Non_archimedean

section Archimedean

/-! ## Archimedean case -/

/-! ## Preliminary result -/

/-- Given an two integers `n, m` with `m > 1` the mulRingNorm of `n` is bounded by
`m + m * f m + m * (f m) ^ 2 + ... + m * (f m) ^ d` where `d` is the number of digits of the
expansion of `n` in base `m`. -/
lemma mulRingNorm_apply_le_sum_digits (n : ℕ) {m : ℕ} (hm : 1 < m) :
    f n ≤ ((Nat.digits m n).mapIdx fun i _ ↦ m * (f m) ^ i).sum := by
  set L := Nat.digits m n
  set L' : List ℚ := List.map Nat.cast (L.mapIdx fun i a ↦ (a * m ^ i)) with hL'
  -- If `c` is a digit in the expansion of `n` in base `m`, then `f c` is less than `m`.
  have hcoef {c : ℕ} (hc : c ∈ Nat.digits m n) : f c < m :=
    lt_of_le_of_lt (MulRingNorm_nat_le_nat c f) (mod_cast Nat.digits_lt_base hm hc)
  calc
  f n = f ((Nat.ofDigits m L : ℕ) : ℚ) := by rw [Nat.ofDigits_digits m n]
    _ = f (L'.sum) := by rw [Nat.ofDigits_eq_sum_mapIdx]; norm_cast
    _ ≤ (L'.map f).sum := mulRingNorm_sum_le_sum_mulRingNorm L' f
    _ ≤ (L.mapIdx fun i _ ↦ m * (f m) ^ i).sum := ?_
  simp only [hL', List.mapIdx_eq_enum_map, List.map_map]
  apply List.sum_le_sum
  rintro ⟨i, a⟩ hia
  dsimp [Function.uncurry]
  replace hia := List.mem_enumFrom hia
  push_cast
  rw [map_mul, map_pow]
  gcongr
  simp only [zero_le, zero_add, tsub_zero, true_and] at hia
  exact (hcoef (List.mem_iff_get.mpr ⟨⟨i, hia.1⟩, hia.2.symm⟩)).le

/-! ## Step 1: if f is a MulRingNorm and f n > 1 for some natural n, then f n > 1 for all n ≥ 2 -/

/-- If `f n > 1` for some `n` then `f n > 1` for all `n ≥ 2` -/
lemma one_lt_of_not_bounded (notbdd : ¬ ∀ n : ℕ, f n ≤ 1) {n₀ : ℕ} (hn₀ : 1 < n₀) : 1 < f n₀ := by
  contrapose! notbdd with h
  intro n
  have h_ineq1 {m : ℕ} (hm : 1 ≤ m) : f m ≤ n₀ * (logb n₀ m + 1) := by
    /- L is the string of digits of `n` in the base `n₀`-/
    set L := Nat.digits n₀ m
    calc
    f m ≤ (L.mapIdx fun i _ ↦ n₀ * f n₀ ^ i).sum := mulRingNorm_apply_le_sum_digits m hn₀
    _ ≤ (L.mapIdx fun _ _ ↦ (n₀ : ℝ)).sum := by
      simp only [List.mapIdx_eq_enum_map, List.map_map]
      apply List.sum_le_sum
      rintro ⟨i, a⟩ _
      simp only [Function.comp_apply, Function.uncurry_apply_pair]
      exact mul_le_of_le_of_le_one' (mod_cast le_refl n₀) (pow_le_one₀ (by positivity) h)
        (by positivity) (by positivity)
    _ = n₀ * (Nat.log n₀ m + 1) := by
      rw [List.mapIdx_eq_enum_map, List.eq_replicate_of_mem (a := (n₀ : ℝ))
        (l := List.map (Function.uncurry fun _ _ ↦ n₀) (List.enum L)),
        List.sum_replicate, List.length_map, List.enum_length, nsmul_eq_mul, mul_comm,
        Nat.digits_len n₀ m hn₀ (not_eq_zero_of_lt hm), Nat.cast_add_one]
      simp (config := { contextual := true })
    _ ≤ n₀ * (logb n₀ m + 1) := by gcongr; exact natLog_le_logb ..
  -- For h_ineq2 we need to exclude the case n = 0.
  rcases eq_or_ne n 0 with rfl | h₀
  · simp only [CharP.cast_eq_zero, map_zero, zero_le_one]
  have h_ineq2 (k : ℕ) (hk : 0 < k) :
      f n ≤ (n₀ * (logb n₀ n + 1)) ^ (k : ℝ)⁻¹ * k ^ (k : ℝ)⁻¹ := by
    have : 0 ≤ logb n₀ n := logb_nonneg (one_lt_cast.2 hn₀) (mod_cast Nat.one_le_of_lt h₀.bot_lt)
    calc
    f n = (f ↑(n ^ k)) ^ (k : ℝ)⁻¹ := by
      rw [Nat.cast_pow, map_pow, ← rpow_natCast, rpow_rpow_inv (by positivity) (by positivity)]
    _   ≤ (n₀ * (logb n₀ ↑(n ^ k) + 1)) ^ (k : ℝ)⁻¹ := by
      gcongr
      exact h_ineq1 <| one_le_pow₀ (one_le_iff_ne_zero.mpr h₀)
    _   = (n₀ * (k * logb n₀ n + 1)) ^ (k : ℝ)⁻¹ := by
      rw [Nat.cast_pow, logb_pow (mod_cast h₀.bot_lt)]
    _   ≤ (n₀ * ( k * logb n₀ n + k)) ^ (k : ℝ)⁻¹ := by
      gcongr
      exact one_le_cast.mpr hk
    _ = (n₀ * (logb n₀ n + 1)) ^ (k : ℝ)⁻¹ * k ^ (k : ℝ)⁻¹ := by
      rw [← mul_rpow (by positivity) (by positivity), mul_assoc, add_mul, one_mul,
      mul_comm _ (k : ℝ)]
-- For 0 < logb n₀ n below we also need to exclude n = 1.
  rcases eq_or_ne n 1 with rfl | h₁; simp only [Nat.cast_one, map_one, le_refl]
  refine le_of_tendsto_of_tendsto tendsto_const_nhds ?_ (eventually_atTop.2 ⟨1, h_ineq2⟩)
  nth_rw 2 [← mul_one 1]
  have : 0 < logb n₀ n := logb_pos (mod_cast hn₀) (by norm_cast; omega)
  have hnlim : Tendsto (fun k : ℕ ↦ (n₀ * (logb n₀ n + 1)) ^ (k : ℝ)⁻¹) atTop (𝓝 1) :=
    tendsto_root_atTop_nhds_one (by positivity)
  exact hnlim.mul tendsto_nat_rpow_div

end Archimedean

end Rat.MulRingNorm
