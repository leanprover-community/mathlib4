/-
Copyright (c) 2026 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.SInteger

/-!
# Ostrowski’s Theorem for number fields

Ostrowski's Theorem for number fields and non-archimedean absolute values:
every non-archimedean absolute value on `K` is equivalent to .

## Main results

## TODO

Archimedean case.

## References

* [K. Conrad, *Ostrowski for number fields*][conradnumbfield]

## Tags

absolute value, number field, Ostrowski's theorem
-/

@[expose] public section

section Non_archimedean

/-!
### The non-archimedean case

Every bounded absolute value on `K` is equivalent to .
-/

open IsDedekindDomain HeightOneSpectrum WithZeroMulInt NumberField NNReal

variable {K : Type*} [Field K] [NumberField K] (f : AbsoluteValue K ℝ)

section Nonarchimedean

open NumberField.RingOfIntegers.HeightOneSpectrum

/-- If the `v`-adic absolute value of `α` is at most one, then `α` can be written
as a quotient of algebraic integers with denominator a `v`-adic unit. -/
lemma exists_num_denom_absolute_value_one {α : K} {v : HeightOneSpectrum (𝓞 K)}
    {b : ℝ≥0} (hb : 1 < b) (h_abs : adicAbv v hb α ≤ 1) :
  ∃ x y : 𝓞 K, α = x / y ∧ adicAbv v hb (y : K) = 1 := by
  -- Allow denominators away from `v`, so the only condition to check is at `v`.
  let S : Set (HeightOneSpectrum (𝓞 K)) := {v}ᶜ
  have mem : α ∈ S.integer K := by
    intro _ hw
    simp_all [S, (toNNReal_le_one_iff hb).mp h_abs]
  -- Use the localization description of `S`-integers to choose a numerator and
  -- denominator in `𝓞 K`.
  letI : Fact (Monoid.IsTorsion (ClassGroup (𝓞 K))) := fact_iff.mpr isTorsion_of_finite
  let γ : S.integer K := ⟨α, mem⟩
  obtain ⟨⟨x, ⟨y, hy_away, hy_nzd⟩⟩, h⟩ := IsLocalization.surj S.submonoid γ
  refine ⟨x, y, ?_, by simpa [adicAbv_coe_eq_one_iff, S] using hy_away⟩
  rw [eq_div_iff <| IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy_nzd]
  exact Subtype.ext_iff.mp h

variable (nonarch : IsNonarchimedean f)

open Polynomial minpoly

include nonarch in
/-- Algebraic integers are contained in the closed unit ball of a nonarchimedean
absolute value. -/
lemma integers_closed_unit_ball (x : 𝓞 K) : f x ≤ 1 := by
  -- x can be written in a basis of 𝓞 K
  let B := RingOfIntegers.basis K
  let C := ∑ i, f (B i)
  -- The integral basis gives a bound that is uniform in the algebraic integer.
  have hC (y : 𝓞 K) : f y ≤ C := by
    rw [← B.sum_repr y]
    calc
      f (↑(∑ i, (B.repr y i) • B i) : K) ≤ ∑ i, f ((B.repr y i) • B i) := by
        rw [RingOfIntegers.coe_eq_algebraMap, map_sum]
        exact f.sum_le Finset.univ _
      _ ≤ ∑ i, f (B i) := by
        apply Finset.sum_le_sum
        intro _ _
        rw [zsmul_eq_mul, map_mul]
        exact mul_le_of_le_one_left (apply_nonneg f _) <|
          IsNonarchimedean.apply_intCast_le_one nonarch
  have hC_one : 1 ≤ C := by simpa using hC 1
  -- Apply the uniform bound to powers and take the corresponding real root.
  have hx_root {k : ℕ} (hk : k ≠ 0) : f x ≤ C ^ (1 / (k : ℝ)) := by
    have hpow := hC (x ^ k)
    rw [RingOfIntegers.coe_eq_algebraMap, map_pow, map_pow] at hpow
    rw [one_div, ← Real.pow_rpow_inv_natCast (apply_nonneg f (x : K)) hk]
    exact Real.rpow_le_rpow (by positivity) hpow (by positivity)
  -- These roots converge to one.
  have ht : Filter.Tendsto (fun k : ℕ ↦ C ^ (1 / (k : ℝ))) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.rpow (tendsto_one_div_atTop_nhds_zero_nat)
      (Or.inl <| ne_of_gt <| lt_of_lt_of_le zero_lt_one hC_one)
  exact ge_of_tendsto ht <| Filter.eventually_atTop.2 ⟨1, fun k hk ↦ hx_root (Nat.ne_of_gt hk)⟩

include nonarch in
/-- The open unit ball in `𝓞 K` is a non-zero prime ideal of `𝓞 K`. -/
def prime_ideal (hf_nontriv : f.IsNontrivial) : IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := {
    carrier := {a : (𝓞 K) | f a < 1}
    add_mem' := by
                  -- The ultrametric inequality makes the open unit ball additively closed.
                  simp only [Set.mem_setOf_eq, map_add]
                  exact fun ha hb ↦ lt_of_le_of_lt (nonarch _ _) (max_lt ha hb)
    zero_mem' := by simp
    smul_mem' := by
                  -- Algebraic integers have absolute value at most one, so multiplying by
                  -- an algebraic integer preserves the open unit ball.
                  simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul]
                  exact fun c x hx ↦ mul_lt_one_of_nonneg_of_lt_one_right
                    (integers_closed_unit_ball f nonarch c) (apply_nonneg f ↑x) hx
  }
  isPrime := by
      rw [Ideal.isPrime_iff]
      constructor
      -- The open unit ball is proper because `1` has absolute value `1`.
      · simp [-ne_eq, -AddSubsemigroup.mk_eq_top, Ideal.ne_top_iff_one]
      -- If `x * y` has absolute value less than `1`, one of the two factors must.
      · simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
        Set.mem_setOf_eq, map_mul]
        intro x y hxy
        by_contra! h
        linarith [one_le_mul_of_one_le_of_one_le h.1 h.2]
  ne_bot := by
      -- Nontriviality gives an element with absolute value different from `1`.
      -- Writing it as a fraction of algebraic integers shows that one of the
      -- numerator or denominator lies in the open unit ball.
      rw [Submodule.ne_bot_iff]
      simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
        ne_eq]
      obtain ⟨a, ha, hfa⟩ := hf_nontriv
      obtain ⟨c, b, h3, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
      have h_b_nezero : b ≠ 0 := nonZeroDivisors.ne_zero h3
      by_cases h : f b < 1; exact ⟨b, h, h_b_nezero⟩
      have h_c_nezero : c ≠ 0 := by
        by_contra! h
        simp [h] at ha
      have h_b : f b = 1 := by linarith [integers_closed_unit_ball f nonarch b]
      simp only [map_div₀, h_b, div_one, ne_eq] at hfa
      have h_c_lt_one : f c < 1 := by
        linarith [lt_of_le_of_ne (integers_closed_unit_ball f nonarch c) hfa]
      exact ⟨c, h_c_lt_one, h_c_nezero⟩

--TODO: clean up
open AbsoluteValue in
include nonarch in
/-- A nontrivial nonarchimedean absolute value on a number field is uniquely equal
to an adic absolute value attached to a height-one prime of `𝓞 K`. -/
theorem Ostr_nonarch (hf_nontriv : f.IsNontrivial) :
    ∃! P : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    ∃ b : ℝ≥0, ∃ hb : 1 < b,
    f = adicAbv P hb := by
  -- Let `P` be the height-one prime given by the open unit ball.
  let P := prime_ideal f nonarch hf_nontriv
  use P
  simp only [forall_exists_index]
  have h_norm := HeightOneSpectrum.one_lt_absNorm P
  -- Choose a uniformizer of `P`; its absolute value determines the base `b`.
  rcases IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer P with ⟨π, hπ⟩
  -- Basic facts about the chosen uniformizer.
  have hπ_ne_zero : π ≠ 0 := by
    by_contra! h
    rw [h] at hπ
    simp at hπ
    have := @WithZero.exp_ne_zero ℤ 1
    contradiction
  have hπ_zero_le_f : 0 < f π := by simp [hπ_ne_zero]
  have hπ_f_lt_one : f π < 1 := by
    exact (show (π : 𝓞 K) ∈ P.asIdeal ↔ f (π : K) < 1 from Iff.rfl).1 <|
      (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem P π).1 <| by
        rw [hπ]
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        norm_num
  have hπ_val_ne_zero : P.valuation K (π : K) ≠ 0 := by simp_all
  have hπ_toAdd: Multiplicative.toAdd (WithZero.unzero hπ_val_ne_zero) = -1 := by
    simp_all [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap P π, P]
    rfl
  -- Elements of `v`-adic absolute value `1` also have `f`-absolute value `1`.
  -- First reduce to algebraic integers using the denominator lemma above.
  have absolute_value_eq_one_of_vadic_abv_eq_one {x : K} (hx : x ≠ 0) {b : ℝ≥0} (hb : 1 < b)
      (h : adicAbv P hb x = 1) : f x = 1 := by
    obtain ⟨y, z, rfl, hz⟩ := exists_num_denom_absolute_value_one hb (le_of_eq h)
    have : y ≠ 0 ∧ z ≠ 0 := by
      by_contra! h'
      apply hx
      by_cases h'' : y = 0
      · simp_all
      · simp_all [h' h'']
    have absolute_value_eq_one_of_vadic_abv_eq_one_int {x : 𝓞 K} (hx : x ≠ 0) (h : adicAbv P hb (x : K) = 1) :
      f x = 1 := by
      -- For algebraic integers, being a `P`-adic unit means not lying in the
      -- open unit ball, and the closed unit ball lemma gives the reverse bound.
      rw [adicAbv_coe_eq_one_iff] at h
      have : 1 ≤ f x := le_of_not_gt h
      linarith [integers_closed_unit_ball f nonarch x]
    simp_all
  let b : ℝ≥0 := ⟨(f π)⁻¹, by positivity⟩
  have hb : 1 < b := by
    change (1 : ℝ) < (f π)⁻¹
    exact (one_lt_inv₀ hπ_zero_le_f).2 hπ_f_lt_one
  -- The chosen base makes the adic absolute value take the same value as `f` on
  -- the uniformizer.
  --let c := Real.logb (Ideal.absNorm P.asIdeal)⁻¹ (f π)
  constructor
  · use b, hb
    ext x
    by_cases hx : x = 0; simp [hx]
    -- Divide `x` by the matching power of the uniformizer. The quotient has
    -- `P`-adic absolute value `1`, so it has `f`-absolute value `1`.
    have hx_val_ne_zero : P.valuation K x ≠ 0 := (Valuation.ne_zero_iff (P.valuation K)).mpr hx
    have : (b : ℝ) = (f π)⁻¹ := rfl
    simp [IsDedekindDomain.HeightOneSpectrum.adicAbv, adicAbvDef]
    simp only [WithZeroMulInt.toNNReal_neg_apply _ hx_val_ne_zero, NNReal.coe_zpow, this]
    rw [← neg_neg <| Multiplicative.toAdd (WithZero.unzero hx_val_ne_zero), ← inv_zpow', inv_inv,
      ← map_zpow₀, ← mul_inv_eq_one₀ <| (AbsoluteValue.ne_zero_iff f).mpr <|
      zpow_ne_zero _ (RingOfIntegers.coe_ne_zero_iff.mpr hπ_ne_zero), ← map_inv₀, ← map_mul]
    rw [zpow_neg, inv_inv]
    apply absolute_value_eq_one_of_vadic_abv_eq_one (mul_ne_zero hx
      (zpow_ne_zero _ (RingOfIntegers.coe_ne_zero_iff.mpr hπ_ne_zero))) hb
    simp [IsDedekindDomain.HeightOneSpectrum.adicAbv, adicAbvDef, this,
      WithZeroMulInt.toNNReal_neg_apply _ hπ_val_ne_zero,
      WithZeroMulInt.toNNReal_neg_apply _ hx_val_ne_zero, hπ_toAdd]
    have hπf_ne_zero : f (π : K) ≠ 0 :=
      (AbsoluteValue.ne_zero_iff f).2 (RingOfIntegers.coe_ne_zero_iff.mpr hπ_ne_zero)
    simpa [zpow_neg] using
      inv_mul_cancel₀ (zpow_ne_zero (Multiplicative.toAdd (WithZero.unzero hx_val_ne_zero)) hπf_ne_zero)
  · -- Uniqueness: the prime is recovered as the set of algebraic integers with
    -- absolute value less than `1`.
    intro Q c hc heq
    simp [IsDedekindDomain.HeightOneSpectrum.ext_iff, ← SetLike.coe_set_eq, Set.ext_iff]
    intro x
    constructor
    · intro hxQ
      have hQlt : adicAbv Q hc (x : K) < 1 :=
        (adicAbv_coe_lt_one_iff (v := Q) (hb := hc) (r := x)).2 hxQ
      have hflt : f x < 1 := by simpa [heq] using hQlt
      exact (show x ∈ P.asIdeal ↔ f x < 1 by rfl).2 hflt
    · intro hxP
      have hflt : f x < 1 := (show x ∈ P.asIdeal ↔ f x < 1 by rfl).1 hxP
      have hQlt : adicAbv Q hc (x : K) < 1 := by simpa [heq] using hflt
      exact (adicAbv_coe_lt_one_iff (v := Q) (hb := hc) (r := x)).1 hQlt

end Nonarchimedean
