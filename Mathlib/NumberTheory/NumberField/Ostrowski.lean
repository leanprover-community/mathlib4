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

namespace NumberField

section Nonarchimedean

/-!
### The non-archimedean case

Every bounded absolute value on `K` is equivalent to .
-/

open IsDedekindDomain HeightOneSpectrum WithZeroMulInt NumberField NNReal

variable {K : Type*} [Field K] [NumberField K] (f : AbsoluteValue K ℝ)

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
  letI : Fact (IsMulTorsion (ClassGroup (𝓞 K))) := fact_iff.mpr isMulTorsion_of_finite
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
def prime_ideal (hf_nontriv : f.IsNontrivial) : HeightOneSpectrum (𝓞 K) where
  asIdeal := {
    carrier := {a | f a < 1}
    add_mem' := fun ha hb ↦ lt_of_le_of_lt (nonarch _ _) (max_lt ha hb)
    zero_mem' := by simp
    smul_mem' := by
      simpa [Set.mem_ofPred_eq] using
        (fun (c x : 𝓞 K) hx ↦
          mul_lt_one_of_nonneg_of_lt_one_right
            (integers_closed_unit_ball f nonarch c) (apply_nonneg f ↑x) hx)
  }
  isPrime := by
      rw [Ideal.isPrime_iff]
      constructor
      · rw [Ideal.ne_top_iff_one]
        change ¬f (1 : RingOfIntegers K) < 1
        simp
      -- If `x * y` has absolute value less than `1`, one of the two factors must.
      · intro x y hxy
        change f (x * y) < 1 at hxy
        rw [map_mul] at hxy
        change f x < 1 ∨ f y < 1
        by_contra! h
        linarith [one_le_mul_of_one_le_of_one_le h.1 h.2]
  ne_bot := by
    rw [Submodule.ne_bot_iff]
    change ∃ x : 𝓞 K, f x < 1 ∧ x ≠ 0
    obtain ⟨a, ha, hfa⟩ := hf_nontriv
    obtain ⟨c, b, h, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    by_cases hfb : f b < 1
    · exact ⟨b, hfb, nonZeroDivisors.ne_zero h⟩
    rw [map_div₀, le_antisymm (integers_closed_unit_ball f nonarch b) (le_of_not_gt hfb)] at hfa
    grind [integers_closed_unit_ball]

open AbsoluteValue in
include nonarch in
/-- A nontrivial nonarchimedean absolute value on a number field is equal to a `v`-adic absolute
value attached for some `v : HeightOneSpectrum (𝓞 K)`. -/
theorem Ostr_nonarch (hf_nontriv : f.IsNontrivial) :
    ∃! P : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    ∃ b : ℝ≥0, ∃ hb : 1 < b,
    f = adicAbv P hb := by
  -- Let `P` be the non-zero prime given by the open unit ball.
  let P := prime_ideal f nonarch hf_nontriv
  use P
  -- Choose a uniformizer of `P`; its absolute value determines the base `b`.
  rcases intValuation_exists_uniformizer P with ⟨π, hπ⟩
  -- Basic facts about the chosen uniformizer.
  have hπv_eq : P.valuation K π = WithZero.exp (-1) := by
    simpa [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap P π] using hπ
  have hπv_ne : P.valuation K (π : K) ≠ 0 := by simp [hπv_eq]
  have hπ_ne_zero : π ≠ 0 := by grind
  have hπ_pos : 0 < f π := by simp [hπ_ne_zero]
  have hπ_lt_one : f π < 1 := by
    change π ∈ P.asIdeal
    rw [← intValuation_lt_one_iff_mem, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπv : Multiplicative.toAdd (WithZero.unzero hπv_ne) = -1 := by
    simp only [hπv_eq]
    rfl
  let b : ℝ≥0 := ⟨(f π)⁻¹, by positivity⟩
  have hb : 1 < b := by
    exact_mod_cast (one_lt_inv₀ hπ_pos).2 hπ_lt_one
  -- Elements of `v`-adic absolute value `1` also have `f`-absolute value `1`.
  have f_eq_one_of_adicAbv_eq_one {x : K} (hx : adicAbv P hb x = 1) : f x = 1 := by
    obtain ⟨y, z, rfl, hz⟩ := exists_num_denom_absolute_value_one hb (le_of_eq hx)
    have int_unit {x : 𝓞 K} (hx : adicAbv P hb (x : K) = 1) : f x = 1 := by
      rw [adicAbv_coe_eq_one_iff] at hx
      exact le_antisymm (integers_closed_unit_ball f nonarch x) (le_of_not_gt hx)
    have hy : adicAbv P hb (y : K) = 1 := by simpa [map_div₀, hz] using hx
    simp [map_div₀, int_unit hy, int_unit hz]
  -- The chosen base makes the adic absolute value take the same value as `f` on π.
  constructor
  · use b, hb
    ext x
    by_cases hx : x = 0
    · simp [hx]
    -- Divide `x` by the matching power of the uniformizer. The quotient has
    -- `P`-adic absolute value `1`, so it has `f`-absolute value `1`.
    have hxv_ne : P.valuation K x ≠ 0 := (Valuation.ne_zero_iff (P.valuation K)).mpr hx
    have coe_b : (b : ℝ) = (f π)⁻¹ := rfl
    simp only [IsDedekindDomain.HeightOneSpectrum.adicAbv, adicAbvDef, AbsoluteValue.coe_mk,
      MulHom.coe_mk, WithZeroMulInt.toNNReal_neg_apply _ hxv_ne, NNReal.coe_zpow, coe_b, inv_zpow]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_zpow₀, ← map_mul]
    apply f_eq_one_of_adicAbv_eq_one
    simp [IsDedekindDomain.HeightOneSpectrum.adicAbv, adicAbvDef, coe_b,
      WithZeroMulInt.toNNReal_neg_apply _ hπv_ne, WithZeroMulInt.toNNReal_neg_apply _ hxv_ne, hπv]
    field_simp
  · -- Uniqueness: the prime is recovered as the set of algebraic integers with
    -- absolute value less than `1`.
    simp only [forall_exists_index]
    rintro Q _ hc rfl
    ext x
    exact (adicAbv_coe_lt_one_iff Q hc x).symm

end Nonarchimedean

end NumberField
