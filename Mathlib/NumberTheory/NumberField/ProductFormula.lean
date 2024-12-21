/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Mathlib.NumberTheory.NumberField.FinitePlaces

/-!
# The Product Formula for number fields
In this file we prove the Product Formula for number fields: for any non-zero element `x` of a
number field `K`, we have `∏|x|ᵥ=1` where the product runs over the equivalence classes of absoulte
values of `K` and the `|⬝|ᵥ` are suitably normalized.

## Main Results
* `NumberField.FinitePlace.prod_eq_inv_abs_norm`: for any non-zero element `x` of a number field
`K`, the product `∏|x|ᵥ` of the absolute values of `x` associated to the finite places of `K` is
equal to the inverse of the norm of `x`.
* `NumberField.prod_abs_eq_one`: for any non-zero element `x` of a number field `K`, we have
`∏|x|ᵥ=1` where the product runs over the equivalence classes of absoulte values of `K`.

## Tags
number field, embeddings, places, infinite places, finite places, product formula
-/

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

open Algebra Classical FinitePlace Function Ideal IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum

/-- For any non-zero `x` in `𝓞 K`, the prduct of `w x`, where `w` runs over `FinitePlace K`, is
equal to the inverse of the absolute value of `Algebra.norm ℤ x`. -/
theorem FinitePlace.prod_eq_inv_abs_norm_int {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ w : FinitePlace K, w x = (|norm ℤ x| : ℝ)⁻¹ := by
  convert_to ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖embedding v x‖ = |↑(norm ℤ x)|⁻¹
  · exact (finprod_eq_of_bijective maximalIdeal ((bijective_iff_existsUnique _).mpr
      <| fun v ↦ ⟨mk v, maximalIdeal_mk v, fun _ a ↦ by rw [← a, mk_maximalIdeal]⟩)
      (fun w ↦ (norm_embedding_eq w (x : K)).symm))
  apply (inv_eq_of_mul_eq_one_left _).symm
  norm_cast
  have h_span_nezero : span {x} ≠ 0 := by
    simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, h_x_nezero, not_false_eq_true]
  rw [Int.abs_eq_natAbs, ← Ideal.absNorm_span_singleton,
    ← Ideal.finprod_heightOneSpectrum_factorization h_span_nezero, Int.cast_natCast]
  --Aim: transform the two finprod into Finset.prod
  let t₀ := {v : HeightOneSpectrum (𝓞 K) | x ∈ v.asIdeal}
  have h_fin₀ : t₀.Finite := by
    simp only [← dvd_span_singleton, finite_factors h_span_nezero, t₀]
  let s := h_fin₀.toFinset
  let t₁ := (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(embedding v) x‖).mulSupport
  let t₂ := (fun v : HeightOneSpectrum (𝓞 K) ↦ v.maxPowDividing (span {x})).mulSupport
  have h_subs₁ : t₁ ⊆ t₀ := by
    simp only [mulSupport_subset_iff, ne_eq, norm_eq_one_iff_not_mem, Decidable.not_not,
    Set.mem_setOf_eq, imp_self, implies_true, t₁, t₀]
  have h_subs₂ : t₂ ⊆ t₀ := by
    simp only [Set.le_eq_subset, mulSupport_subset_iff, Set.mem_setOf_eq, t₂, t₀,
      maxPowDividing, ← dvd_span_singleton]
    intro v hv
    rw [← pow_zero v.asIdeal] at hv
    replace hv := fun h ↦ hv (congrArg (HPow.hPow v.asIdeal) h)
    rwa [imp_false, ← ne_eq, Associates.count_ne_zero_iff_dvd h_span_nezero (irreducible v)] at hv
  have h_fin₁ : t₁.Finite := h_fin₀.subset h_subs₁
  have h_fin₂ : t₂.Finite := h_fin₀.subset h_subs₂
  have h_sub₁ : h_fin₁.toFinset ⊆ s := Set.Finite.toFinset_subset_toFinset.mpr h_subs₁
  have h_sub₂ : h_fin₂.toFinset ⊆ s := Set.Finite.toFinset_subset_toFinset.mpr h_subs₂
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset _ h_fin₁ h_sub₁,
    finprod_eq_prod_of_mulSupport_toFinset_subset _ h_fin₂ h_sub₂, map_prod, Nat.cast_prod,
    ← Finset.prod_mul_distrib, Finset.prod_eq_one]
  intro v _
  rw [maxPowDividing, map_pow, Nat.cast_pow, norm_def, vadicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply _ (v.valuation.ne_zero_iff.mpr
    (RingOfIntegers.coe_ne_zero_iff.mpr h_x_nezero))]
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_intCast, ← Real.rpow_add (mod_cast Nat.zero_lt_of_lt
    (mod_cast one_lt_norm v))]
  norm_cast
  rw [zpow_eq_one_iff_right₀ (Nat.cast_nonneg' (Nat.card (𝓞 K ⧸ v.asIdeal)))
    (by exact ne_of_gt (one_lt_norm v))]
  simp only [valuation_eq_intValuationDef v x, intValuationDef_if_neg v h_x_nezero,
    WithZero.unzero_coe, toAdd_ofAdd, neg_add_cancel]

/-- For any non-zero `x` in `K`, the prduct of `w x`, where `w` runs over `FinitePlace K`, is
equal to the inverse of the absolute value of `Algebra.norm ℚ x`. -/
theorem FinitePlace.prod_eq_inv_abs_norm {x : K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ w : FinitePlace K, w x = |(Algebra.norm ℚ) x|⁻¹ := by
  --reduce to 𝓞 K
  rcases IsFractionRing.div_surjective (A := 𝓞 K) x with ⟨a, b, hb, rfl⟩
  apply nonZeroDivisors.ne_zero at hb
  have ha : a ≠ 0 := by
    by_contra! ha
    apply h_x_nezero
    simp only [ha, map_zero, zero_div]
  simp_rw [map_div₀, Rat.cast_inv, Rat.cast_abs, finprod_div_distrib (mulSupport_finite_int ha)
    (mulSupport_finite_int hb), prod_eq_inv_abs_norm_int ha, prod_eq_inv_abs_norm_int hb]
  rw [← inv_eq_iff_eq_inv, div_inv_eq_mul, mul_inv_rev, inv_inv, inv_mul_eq_div, ← abs_div]
  congr
  apply (eq_div_of_mul_eq (by simp only [ne_eq, Int.cast_eq_zero, norm_eq_zero_iff, hb,
    not_false_eq_true]) ?_).symm
  norm_cast
  rw [coe_norm_int a, coe_norm_int b, ← MonoidHom.map_mul, div_mul_cancel₀ _
    (RingOfIntegers.coe_ne_zero_iff.mpr hb)]

/-- The Product Formula for the Number Field `K`. -/
theorem prod_abs_eq_one {x : K} (h_x_nezero : x ≠ 0) :
    (∏ w : InfinitePlace K, w x ^ w.mult) * ∏ᶠ w : FinitePlace K, w x = 1 := by
  simp_all only [prod_eq_inv_abs_norm h_x_nezero, InfinitePlace.prod_eq_abs_norm, ne_eq,
    Rat.cast_inv, isUnit_iff_ne_zero, abs_eq_zero, Rat.cast_eq_zero, norm_eq_zero_iff,
    not_false_eq_true, IsUnit.mul_inv_cancel]

end NumberField
