/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Mathlib.NumberTheory.NumberField.FinitePlaces

/-!
# The Product Formula for number fields

In this file we prove the Product Formula for number fields: for any non-zero element `x` of a
number field `K`, we have `∏ |x|ᵥ=1` where the product runs over the equivalence classes of absolute
values of `K`. The `|⬝|ᵥ` are normalized as follows:
- for the infinite places, `|⬝|ᵥ` is the absolute value on `K` induced by the corresponding field
embedding in `ℂ` and the usual absolute value on `ℂ`;
- for the finite places and a non-zero `x`, `|x|ᵥ` is equal to the norm of the corresponding maximal
ideal of `𝓞 K` raised to the power of the `v`-adic valuation of `x`.

## Main Results

* `NumberField.FinitePlace.prod_eq_inv_abs_norm`: for any non-zero element `x` of a number field
`K`, the product `∏ |x|ᵥ` of the absolute values of `x` associated to the finite places of `K` is
equal to the inverse of the norm of `x`.
* `NumberField.prod_abs_eq_one`: for any non-zero element `x` of a number field `K`, we have
`∏ |x|ᵥ=1`, where the product runs over the equivalence classes of absolute values of `K`.

## Tags
number field, embeddings, places, infinite places, finite places, product formula
-/

variable {K : Type*} [Field K] [NumberField K]

namespace IsDedekindDomain.HeightOneSpectrum

open NumberField FinitePlace

lemma equivHeightOneSpectrum_symm_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (equivHeightOneSpectrum.symm v) x = ‖embedding v x‖ := by
  have : v = (equivHeightOneSpectrum.symm v).maximalIdeal := by
    show v = equivHeightOneSpectrum (equivHeightOneSpectrum.symm v)
    exact (Equiv.apply_symm_apply _ v).symm
  convert (norm_embedding_eq (equivHeightOneSpectrum.symm v) x).symm

open Ideal in
lemma embedding_mul_absNorm (v : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    ‖(embedding v) ↑x‖ * absNorm (v.maxPowDividing (span {x})) = 1 := by
  rw [maxPowDividing, map_pow, Nat.cast_pow, norm_def, vadicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply _
      (v.valuation.ne_zero_iff.mpr (RingOfIntegers.coe_ne_zero_iff.mpr h_x_nezero))]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ <| mod_cast (zero_lt_one.trans (one_lt_norm v)).ne']
  norm_cast
  rw [zpow_eq_one_iff_right₀ (Nat.cast_nonneg' _) (mod_cast (one_lt_norm v).ne')]
  simp [valuation_eq_intValuationDef, intValuationDef_if_neg, h_x_nezero]

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField

open Algebra

open Function Ideal IsDedekindDomain HeightOneSpectrum in
/-- For any non-zero `x` in `𝓞 K`, the prduct of `w x`, where `w` runs over `FinitePlace K`, is
equal to the inverse of the absolute value of `Algebra.norm ℤ x`. -/
theorem FinitePlace.prod_eq_inv_abs_norm_int {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ w : FinitePlace K, w x = (|norm ℤ x| : ℝ)⁻¹ := by
  simp only [← finprod_comp_equiv equivHeightOneSpectrum.symm, equivHeightOneSpectrum_symm_apply]
  refine (inv_eq_of_mul_eq_one_left ?_).symm
  norm_cast
  have h_span_nezero : span {x} ≠ 0 := by simp [h_x_nezero]
  rw [Int.abs_eq_natAbs, ← absNorm_span_singleton,
    ← finprod_heightOneSpectrum_factorization h_span_nezero, Int.cast_natCast]
  let t₀ := {v : HeightOneSpectrum (𝓞 K) | x ∈ v.asIdeal}
  have h_fin₀ : t₀.Finite := by simp only [← dvd_span_singleton, finite_factors h_span_nezero, t₀]
  let t₁ := (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖embedding v x‖).mulSupport
  let t₂ :=
    (fun v : HeightOneSpectrum (𝓞 K) ↦ (absNorm (v.maxPowDividing (span {x})) : ℝ)).mulSupport
  have h_fin₁ : t₁.Finite := h_fin₀.subset <| by simp [norm_eq_one_iff_not_mem, t₁, t₀]
  have h_fin₂ : t₂.Finite := by
    refine h_fin₀.subset ?_
    simp only [Set.le_eq_subset, mulSupport_subset_iff, Set.mem_setOf_eq, t₂, t₀,
      maxPowDividing, ← dvd_span_singleton]
    intro v hv
    simp only [map_pow, Nat.cast_pow, ← pow_zero (absNorm v.asIdeal : ℝ)] at hv
    replace hv := fun h ↦ hv (congrArg (HPow.hPow (absNorm v.asIdeal : ℝ)) h)
    classical
    simpa only [imp_false, Associates.count_ne_zero_iff_dvd h_span_nezero (irreducible v)] using hv
  have h_prod : (absNorm (∏ᶠ (v : HeightOneSpectrum (𝓞 K)), v.maxPowDividing (span {x})) : ℝ) =
      ∏ᶠ (v : HeightOneSpectrum (𝓞 K)), (absNorm (v.maxPowDividing (span {x})) : ℝ) :=
    ((Nat.castRingHom ℝ).toMonoidHom.comp absNorm.toMonoidHom).map_finprod_of_preimage_one
      (by simp) _
  rw [h_prod, ← finprod_mul_distrib h_fin₁ h_fin₂]
  exact finprod_eq_one_of_forall_eq_one fun v ↦ v.embedding_mul_absNorm h_x_nezero

/-- For any non-zero `x` in `K`, the prduct of `w x`, where `w` runs over `FinitePlace K`, is
equal to the inverse of the absolute value of `Algebra.norm ℚ x`. -/
theorem FinitePlace.prod_eq_inv_abs_norm {x : K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ w : FinitePlace K, w x = |(Algebra.norm ℚ) x|⁻¹ := by
  --reduce to 𝓞 K
  rcases IsFractionRing.div_surjective (A := 𝓞 K) x with ⟨a, b, hb, rfl⟩
  apply nonZeroDivisors.ne_zero at hb
  have ha : a ≠ 0 := by
    rintro rfl
    simp at h_x_nezero
  simp_rw [map_div₀, Rat.cast_inv, Rat.cast_abs, finprod_div_distrib (mulSupport_finite_int ha)
    (mulSupport_finite_int hb), prod_eq_inv_abs_norm_int ha, prod_eq_inv_abs_norm_int hb]
  rw [← inv_eq_iff_eq_inv, inv_inv_div_inv, ← abs_div]
  congr
  have hb₀ : ((Algebra.norm ℤ) b : ℝ) ≠ 0 := by simp [hb]
  refine (eq_div_of_mul_eq hb₀ ?_).symm
  norm_cast
  rw [coe_norm_int a, coe_norm_int b, ← MonoidHom.map_mul, div_mul_cancel₀ _
    (RingOfIntegers.coe_ne_zero_iff.mpr hb)]

open FinitePlace in
/-- The Product Formula for the Number Field `K`. -/
theorem prod_abs_eq_one {x : K} (h_x_nezero : x ≠ 0) :
    (∏ w : InfinitePlace K, w x ^ w.mult) * ∏ᶠ w : FinitePlace K, w x = 1 := by
  simp [prod_eq_inv_abs_norm, InfinitePlace.prod_eq_abs_norm, h_x_nezero]

end NumberField
