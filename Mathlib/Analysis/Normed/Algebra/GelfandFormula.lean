/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Gelfand's formula and other results on the spectrum in complex Banach algebras

This file contains results on the spectrum of elements in a complex Banach algebra, including
**Gelfand's formula** and the **Gelfand-Mazur theorem** and the fact that every element in a
complex Banach algebra has nonempty spectrum.

## Main results

* `spectrum.hasDerivAt_resolvent`: the resolvent function is differentiable on the resolvent set.
* `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`: Gelfand's formula for the
  spectral radius in Banach algebras over `ℂ`.
* `spectrum.nonempty`: the spectrum of any element in a complex Banach algebra is nonempty.
* `NormedRing.algEquivComplexOfComplete`: **Gelfand-Mazur theorem** For a complex
  Banach division algebra, the natural `algebraMap ℂ A` is an algebra isomorphism whose inverse
  is given by selecting the (unique) element of `spectrum ℂ a`

-/

variable {𝕜 A : Type*}

open scoped NNReal Topology
open Filter ENNReal

namespace spectrum

theorem hasDerivAt_resolvent [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    [CompleteSpace A] {a : A} {k : 𝕜} (hk : k ∈ resolventSet 𝕜 a) :
    HasDerivAt (resolvent a) (-resolvent a k ^ 2) k := by
  have H₁ : HasFDerivAt Ring.inverse _ (algebraMap 𝕜 A k - a) :=
    hasFDerivAt_ringInverse (𝕜 := 𝕜) hk.unit
  have H₂ : HasDerivAt (fun k => algebraMap 𝕜 A k - a) 1 k := by
    simpa using (Algebra.linearMap 𝕜 A).hasDerivAt.sub_const a
  simpa [resolvent, sq, hk.unit_spec, ← Ring.inverse_unit hk.unit] using H₁.comp_hasDerivAt k H₂

open ENNReal in
/-- In a Banach algebra `A` over `𝕜`, for `a : A` the function `fun z ↦ (1 - z • a)⁻¹` is
differentiable on any closed ball centered at zero of radius `r < (spectralRadius 𝕜 a)⁻¹`. -/
theorem differentiableOn_inverse_one_sub_smul [NontriviallyNormedField 𝕜] [NormedRing A]
    [NormedAlgebra 𝕜 A] [CompleteSpace A] {a : A} {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < (spectralRadius 𝕜 a)⁻¹) :
    DifferentiableOn 𝕜 (fun z : 𝕜 => Ring.inverse (1 - z • a)) (Metric.closedBall 0 r) := by
  intro z z_mem
  apply DifferentiableAt.differentiableWithinAt
  have hu : IsUnit (1 - z • a) := by
    refine isUnit_one_sub_smul_of_lt_inv_radius (lt_of_le_of_lt (coe_mono ?_) hr)
    simpa only [norm_toNNReal, Real.toNNReal_coe] using
      Real.toNNReal_mono (mem_closedBall_zero_iff.mp z_mem)
  have H₁ : Differentiable 𝕜 fun w : 𝕜 => 1 - w • a := (differentiable_id.smul_const a).const_sub 1
  exact DifferentiableAt.comp z (differentiableAt_inverse hu) H₁.differentiableAt

section Complex

variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

open ContinuousMultilinearMap in
/-- The `limsup` relationship for the spectral radius used to prove `spectrum.gelfand_formula`. -/
theorem limsup_pow_nnnorm_pow_one_div_le_spectralRadius (a : A) :
    limsup (fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) atTop ≤ spectralRadius ℂ a := by
  refine ENNReal.inv_le_inv.mp (le_of_forall_pos_nnreal_lt fun r r_pos r_lt => ?_)
  simp_rw [inv_limsup, ← one_div]
  let p : FormalMultilinearSeries ℂ ℂ A := fun n =>
    ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a ^ n)
  suffices h : (r : ℝ≥0∞) ≤ p.radius by
    convert h
    simp only [p, p.radius_eq_liminf, ← norm_toNNReal, norm_mkPiRing]
    congr
    ext n
    rw [norm_toNNReal, ENNReal.coe_rpow_def ‖a ^ n‖₊ (1 / n : ℝ), if_neg]
    exact fun ha => (lt_self_iff_false _).mp
      (ha.2.trans_le (one_div_nonneg.mpr n.cast_nonneg : 0 ≤ (1 / n : ℝ)))
  have H₁ := (differentiableOn_inverse_one_sub_smul r_lt).hasFPowerSeriesOnBall r_pos
  exact ((hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ a).exchange_radius H₁).r_le

/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectralRadius` of `a` is the limit of the sequence `‖a ^ n‖₊ ^ (1 / n)`. -/
theorem pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a : A) :
    Tendsto (fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) atTop (𝓝 (spectralRadius ℂ a)) :=
  tendsto_of_le_liminf_of_limsup_le (spectralRadius_le_liminf_pow_nnnorm_pow_one_div ℂ a)
    (limsup_pow_nnnorm_pow_one_div_le_spectralRadius a)

alias gelfand_formula := pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius

/- This is the same as `pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` but for `norm`
instead of `nnnorm`. -/
/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectralRadius` of `a` is the limit of the sequence `‖a ^ n‖₊ ^ (1 / n)`. -/
theorem pow_norm_pow_one_div_tendsto_nhds_spectralRadius (a : A) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (‖a ^ n‖ ^ (1 / n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ a)) := by
  convert pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a using 1
  ext1
  rw [← ofReal_rpow_of_nonneg (norm_nonneg _) _, ← coe_nnnorm, coe_nnreal_eq]
  exact one_div_nonneg.mpr (mod_cast zero_le _)

section Nontrivial

variable [Nontrivial A]

/-- In a (nontrivial) complex Banach algebra, every element has nonempty spectrum. -/
protected theorem nonempty (a : A) : (spectrum ℂ a).Nonempty := by
  /- Suppose `σ a = ∅`, then resolvent set is `ℂ`, any `(z • 1 - a)` is a unit, and `resolvent a`
    is differentiable on `ℂ`. -/
  by_contra! h
  have H₀ : resolventSet ℂ a = Set.univ := by rwa [spectrum, Set.compl_empty_iff] at h
  have H₁ : Differentiable ℂ fun z : ℂ => resolvent a z := fun z =>
    (hasDerivAt_resolvent (H₀.symm ▸ Set.mem_univ z : z ∈ resolventSet ℂ a)).differentiableAt
  /- Since `resolvent a` tends to zero at infinity, by Liouville's theorem `resolvent a = 0`,
  which contradicts that `resolvent a z` is invertible. -/
  have H₃ := H₁.apply_eq_of_tendsto_cocompact 0 <| by
    simpa [Metric.cobounded_eq_cocompact] using resolvent_tendsto_cobounded a (𝕜 := ℂ)
  exact not_isUnit_zero <| H₃ ▸ (isUnit_resolvent.mp <| H₀.symm ▸ Set.mem_univ 0)

/-- In a complex Banach algebra, the spectral radius is always attained by some element of the
spectrum. -/
theorem exists_nnnorm_eq_spectralRadius (a : A) :
    ∃ z ∈ spectrum ℂ a, (‖z‖₊ : ℝ≥0∞) = spectralRadius ℂ a :=
  exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty a)

/-- In a complex Banach algebra, if every element of the spectrum has norm strictly less than
`r : ℝ≥0`, then the spectral radius is also strictly less than `r`. -/
theorem spectralRadius_lt_of_forall_lt (a : A) {r : ℝ≥0}
    (hr : ∀ z ∈ spectrum ℂ a, ‖z‖₊ < r) : spectralRadius ℂ a < r :=
  spectralRadius_lt_of_forall_lt_of_nonempty (spectrum.nonempty a) hr


open Polynomial in
/-- The **spectral mapping theorem** for polynomials in a Banach algebra over `ℂ`. -/
theorem map_polynomial_aeval (a : A) (p : ℂ[X]) :
    spectrum ℂ (aeval a p) = (fun k => eval k p) '' spectrum ℂ a :=
  map_polynomial_aeval_of_nonempty a p (spectrum.nonempty a)

open Polynomial in
/-- A specialization of the spectral mapping theorem for polynomials in a Banach algebra over `ℂ`
to monic monomials. -/
protected theorem map_pow (a : A) (n : ℕ) :
    spectrum ℂ (a ^ n) = (· ^ n) '' spectrum ℂ a := by
  simpa only [aeval_X_pow, eval_X_pow] using map_polynomial_aeval a (X ^ n)

end Nontrivial

omit [CompleteSpace A] in
theorem algebraMap_eq_of_mem (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) {a : A} {z : ℂ}
    (h : z ∈ spectrum ℂ a) : algebraMap ℂ A z = a := by
  rwa [mem_iff, hA, Classical.not_not, sub_eq_zero] at h

/-- **Gelfand-Mazur theorem**: For a complex Banach division algebra, the natural `algebraMap ℂ A`
is an algebra isomorphism whose inverse is given by selecting the (unique) element of
`spectrum ℂ a`. In addition, `algebraMap_isometry` guarantees this map is an isometry.

Note: because `NormedDivisionRing` requires the field `norm_mul : ∀ a b, ‖a * b‖ = ‖a‖ * ‖b‖`, we
don't use this type class and instead opt for a `NormedRing` in which the nonzero elements are
precisely the units. This allows for the application of this isomorphism in broader contexts, e.g.,
to the quotient of a complex Banach algebra by a maximal ideal. In the case when `A` is actually a
`NormedDivisionRing`, one may fill in the argument `hA` with the lemma `isUnit_iff_ne_zero`. -/
@[simps]
noncomputable def _root_.NormedRing.algEquivComplexOfComplete (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0)
    [CompleteSpace A] : ℂ ≃ₐ[ℂ] A :=
  let nt : Nontrivial A := ⟨⟨1, 0, hA.mp ⟨⟨1, 1, mul_one _, mul_one _⟩, rfl⟩⟩⟩
  { Algebra.ofId ℂ A with
    toFun := algebraMap ℂ A
    invFun := fun a => (@spectrum.nonempty _ _ _ _ nt a).some
    left_inv := fun z => by
      simpa only [@scalar_eq _ _ _ _ _ nt _] using
        (@spectrum.nonempty _ _ _ _ nt <| algebraMap ℂ A z).some_mem
    right_inv := fun a => algebraMap_eq_of_mem (@hA) (@spectrum.nonempty _ _ _ _ nt a).some_mem }

end Complex

end spectrum
