/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Invariant measure on the upper half-plane

We equip the upper half-plane with a measure, defined as the restriction of the usual measure
on `ℂ` weighted by the function `1 / (im z) ^ 2`. We show that this measure is invariant under
the action of `GL(2, ℝ)`.
-/

open MeasureTheory

@[expose] public noncomputable section

namespace UpperHalfPlane

instance : MeasurableSpace ℍ := Subtype.instMeasurableSpace

instance : BorelSpace ℍ := Subtype.borelSpace _

lemma measurableEmbedding_coe : MeasurableEmbedding UpperHalfPlane.coe :=
  isOpenEmbedding_coe.measurableEmbedding

/-- The invariant measure on the upper half-plane, defined by `dx dy / y ^ 2`. -/
instance : MeasureSpace ℍ :=
  ⟨(volume.comap UpperHalfPlane.coe).withDensity fun z ↦ ↑((1 / ⟨z.im, z.im_pos.le⟩ : NNReal) ^ 2)⟩

/-- Express the volume of a measurable set as a lintegral over the corresponding subset of `ℂ`. -/
lemma volume_eq_lintegral {s : Set ℍ} (hs : MeasurableSet s) :
    volume s = ∫⁻ z : ℂ in (↑) '' s, ↑((1 / ‖z.im‖₊) ^ 2 : NNReal) := by
  simp only [volume, one_div]
  -- This proof is annoying because `setLIntegral_subtype` only works on a literal subtype,
  -- while `UpperHalfPlane` is a _type alias_ for a subtype, so we need to do some annoying
  -- defeq abuse.
  rw [show UpperHalfPlane.coe = Subtype.val from rfl,
    ← setLIntegral_subtype (by exact isOpen_upperHalfPlaneSet.measurableSet),
    withDensity_apply _ hs]
  congr 1 with z
  congr 4
  rw [Real.norm_of_nonneg (by simpa using z.im_pos.le), ← z.coe_im,
    show UpperHalfPlane.coe = Subtype.val from rfl]

/-- The measure on the upper half-plane is invariant under `GL(2, ℝ)`. -/
instance : SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ volume := by
  -- It suffices to show `volume (g • s) = volume s` for measurable sets `s`. First
  -- we write this as a lintegral over subsets of `ℂ`.
  refine ((smulInvariantMeasure_tfae _ _).out 2 0).mp fun g s hs ↦ ?_
  rw [volume_eq_lintegral hs, volume_eq_lintegral (hs.const_smul _)]
  -- We want to apply the Jacobian change-of-variable formula, so first
  -- we establish the hypotheses.
  have aux1 (x : ℂ) (hx : x ∈ (↑) '' s) :
      HasFDerivWithinAt (𝕜 := ℝ) (smulAux' g) (smulFDeriv g x) ((↑) '' s) x := by
    apply HasFDerivAt.hasFDerivWithinAt
    rcases hx with ⟨τ, hτ, rfl⟩
    apply (hasFDerivAt_smul g τ).congr_of_eventuallyEq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.property] with z hz
    simp_all [σ, coe_smul, ofComplex_apply_of_im_pos, smulAux']
  have aux2 : ((↑) '' s).InjOn (smulAux' g) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← UpperHalfPlane.ext_iff]
      change (↑(g • x) : ℂ) = ↑(g • y) → x = y
      simp only [ext_iff', smul_left_cancel_iff, imp_self]
  -- Now invoke the change-of-variable formula.
  have main := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      volume (measurableEmbedding_coe.measurableSet_image.mpr hs) aux1 aux2
      (fun z ↦ ↑((1 / ‖z.im‖₊) ^ 2 : NNReal))
  -- Adjust the LHS of the resulting statement slightly to match our goal.
  have aux3 : smulAux' g ∘ ((↑) : ℍ → ℂ) = (↑) ∘ (fun x ↦ g • x) := by rfl
  rw [← Set.image_comp, aux3, Set.image_comp, Set.image_smul] at main
  rw [main]
  -- Now it remains to compare two integrals over `coe '' s`.
  apply setLIntegral_congr_fun (measurableEmbedding_coe.measurableSet_image.mpr hs)
  rintro _ ⟨τ, hτ, rfl⟩
  simp only [det_smulFDeriv, abs_div, abs_mul, abs_pow, abs_pow, sq_abs,
    (show Even 4 by grind).pow_abs]
  have : |(SignType.sign g.det.val : ℝ)| = 1 := by
    rcases lt_or_gt_of_ne (NeZero.ne g.det.val) with h | h <;>
    simp [-Matrix.GeneralLinearGroup.val_det_apply, h]
  rw [this, one_mul, ENNReal.ofReal_eq_coe_nnreal (by positivity), ← ENNReal.coe_mul,
    ENNReal.coe_inj, NNReal.eq_iff]
  push_cast
  rw [div_pow, one_pow, mul_one_div, show 4 = 2 * 2 by rfl, pow_mul, ← div_pow, ← div_pow]
  simp only [sq_eq_sq_iff_abs_eq_abs, abs_div, abs_pow, abs_one, abs_norm,
    show smulAux' g τ = ↑(g • τ) by rfl, coe_im, im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  simp only [norm_div, norm_pow, norm_mul, norm_abs_eq_norm, Real.norm_eq_abs, abs_norm]
  rw [div_div_div_cancel_right₀ (by simpa using denom_ne_zero g τ),
    ← div_div, div_self (by aesop)]

end UpperHalfPlane

end
