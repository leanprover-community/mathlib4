/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.NumberTheory.DirichletCharacter.GaussSum

/-!
# Fourier theory on `ZMod N`

Basic definitions and properties of the discrete Fourier transform for functions on `ZMod N`.

### Main definitions and results

* `ZMod.dft`: the Fourier transform with respect to the standard additive character
  `ZMod.stdAddChar` (mapping `j mod N` to `exp (2 * π * I * j / N)`). The notation `𝓕`, scoped in
  namespace `ZMod`, is available for this.
* `DirichletCharacter.fourierTransform_eq_inv_mul_gaussSum`: the discrete Fourier transform of a
  primitive Dirichlet character `χ` is a Gauss sum times `χ⁻¹`.
-/

open scoped Real

open MeasureTheory

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- The discrete Fourier transform on `ℤ / N ℤ` (with the counting measure) -/
noncomputable def dft (Φ : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  Fourier.fourierIntegral toCircle Measure.count Φ k

@[inherit_doc] scoped notation "𝓕" => dft

lemma dft_apply (Φ : ZMod N → ℂ) (k : ZMod N) :
    𝓕 Φ k = ∑ j : ZMod N, toCircle (-(j * k)) • Φ j := by
  simp only [dft, Fourier.fourierIntegral_def, integral_countable' <| .of_finite ..,
    Measure.count_singleton, ENNReal.one_toReal, one_smul, tsum_fintype]

lemma dft_def (Φ : ZMod N → ℂ) : 𝓕 Φ = fun k ↦ ∑ j : ZMod N, toCircle (-(j * k)) • Φ j :=
  funext (dft_apply Φ)

end ZMod

open ZMod

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

lemma fourierTransform_eq_gaussSum_mulShift (k : ZMod N) :
    𝓕 χ k = gaussSum χ (stdAddChar.mulShift (-k)) := by
  simp only [dft_def]
  congr 1 with j
  rw [AddChar.mulShift_apply, mul_comm j, Submonoid.smul_def, smul_eq_mul, neg_mul,
    stdAddChar_apply, mul_comm (χ _)]

/-- For a primitive Dirichlet character `χ`, the Fourier transform of `χ` is a constant multiple
of `χ⁻¹` (and the constant is essentially the Gauss sum). -/
lemma fourierTransform_eq_inv_mul_gaussSum (k : ZMod N) (hχ : IsPrimitive χ) :
    𝓕 χ k = χ⁻¹ (-k) * gaussSum χ stdAddChar := by
  rw [fourierTransform_eq_gaussSum_mulShift, gaussSum_mulShift_of_isPrimitive _ hχ]

end DirichletCharacter
