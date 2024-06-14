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

* `ZMod.stdAddChar`: the additive character of `ZMod N` sending `1` to `exp (2 * π * I / N)`.
* `ZMod.discreteFourierTransform`: the Fourier transform with respect to this add char. The local
  notation `𝓕`, scoped in namespace `ZMod`, is available for this.
* `DirichletCharacter.fourierTransform_eq_inv_mul_gaussSum`: the discrete Fourier transform of a
  primitive Dirichlet character `χ` is a Gauss sum times `χ⁻¹`.
-/

open scoped Real

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- The `AddMonoidHom` from `ZMod N` to `ℝ / ℤ` sending `j mod N` to `j / N mod 1`. -/
noncomputable def toAddCircle : ZMod N →+ UnitAddCircle :=
  lift N ⟨AddMonoidHom.mk' (fun j ↦ ↑(j / N : ℝ)) (by simp [add_div]), by simp⟩

lemma toAddCircle_coe (j : ℤ) :
    toAddCircle (j : ZMod N) = ↑(j / N : ℝ) := by
  simp [toAddCircle]

lemma toAddCircle_apply (j : ZMod N) :
    toAddCircle j = ↑(j.val / N : ℝ) := by
  conv_lhs => rw [show j = (val j : ℤ) by simp, toAddCircle_coe]
  simp only [natCast_val, intCast_cast]

variable (N) in
lemma toAddCircle_injective : Function.Injective (toAddCircle : ZMod N → _) := by
  intro x y hxy
  have : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos _)
  rwa [toAddCircle_apply, toAddCircle_apply, AddCircle.coe_eq_coe_iff_of_mem_Ico
    (hp := Real.fact_zero_lt_one) (a := 0), div_left_inj' this.ne', Nat.cast_inj,
    (val_injective N).eq_iff] at hxy <;>
  exact ⟨by positivity, by simpa only [zero_add, div_lt_one this, Nat.cast_lt] using val_lt _⟩

/-- The additive character from `ZMod N` to the unit circle in `ℂ`, sending `j mod N` to
`exp (2 * π * I * j / N)`. -/
noncomputable def toCircle : AddChar (ZMod N) circle where
  toFun := fun j ↦ (toAddCircle j).toCircle
  map_add_mul' a b := by simp_rw [map_add, AddCircle.toCircle_add]
  map_zero_one' := by simp_rw [map_zero, AddCircle.toCircle, ← QuotientAddGroup.mk_zero,
    Function.Periodic.lift_coe, mul_zero, expMapCircle_zero]

lemma toCircle_coe (j : ℤ) :
    toCircle (j : ZMod N) = Complex.exp (2 * π * Complex.I * j / N) := by
  rw [toCircle, AddChar.coe_mk, AddCircle.toCircle, toAddCircle_coe,
    Function.Periodic.lift_coe, expMapCircle_apply]
  push_cast
  ring_nf

lemma toCircle_apply (j : ZMod N) :
    toCircle j = Complex.exp (2 * π * Complex.I * j.val / N) := by
  rw [← Int.cast_natCast, ← toCircle_coe, natCast_val, intCast_zmod_cast]

/-- The additive character from `ZMod N` to `ℂ`, sending
`j mod N` to `exp (2 * π * I * j / N)`. -/
noncomputable def stdAddChar : AddChar (ZMod N) ℂ := circle.subtype.compAddChar toCircle

lemma stdAddChar_coe (j : ℤ) :
    stdAddChar (j : ZMod N) = Complex.exp (2 * π * Complex.I * j / N) := by
  simp only [stdAddChar, MonoidHom.coe_compAddChar, Function.comp_apply,
    Submonoid.coe_subtype, toCircle_coe]

lemma stdAddChar_apply (j : ZMod N) : stdAddChar j = ↑(toCircle j) := rfl

section fourier

open MeasureTheory

/-- The discrete measurable space structure (every set is measurable). -/
instance instMeasurableSpaceZMod : MeasurableSpace (ZMod N) := ⊤

/-- The discrete Fourier transform on `ℤ / Nℤ` (with the counting measure) -/
noncomputable def dft (Φ : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  Fourier.fourierIntegral toCircle Measure.count Φ k

@[inherit_doc] scoped notation "𝓕" => dft

lemma dft_def (Φ : ZMod N → ℂ) (k : ZMod N) :
    𝓕 Φ k = ∑ j : ZMod N, toCircle (-(j * k)) • Φ j := by
  simp only [dft, Fourier.fourierIntegral_def,
    integral_countable' (integrable_count_iff.mpr <| Finite.summable _), Measure.count_singleton,
    ENNReal.one_toReal, one_smul, tsum_fintype]

end fourier

end ZMod

open ZMod

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

lemma fourierTransform_eq_gaussSum_mulShift (k : ZMod N) :
    𝓕 χ k = gaussSum χ (stdAddChar.mulShift (-k)) := by
  simp only [dft_def]
  refine congr_arg Finset.univ.sum (funext fun j ↦ ?_)
  rw [AddChar.mulShift_apply, mul_comm j, Submonoid.smul_def, smul_eq_mul, neg_mul,
    stdAddChar_apply, mul_comm (χ _)]

/-- For a primitive Dirichlet character `χ`, the Fourier transform of `χ` is a constant multiple
of `χ⁻¹` (and the constant is essentially the Gauss sum). -/
lemma fourierTransform_eq_inv_mul_gaussSum (k : ZMod N) (hχ : isPrimitive χ) :
    𝓕 χ k = χ⁻¹ (-k) * gaussSum χ stdAddChar := by
  rw [fourierTransform_eq_gaussSum_mulShift, gaussSum_mulShift_of_isPrimitive _ hχ]

end DirichletCharacter
