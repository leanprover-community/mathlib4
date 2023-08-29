/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Measure.VectorMeasure

#align_import measure_theory.measure.complex from "leanprover-community/mathlib"@"17b3357baa47f48697ca9c243e300eb8cdd16a15"

/-!
# Complex measure

This file proves some elementary results about complex measures. In particular, we prove that
a complex measure is always in the form `s + it` where `s` and `t` are signed measures.

The complex measure is defined to be vector measure over `ℂ`, this definition can be found
in `Mathlib/MeasureTheory/Measure/VectorMeasure.lean` and is known as
`MeasureTheory.ComplexMeasure`.

## Main definitions

* `MeasureTheory.ComplexMeasure.re`: obtains a signed measure `s` from a complex measure `c`
  such that `s i = (c i).re` for all measurable sets `i`.
* `MeasureTheory.ComplexMeasure.im`: obtains a signed measure `s` from a complex measure `c`
  such that `s i = (c i).im` for all measurable sets `i`.
* `MeasureTheory.SignedMeasure.toComplexMeasure`: given two signed measures `s` and `t`,
  `s.to_complex_measure t` provides a complex measure of the form `s + it`.
* `MeasureTheory.ComplexMeasure.equivSignedMeasure`: is the equivalence between the complex
  measures and the type of the product of the signed measures with itself.

# Tags

Complex measure
-/


noncomputable section

open scoped Classical MeasureTheory ENNReal NNReal

variable {α β : Type*} {m : MeasurableSpace α}

namespace MeasureTheory

open VectorMeasure

namespace ComplexMeasure

/-- The real part of a complex measure is a signed measure. -/
@[simps! apply]
def re : ComplexMeasure α →ₗ[ℝ] SignedMeasure α :=
  mapRangeₗ Complex.reClm Complex.continuous_re
#align measure_theory.complex_measure.re MeasureTheory.ComplexMeasure.re

/-- The imaginary part of a complex measure is a signed measure. -/
@[simps! apply]
def im : ComplexMeasure α →ₗ[ℝ] SignedMeasure α :=
  mapRangeₗ Complex.imClm Complex.continuous_im
#align measure_theory.complex_measure.im MeasureTheory.ComplexMeasure.im

/-- Given `s` and `t` signed measures, `s + it` is a complex measure-/
@[simps!]
def _root_.MeasureTheory.SignedMeasure.toComplexMeasure (s t : SignedMeasure α) :
    ComplexMeasure α where
  measureOf' i := ⟨s i, t i⟩
  empty' := by dsimp only; rw [s.empty, t.empty]; rfl
               -- ⊢ { re := ↑s ∅, im := ↑t ∅ } = 0
                           -- ⊢ { re := 0, im := 0 } = 0
                                                  -- 🎉 no goals
  not_measurable' i hi := by dsimp only; rw [s.not_measurable hi, t.not_measurable hi]; rfl
                             -- ⊢ { re := ↑s i, im := ↑t i } = 0
                                         -- ⊢ { re := 0, im := 0 } = 0
                                                                                        -- 🎉 no goals
  m_iUnion' f hf hfdisj := (Complex.hasSum_iff _ _).2 ⟨s.m_iUnion hf hfdisj, t.m_iUnion hf hfdisj⟩
#align measure_theory.signed_measure.to_complex_measure MeasureTheory.SignedMeasure.toComplexMeasure

theorem _root_.MeasureTheory.SignedMeasure.toComplexMeasure_apply
  {s t : SignedMeasure α} {i : Set α} : s.toComplexMeasure t i = ⟨s i, t i⟩ := rfl
#align measure_theory.signed_measure.to_complex_measure_apply MeasureTheory.SignedMeasure.toComplexMeasure_apply

theorem toComplexMeasure_to_signedMeasure (c : ComplexMeasure α) :
    SignedMeasure.toComplexMeasure (ComplexMeasure.re c) (ComplexMeasure.im c) = c := rfl
#align measure_theory.complex_measure.to_complex_measure_to_signed_measure MeasureTheory.ComplexMeasure.toComplexMeasure_to_signedMeasure

theorem _root_.MeasureTheory.SignedMeasure.re_toComplexMeasure (s t : SignedMeasure α) :
    ComplexMeasure.re (SignedMeasure.toComplexMeasure s t) = s := rfl
#align measure_theory.signed_measure.re_to_complex_measure MeasureTheory.SignedMeasure.re_toComplexMeasure

theorem _root_.MeasureTheory.SignedMeasure.im_toComplexMeasure (s t : SignedMeasure α) :
    ComplexMeasure.im (SignedMeasure.toComplexMeasure s t) = t := rfl
#align measure_theory.signed_measure.im_to_complex_measure MeasureTheory.SignedMeasure.im_toComplexMeasure

/-- The complex measures form an equivalence to the type of pairs of signed measures. -/
@[simps]
def equivSignedMeasure : ComplexMeasure α ≃ SignedMeasure α × SignedMeasure α where
  toFun c := ⟨ComplexMeasure.re c, ComplexMeasure.im c⟩
  invFun := fun ⟨s, t⟩ => s.toComplexMeasure t
  left_inv c := c.toComplexMeasure_to_signedMeasure
  right_inv := fun ⟨s, t⟩ => Prod.mk.inj_iff.2 ⟨s.re_toComplexMeasure t, s.im_toComplexMeasure t⟩
#align measure_theory.complex_measure.equiv_signed_measure MeasureTheory.ComplexMeasure.equivSignedMeasure

section

variable {R : Type*} [Semiring R] [Module R ℝ]

variable [ContinuousConstSMul R ℝ] [ContinuousConstSMul R ℂ]

/-- The complex measures form a linear isomorphism to the type of pairs of signed measures. -/
@[simps]
def equivSignedMeasureₗ : ComplexMeasure α ≃ₗ[R] SignedMeasure α × SignedMeasure α :=
  { equivSignedMeasure with
    map_add' := fun c d => by rfl
                              -- 🎉 no goals
    map_smul' := by
      intro r c
      -- ⊢ AddHom.toFun { toFun := src✝.toFun, map_add' := (_ : ∀ (c d : ComplexMeasure …
      dsimp
      -- ⊢ (mapRange (r • c) (LinearMap.toAddMonoidHom Complex.reLm) Complex.continuous …
      ext
      -- ⊢ ↑(mapRange (r • c) (LinearMap.toAddMonoidHom Complex.reLm) Complex.continuou …
      · simp [Complex.smul_re]
        -- 🎉 no goals
      · simp [Complex.smul_im] }
        -- 🎉 no goals
#align measure_theory.complex_measure.equiv_signed_measureₗ MeasureTheory.ComplexMeasure.equivSignedMeasureₗ

end

theorem absolutelyContinuous_ennreal_iff (c : ComplexMeasure α) (μ : VectorMeasure α ℝ≥0∞) :
    c ≪ᵥ μ ↔ ComplexMeasure.re c ≪ᵥ μ ∧ ComplexMeasure.im c ≪ᵥ μ := by
  constructor <;> intro h
  -- ⊢ c ≪ᵥ μ → ↑re c ≪ᵥ μ ∧ ↑im c ≪ᵥ μ
                  -- ⊢ ↑re c ≪ᵥ μ ∧ ↑im c ≪ᵥ μ
                  -- ⊢ c ≪ᵥ μ
  · constructor <;> · intro i hi; simp [h hi]
    -- ⊢ ↑re c ≪ᵥ μ
                      -- ⊢ ↑(↑re c) i = 0
                                  -- 🎉 no goals
                      -- ⊢ ↑(↑im c) i = 0
                                  -- 🎉 no goals
  · intro i hi
    -- ⊢ ↑c i = 0
    rw [← Complex.re_add_im (c i), (_ : (c i).re = 0), (_ : (c i).im = 0)]
    exacts [by simp, h.2 hi, h.1 hi]
    -- 🎉 no goals
#align measure_theory.complex_measure.absolutely_continuous_ennreal_iff MeasureTheory.ComplexMeasure.absolutelyContinuous_ennreal_iff

end ComplexMeasure

end MeasureTheory
