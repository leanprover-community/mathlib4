/-
Copyright (c) 2025 Loic Simon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Loic Simon
-/
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.Measure.Sub

/-!
# Jordan Decomposition from Signed Measure Subtraction

This file develops the Jordan decomposition of the signed measure `μ - ν` for finite measures `μ`
and `ν`, expressing it as the pair `(μ - ν, ν - μ)` of mutually singular finite measures.

The key tool is the Hahn decomposition theorem, which yields a measurable partition of the space
where `μ ≤ ν` and `ν ≤ μ`, and the measure difference behaves like a signed measure difference.

## Main results

* `toJordanDecomposition_toSignedMeasure_sub`:
  The Jordan decomposition of `μ.toSignedMeasure - ν.toSignedMeasure` is given by
  `(μ - ν, ν - μ)`. It relies on the following intermediate results.
* `mutually_singular_measure_sub`:
  The measures `μ - ν` and `ν - μ` are mutually singular.
* `sub_toSignedMeasure_eq_toSignedMeasure_sub`:
  The signed measure `μ.toSignedMeasure - ν.toSignedMeasure` equals
  `(μ - ν).toSignedMeasure - (ν - μ).toSignedMeasure`.
* `setWhereLe_iff_setWhereLeSignedMeasure`:
  The set-theoretic condition for `μ ≥ ν` is equivalent to its reformulation using signed measures.
-/
open scoped MeasureTheory ENNReal NNReal

namespace MeasureTheory

noncomputable section

variable {X : Type*} {mX : MeasurableSpace X}
variable {s : Set X}
variable {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

namespace Measure

/-- The set where `μ ≤ ν`, defined via measurable set and measure restriction comparisons. -/
structure SetWhereLe (μ ν : Measure X) (s : Set X) : Prop where
  measurable : MeasurableSet s
  le_on : μ.restrict s ≤ ν.restrict s
  ge_on_compl : ν.restrict sᶜ ≤ μ.restrict sᶜ

lemma SetWhereLe.compl {μ ν : Measure X} {s : Set X}
    (h : SetWhereLe μ ν s) : SetWhereLe ν μ sᶜ where
  measurable := h.measurable.compl
  le_on := h.ge_on_compl
  ge_on_compl := by rw [compl_compl]; exact h.le_on

end Measure

namespace SignedMeasure

/-- The set where `μ ≥ ν`, reformulated via nonnegativity of signed measure differences. -/
structure SetWhereLe (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (s : Set X) : Prop
where
  measurable : MeasurableSet s
  le_on : μ.toSignedMeasure.restrict s ≤  ν.toSignedMeasure.restrict s
  ge_on_compl : ν.toSignedMeasure.restrict sᶜ ≤  μ.toSignedMeasure.restrict sᶜ

lemma SetWhereLe.compl {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set X} (h : SetWhereLe μ ν s) : SetWhereLe ν μ sᶜ where
  measurable := h.measurable.compl
  le_on := h.ge_on_compl
  ge_on_compl := by rw [compl_compl]; exact h.le_on

end SignedMeasure

lemma exists_SetWhereLeSignedMeasure (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∃ s : Set X, SignedMeasure.SetWhereLe μ ν s := by
  obtain ⟨s, hs, h₂, h₃⟩ := (ν.toSignedMeasure - μ.toSignedMeasure).exists_compl_positive_negative
  simp [VectorMeasure.restrict_sub] at h₂ h₃
  exact ⟨s, hs, h₂, h₃⟩

namespace Measure

lemma sub_eq_zero_of_le_on {μ ν : Measure X} (hs : SetWhereLe μ ν s) : (μ - ν) s = 0 := by
  rw [← restrict_eq_zero, restrict_sub_eq_restrict_sub_restrict hs.measurable]
  exact sub_eq_zero_of_le hs.le_on

lemma ofSignedMeasure_setWhereLe (hs : SignedMeasure.SetWhereLe μ ν s) : SetWhereLe μ ν s where
  measurable := hs.measurable
  le_on := by
    rw [(toSignedMeasure_le_iff _ _).symm, ← sub_nonneg,
        ← toSignedMeasure_restrict_eq_restrict_toSigned _ _ hs.measurable,
        ← toSignedMeasure_restrict_eq_restrict_toSigned _ _ hs.measurable]
    simp [hs.le_on]
  ge_on_compl := by
    rw [(toSignedMeasure_le_iff _ _).symm, ← sub_nonneg,
        ← toSignedMeasure_restrict_eq_restrict_toSigned _ _ hs.measurable.compl,
        ← toSignedMeasure_restrict_eq_restrict_toSigned _ _ hs.measurable.compl]
    simp [hs.ge_on_compl]

lemma toSignedMeasure_setWhereLe (hs : SetWhereLe μ ν s) : SignedMeasure.SetWhereLe μ ν s where
  measurable := hs.measurable
  le_on := by
    rw [toSignedMeasure_restrict_eq_restrict_toSigned _ _ hs.measurable,
        toSignedMeasure_restrict_eq_restrict_toSigned _ _ hs.measurable]
    exact (toSignedMeasure_le_iff _ _).mpr hs.le_on
  ge_on_compl := by
    rw [toSignedMeasure_restrict_eq_restrict_toSigned _ _ hs.measurable.compl,
        toSignedMeasure_restrict_eq_restrict_toSigned _ _ hs.measurable.compl]
    exact (toSignedMeasure_le_iff _ _).mpr hs.ge_on_compl

@[simp]
theorem setWhereLe_iff_setWhereLeSignedMeasure :
    SetWhereLe μ ν s ↔ SignedMeasure.SetWhereLe μ ν s :=
      ⟨toSignedMeasure_setWhereLe, ofSignedMeasure_setWhereLe⟩

lemma sub_eq_zero_of_le_on' (hs : SignedMeasure.SetWhereLe μ ν s) : (μ - ν) s = 0 :=
  sub_eq_zero_of_le_on (ofSignedMeasure_setWhereLe hs)

theorem mutually_singular_measure_sub :
    (μ - ν).MutuallySingular (ν - μ) := by
  obtain ⟨s, hs⟩ := exists_SetWhereLeSignedMeasure μ ν
  exact ⟨s, hs.measurable,
    sub_eq_zero_of_le_on' hs,
    sub_eq_zero_of_le_on' hs.compl⟩

lemma toSignedMeasure_restrict_sub (hs : SignedMeasure.SetWhereLe μ ν s) :
    ((ν - μ).restrict s).toSignedMeasure =
      ν.toSignedMeasure.restrict s - μ.toSignedMeasure.restrict s := by
  have hmeas := hs.measurable
  have hle : μ.restrict s ≤ ν.restrict s := (setWhereLe_iff_setWhereLeSignedMeasure.2 hs).le_on
  rw [eq_sub_iff_add_eq, toSignedMeasure_restrict_eq_restrict_toSigned _ _ hmeas]
  rw [← toSignedMeasure_add]
  have h_restrict := @restrict_sub_eq_restrict_sub_restrict _ _ ν μ s hmeas
  simp only [h_restrict]
  simp only [sub_add_cancel_of_le hle]
  exact (toSignedMeasure_restrict_eq_restrict_toSigned _ _ hmeas).symm

theorem sub_toSignedMeasure_eq_toSignedMeasure_sub :
    μ.toSignedMeasure - ν.toSignedMeasure =
      (μ - ν).toSignedMeasure - (ν - μ).toSignedMeasure := by
  obtain ⟨s, hs⟩ := exists_SetWhereLeSignedMeasure μ ν
  let hsc := hs.compl

  have h₁ := toSignedMeasure_restrict_sub hs
  have h₂ := toSignedMeasure_restrict_sub hsc

  have h₁' := toSignedMeasure_congr <|restrict_eq_zero.mpr <|sub_eq_zero_of_le_on
    <|ofSignedMeasure_setWhereLe hs
  have h₂' := toSignedMeasure_congr <|restrict_eq_zero.mpr <|sub_eq_zero_of_le_on
    <|ofSignedMeasure_setWhereLe hsc

  have partition₁ := VectorMeasure.restrict_add_restrict_compl (μ - ν).toSignedMeasure hs.measurable
  have partition₂ := VectorMeasure.restrict_add_restrict_compl (ν - μ).toSignedMeasure hs.measurable

  rw [toSignedMeasure_restrict_eq_restrict_toSigned _ _ hs.measurable,
      toSignedMeasure_restrict_eq_restrict_toSigned _ _ hs.measurable.compl]
      at partition₁ partition₂

  rw [h₁', h₂] at partition₁
  rw [h₁, h₂'] at partition₂
  simp only [toSignedMeasure_zero, zero_add] at partition₁ partition₂

  rw [← VectorMeasure.restrict_add_restrict_compl μ.toSignedMeasure hs.measurable,
      ← VectorMeasure.restrict_add_restrict_compl ν.toSignedMeasure hs.measurable,
      ← partition₁, ← partition₂]

  repeat rw [sub_eq_add_neg]
  abel


/-- The Jordan decomposition associated to the pair of mutually singular measures μ-ν and ν-μ . -/
def jordanDecomposition_of_toSignedMeasure_sub
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    JordanDecomposition X where
  posPart := μ - ν
  negPart := ν - μ
  mutuallySingular := mutually_singular_measure_sub

/-- The Jordan decomposition of `μ.toSignedMeasure - ν.toSignedMeasure` is `(μ - ν, ν - μ)`. -/
@[simp]
theorem toJordanDecomposition_toSignedMeasure_sub :
    (μ.toSignedMeasure - ν.toSignedMeasure).toJordanDecomposition =
      jordanDecomposition_of_toSignedMeasure_sub μ ν := by
  apply JordanDecomposition.toSignedMeasure_injective
  rw [SignedMeasure.toSignedMeasure_toJordanDecomposition,
    sub_toSignedMeasure_eq_toSignedMeasure_sub]
  rfl

end Measure

end
end MeasureTheory
