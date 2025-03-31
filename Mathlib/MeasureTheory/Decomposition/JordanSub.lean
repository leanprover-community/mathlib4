  /-
Copyright (c) 2025 Loic Simon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Loic Simon
-/
import Mathlib.MeasureTheory.Decomposition.Jordan
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Tactic.NoncommRing

/-!
# Jordan Decomposition from Signed Measure Subtraction

This file develops the Jordan decomposition of the signed measure `μ - ν` for finite measures `μ`
and `ν`, expressing it as the pair `(μ - ν, ν - μ)` of mutually singular finite measures.

The key tool is the Hahn decomposition theorem, which yields a measurable partition of the space
where `μ ≥ ν` and `ν ≥ μ`, and the measure difference behaves like a signed measure difference.

## Main results

* `toJordanDecomposition_toSignedMeasure_sub`:
  The Jordan decomposition of `μ.toSignedMeasure - ν.toSignedMeasure` is given by
  `(μ - ν, ν - μ)`. It relies on the following intermediate results.
* `mutually_singular_measure_sub`:
  The measures `μ - ν` and `ν - μ` are mutually singular.
* `sub_toSignedMeasure_eq_toSignedMeasure_sub`:
  The signed measure `μ.toSignedMeasure - ν.toSignedMeasure` equals
  `(μ - ν).toSignedMeasure - (ν - μ).toSignedMeasure`.
* `setWhereGe_iff_setWhereGeSignedMeasure`:
  The set-theoretic condition for `μ ≥ ν` is equivalent to its reformulation using signed measures.

## Notations

- `μ - ν` : Subtraction of finite measures i.e. the least measure `τ` such that `μ ≤ τ + ν`.

  It is the equivalent of `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
- `μ.restrict s` : Restriction of a measure `μ` to the set `s`.
- `μ.toSignedMeasure` : Signed measure corresponding to `μ`.
- `0 ≤[s] μ` : The signed measure `μ` is nonnegative on the set `s`.
- `sᶜ` : Complement of a measurable set `s`.
-/

open scoped MeasureTheory ENNReal NNReal

namespace MeasureTheory

noncomputable section

variable {α : Type*} [m : MeasurableSpace α]
variable {s : Set α}
variable {μ ν : Measure α} [hμ : IsFiniteMeasure μ] [hν : IsFiniteMeasure ν]

namespace Measure
/-- The set where `μ ≥ ν`, defined via measurable set and measure restriction comparisons. -/
class SetWhereGe (μ ν : Measure α) (s : Set α) : Prop where
  measurable : MeasurableSet s
  ge_on : ν.restrict s ≤ μ.restrict s
  ge_on_compl : μ.restrict sᶜ ≤ ν.restrict sᶜ

instance SetWhereGe.compl_symm {μ ν : Measure α} {s : Set α}
    [h : SetWhereGe μ ν s] : SetWhereGe ν μ sᶜ where
  measurable := h.measurable.compl
  ge_on := h.ge_on_compl
  ge_on_compl := by rw [compl_compl]; exact h.ge_on
end Measure

namespace SignedMeasure

/-- The set where `μ ≥ ν`, reformulated via nonnegativity of signed measure differences. -/
class SetWhereGe (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (s : Set α) : Prop where
  measurable : MeasurableSet s
  ge_on : ν.toSignedMeasure.restrict s ≤  μ.toSignedMeasure.restrict s
  ge_on_compl : μ.toSignedMeasure.restrict sᶜ ≤  ν.toSignedMeasure.restrict sᶜ

instance SetWhereGe.compl_symm {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} [h : SetWhereGe μ ν s] : SetWhereGe ν μ sᶜ where
  measurable := h.measurable.compl
  ge_on := h.ge_on_compl
  ge_on_compl := by rw [compl_compl]; exact h.ge_on

end SignedMeasure

namespace VectorMeasure

variable {α : Type*} [m : MeasurableSpace α]
variable (μ ν : VectorMeasure α ℝ) (s : Set α)

@[simp]
theorem restrict_neg :
    (-μ).restrict s = -(μ.restrict s) := by
  by_cases hs : MeasurableSet s
  · ext t ht; simp [restrict_apply _ hs ht]
  · simp [restrict_not_measurable _ hs]

@[simp]
theorem restrict_sub :
    (μ - ν).restrict s = μ.restrict s - ν.restrict s := by
  simp [sub_eq_add_neg, restrict_add]

@[simp]
theorem restrict_add_restrict_compl (μ : VectorMeasure α ℝ) {s : Set α} (hs : MeasurableSet s) :
    μ.restrict s + μ.restrict sᶜ = μ := by
  ext A hA
  rw [add_apply, restrict_apply _ hs hA, restrict_apply _ hs.compl hA,
    ← of_union _ (hA.inter hs) (hA.inter hs.compl)]

  · simp [Set.inter_union_compl]
  · refine Disjoint.inter_left' A ?_
    refine Disjoint.inter_right' A ?_
    apply disjoint_compl_right

end VectorMeasure

lemma exists_SetWhereGeSignedMeasure (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∃ s : Set α, SignedMeasure.SetWhereGe μ ν s := by
  obtain ⟨s, hs, h₂, h₃⟩ := (μ.toSignedMeasure - ν.toSignedMeasure).exists_compl_positive_negative
  simp at h₂ h₃
  exact ⟨s, hs, h₂, h₃⟩

namespace Measure

@[simp]
theorem toSignedMeasure_restrict_eq_restrict_toSigned (hs : MeasurableSet s) :
    μ.toSignedMeasure.restrict s = (μ.restrict s).toSignedMeasure := by
  ext A hA
  rw [VectorMeasure.restrict_apply _ hs hA]
  simp [toSignedMeasure_apply, hA, hs, MeasurableSet.inter, ↓reduceIte, restrict_apply]

@[simp]
theorem toSignedMeasure_le_iff : μ ≤ ν ↔ μ.toSignedMeasure ≤ ν.toSignedMeasure := by
  constructor
  · intro h A hA
    simp [toSignedMeasure_apply, hA, measure_ne_top, ENNReal.toReal_le_toReal]
    exact h A
  · intro h
    rw [Measure.le_iff]
    intro A hA
    specialize h A hA
    simp only [toSignedMeasure_apply, hA, ↓reduceIte, ne_eq, measure_ne_top,
      not_false_eq_true, ENNReal.toReal_le_toReal] at h
    exact h

@[simp]
theorem sub_zero {μ : Measure α} : μ - 0 = μ := by
  rw [sub_def]
  apply le_antisymm
  · simp [add_zero]; exact sInf_le (by simp)
  · simp [add_zero]

lemma sub_eq_zero_of_ge_on {μ ν : Measure α} (hs : SetWhereGe μ ν s) : (ν - μ) s = 0 := by
  have : ν.restrict s ≤ μ.restrict s + 0 := by simp [hs.ge_on]
  replace this := Measure.sub_le_of_le_add this
  simp only [sub_zero] at this
  replace this := sub_eq_zero_of_le this
  rw [← restrict_sub_eq_restrict_sub_restrict hs.measurable] at this
  simp only [restrict_eq_zero] at this
  exact this

lemma ofSignedMeasure_setWhereGe (hs : SignedMeasure.SetWhereGe μ ν s) : SetWhereGe μ ν s := by
  constructor
  · exact hs.measurable
  · rw [toSignedMeasure_le_iff, ← sub_nonneg,
        ← toSignedMeasure_restrict_eq_restrict_toSigned hs.measurable,
        ← toSignedMeasure_restrict_eq_restrict_toSigned hs.measurable]
    simp [hs.ge_on]
  · rw [toSignedMeasure_le_iff, ← sub_nonneg,
        ← toSignedMeasure_restrict_eq_restrict_toSigned hs.measurable.compl,
        ← toSignedMeasure_restrict_eq_restrict_toSigned hs.measurable.compl]
    simp [hs.ge_on_compl]

lemma toSignedMeasure_setWhereGe (hs : SetWhereGe μ ν s) : SignedMeasure.SetWhereGe μ ν s := by
  constructor
  · exact hs.measurable
  · rw [toSignedMeasure_restrict_eq_restrict_toSigned hs.measurable,
        toSignedMeasure_restrict_eq_restrict_toSigned hs.measurable]
    exact toSignedMeasure_le_iff.mp hs.ge_on
  · rw [toSignedMeasure_restrict_eq_restrict_toSigned hs.measurable.compl,
        toSignedMeasure_restrict_eq_restrict_toSigned hs.measurable.compl]
    exact toSignedMeasure_le_iff.mp hs.ge_on_compl

@[simp]
theorem setWhereGe_iff_setWhereGeSignedMeasure :
    SetWhereGe μ ν s ↔ SignedMeasure.SetWhereGe μ ν s :=
      ⟨toSignedMeasure_setWhereGe, ofSignedMeasure_setWhereGe⟩

lemma sub_eq_zero_of_ge_on' (hs : SignedMeasure.SetWhereGe μ ν s) : (ν - μ) s = 0 :=
  sub_eq_zero_of_ge_on (ofSignedMeasure_setWhereGe hs)

theorem mutually_singular_measure_sub :
    (μ - ν).MutuallySingular (ν - μ) := by
  obtain ⟨s, hs⟩ := exists_SetWhereGeSignedMeasure ν μ
  exact ⟨s, hs.measurable,
    sub_eq_zero_of_ge_on' hs,
    sub_eq_zero_of_ge_on' inferInstance⟩

lemma toSignedMeasure_restrict_sub (hs : SignedMeasure.SetWhereGe μ ν s) :
    ((μ - ν).restrict s).toSignedMeasure =
      μ.toSignedMeasure.restrict s - ν.toSignedMeasure.restrict s := by
  have hmeas := hs.measurable
  have hle : ν.restrict s ≤ μ.restrict s := by
    rw [toSignedMeasure_le_iff]
    rw [← toSignedMeasure_restrict_eq_restrict_toSigned hmeas,
        ← toSignedMeasure_restrict_eq_restrict_toSigned hmeas]
    exact hs.ge_on
  rw [eq_sub_iff_add_eq, toSignedMeasure_restrict_eq_restrict_toSigned hmeas, ← toSignedMeasure_add]
  have h_restrict := @restrict_sub_eq_restrict_sub_restrict _ _ μ ν s hmeas
  simp only [h_restrict]
  simp only [sub_add_cancel_of_le hle]
  exact (toSignedMeasure_restrict_eq_restrict_toSigned hmeas).symm

theorem sub_toSignedMeasure_eq_toSignedMeasure_sub :
    μ.toSignedMeasure - ν.toSignedMeasure =
      (μ - ν).toSignedMeasure - (ν - μ).toSignedMeasure := by
  obtain ⟨s, hs⟩ := exists_SetWhereGeSignedMeasure ν μ
  let hsc : SignedMeasure.SetWhereGe μ ν sᶜ := inferInstance

  have h₁ := toSignedMeasure_restrict_sub hs
  have h₂ := toSignedMeasure_restrict_sub hsc

  have h₁' := toSignedMeasure_congr <|restrict_eq_zero.mpr <|sub_eq_zero_of_ge_on
    <|ofSignedMeasure_setWhereGe hs
  have h₂' := toSignedMeasure_congr <|restrict_eq_zero.mpr <|sub_eq_zero_of_ge_on
    <|ofSignedMeasure_setWhereGe hsc

  have partition₁ := VectorMeasure.restrict_add_restrict_compl (μ - ν).toSignedMeasure hs.measurable
  have partition₂ := VectorMeasure.restrict_add_restrict_compl (ν - μ).toSignedMeasure hs.measurable

  rw [toSignedMeasure_restrict_eq_restrict_toSigned hs.measurable,
      toSignedMeasure_restrict_eq_restrict_toSigned hs.measurable.compl] at partition₁ partition₂

  rw [h₁', h₂] at partition₁
  rw [h₁, h₂'] at partition₂
  simp only [toSignedMeasure_zero, zero_add] at partition₁ partition₂

  rw [← VectorMeasure.restrict_add_restrict_compl μ.toSignedMeasure hs.measurable,
      ← VectorMeasure.restrict_add_restrict_compl ν.toSignedMeasure hs.measurable,
      ← partition₁, ← partition₂]

  noncomm_ring


 def jordanDecomposition_of_toSignedMeasure_sub
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    JordanDecomposition α where
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
