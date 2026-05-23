/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Vector measure with density with respect to a vector measure

-/

open Set

namespace MeasureTheory.VectorMeasure

variable {X E F G : Type*} {mX : MeasurableSpace X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : VectorMeasure X F} {f : X → E} {B : E →L[ℝ] F →L[ℝ] G} {s : Set X}

open scoped Classical in
/-- The vector measure with density `f` with respect to a vector measure `μ`, associating to a
measurable set the mass `∫ᵛ x in s, f x ∂[B; μ]`.
If `f` is not integrable, we use the junk value `0`. -/
noncomputable def withDensity (μ : VectorMeasure X F) (f : X → E) (B : E →L[ℝ] F →L[ℝ] G) :
    VectorMeasure X G :=
  if h : μ.Integrable f B then
    { measureOf' s := ∫ᵛ x in s, f x ∂[B; μ]
      empty' := by simp
      not_measurable' s hs := setIntegral_eq_zero_of_not_measurableSet hs
      m_iUnion' s s_meas s_disj := hasSum_setIntegral_iUnion s_meas s_disj h.integrableOn }
  else 0

lemma withDensity_apply (hf : μ.Integrable f B) :
    μ.withDensity f B s = ∫ᵛ x in s, f x ∂[B; μ] := by
  simp [withDensity, hf]

lemma withDensity_apply_univ : μ.withDensity f B univ = ∫ᵛ x, f x ∂[B; μ] := by
  by_cases hf : μ.Integrable f B
  · simp [withDensity_apply hf]
  · simp [withDensity, hf, integral_undef]

@[simp]
lemma withDensity_zero_vectorMeasure : (0 : VectorMeasure X F).withDensity f B = 0 := by
  ext s hs
  simp [withDensity_apply]

@[simp]
lemma withDensity_zero : μ.withDensity 0 B = 0 := by
  ext s hs
  have : μ.Integrable 0 B := by
    simp [VectorMeasure.Integrable]
    apply integrable_zero
  simp [withDensity_apply]


lemma restrict_withDensity (hf : μ.Integrable f B) :
    (μ.withDensity f B).restrict s = (μ.restrict s).withDensity f B := by
  by_cases hs : MeasurableSet s; swap
  · simp [restrict_not_measurable _ hs]


end MeasureTheory.VectorMeasure
