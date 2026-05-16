/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Integral

/-!
# Vector measure with density with respect to a vector measure

-/

namespace MeasureTheory.VectorMeasure


variable {X E F G : Type*} {mX : MeasurableSpace X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

open scoped Classical in
noncomputable def withDensity (μ : VectorMeasure X F) (f : X → E) (B : E →L[ℝ] F →L[ℝ] G) :
    VectorMeasure X G :=
  if μ.Integrable f B then
    { measureOf' s := ∫ᵛ x in s, f x ∂[B; μ]
      empty' := by simp
      not_measurable' s hs := by simp [restrict_not_measurable _ hs]
      m_iUnion' s s_meas s_disj := by
         }
  else 0

end MeasureTheory.VectorMeasure
