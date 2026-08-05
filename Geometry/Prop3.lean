/-!
  Euclid's Elements, Book I, Proposition 3
  "Given two unequal straight lines, to cut off from the greater a straight line
  equal to the less."

  Author: Warren Wong
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.Analysis.Convex.Between

open Real

namespace Euclid.BookI.Prop3

/-- **Euclid I.3**: From the greater of two segments, cut off a part
    equal to the lesser.

    Given |AB| > |CD|, there exists E between A and B with |AE| = |CD|. -/
theorem cut_segment
    (A B C D : EuclideanSpace ℝ (Fin 2))
    (hAB : A ≠ B)
    (h : dist C D < dist A B) :
    ∃ E : EuclideanSpace ℝ (Fin 2),
      Wbtw ℝ A E B ∧ dist A E = dist C D := by
  set r := dist C D / dist A B
  set E := AffineMap.lineMap A B r
  refine ⟨E, ?_, ?_⟩
  · -- E is between A and B
    apply wbtw_lineMap_iff.mpr
    right
    refine ⟨?_, ?_⟩
    · exact div_nonneg (dist_nonneg) (dist_nonneg)
    · exact (div_le_one (dist_pos.mpr hAB)).mpr (le_of_lt h)
  · -- |AE| = |CD|
    show dist A ((AffineMap.lineMap A B) (dist C D / dist A B)) = dist C D
    rw [AffineMap.lineMap_apply, dist_eq_norm_vsub', vadd_vsub, norm_smul]
    -- Goal: ‖dist C D / dist A B‖ * ‖B -ᵥ A‖ = dist C D
    -- ‖x‖ = |x| for reals, and |x| = x when x ≥ 0
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg dist_nonneg dist_nonneg)]
    have hBA : ‖B -ᵥ A‖ = dist A B := by
      rw [← dist_eq_norm_vsub', dist_comm]
    rw [hBA]
    -- Goal: (dist C D / dist A B) * dist A B = dist C D
    exact div_mul_cancel₀ (dist C D) (dist_pos.mpr hAB).ne'

end Euclid.BookI.Prop3
