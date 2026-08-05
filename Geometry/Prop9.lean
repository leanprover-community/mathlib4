/-!
  Euclid's Elements, Book I, Proposition 9
  "To bisect a given rectilinear angle."

  Given an angle at a point, construct a line that bisects it
  (divides it into two equal angles).

  We prove: given three points A, B, C (angle at B), there exists
  a point D such that angle ABD = angle DBC.

  Construction: Take a point E on BA and F on BC with |BE| = |BF|.
  Construct equilateral triangle EFG on EF (by I.1). The line BG
  bisects angle ABC.

  We give a simpler existence proof using the angle bisector
  direction: D = B + normalize(BA) + normalize(BC), which lies
  on the angle bisector.

  Author: Warren Wong
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real
open scoped InnerProductSpace

namespace Euclid.BookI.Prop9

/-- Euclid I.9: A given angle can be bisected.

    Given an angle ABC (at vertex B), there exists a point D such
    that the angle ABD equals the angle DBC.

    We construct D along the angle bisector direction:
    D = B + (normalize(B-A) + normalize(C-B))
    The sum of two unit vectors points along the angle bisector. -/
theorem angle_bisector_exists
    (A B C : EuclideanSpace ℝ (Fin 2))
    (hBA : A ≠ B)
    (hBC : C ≠ B)
    (hangle : @inner ℝ (EuclideanSpace ℝ (Fin 2)) _ (A - B) (C - B) ≠
        -(norm (A - B) * norm (C - B))) :
    ∃ D : EuclideanSpace ℝ (Fin 2),
      @inner ℝ (EuclideanSpace ℝ (Fin 2)) _ (A - B) (D - B) /
        (norm (A - B) * norm (D - B)) =
      @inner ℝ (EuclideanSpace ℝ (Fin 2)) _ (C - B) (D - B) /
        (norm (C - B) * norm (D - B)) := by
  -- D = B + (normalize(A-B) + normalize(C-B))
  -- The angle bisector direction is normalize(A-B) + normalize(C-B)
  -- when both vectors are nonzero
  let u := (norm (A - B))⁻¹ • (A - B)
  let v := (norm (C - B))⁻¹ • (C - B)
  let D := B + (u + v)
  refine ⟨D, ?_⟩
  · -- The cosines of the angles are equal.
    -- Goal: <A-B, D-B>/(|A-B|*|D-B|) = <C-B, D-B>/(|C-B|*|D-B|)
    -- where D = B + u + v, so D - B = u + v = normalize(A-B) + normalize(C-B)
    -- Expand <A-B, u+v> = |A-B| + <A-B,C-B>/|C-B|  (using u = (A-B)/|A-B|)
    -- Expand <C-B, u+v> = |C-B| + <C-B,A-B>/|A-B|
    -- Dividing: LHS = 1/|D-B| + <A-B,C-B>/(|A-B|*|C-B|*|D-B|)
    --           RHS = 1/|D-B| + <A-B,C-B>/(|A-B|*|C-B|*|D-B|)
    -- So LHS = RHS.
    rw [show D - B = u + v from by unfold D; abel]
    simp only [u, v, inner_add_right, inner_smul_right,
               real_inner_self_eq_norm_sq, real_inner_comm]
    have hnA : norm (A - B) ≠ 0 := by simpa using sub_ne_zero.mpr hBA
    have hnC : norm (C - B) ≠ 0 := by simpa using sub_ne_zero.mpr hBC
    have hnD : norm (u + v) ≠ 0 := by
      -- u + v = 0 → u = -v → ⟨u,v⟩ = -1 → ⟨A-B, C-B⟩ = -|A-B||C-B| → contradiction
      rw [norm_ne_zero_iff]
      intro h
      -- u + v = 0 → u = -v
      have hu : u = -v := by rw [← sub_eq_zero, sub_neg_eq_add, h]
      -- u, v are unit vectors: ‖u‖ = ‖v‖ = 1
      have hnu : norm u = 1 := norm_smul_inv_norm (sub_ne_zero.mpr hBA)
      have hnv : norm v = 1 := norm_smul_inv_norm (sub_ne_zero.mpr hBC)
      -- ⟨u, v⟩ = -1 ↔ u = -v (when both are unit vectors)
      have huv : @inner ℝ _ _ u v = -1 :=
        (inner_eq_neg_one_iff_of_norm_eq_one hnu hnv).mpr hu
      -- But ⟨u,v⟩ = ⟨A-B, C-B⟩ / (|A-B| * |C-B|)
      have huv' : @inner ℝ _ _ u v =
          @inner ℝ _ _ (A - B) (C - B) / (norm (A - B) * norm (C - B)) := by
        unfold u v
        simp [inner_smul_left, inner_smul_right, div_eq_mul_inv, mul_inv_rev]
        ring
      have : @inner ℝ _ _ (A - B) (C - B) = -(norm (A - B) * norm (C - B)) := by
        -- ⟨u,v⟩ = -1 and ⟨u,v⟩ = ⟨A-B,C-B⟩/(|A-B||C-B|), so:
        have hdiv : @inner ℝ _ _ (A - B) (C - B) / (norm (A - B) * norm (C - B)) = -1 := by
          rw [← huv', huv]
        -- Convert division equation to the goal form
        field_simp [hnA, hnC] at hdiv
        exact hdiv
      exact hangle this
    field_simp [hnA, hnC, hnD]
    ring

end Euclid.BookI.Prop9
