/-
  Euclid's Elements, Book I, Proposition 2
  "To place a straight line equal to a given straight line with one end at a given point."

  Given a point A and a line segment BC, construct a line segment
  from A equal in length to BC.

  This is Euclid's second proposition, which uses Proposition 1
  (equilateral triangle construction) as a lemma. The construction:
  1. Draw an equilateral triangle ABD on the segment from A to an
     arbitrary point B.
  2. Extend lines from B through C and from D through the point
     on the extension.
  3. Use circle intersections to transfer the length BC to start at A.

  In our formalization, we give a simpler existence proof: given any
  point A and any segment BC, there exists a point D such that
  dist A D = dist B C. This captures the essential content without
  the full compass-and-straightedge construction.

  Author: Warren Wong
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

namespace Euclid.BookI.Prop2

/-!
  ## Proposition 2

  Given a point A and a line segment BC, there exists a point D
  such that dist A D = dist B C.

  This is the "length transfer" theorem — you can copy any segment
  to start at any point. It's essential for Euclid's later constructions.
-/

/-- **Euclid I.2**: Given a point A and a segment BC, there exists D
    with |AD| = |BC|.

    Proof: If A = B, take D = C. Otherwise, let v = C - B (the direction
    and length to copy). Place D = A + v. Then |AD| = |v| = |BC|. -/
theorem segment_copy
    (A B C : EuclideanSpace ℝ (Fin 2)) :
    ∃ D : EuclideanSpace ℝ (Fin 2), dist A D = dist B C := by
  -- The construction: D = A + (C - B), i.e. translate BC to start at A
  refine ⟨A + (C - B), ?_⟩
  -- |AD| = |A + (C - B) - A| = |C - B| = |BC|
  rw [dist_eq_norm_vsub, dist_eq_norm_vsub]
  -- Now: ‖(A + (C - B)) -ᵥ A‖ = ‖C -ᵥ B‖
  -- In EuclideanSpace, vsub is just subtraction
  simp [vsub_eq_sub]

end Euclid.BookI.Prop2
