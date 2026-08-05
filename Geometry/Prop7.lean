/-!
  Euclid's Elements, Book I, Proposition 7
  "On the same base and on the same side, two straight lines cannot be
  constructed meeting at a different point while having the same endpoints."

  If two points C and D are equidistant from both A and B,
  then C - D is perpendicular to B - A.

  Author: Warren Wong
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real
open scoped InnerProductSpace

namespace Euclid.BookI.Prop7

/-- Euclid I.7 (algebraic core): If C and D are equidistant from
    both A and B, then the vector C - D is perpendicular to B - A.

    This means C and D lie on a line perpendicular to AB, i.e., they
    are reflections across line AB (or coincide if on the same side). -/
theorem equidistant_implies_perp
    (A B C D : EuclideanSpace ℝ (Fin 2))
    (hAC : dist A C = dist A D)
    (hBC : dist B C = dist B D) :
    @inner ℝ (EuclideanSpace ℝ (Fin 2)) _ (B - A) (C - D) = 0 := by
  -- |AC|^2 = |AD|^2 and |BC|^2 = |BD|^2
  have h1 : dist A C ^ 2 = dist A D ^ 2 := by rw [hAC]
  have h2 : dist B C ^ 2 = dist B D ^ 2 := by rw [hBC]
  -- Convert dist to norm of vsub, then vsub to sub
  rw [dist_eq_norm_vsub, dist_eq_norm_vsub] at h1
  rw [dist_eq_norm_vsub, dist_eq_norm_vsub] at h2
  rw [vsub_eq_sub, vsub_eq_sub] at h1
  rw [vsub_eq_sub, vsub_eq_sub] at h2
  -- h1: ||A - C||^2 = ||A - D||^2
  -- h2: ||B - C||^2 = ||B - D||^2
  -- Expand: ||x - y||^2 = ||x||^2 - 2<x,y> + ||y||^2
  rw [norm_sub_sq_real, norm_sub_sq_real] at h1 h2
  -- h1: ||A||^2 - 2<A,C> + ||C||^2 = ||A||^2 - 2<A,D> + ||D||^2
  -- h2: ||B||^2 - 2<B,C> + ||C||^2 = ||B||^2 - 2<B,D> + ||D||^2
  -- From h1: -2<A,C> + ||C||^2 = -2<A,D> + ||D||^2
  -- From h2: -2<B,C> + ||C||^2 = -2<B,D> + ||D||^2
  -- Subtract: -2<A,C> + 2<B,C> = -2<A,D> + 2<B,D>
  -- 2<B-A, C> = 2<B-A, D>
  -- <B-A, C-D> = 0
  have h3 : @inner ℝ _ _ A C - @inner ℝ _ _ A D = @inner ℝ _ _ B C - @inner ℝ _ _ B D := by linarith
  -- <A, C> - <A, D> = <B, C> - <B, D>
  -- <A, C-D> = <B, C-D>
  -- <B-A, C-D> = <B, C-D> - <A, C-D> = 0
  -- Expand <B-A, C-D> = <B, C-D> - <A, C-D> using inner_sub_left
  simp only [inner_sub_left]
  -- Expand <B, C-D> = <B,C> - <B,D> and <A, C-D> = <A,C> - <A,D>
  simp only [inner_sub_right]
  -- Goal: (<B,C> - <B,D>) - (<A,C> - <A,D>) = 0
  -- h3: <A,C> - <A,D> = <B,C> - <B,D>
  linarith

end Euclid.BookI.Prop7
