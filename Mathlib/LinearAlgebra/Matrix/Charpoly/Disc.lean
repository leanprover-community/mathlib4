/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Polynomial.Resultant.Basic


/-!
# The discriminant of a matrix
-/

open Polynomial

namespace Matrix

variable {R n : Type*} [CommRing R] [Nontrivial R] [Fintype n] [DecidableEq n]

/-- The discriminant of a matrix is defined to be the discriminant of its characteristic
polynomial. -/
noncomputable def disc (A : Matrix n n R) : R := A.charpoly.disc

lemma disc_of_card_eq_two (A : Matrix n n R) (hn : Fintype.card n = 2) :
    A.disc = A.trace ^ 2 - 4 * A.det := by
  rw [disc, Polynomial.disc_of_degree_eq_two (by simp; norm_cast)]
  simp [A.charpoly_of_card_eq_two hn]

lemma disc_fin_two (A : Matrix (Fin 2) (Fin 2) R) :
    A.disc = A.trace ^ 2 - 4 * A.det :=
  A.disc_of_card_eq_two <| Fintype.card_fin _

end Matrix
