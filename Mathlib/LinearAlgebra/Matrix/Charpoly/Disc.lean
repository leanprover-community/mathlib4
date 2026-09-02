/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Polynomial.Resultant.Basic


/-!
# The discriminant of a matrix
-/

@[expose] public section

open Polynomial

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- The discriminant of a matrix is defined to be the discriminant of its characteristic
polynomial. -/
noncomputable def discr (A : Matrix n n R) : R := A.charpoly.discr

@[simp]
lemma discr_conj (g : GL n R) (m : Matrix n n R) : (g.val * m * g.val⁻¹).discr = m.discr := by
  simp [discr]

@[simp]
lemma discr_conj' (g : GL n R) (m : Matrix n n R) : (g.val⁻¹ * m * g.val).discr = m.discr := by
  simp [discr]

lemma discr_of_card_eq_two (A : Matrix n n R) (hn : Fintype.card n = 2) :
    A.discr = A.trace ^ 2 - 4 * A.det := by
  nontriviality R
  rw [discr, Polynomial.discr_of_degree_eq_two (by simp; norm_cast)]
  simp [A.charpoly_of_card_eq_two hn]

lemma discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) :
    A.discr = A.trace ^ 2 - 4 * A.det :=
  A.discr_of_card_eq_two <| Fintype.card_fin _

end Matrix
