/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Nontriviality.Core
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike


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

lemma discr_of_card_eq_two (A : Matrix n n R) (hn : Fintype.card n = 2) :
    A.discr = A.trace ^ 2 - 4 * A.det := by
  nontriviality R
  rw [discr, Polynomial.discr_of_degree_eq_two (by simp; norm_cast)]
  simp [A.charpoly_of_card_eq_two hn]

lemma discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) :
    A.discr = A.trace ^ 2 - 4 * A.det :=
  A.discr_of_card_eq_two <| Fintype.card_fin _

@[deprecated (since := "2025-10-20")] alias disc := discr
@[deprecated (since := "2025-10-20")] alias disc_of_card_eq_two := discr_of_card_eq_two
@[deprecated (since := "2025-10-20")] alias disc_fin_two := discr_fin_two

end Matrix
