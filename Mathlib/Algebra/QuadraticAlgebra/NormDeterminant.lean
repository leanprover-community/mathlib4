/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike

/-!
# Quadratic Algebra

We prove that the expression for the norm of an element in a quadratic algebra comes from looking at
the endomorphism defined by left multiplication by that element and taking its determinant.
-/

public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R}

/-- The norm of an element in a quadratic algebra is the determinant of the endomorphism defined by
left multiplication by that element. -/
@[simp]
theorem det_toLinearMap_eq_norm (z : QuadraticAlgebra R a b) :
    (DistribSMul.toLinearMap R (QuadraticAlgebra R a b) z).det = z.norm := by
  rw [← LinearMap.det_toMatrix <| basis ..]
  have : !![z.re, a * z.im; z.im, z.re + b * z.im].det = z.norm := by
    simp [norm]
    ring
  convert this
  apply LinearEquiv.eq_symm_apply _ |>.mp
  ext1 w
  apply basis .. |>.repr.injective
  apply DFunLike.coe_injective'
  rw [LinearMap.toMatrix_symm, Matrix.repr_toLin]
  ext i
  fin_cases i
    <;> simp
    <;> ring

end QuadraticAlgebra
