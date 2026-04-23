/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
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
# Quadratic forms are line (Gateaux) differentiable

In this file we prove that a quadratic form is line differentiable,
with the line derivative given by the polar bilinear form.
Note that this statement does not need topology on the domain.
In particular, it applies to discontinuous quadratic forms on infinite-dimensional spaces.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace QuadraticMap

theorem hasLineDerivAt (f : QuadraticMap 𝕜 E F) (a b : E) :
    HasLineDerivAt 𝕜 f (polar f a b) a b := by
  simpa [HasLineDerivAt, QuadraticMap.map_add, f.map_smul] using
    ((hasDerivAt_const (0 : 𝕜) (f a)).add <|
      ((hasDerivAt_id 0).mul (hasDerivAt_id 0)).smul (hasDerivAt_const 0 (f b))).add
      ((hasDerivAt_id 0).smul (hasDerivAt_const 0 (polar f a b)))

theorem lineDifferentiableAt (f : QuadraticMap 𝕜 E F) (a b : E) : LineDifferentiableAt 𝕜 f a b :=
  (f.hasLineDerivAt a b).lineDifferentiableAt

@[simp]
protected theorem lineDeriv (f : QuadraticMap 𝕜 E F) : lineDeriv 𝕜 f = polar f := by
  ext a b
  exact (f.hasLineDerivAt a b).lineDeriv

end QuadraticMap
