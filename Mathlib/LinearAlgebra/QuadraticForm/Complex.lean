/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.CharP.Invertible
import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

deprecated_module (since := "2026-01-19")

public section

namespace QuadraticForm
open QuadraticMap

@[deprecated "Use QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed"
  (since := "2026-01-19")]
theorem equivalent_sum_squares {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (Q : QuadraticForm ℂ M) (hQ : (associated (R := ℂ) Q).SeparatingLeft) :
    Equivalent Q (weightedSumSquares ℂ (1 : Fin (Module.finrank ℂ M) → ℂ)) :=
  equivalent_weightedSumSquares_of_isAlgClosed Q hQ

@[deprecated "Use QuadraticForm.equivalent_of_isAlgClosed" (since := "2026-01-19")]
theorem complex_equivalent {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (Q₁ Q₂ : QuadraticForm ℂ M)
    (hQ₁ : (associated Q₁).SeparatingLeft)
    (hQ₂ : (associated Q₂).SeparatingLeft) : Equivalent Q₁ Q₂ :=
  equivalent_of_isAlgClosed Q₁ Q₂ hQ₁ hQ₂

end QuadraticForm
