/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module -- shake: keep-all

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.Tactic.Linter.DeprecatedModule
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.ArithMult.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

deprecated_module "Use `Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula` instead."
  (since := "2026-05-06")
