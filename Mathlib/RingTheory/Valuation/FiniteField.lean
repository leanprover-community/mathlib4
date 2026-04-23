/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos-Fernández
-/
module -- shake: keep-all

public import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
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

deprecated_module (since := "2026-03-31")

public section

@[deprecated (since := "2026-03-31")] alias Valuation.FiniteField.algebraMap_eq_one :=
  FiniteField.valuation_algebraMap_eq_one

@[deprecated (since := "2026-03-31")] alias Valuation.FiniteField.algebraMap_le_one :=
  FiniteField.valuation_algebraMap_le_one

@[deprecated (since := "2026-03-31")] alias Valuation.FiniteField.instIsTrivialOn :=
  FiniteField.instIsTrivialOn
