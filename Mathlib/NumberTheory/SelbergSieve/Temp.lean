/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section

open scoped BigOperators

open Nat ArithmeticFunction Finset

namespace ArithmeticFunction.IsMultiplicative

variable {R : Type*}

end ArithmeticFunction.IsMultiplicative


@[to_additive]
theorem ite_prod_one {R ι : Type*} [CommMonoid R] {p : Prop} [Decidable p] (s : Finset ι)
    (f : ι → R) :
    (if p then (∏ x in s, f x) else 1) = ∏ x in s, if p then f x else 1 := by
  simp only [prod_ite_irrel, prod_const_one]

@[to_additive]
theorem ite_one_prod {R ι : Type*} [CommMonoid R] {p : Prop} [Decidable p] (s : Finset ι)
    (f : ι → R) :
    (if p then 1 else (∏ x in s, f x)) = ∏ x in s, if p then 1 else f x := by
  simp only [prod_ite_irrel, prod_const_one]
