/-
Copyright (c) 2026 María Inés de Frutos-Fernández, Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Xavier Généreux
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.Finite.Basic
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
# Valuations on an algebra over a finite field.
-/

@[expose] public section

namespace FiniteField

open Valuation

variable {Fq A Γ : Type*} [Field Fq] [Finite Fq] [Ring A] [Algebra Fq A]
  [LinearOrderedCommMonoidWithZero Γ] (v : Valuation A Γ)

@[grind =>]
lemma valuation_algebraMap_eq_one (a : Fq) (ha : a ≠ 0) : v (algebraMap Fq A a) = 1 := by
  have : Fintype Fq := Fintype.ofFinite Fq
  have hpow : (v (algebraMap Fq A a)) ^ (Fintype.card Fq - 1) = 1 := by
    simp [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha]
  grind [pow_eq_one_iff, → IsPrimePow.two_le, FiniteField.isPrimePow_card]

lemma valuation_algebraMap_le_one (v : Valuation A Γ) (a : Fq) :
    v (algebraMap Fq A a) ≤ 1 := by by_cases a = 0 <;> grind [zero_le']

instance : IsTrivialOn Fq v where
  eq_one a ha := FiniteField.valuation_algebraMap_eq_one v a ha

end FiniteField
