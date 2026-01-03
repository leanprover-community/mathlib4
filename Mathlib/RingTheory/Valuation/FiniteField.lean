/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos-Fernández
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Valuation.Basic

/-!

# Valuations on algebras over finite fields

Basic results on valuations over `Fq`-algebras. -/

@[expose] public section

namespace Valuation

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

namespace FiniteField

variable {Fq A : Type*} [Field Fq] [Fintype Fq] [Ring A] [Algebra Fq A] (v : Valuation A Γ₀)

@[grind =>]
lemma algebraMap_eq_one (a : Fq) (ha : a ≠ 0) : v (algebraMap Fq A a) = 1 := by
  have hpow : (v (algebraMap Fq A a)) ^ (Fintype.card Fq - 1) = 1 := by
    simp [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha]
  grind [pow_eq_one_iff, → IsPrimePow.two_le, FiniteField.isPrimePow_card]

lemma algebraMap_le_one (v : Valuation A Γ₀) (a : Fq) : v (algebraMap Fq A a) ≤ 1 := by
  by_cases a = 0 <;> grind [zero_le']

instance (priority := low) : v.IsTrivialOn Fq where
  eq_one a ha := FiniteField.algebraMap_eq_one v a ha

end FiniteField

end Valuation
