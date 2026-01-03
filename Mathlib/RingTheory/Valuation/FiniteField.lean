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

variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

variable {A : Type*} [Ring A] (v : Valuation A Γ₀)

section IsOfFinOrder

@[grind =>]
lemma eq_one_of_isOfFinOrder (a : A) (h : IsOfFinOrder a) : v a = 1 := by
  rw [isOfFinOrder_iff_pow_eq_one] at h
  obtain ⟨n, h0, ha⟩ := h
  have hpow : (v a) ^ n = 1 := by simp_all [← map_pow]
  grind [pow_eq_one_iff, → IsPrimePow.two_le, FiniteField.isPrimePow_card]

end IsOfFinOrder

namespace FiniteField

variable {Fq : Type*} [Field Fq] [Finite Fq] [Algebra Fq A]

@[grind =>]
lemma algebraMap_eq_one (a : Fq) (ha : a ≠ 0) : v (algebraMap Fq A a) = 1 :=
  eq_one_of_isOfFinOrder _ _ (MonoidHom.isOfFinOrder _ (isOfFinOrder_iff_isUnit.mpr (Ne.isUnit ha)))

lemma algebraMap_le_one (a : Fq) : v (algebraMap Fq A a) ≤ 1 := by
  by_cases a = 0 <;> grind [zero_le']

instance (priority := low) : v.IsTrivialOn Fq where eq_one a ha := algebraMap_eq_one v a ha

end FiniteField

end Valuation
