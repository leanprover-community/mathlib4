/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison, Bolton Bailey
-/
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Module.Defs

/-!
# Operations on `Finsupp`s with an `Option` domain

Similar to how `Finsupp.cons` and `Finsupp.tail` construct
an object of type `Fin (n + 1) →₀ M` from a map `Fin n →₀ M` and vice versa,
we define `Finsupp.optionElim'` and `Finsupp.some`
to construct `Option α →₀ M` from a map α →₀ M, and vice versa.

As functions, these behave as `Option.elim'`, and as an application of `some` hence the names.

We prove a variety of API lemmas, see `Data/Finsupp/Fin.lean` for comparison.

## Main declarations

* `Finsupp.some`: restrict a finitely supported function on `Option α` to a finitely supported
  function on `α`.
* `Finsupp.optionElim'`: extend a finitely supported function on `α`
  to a finitely supported function on `Option α`, provided a default value for `none`.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

-/

noncomputable section

open Finset Function

variable {α M N R S : Type*}

namespace Finsupp

section Option

section Zero

variable [Zero M]

/-- Restrict a finitely supported function on `Option α` to a finitely supported function on `α`. -/
def some (f : Option α →₀ M) : α →₀ M :=
  f.comapDomain Option.some fun _ => by simp

@[simp]
theorem some_apply (f : Option α →₀ M) (a : α) : f.some a = f (Option.some a) :=
  rfl

@[simp]
theorem some_zero : (0 : Option α →₀ M).some = 0 := by
  ext
  simp

@[simp]
theorem some_single_none (m : M) : (single none m : Option α →₀ M).some = 0 := by
  ext
  simp

@[simp]
theorem some_single_some (a : α) (m : M) :
    (single (Option.some a) m : Option α →₀ M).some = single a m := by
  classical
    ext b
    simp [single_apply]

@[simp]
lemma some_update_none (f : Option α →₀ M) (y : M) : (update f none y).some = f.some := by
  ext
  simp

@[simp]
lemma some_update_some (f : Option α →₀ M) (x : α) (y : M) :
    (f.update (Option.some x) y).some = (f.some.update x y) := by
  ext a
  by_cases h : a = x
  · simp [h]
  · simp [h]

/--
Extend a finitely supported function on `α` to a finitely supported function on `Option α`,
provided a default value for `none`.
-/
def optionElim' (y : M) (f : α →₀ M) : Option α →₀ M :=
  (Finsupp.embDomain Function.Embedding.some f).update none y

lemma optionElim'_apply_none (y : M) (f : α →₀ M) : f.optionElim' y none = y := by
  simp [optionElim']

lemma optionElim'_apply_some (y : M) (f : α →₀ M) (x : α) :
    f.optionElim' y (Option.some x) = f x := by
  have : Option.some x = Embedding.some x := by rfl
  simp only [optionElim', ne_eq, reduceCtorEq, not_false_eq_true, update_apply_of_ne]
  rw [this, embDomain_apply]

@[simp]
lemma optionElim'_apply (y : M) (f : α →₀ M) (a : Option α) :
    f.optionElim' y a = a.elim y f := by
  cases a with
  | none => exact optionElim'_apply_none y f
  | some x => simp only [optionElim'_apply_some, Option.elim_some]

lemma optionElim'_eq_elim' (y : M) (f : α →₀ M) (a : Option α) :
    optionElim' y f a = Option.elim' y f a := by
  rw [optionElim'_apply, Option.elim'_eq_elim]

@[simp]
lemma some_optionElim' (y : M) (f : α →₀ M) : (f.optionElim' y).some = f := by
  ext
  simp

@[simp]
lemma optionElim'_some (f : Option α →₀ M) : f.some.optionElim' (f none) = f := by
  ext a
  cases a
  · rw [optionElim'_apply_none]
  · simp

@[simp]
theorem optionElim'_zero (y : M) : (0 : α →₀ M).optionElim' y = single none y := by
  ext a
  cases a
  · simp
  · simp

theorem optionElim'_ne_zero_of_left (y : M) (f : α →₀ M) (h : y ≠ 0) : f.optionElim' y ≠ 0 := by
  contrapose! h with c
  have : f.optionElim' y none = (0 : Option α →₀ M) none := by
    rw [c]
  simp only [optionElim'_apply, Option.elim_none, coe_zero, Pi.zero_apply] at this
  exact this

theorem optionElim'_ne_zero_of_right (y : M) (f : α →₀ M) (h : f ≠ 0) : f.optionElim' y ≠ 0 := by
  contrapose! h with c
  ext a
  have : f.optionElim' y (Option.some a) = (0 : Option α →₀ M) (Option.some a) := by
    rw [c]
  simp only [optionElim'_apply, Option.elim_some, coe_zero, Pi.zero_apply] at this
  exact this

theorem optionElim'_ne_zero_iff (y : M) (f : α →₀ M) :
    f.optionElim' y ≠ 0 ↔ f ≠ 0 ∨ y ≠ 0 := by
  constructor
  · intro h
    contrapose! h
    rcases h with ⟨rfl, rfl⟩
    rw [optionElim'_zero, single_zero]
  · intro h
    cases h with
    | inl h => exact optionElim'_ne_zero_of_right y f h
    | inr h => exact optionElim'_ne_zero_of_left y f h

end Zero

@[simp]
theorem some_add [AddZeroClass M] (f g : Option α →₀ M) : (f + g).some = f.some + g.some := by
  ext
  simp

@[to_additive]
theorem prod_option_index [AddZeroClass M] [CommMonoid N] (f : Option α →₀ M)
    (b : Option α → M → N) (h_zero : ∀ o, b o 0 = 1)
    (h_add : ∀ o m₁ m₂, b o (m₁ + m₂) = b o m₁ * b o m₂) :
    f.prod b = b none (f none) * f.some.prod fun a => b (Option.some a) := by
  classical
    induction f using induction_linear with
    | zero => simp [some_zero, h_zero]
    | add f₁ f₂ h₁ h₂ =>
      rw [Finsupp.prod_add_index, h₁, h₂, some_add, Finsupp.prod_add_index]
      · simp only [h_add, Pi.add_apply, Finsupp.coe_add]
        rw [mul_mul_mul_comm]
      all_goals simp [h_zero, h_add]
    | single a m => cases a <;> simp [h_zero, h_add]

theorem sum_option_index_smul [Semiring R] [AddCommMonoid M] [Module R M] (f : Option α →₀ R)
    (b : Option α → M) :
    (f.sum fun o r => r • b o) = f none • b none + f.some.sum fun a r => r • b (Option.some a) :=
  f.sum_option_index _ (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

end Option

end Finsupp
