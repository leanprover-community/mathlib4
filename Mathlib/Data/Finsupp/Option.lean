/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Module.Defs

/-!
# Declarations about finitely supported functions whose support is an `Option` type p

## Main declarations

* `Finsupp.some`: restrict a finitely supported function on `Option α` to a finitely supported
  function on `α`.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

-/


noncomputable section

open Finset Function

variable {α M N R : Type*}

namespace Finsupp

section Option

/-- Restrict a finitely supported function on `Option α` to a finitely supported function on `α`. -/
def some [Zero M] (f : Option α →₀ M) : α →₀ M :=
  f.comapDomain Option.some fun _ => by simp

@[simp]
theorem some_apply [Zero M] (f : Option α →₀ M) (a : α) : f.some a = f (Option.some a) :=
  rfl

@[simp]
theorem some_zero [Zero M] : (0 : Option α →₀ M).some = 0 := by
  ext
  simp

@[simp]
theorem some_add [AddZeroClass M] (f g : Option α →₀ M) : (f + g).some = f.some + g.some := by
  ext
  simp

@[simp]
theorem some_single_none [Zero M] (m : M) : (single none m : Option α →₀ M).some = 0 := by
  ext
  simp

@[simp]
theorem some_single_some [Zero M] (a : α) (m : M) :
    (single (Option.some a) m : Option α →₀ M).some = single a m := by
  classical
    ext b
    simp [single_apply]

@[simp]
theorem embDomain_some_some [Zero M] (f : α →₀ M) (x) : f.embDomain .some (.some x) = f x := by
  simp [← Function.Embedding.some_apply]

@[simp]
theorem some_update_none [Zero M] (f : Option α →₀ M) (a : M) :
    (f.update none a).some = f.some := by
  ext
  simp [Finsupp.update]

/-- `Finsupp`s from `Option` are equivalent to
pairs of an element and a `Finsupp` on the original type. -/
@[simps]
noncomputable
def optionEquiv [Zero M] : (Option α →₀ M) ≃ M × (α →₀ M) where
  toFun P := (P none, P.some)
  invFun P := (P.2.embDomain .some).update none P.1
  left_inv P := by ext (_ | a) <;> simp [Finsupp.update]
  right_inv P := by ext <;> simp [Finsupp.update]

theorem eq_option_embedding_update_none_iff [Zero M] {n : Option α →₀ M} {m : α →₀ M} {i : M} :
    n = (embDomain Embedding.some m).update none i ↔ n none = i ∧ n.some = m :=
  (optionEquiv.apply_eq_iff_eq_symm_apply (y := (_, _))).symm.trans Prod.ext_iff

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
    | single a m => cases a <;> simp [h_zero]

theorem sum_option_index_smul [Semiring R] [AddCommMonoid M] [Module R M] (f : Option α →₀ R)
    (b : Option α → M) :
    (f.sum fun o r => r • b o) = f none • b none + f.some.sum fun a r => r • b (Option.some a) :=
  f.sum_option_index _ (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

@[simp] lemma some_embDomain_some [Zero M] (f : α →₀ M) : (f.embDomain .some).some = f := by
  ext; rw [some_apply]; exact embDomain_apply _ _ _

@[simp] lemma embDomain_some_none [Zero M] (f : α →₀ M) : f.embDomain .some none = 0 :=
  embDomain_notin_range _ _ _ (by simp)

end Option

end Finsupp
