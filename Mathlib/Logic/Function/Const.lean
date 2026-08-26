/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Data.Setoid.Basic

/-!
# Constant functions

This file defines `Function.IsConst`, the predicate that a function takes the same value
at every pair of inputs.

Note that a function with empty domain is considered constant.
If a constant function has non-empty codomain, then it can be represented by `Function.const`,
see `isConst_iff_exists_eq_const`.
-/

public section

namespace Function

variable {α β γ : Sort*}

/-- A function is constant if it takes equal values at any two inputs.

Note that a function with empty domain is considered constant.
If a constant function has non-empty co domain, then it can be represented by `Function.const`,
see `isConst_iff_exists_eq_const`.

The intended use is for expressing that a function is constant when the exact constant value is
not known, not unique or not easy to express. To state the constant value explicitly,
use `Function.const`. -/
@[expose]
def IsConst (f : α → β) : Prop :=
  ∀ x y, f x = f y

theorem isConst_iff {f : α → β} :
    IsConst f ↔ ∀ x y, f x = f y :=
  .rfl

protected theorem IsConst.eq {f : α → β} (hf : IsConst f) (x y : α) :
    f x = f y :=
  hf x y

@[simp]
protected theorem IsConst.const (b : β) :
    IsConst (const α b) := fun _ _ ↦ rfl

/-- All function on a subsingleton domain are constant. -/
@[simp]
theorem IsConst.of_subsingleton_domain [Subsingleton α] (f : α → β) : IsConst f :=
  fun _ _ ↦ congrArg f <| Subsingleton.elim _ _

/-- All function to a subsingleton codomain are constant. -/
@[simp]
theorem IsConst.of_subsingleton_codomain [Subsingleton β] (f : α → β) : IsConst f :=
  fun _ _ ↦ Subsingleton.elim _ _

theorem IsConst.of_forall_eq {f : α → β} (b : β) (h : ∀ x, f x = b) : IsConst f :=
  fun x y ↦ (h x).trans (h y).symm

/-- A function `f : α → β` is constant on a non-empty codomain if and only if there is `b : β` so
that `f a = b` for all `a : α`. -/
theorem isConst_iff_exists_forall_eq [Nonempty β] {f : α → β} :
    IsConst f ↔ ∃ b, ∀ x, f x = b where
  mp hf := (isEmpty_or_nonempty α).elim
    fun _ ↦ by simp
    fun _ ↦ ⟨f (Classical.arbitrary α), fun _ ↦ hf ..⟩
  mpr _ _ := by grind

/-- A function `f : α → β` is constant on a non-empty domain if and only if there is `b : β` so
that `f a = b` for all `a : α`. -/
theorem isConst_iff_exists_forall_eq_of_nonempty_domain [Nonempty α] {f : α → β} :
    IsConst f ↔ ∃ b, ∀ x, f x = b :=
  have := Nonempty.map f inferInstance; isConst_iff_exists_forall_eq

/-- A function `α → β` is constant on a non-empty codomain if and only if there is `b : β` so that
the function can be written as `Function.const α b`. -/
theorem isConst_iff_exists_eq_const [Nonempty β] {f : α → β} :
    IsConst f ↔ ∃ b, f = const α b := by
  simp only [isConst_iff_exists_forall_eq, funext_iff, const_apply]

/-- A function `α → β` is constant on a non-empty domain if and only if there is `b : β` so that
the function can be written as `Function.const α b`. -/
theorem isConst_iff_exists_eq_const_of_nonempty_domain [Nonempty α] {f : α → β} :
    IsConst f ↔ ∃ b, f = const α b :=
  have := Nonempty.map f inferInstance; isConst_iff_exists_eq_const

/-- Postcomposition preserves being constant. -/
theorem IsConst.comp_left {f : α → β} (hf : IsConst f) (g : β → γ) :
    IsConst (g ∘ f) :=
  fun x y ↦ congrArg g (hf x y)

/-- Precomposing a constant function gives a constant function. -/
theorem IsConst.comp_right {g : β → γ} (hg : IsConst g) (f : α → β) :
    IsConst (g ∘ f) :=
  fun x y ↦ hg (f x) (f y)

theorem not_isConst_of_apply_ne {f : α → β} {x y : α} (h : f x ≠ f y) :
    ¬ IsConst f := fun hf ↦ h (hf x y)

theorem not_isConst_iff_exists_apply_ne {f : α → β} :
    ¬ IsConst f ↔ ∃ x y, f x ≠ f y := by
  simp [isConst_iff]

/-- The identity function on a type is constant if and only if the type is a subsingleton. -/
@[simp]
theorem isConst_id_iff : IsConst (id : α → α) ↔ Subsingleton α :=
  ⟨(⟨·⟩), fun _ ↦ .of_subsingleton_domain _⟩

@[simp]
theorem _root_.Setoid.ker_eq_top {α β : Type*} {f : α → β} :
    Setoid.ker f = ⊤ ↔ IsConst f :=
  Setoid.ker f |>.eq_top_iff

end Function
