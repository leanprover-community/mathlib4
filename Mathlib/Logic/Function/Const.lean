/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Logic.Function.Basic

/-!
# Constant functions

This file defines `Function.IsConst`, the predicate that a function takes the same value
at every pair of inputs.

Note that a function with empty domain and codomain is considered constant.
If a constant function has non-empty domain, then it can be represented by `Function.const`,
see `isConst_iff_exists_eq_const`.
-/

public section

namespace Function

universe u v w

variable {α : Sort u} {β : Sort v} {γ : Sort w}

/-- A function is constant if it takes equal values at any two inputs.

Note that a function with empty domain and codomain is considered constant.
If a constant function has non-empty domain, then it can be represented by `Function.const`,
see `isConst_iff_exists_eq_const` -/
def IsConst (f : α → β) : Prop :=
  ∀ x y, f x = f y

theorem isConst_iff {f : α → β} :
    IsConst f ↔ ∀ x y, f x = f y :=
  .rfl

theorem IsConst.eq {f : α → β} (hf : IsConst f) (x y : α) :
    f x = f y :=
  hf x y

@[simp]
theorem IsConst.const (b : β) :
    IsConst (const α b) := fun _ _ => rfl

/- All function on a subsingleton domain are constant. -/
theorem IsConst.of_subsingleton_domain [Subsingleton α] (f : α → β) : IsConst f :=
  fun _ _ => congrArg f <| Subsingleton.elim _ _

/- All function on into a subsingleton codomain are constant. -/
theorem IsConst.of_subsingleton_codomain [Subsingleton β] (f : α → β) : IsConst f :=
  fun _ _ => Subsingleton.elim _ _

theorem IsConst.of_forall_eq {f : α → β} (b : β) (h : ∀ x, f x = b) : IsConst f :=
  fun x y => (h x).trans (h y).symm

/-- A function `f : α → β` is constant on a non-empty domain if and only if there is `b : β` so that
`f a = b` for all `a : α`. -/
theorem isConst_iff_exists_eq [Nonempty α] {f : α → β} :
    IsConst f ↔ ∃ b, ∀ x, f x = b where
  mp hf := by
    rcases ‹Nonempty α› with ⟨x₀⟩
    exact ⟨f x₀, (hf · x₀)⟩
  mpr := by
    rintro ⟨b, hb⟩
    exact .of_forall_eq b hb

/-- A function `α → β` is constant on a non-empty domain if and only if there is `b : β` so that
the function can be written as `Function.const α b`. -/
theorem isConst_iff_exists_eq_const [Nonempty α] {f : α → β} :
    IsConst f ↔ ∃ b, f = const α b := by
  rw [isConst_iff_exists_eq]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, funext hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, congrFun hb⟩

theorem IsConst.congr {f g : α → β} (hf : IsConst f) (hfg : ∀ x, f x = g x) : IsConst g :=
  fun x y => (hfg x).symm.trans ((hf x y).trans (hfg y))

theorem isConst_congr {f g : α → β} (hfg : ∀ x, f x = g x) :
    IsConst f ↔ IsConst g :=
  ⟨fun hf => hf.congr hfg, fun hg => hg.congr fun x => (hfg x).symm⟩

/-- Postcomposition preserves being constant. -/
theorem IsConst.comp {f : α → β} (hf : IsConst f) (g : β → γ) :
    IsConst (g ∘ f) :=
  fun x y => congrArg g (hf x y)

/-- Precomposing a constant function gives a constant function. -/
theorem IsConst.comp_left {g : β → γ} (hg : IsConst g) (f : α → β) :
    IsConst (g ∘ f) :=
  fun x y => hg (f x) (f y)

theorem not_isConst_of_apply_ne {f : α → β} {x y : α} (h : f x ≠ f y) :
    ¬ IsConst f := fun hf => h (hf x y)

theorem not_isConst_iff_exists_apply_ne {f : α → β} :
    ¬ IsConst f ↔ ∃ x y, f x ≠ f y := by classical
  constructor
  · intro h
    by_contra h'
    apply h
    intro x y
    by_contra hxy
    exact h' ⟨x, y, hxy⟩
  · rintro ⟨x, y, hxy⟩ hf
    exact hxy (hf x y)

@[simp]
/- The identity function on a type is constant if and only if the type is a singleton. -/
theorem isConst_id_iff : IsConst (id : α → α) ↔ Subsingleton α :=
  ⟨fun h => ⟨fun x y => h x y⟩, fun _ => .of_subsingleton_domain _⟩

end Function
