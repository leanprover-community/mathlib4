/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Felix Pernegger
-/
module

public import Mathlib.Data.Set.Subsingleton

import Mathlib.Data.Set.Function

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Constant functions

This file defines `Function.IsConst`, the predicate that a function takes the same value
at every pair of inputs, and its restricted variant `Function.IsConstOn`, the predicate that a
function takes the same value at every pair of points of a given set.

Note that a function with empty domain is considered constant.
If a constant function has non-empty codomain, then it can be represented by `Function.const`,
see `isConst_iff_exists_eq_const`.
-/

assert_not_exists CompleteLattice

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

/-- All functions on a subsingleton domain are constant. -/
@[simp]
theorem IsConst.of_subsingleton_domain [Subsingleton α] (f : α → β) : IsConst f :=
  fun _ _ ↦ congrArg f <| Subsingleton.elim _ _

/-- All functions to a subsingleton codomain are constant. -/
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

alias ⟨IsConst.exists_eq_const, _⟩ := isConst_iff_exists_eq_const

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
theorem _root_.Set.subsingleton_range_iff {β : Type*} {f : α → β} :
    (Set.range f).Subsingleton ↔ f.IsConst := by
  simp [Set.Subsingleton, isConst_iff]

@[simp]
theorem _root_.Set.nontrivial_range_iff {β : Type*} {f : α → β} :
    (Set.range f).Nontrivial ↔ ¬f.IsConst := by
  rw [← Set.not_subsingleton_iff, Set.subsingleton_range_iff]

theorem isConst_and_injective_iff (f : α → β) : f.IsConst ∧ f.Injective ↔ Subsingleton α where
  mp := fun ⟨hc, hinj⟩ ↦ ⟨(hinj <| hc · ·)⟩
  mpr _ := ⟨.of_subsingleton_domain f, injective_of_subsingleton f⟩

theorem IsConst.injective_iff {f : α → β} (h : f.IsConst) : f.Injective ↔ Subsingleton α := by
  simp [← f.isConst_and_injective_iff, h]

theorem Injective.isConst_iff {f : α → β} (h : f.Injective) : f.IsConst ↔ Subsingleton α := by
  simp [← f.isConst_and_injective_iff, h]

theorem isConst_and_surjective_iff (f : α → β) :
    f.IsConst ∧ f.Surjective ↔ IsEmpty β ∨ Nonempty α ∧ Subsingleton β where
  mp := fun ⟨hc, hsurj⟩ ↦
    isEmpty_or_nonempty α |>.imp (@hsurj.isEmpty α β) (⟨·, ⟨hsurj.forall₂.mpr hc.eq⟩⟩)
  mpr h := h.elim (fun _ ↦ ⟨.of_subsingleton_codomain f, .of_isEmpty f⟩)
    (fun ⟨_, _⟩ ↦ ⟨.of_subsingleton_codomain f, surjective_to_subsingleton f⟩)

theorem isConst_and_surjective_iff_of_nonempty [Nonempty α] (f : α → β) :
    f.IsConst ∧ f.Surjective ↔ Subsingleton β := by
  simp +contextual [isConst_and_surjective_iff, IsEmpty.subsingleton, ‹Nonempty α›]

theorem IsConst.surjective_iff [Nonempty α] {f : α → β} (h : f.IsConst) :
    f.Surjective ↔ Subsingleton β := by
  simp [← f.isConst_and_surjective_iff_of_nonempty, h]

theorem Surjective.isConst_iff {f : α → β} (h : f.Surjective) : IsConst f ↔ Subsingleton β :=
  ⟨(⟨h.forall₂.mpr ·.eq⟩), fun _ ↦ .of_subsingleton_codomain f⟩

section IsConstOn

variable {α : Type*}

/-- A function is constant on a set `s` if it takes equal values at any two points of `s`.

The intended use is for expressing that a function is constant on `s` when the exact constant
value is not known, not unique or not easy to express. To state the constant value explicitly,
use `Set.EqOn f (Function.const α b) s`. -/
@[expose]
def IsConstOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → f x = f y

theorem isConstOn_iff {f : α → β} {s : Set α} : IsConstOn f s ↔ ∀ x ∈ s, ∀ y ∈ s, f x = f y :=
  ⟨fun h _ hx _ hy ↦ h hx hy, fun h _ hx _ hy ↦ h _ hx _ hy⟩

protected theorem IsConstOn.eq {f : α → β} {s : Set α} (hf : IsConstOn f s) {x y : α} (hx : x ∈ s)
    (hy : y ∈ s) : f x = f y :=
  hf hx hy

theorem isConstOn_iff_isConst_comp_val (f : α → β) (s : Set α) :
    IsConstOn f s ↔ IsConst (f ∘ Subtype.val : s → β) :=
  ⟨fun h ⟨_, hx⟩ ⟨_, hy⟩ ↦ h hx hy, fun h x hx y hy ↦ h ⟨x, hx⟩ ⟨y, hy⟩⟩

@[simp]
theorem isConstOn_univ (f : α → β) : IsConstOn f Set.univ ↔ IsConst f := by
  simp [isConstOn_iff, IsConst]

theorem IsConst.isConstOn {f : α → β} {s : Set α} (hf : IsConst f) : IsConstOn f s :=
  fun x _ y _ ↦ hf x y

theorem IsConstOn.anti {f : α → β} {s t : Set α} (hf : IsConstOn f t) (hst : s ⊆ t) :
    IsConstOn f s :=
  fun _ hx _ hy ↦ hf (hst hx) (hst hy)

theorem IsConstOn.of_eqOn {β : Type*} {f g : α → β} {s : Set α} (hf : IsConstOn f s)
    (h : Set.EqOn f g s) : IsConstOn g s :=
  fun _ hx _ hy ↦ (h hx).symm.trans <| (hf hx hy).trans (h hy)

theorem IsConstOn.congr {β : Type*} {f g : α → β} {s t : Set α} (hf : IsConstOn f s)
    (h : Set.EqOn f g s) (hst : s = t) : IsConstOn g t :=
  hst ▸ hf.of_eqOn h

theorem _root_.Set.EqOn.isConstOn_iff {β : Type*} {f g : α → β} {s : Set α} (h : Set.EqOn f g s) :
    IsConstOn f s ↔ IsConstOn g s :=
  ⟨(·.of_eqOn h), (·.of_eqOn h.symm)⟩

@[simp]
protected theorem IsConstOn.const (b : β) (s : Set α) : IsConstOn (const α b) s :=
  (IsConst.const b).isConstOn

@[simp]
protected theorem IsConstOn.fun_const (b : β) (s : Set α) : IsConstOn (fun _ : α ↦ b) s :=
  (IsConst.const b).isConstOn

/-- Every function is constant on a subsingleton set. -/
theorem IsConstOn.of_subsingleton {s : Set α} (hs : s.Subsingleton) (f : α → β) :
    IsConstOn f s :=
  fun _ hx _ hy ↦ congrArg f <| hs hx hy

@[simp]
theorem isConstOn_empty (f : α → β) : IsConstOn f ∅ :=
  .of_subsingleton Set.subsingleton_empty f

@[simp]
theorem isConstOn_singleton (f : α → β) (a : α) : IsConstOn f {a} :=
  .of_subsingleton (Set.subsingleton_singleton) f

theorem IsConstOn.of_forall_eq {f : α → β} {s : Set α} (b : β) (h : ∀ x ∈ s, f x = b) :
    IsConstOn f s :=
  fun x hx y hy ↦ (h x hx).trans (h y hy).symm

/-- A function `f : α → β` to a non-empty codomain is constant on `s` if and only if there is
`b : β` so that `f a = b` for all `a ∈ s`. -/
theorem isConstOn_iff_exists_forall_eq [Nonempty β] {f : α → β} {s : Set α} :
    IsConstOn f s ↔ ∃ b, ∀ x ∈ s, f x = b := by
  simp [isConstOn_iff_isConst_comp_val, isConst_iff_exists_forall_eq]

/-- A function `f : α → β` is constant on a non-empty set `s` if and only if there is `b : β` so
that `f a = b` for all `a ∈ s`. -/
theorem isConstOn_iff_exists_forall_eq_of_nonempty {f : α → β} {s : Set α} (hs : s.Nonempty) :
    IsConstOn f s ↔ ∃ b, ∀ x ∈ s, f x = b :=
  have := Nonempty.intro (f hs.some)
  isConstOn_iff_exists_forall_eq

/-- A function `α → β` to a non-empty codomain is constant on `s` if and only if there is `b : β`
so that the function agrees with `Function.const α b` on `s`. -/
theorem isConstOn_iff_exists_eqOn_const {β : Type*} [Nonempty β] {f : α → β} {s : Set α} :
    IsConstOn f s ↔ ∃ b, Set.EqOn f (const α b) s :=
  isConstOn_iff_exists_forall_eq

alias ⟨IsConstOn.exists_eqOn_const, _⟩ := isConstOn_iff_exists_eqOn_const

/-- A function `α → β` is constant on a non-empty set `s` if and only if there is `b : β` so that
the function agrees with `Function.const α b` on `s`. -/
theorem isConstOn_iff_exists_eqOn_const_of_nonempty {β : Type*} {f : α → β} {s : Set α}
    (hs : s.Nonempty) : IsConstOn f s ↔ ∃ b, Set.EqOn f (const α b) s :=
  isConstOn_iff_exists_forall_eq_of_nonempty hs

/-- Postcomposition preserves being constant on a set. -/
theorem IsConstOn.comp_left {f : α → β} {s : Set α} (hf : IsConstOn f s) (g : β → γ) :
    IsConstOn (g ∘ f) s :=
  fun _ hx _ hy ↦ congrArg g (hf hx hy)

/-- Precomposing a function constant on `t` with a function mapping `s` to `t` gives a function
constant on `s`. -/
theorem IsConstOn.comp_right {γ : Type*} {g : γ → γ} {t : Set γ} (hg : IsConstOn g t)
    {f : α → γ} {s : Set α} (hf : Set.MapsTo f s t) :
    IsConstOn (g ∘ f) s :=
  fun _ hx _ hy ↦ hg (hf hx) (hf hy)

/-- Precomposing a constant function gives a function constant on any set. -/
theorem IsConst.isConstOn_comp {γ : Sort*} {g : γ → γ} (hg : IsConst g) (f : α → γ)
    (s : Set α) : IsConstOn (g ∘ f) s :=
  (hg.comp_right f).isConstOn

theorem not_isConstOn_of_apply_ne {f : α → β} {s : Set α} {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    (h : f x ≠ f y) : ¬ IsConstOn f s :=
  fun hf ↦ h (hf hx hy)

theorem not_isConstOn_iff_exists_apply_ne {f : α → β} {s : Set α} :
    ¬ IsConstOn f s ↔ ∃ x ∈ s, ∃ y ∈ s, f x ≠ f y := by
  simp [isConstOn_iff]

/-- The identity function is constant on a set if and only if the set is a subsingleton. -/
theorem isConstOn_id_iff {s : Set α} : IsConstOn id s ↔ s.Subsingleton :=
  ⟨fun h _ hx _ hy ↦ h hx hy, (.of_subsingleton · _)⟩

@[simp]
theorem _root_.Set.subsingleton_image_iff {β : Type*} {f : α → β} {s : Set α} :
    (f '' s).Subsingleton ↔ IsConstOn f s := by
  simp [Set.Subsingleton, isConstOn_iff]

@[simp]
theorem _root_.Set.nontrivial_image_iff {β : Type*} {f : α → β} {s : Set α} :
    (f '' s).Nontrivial ↔ ¬ IsConstOn f s := by
  rw [← Set.not_subsingleton_iff, Set.subsingleton_image_iff]

theorem isConstOn_and_injOn_iff {β : Type*} (f : α → β) (s : Set α) :
    IsConstOn f s ∧ Set.InjOn f s ↔ s.Subsingleton where
  mp := fun ⟨hc, hinj⟩ _ hx _ hy ↦ hinj hx hy (hc hx hy)
  mpr hs := ⟨.of_subsingleton hs f, hs.injOn f⟩

theorem IsConstOn.injOn_iff {β : Type*} {f : α → β} {s : Set α} (h : IsConstOn f s) :
    Set.InjOn f s ↔ s.Subsingleton :=
  (and_iff_right h).symm.trans (isConstOn_and_injOn_iff f s)

@[simp]
theorem _root_.Set.InjOn.isConstOn_iff {β : Type*} {f : α → β} {s : Set α} (h : Set.InjOn f s) :
    IsConstOn f s ↔ s.Subsingleton :=
  (and_iff_left h).symm.trans (isConstOn_and_injOn_iff f s)

end IsConstOn

end Function
