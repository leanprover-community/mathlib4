/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Init

/-!
# Types that are empty

In this file we define a typeclass `IsEmpty`, which expresses that a type has no elements.

## Main declaration

* `IsEmpty`: a typeclass that expresses that a type is empty.
-/

@[expose] public section

universe u v

variable {α : Sort u} {β : Sort v}

/-- `IsEmpty α` expresses that `α` is empty. -/
class IsEmpty (α : Sort u) : Prop where
  protected false : α → False

instance Empty.instIsEmpty : IsEmpty Empty :=
  ⟨Empty.elim⟩

instance PEmpty.instIsEmpty : IsEmpty PEmpty :=
  ⟨PEmpty.elim⟩

instance : IsEmpty False :=
  ⟨id⟩

instance Fin.isEmpty : IsEmpty (Fin 0) :=
  ⟨fun n ↦ Nat.not_lt_zero n.1 n.2⟩

instance Fin.isEmpty' : IsEmpty (Fin Nat.zero) :=
  Fin.isEmpty

protected theorem Function.isEmpty [IsEmpty β] (f : α → β) : IsEmpty α :=
  ⟨fun x ↦ IsEmpty.false (f x)⟩

theorem Function.Surjective.isEmpty [IsEmpty α] {f : α → β} (hf : f.Surjective) : IsEmpty β :=
  ⟨fun y ↦ let ⟨x, _⟩ := hf y; IsEmpty.false x⟩

-- See note [instance argument order]
instance {p : α → Sort v} [∀ x, IsEmpty (p x)] [h : Nonempty α] : IsEmpty (∀ x, p x) :=
  h.elim fun x ↦ Function.isEmpty fun f ↦ f x

instance PProd.isEmpty_left [IsEmpty α] : IsEmpty (PProd α β) :=
  Function.isEmpty PProd.fst

instance PProd.isEmpty_right [IsEmpty β] : IsEmpty (PProd α β) :=
  Function.isEmpty PProd.snd

instance Prod.isEmpty_left {α β} [IsEmpty α] : IsEmpty (α × β) :=
  Function.isEmpty Prod.fst

instance Prod.isEmpty_right {α β} [IsEmpty β] : IsEmpty (α × β) :=
  Function.isEmpty Prod.snd

instance Quot.instIsEmpty [IsEmpty α] {r : α → α → Prop} : IsEmpty (Quot r) :=
  Function.Surjective.isEmpty Quot.exists_rep

instance Quotient.instIsEmpty [IsEmpty α] {s : Setoid α} : IsEmpty (Quotient s) :=
  Quot.instIsEmpty

instance [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕' β) :=
  ⟨fun x ↦ PSum.rec IsEmpty.false IsEmpty.false x⟩

instance instIsEmptySum {α β} [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕ β) :=
  ⟨fun x ↦ Sum.rec IsEmpty.false IsEmpty.false x⟩

/-- subtypes of an empty type are empty -/
instance [IsEmpty α] (p : α → Prop) : IsEmpty (Subtype p) :=
  ⟨fun x ↦ IsEmpty.false x.1⟩

/-- subtypes by an all-false predicate are false. -/
theorem Subtype.isEmpty_of_false {p : α → Prop} (hp : ∀ a, ¬p a) : IsEmpty (Subtype p) :=
  ⟨fun x ↦ hp _ x.2⟩

/-- subtypes by false are false. -/
instance Subtype.isEmpty_false : IsEmpty { _a : α // False } :=
  Subtype.isEmpty_of_false fun _ ↦ id

instance Sigma.isEmpty_left {α} [IsEmpty α] {E : α → Type v} : IsEmpty (Sigma E) :=
  Function.isEmpty Sigma.fst

example [h : Nonempty α] [IsEmpty β] : IsEmpty (α → β) := by infer_instance

/-- Eliminate out of a type that `IsEmpty` (without using projection notation). -/
@[elab_as_elim]
def isEmptyElim [IsEmpty α] {p : α → Sort v} (a : α) : p a :=
  (IsEmpty.false a).elim

theorem isEmpty_iff : IsEmpty α ↔ α → False :=
  ⟨@IsEmpty.false α, IsEmpty.mk⟩

namespace IsEmpty

open Function

/-- Eliminate out of a type that `IsEmpty` (using projection notation). -/
@[elab_as_elim]
protected def elim (_ : IsEmpty α) {p : α → Sort v} (a : α) : p a :=
  isEmptyElim a

/-- Non-dependent version of `IsEmpty.elim`. Helpful if the elaborator cannot elaborate `h.elim a`
correctly. -/
protected def elim' (h : IsEmpty α) (a : α) : β :=
  (h.false a).elim

protected theorem prop_iff {p : Prop} : IsEmpty p ↔ ¬p :=
  isEmpty_iff

variable [IsEmpty α]

@[simp]
theorem forall_iff {p : α → Prop} : (∀ a, p a) ↔ True :=
  iff_true_intro isEmptyElim

@[simp]
theorem exists_iff {p : α → Prop} : (∃ a, p a) ↔ False :=
  iff_false_intro fun ⟨x, _⟩ ↦ IsEmpty.false x

-- see Note [lower instance priority]
instance (priority := 100) : Subsingleton α :=
  ⟨isEmptyElim⟩

end IsEmpty
