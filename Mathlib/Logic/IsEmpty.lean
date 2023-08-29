/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Logic.Function.Basic

#align_import logic.is_empty from "leanprover-community/mathlib"@"c4658a649d216f57e99621708b09dcb3dcccbd23"

/-!
# Types that are empty

In this file we define a typeclass `IsEmpty`, which expresses that a type has no elements.

## Main declaration

* `IsEmpty`: a typeclass that expresses that a type is empty.
-/

set_option autoImplicit true


variable {α β γ : Sort*}

/-- `IsEmpty α` expresses that `α` is empty. -/
class IsEmpty (α : Sort*) : Prop where
  protected false : α → False
#align is_empty IsEmpty

instance instIsEmptyEmpty : IsEmpty Empty :=
  ⟨Empty.elim⟩

instance instIsEmptyPEmpty : IsEmpty PEmpty :=
  ⟨PEmpty.elim⟩

instance : IsEmpty False :=
  ⟨id⟩

instance Fin.isEmpty : IsEmpty (Fin 0) :=
  ⟨fun n ↦ Nat.not_lt_zero n.1 n.2⟩

protected theorem Function.isEmpty [IsEmpty β] (f : α → β) : IsEmpty α :=
  ⟨fun x ↦ IsEmpty.false (f x)⟩
#align function.is_empty Function.isEmpty

instance {p : α → Sort*} [h : Nonempty α] [∀ x, IsEmpty (p x)] : IsEmpty (∀ x, p x) :=
  h.elim fun x ↦ Function.isEmpty <| Function.eval x

instance PProd.isEmpty_left [IsEmpty α] : IsEmpty (PProd α β) :=
  Function.isEmpty PProd.fst

instance PProd.isEmpty_right [IsEmpty β] : IsEmpty (PProd α β) :=
  Function.isEmpty PProd.snd

instance Prod.isEmpty_left {α β} [IsEmpty α] : IsEmpty (α × β) :=
  Function.isEmpty Prod.fst

instance Prod.isEmpty_right {α β} [IsEmpty β] : IsEmpty (α × β) :=
  Function.isEmpty Prod.snd

instance [IsEmpty α] [IsEmpty β] : IsEmpty (PSum α β) :=
  ⟨fun x ↦ PSum.rec IsEmpty.false IsEmpty.false x⟩

instance instIsEmptySum {α β} [IsEmpty α] [IsEmpty β] : IsEmpty (Sum α β) :=
  ⟨fun x ↦ Sum.rec IsEmpty.false IsEmpty.false x⟩

/-- subtypes of an empty type are empty -/
instance [IsEmpty α] (p : α → Prop) : IsEmpty (Subtype p) :=
  ⟨fun x ↦ IsEmpty.false x.1⟩

/-- subtypes by an all-false predicate are false. -/
theorem Subtype.isEmpty_of_false {p : α → Prop} (hp : ∀ a, ¬p a) : IsEmpty (Subtype p) :=
  ⟨fun x ↦ hp _ x.2⟩
#align subtype.is_empty_of_false Subtype.isEmpty_of_false

/-- subtypes by false are false. -/
instance Subtype.isEmpty_false : IsEmpty { _a : α // False } :=
  Subtype.isEmpty_of_false fun _ ↦ id

instance Sigma.isEmpty_left {α} [IsEmpty α] {E : α → Type*} : IsEmpty (Sigma E) :=
  Function.isEmpty Sigma.fst

example [h : Nonempty α] [IsEmpty β] : IsEmpty (α → β) := by infer_instance
                                                             -- 🎉 no goals

/-- Eliminate out of a type that `IsEmpty` (without using projection notation). -/
@[elab_as_elim]
def isEmptyElim [IsEmpty α] {p : α → Sort*} (a : α) : p a :=
  (IsEmpty.false a).elim
#align is_empty_elim isEmptyElim

theorem isEmpty_iff : IsEmpty α ↔ α → False :=
  ⟨@IsEmpty.false α, IsEmpty.mk⟩
#align is_empty_iff isEmpty_iff

namespace IsEmpty

open Function

/-- Eliminate out of a type that `IsEmpty` (using projection notation). -/
@[elab_as_elim]
protected def elim {α : Sort u} (_ : IsEmpty α) {p : α → Sort*} (a : α) : p a :=
  isEmptyElim a
#align is_empty.elim IsEmpty.elim

/-- Non-dependent version of `IsEmpty.elim`. Helpful if the elaborator cannot elaborate `h.elim a`
  correctly. -/
protected def elim' {β : Sort*} (h : IsEmpty α) (a : α) : β :=
  (h.false a).elim
#align is_empty.elim' IsEmpty.elim'

protected theorem prop_iff {p : Prop} : IsEmpty p ↔ ¬p :=
  isEmpty_iff
#align is_empty.prop_iff IsEmpty.prop_iff

variable [IsEmpty α]

@[simp]
theorem forall_iff {p : α → Prop} : (∀ a, p a) ↔ True :=
  iff_true_intro isEmptyElim
#align is_empty.forall_iff IsEmpty.forall_iff

@[simp]
theorem exists_iff {p : α → Prop} : (∃ a, p a) ↔ False :=
  iff_false_intro fun ⟨x, _⟩ ↦ IsEmpty.false x
#align is_empty.exists_iff IsEmpty.exists_iff

-- see Note [lower instance priority]
instance (priority := 100) : Subsingleton α :=
  ⟨isEmptyElim⟩

end IsEmpty

@[simp]
theorem not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α :=
  ⟨fun h ↦ ⟨fun x ↦ h ⟨x⟩⟩, fun h1 h2 ↦ h2.elim h1.elim⟩
#align not_nonempty_iff not_nonempty_iff

@[simp]
theorem not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α :=
  not_iff_comm.mp not_nonempty_iff
#align not_is_empty_iff not_isEmpty_iff

@[simp]
theorem isEmpty_Prop {p : Prop} : IsEmpty p ↔ ¬p := by
  simp only [← not_nonempty_iff, nonempty_Prop]
  -- 🎉 no goals
#align is_empty_Prop isEmpty_Prop

@[simp]
theorem isEmpty_pi {π : α → Sort*} : IsEmpty (∀ a, π a) ↔ ∃ a, IsEmpty (π a) := by
  simp only [← not_nonempty_iff, Classical.nonempty_pi, not_forall]
  -- 🎉 no goals
#align is_empty_pi isEmpty_pi

@[simp]
theorem isEmpty_sigma {α} {E : α → Type*} : IsEmpty (Sigma E) ↔ ∀ a, IsEmpty (E a) := by
  simp only [← not_nonempty_iff, nonempty_sigma, not_exists]
  -- 🎉 no goals
#align is_empty_sigma isEmpty_sigma

@[simp]
theorem isEmpty_psigma {α} {E : α → Sort*} : IsEmpty (PSigma E) ↔ ∀ a, IsEmpty (E a) := by
  simp only [← not_nonempty_iff, nonempty_psigma, not_exists]
  -- 🎉 no goals
#align is_empty_psigma isEmpty_psigma

@[simp]
theorem isEmpty_subtype (p : α → Prop) : IsEmpty (Subtype p) ↔ ∀ x, ¬p x := by
  simp only [← not_nonempty_iff, nonempty_subtype, not_exists]
  -- 🎉 no goals
#align is_empty_subtype isEmpty_subtype

@[simp]
theorem isEmpty_prod {α β : Type*} : IsEmpty (α × β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_prod, not_and_or]
  -- 🎉 no goals
#align is_empty_prod isEmpty_prod

@[simp]
theorem isEmpty_pprod : IsEmpty (PProd α β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_pprod, not_and_or]
  -- 🎉 no goals
#align is_empty_pprod isEmpty_pprod

@[simp]
theorem isEmpty_sum {α β} : IsEmpty (Sum α β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_sum, not_or]
  -- 🎉 no goals
#align is_empty_sum isEmpty_sum

@[simp]
theorem isEmpty_psum {α β} : IsEmpty (PSum α β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_psum, not_or]
  -- 🎉 no goals
#align is_empty_psum isEmpty_psum

@[simp]
theorem isEmpty_ulift {α} : IsEmpty (ULift α) ↔ IsEmpty α := by
  simp only [← not_nonempty_iff, nonempty_ulift]
  -- 🎉 no goals
#align is_empty_ulift isEmpty_ulift

@[simp]
theorem isEmpty_plift {α} : IsEmpty (PLift α) ↔ IsEmpty α := by
  simp only [← not_nonempty_iff, nonempty_plift]
  -- 🎉 no goals
#align is_empty_plift isEmpty_plift

theorem wellFounded_of_isEmpty {α} [IsEmpty α] (r : α → α → Prop) : WellFounded r :=
  ⟨isEmptyElim⟩
#align well_founded_of_empty wellFounded_of_isEmpty

variable (α)

theorem isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α :=
  (em <| IsEmpty α).elim Or.inl <| Or.inr ∘ not_isEmpty_iff.mp
#align is_empty_or_nonempty isEmpty_or_nonempty

@[simp]
theorem not_isEmpty_of_nonempty [h : Nonempty α] : ¬IsEmpty α :=
  not_isEmpty_iff.mpr h
#align not_is_empty_of_nonempty not_isEmpty_of_nonempty

variable {α}

theorem Function.extend_of_isEmpty [IsEmpty α] (f : α → β) (g : α → γ) (h : β → γ) :
    Function.extend f g h = h :=
  funext fun _ ↦ (Function.extend_apply' _ _ _) fun ⟨a, _⟩ ↦ isEmptyElim a
#align function.extend_of_empty Function.extend_of_isEmpty
