/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relator

/-!
# Types that are empty

In this file we define a typeclass `IsEmpty`, which expresses that a type has no elements.

## Main declaration

* `IsEmpty`: a typeclass that expresses that a type is empty.
-/

variable {α β γ : Sort*}

/-- `IsEmpty α` expresses that `α` is empty. -/
class IsEmpty (α : Sort*) : Prop where
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
instance {p : α → Sort*} [∀ x, IsEmpty (p x)] [h : Nonempty α] : IsEmpty (∀ x, p x) :=
  h.elim fun x ↦ Function.isEmpty <| Function.eval x

instance PProd.isEmpty_left [IsEmpty α] : IsEmpty (PProd α β) :=
  Function.isEmpty PProd.fst

instance PProd.isEmpty_right [IsEmpty β] : IsEmpty (PProd α β) :=
  Function.isEmpty PProd.snd

instance Prod.isEmpty_left {α β} [IsEmpty α] : IsEmpty (α × β) :=
  Function.isEmpty Prod.fst

instance Prod.isEmpty_right {α β} [IsEmpty β] : IsEmpty (α × β) :=
  Function.isEmpty Prod.snd

instance Quot.instIsEmpty {α : Sort*} [IsEmpty α] {r : α → α → Prop} : IsEmpty (Quot r) :=
  Function.Surjective.isEmpty Quot.exists_rep

instance Quotient.instIsEmpty {α : Sort*} [IsEmpty α] {s : Setoid α} : IsEmpty (Quotient s) :=
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

instance Sigma.isEmpty_left {α} [IsEmpty α] {E : α → Type*} : IsEmpty (Sigma E) :=
  Function.isEmpty Sigma.fst

example [h : Nonempty α] [IsEmpty β] : IsEmpty (α → β) := by infer_instance

/-- Eliminate out of a type that `IsEmpty` (without using projection notation). -/
@[elab_as_elim]
def isEmptyElim [IsEmpty α] {p : α → Sort*} (a : α) : p a :=
  (IsEmpty.false a).elim

theorem isEmpty_iff : IsEmpty α ↔ α → False :=
  ⟨@IsEmpty.false α, IsEmpty.mk⟩

namespace IsEmpty

open Function

universe u in
/-- Eliminate out of a type that `IsEmpty` (using projection notation). -/
@[elab_as_elim]
protected def elim {α : Sort u} (_ : IsEmpty α) {p : α → Sort*} (a : α) : p a :=
  isEmptyElim a

/-- Non-dependent version of `IsEmpty.elim`. Helpful if the elaborator cannot elaborate `h.elim a`
correctly. -/
protected def elim' {β : Sort*} (h : IsEmpty α) (a : α) : β :=
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

@[simp]
theorem not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α :=
  ⟨fun h ↦ ⟨fun x ↦ h ⟨x⟩⟩, fun h1 h2 ↦ h2.elim h1.elim⟩

@[simp]
theorem not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α :=
  not_iff_comm.mp not_nonempty_iff

@[simp]
theorem isEmpty_Prop {p : Prop} : IsEmpty p ↔ ¬p := by
  simp only [← not_nonempty_iff, nonempty_prop]

@[simp]
theorem isEmpty_pi {π : α → Sort*} : IsEmpty (∀ a, π a) ↔ ∃ a, IsEmpty (π a) := by
  simp only [← not_nonempty_iff, Classical.nonempty_pi, not_forall]

theorem isEmpty_fun : IsEmpty (α → β) ↔ Nonempty α ∧ IsEmpty β := by
  rw [isEmpty_pi, ← exists_true_iff_nonempty, ← exists_and_right, true_and]

@[simp]
theorem nonempty_fun : Nonempty (α → β) ↔ IsEmpty α ∨ Nonempty β :=
  not_iff_not.mp <| by rw [not_or, not_nonempty_iff, not_nonempty_iff, isEmpty_fun, not_isEmpty_iff]

@[simp]
theorem isEmpty_sigma {α} {E : α → Type*} : IsEmpty (Sigma E) ↔ ∀ a, IsEmpty (E a) := by
  simp only [← not_nonempty_iff, nonempty_sigma, not_exists]

@[simp]
theorem isEmpty_psigma {α} {E : α → Sort*} : IsEmpty (PSigma E) ↔ ∀ a, IsEmpty (E a) := by
  simp only [← not_nonempty_iff, nonempty_psigma, not_exists]

theorem isEmpty_subtype (p : α → Prop) : IsEmpty (Subtype p) ↔ ∀ x, ¬p x := by
  simp only [← not_nonempty_iff, nonempty_subtype, not_exists]

@[simp]
theorem isEmpty_prod {α β : Type*} : IsEmpty (α × β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_prod, not_and_or]

@[simp]
theorem isEmpty_pprod : IsEmpty (PProd α β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_pprod, not_and_or]

@[simp]
theorem isEmpty_sum {α β} : IsEmpty (α ⊕ β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_sum, not_or]

@[simp]
theorem isEmpty_psum {α β} : IsEmpty (α ⊕' β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_psum, not_or]

@[simp]
theorem isEmpty_ulift {α} : IsEmpty (ULift α) ↔ IsEmpty α := by
  simp only [← not_nonempty_iff, nonempty_ulift]

@[simp]
theorem isEmpty_plift {α} : IsEmpty (PLift α) ↔ IsEmpty α := by
  simp only [← not_nonempty_iff, nonempty_plift]

theorem wellFounded_of_isEmpty {α} [IsEmpty α] (r : α → α → Prop) : WellFounded r :=
  ⟨isEmptyElim⟩

variable (α)

theorem isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α :=
  (em <| IsEmpty α).elim Or.inl <| Or.inr ∘ not_isEmpty_iff.mp

@[simp]
theorem not_isEmpty_of_nonempty [h : Nonempty α] : ¬IsEmpty α :=
  not_isEmpty_iff.mpr h

variable {α}

theorem Function.extend_of_isEmpty [IsEmpty α] (f : α → β) (g : α → γ) (h : β → γ) :
    Function.extend f g h = h :=
  funext fun _ ↦ (Function.extend_apply' _ _ _) fun ⟨a, _⟩ ↦ isEmptyElim a

open Relator

variable {α β : Type*} (R : α → β → Prop)

@[simp]
theorem leftTotal_empty [IsEmpty α] : LeftTotal R := by
  simp only [LeftTotal, IsEmpty.forall_iff]

theorem leftTotal_iff_isEmpty_left [IsEmpty β] : LeftTotal R ↔ IsEmpty α := by
  simp only [LeftTotal, IsEmpty.exists_iff, isEmpty_iff]

@[simp]
theorem rightTotal_empty [IsEmpty β] : RightTotal R := by
  simp only [RightTotal, IsEmpty.forall_iff]

theorem rightTotal_iff_isEmpty_right [IsEmpty α] : RightTotal R ↔ IsEmpty β := by
  simp only [RightTotal, IsEmpty.exists_iff, isEmpty_iff]

@[simp]
theorem biTotal_empty [IsEmpty α] [IsEmpty β] : BiTotal R :=
  ⟨leftTotal_empty R, rightTotal_empty R⟩

theorem biTotal_iff_isEmpty_right [IsEmpty α] : BiTotal R ↔ IsEmpty β := by
  simp only [BiTotal, leftTotal_empty, rightTotal_iff_isEmpty_right, true_and]

theorem biTotal_iff_isEmpty_left [IsEmpty β] : BiTotal R ↔ IsEmpty α := by
  simp only [BiTotal, leftTotal_iff_isEmpty_left, rightTotal_empty, and_true]
