/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Logic.Relator

/-!
In this file we prove some basic properties about the typeclass `IsEmpty`.
-/

public section

variable {α β γ : Sort*}

@[simp, push]
theorem not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α :=
  ⟨fun h ↦ ⟨fun x ↦ h ⟨x⟩⟩, fun h1 h2 ↦ h2.elim h1.elim⟩

@[simp, push]
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

theorem Function.Surjective.of_isEmpty [IsEmpty β] (f : α → β) : f.Surjective := IsEmpty.elim ‹_›

theorem Function.surjective_iff_isEmpty [IsEmpty α] (f : α → β) : f.Surjective ↔ IsEmpty β :=
  ⟨Surjective.isEmpty, fun _ ↦ .of_isEmpty f⟩

theorem Function.Bijective.of_isEmpty (f : α → β) [IsEmpty β] : f.Bijective :=
  have := f.isEmpty
  ⟨injective_of_subsingleton f, .of_isEmpty f⟩

theorem Function.not_surjective_of_isEmpty_of_nonempty [IsEmpty α] [Nonempty β] (f : α → β) :
    ¬f.Surjective :=
  (not_isEmpty_of_nonempty β ·.isEmpty)
