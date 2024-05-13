/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import Mathlib.Init.Function

#align_import logic.relator from "leanprover-community/mathlib"@"c4658a649d216f57e99621708b09dcb3dcccbd23"

/-!
# Relator for functions, pairs, sums, and lists.
-/

namespace Relator
universe u₁ u₂ v₁ v₂

/- TODO(johoelzl):
 * should we introduce relators of datatypes as recursive function or as inductive
predicate? For now we stick to the recursor approach.
 * relation lift for datatypes, Π, Σ, set, and subtype types
 * proof composition and identity laws
 * implement method to derive relators from datatype
-/

section

variable {α : Sort u₁} {β : Sort u₂} {γ : Sort v₁} {δ : Sort v₂}
variable (R : α → β → Prop) (S : γ → δ → Prop)

/-- The binary relations `R : α → β → Prop` and `S : γ → δ → Prop` induce a binary
    relation on functions `LiftFun : (α → γ) → (β → δ) → Prop`. -/
def LiftFun (f : α → γ) (g : β → δ) : Prop :=
  ∀⦃a b⦄, R a b → S (f a) (g b)
#align relator.lift_fun Relator.LiftFun

/-- `(R ⇒ S) f g` means `LiftFun R S f g`. -/
infixr:40 " ⇒ " => LiftFun

end

section

variable {α : Type u₁} {β : Type u₂} (R : α → β → Prop)

/-- A relation is "right total" if every element appears on the right. -/
def RightTotal : Prop := ∀ b, ∃ a, R a b
#align relator.right_total Relator.RightTotal

/-- A relation is "left total" if every element appears on the left. -/
def LeftTotal : Prop := ∀ a, ∃ b, R a b
#align relator.left_total Relator.LeftTotal

/-- A relation is "bi-total" if it is both right total and left total. -/
def BiTotal : Prop := LeftTotal R ∧ RightTotal R
#align relator.bi_total Relator.BiTotal

/-- A relation is "left unique" if every element on the right is paired with at
    most one element on the left. -/
def LeftUnique : Prop := ∀ ⦃a b c⦄, R a c → R b c → a = b
#align relator.left_unique Relator.LeftUnique

/-- A relation is "right unique" if every element on the left is paired with at
    most one element on the right. -/
def RightUnique : Prop := ∀ ⦃a b c⦄, R a b → R a c → b = c
#align relator.right_unique Relator.RightUnique

/-- A relation is "bi-unique" if it is both left unique and right unique. -/
def BiUnique : Prop := LeftUnique R ∧ RightUnique R
#align relator.bi_unique Relator.BiUnique

variable {R}

lemma RightTotal.rel_forall (h : RightTotal R) :
    ((R ⇒ (· → ·)) ⇒ (· → ·)) (fun p => ∀i, p i) (fun q => ∀i, q i) :=
  fun _ _ Hrel H b => Exists.elim (h b) (fun _ Rab => Hrel Rab (H _))
#align relator.right_total.rel_forall Relator.RightTotal.rel_forall

lemma LeftTotal.rel_exists (h : LeftTotal R) :
    ((R ⇒ (· → ·)) ⇒ (· → ·)) (fun p => ∃i, p i) (fun q => ∃i, q i) :=
  fun _ _ Hrel ⟨a, pa⟩ => (h a).imp fun _ Rab => Hrel Rab pa
#align relator.left_total.rel_exists Relator.LeftTotal.rel_exists

lemma BiTotal.rel_forall (h : BiTotal R) :
    ((R ⇒ Iff) ⇒ Iff) (fun p => ∀i, p i) (fun q => ∀i, q i) :=
  fun _ _ Hrel =>
    ⟨fun H b => Exists.elim (h.right b) (fun _ Rab => (Hrel Rab).mp (H _)),
      fun H a => Exists.elim (h.left a) (fun _ Rab => (Hrel Rab).mpr (H _))⟩
#align relator.bi_total.rel_forall Relator.BiTotal.rel_forall

lemma BiTotal.rel_exists (h : BiTotal R) :
    ((R ⇒ Iff) ⇒ Iff) (fun p => ∃i, p i) (fun q => ∃i, q i) :=
  fun _ _ Hrel =>
    ⟨fun ⟨a, pa⟩ => (h.left a).imp fun _ Rab => (Hrel Rab).1 pa,
      fun ⟨b, qb⟩ => (h.right b).imp fun _ Rab => (Hrel Rab).2 qb⟩
#align relator.bi_total.rel_exists Relator.BiTotal.rel_exists

lemma left_unique_of_rel_eq {eq' : β → β → Prop} (he : (R ⇒ (R ⇒ Iff)) Eq eq') : LeftUnique R :=
  fun a b c (ac : R a c) (bc : R b c) => (he ac bc).mpr ((he bc bc).mp rfl)
#align relator.left_unique_of_rel_eq Relator.left_unique_of_rel_eq

end

lemma rel_imp : (Iff ⇒ (Iff ⇒ Iff)) (· → ·) (· → ·) :=
  fun _ _ h _ _ l => imp_congr h l
#align relator.rel_imp Relator.rel_imp

lemma rel_not : (Iff ⇒ Iff) Not Not :=
  fun _ _ h => not_congr h
#align relator.rel_not Relator.rel_not

lemma bi_total_eq {α : Type u₁} : Relator.BiTotal (@Eq α) :=
  { left := fun a => ⟨a, rfl⟩, right := fun a => ⟨a, rfl⟩ }
#align relator.bi_total_eq Relator.bi_total_eq

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variable {r : α → β → Prop} {p : β → γ → Prop} {q : γ → δ → Prop}

lemma LeftUnique.flip (h : LeftUnique r) : RightUnique (flip r) :=
  fun _ _ _ h₁ h₂ => h h₁ h₂
#align relator.left_unique.flip Relator.LeftUnique.flip

lemma rel_and : ((·↔·) ⇒ (·↔·) ⇒ (·↔·)) (·∧·) (·∧·) :=
  fun _ _ h₁ _ _ h₂ => and_congr h₁ h₂
#align relator.rel_and Relator.rel_and

lemma rel_or : ((·↔·) ⇒ (·↔·) ⇒ (·↔·)) (·∨·) (·∨·) :=
  fun _ _ h₁ _ _ h₂ => or_congr h₁ h₂
#align relator.rel_or Relator.rel_or

lemma rel_iff : ((·↔·) ⇒ (·↔·) ⇒ (·↔·)) (·↔·) (·↔·) :=
  fun _ _ h₁ _ _ h₂ => iff_congr h₁ h₂
#align relator.rel_iff Relator.rel_iff

lemma rel_eq {r : α → β → Prop} (hr : BiUnique r) : (r ⇒ r ⇒ (·↔·)) (·=·) (·=·) :=
  fun _ _ h₁ _ _ h₂ => ⟨fun h => hr.right h₁ <| h.symm ▸ h₂, fun h => hr.left h₁ <| h.symm ▸ h₂⟩
#align relator.rel_eq Relator.rel_eq

open Function

variable {α : Type*} {r₁₁ : α → α → Prop} {r₁₂ : α → β → Prop} {r₂₁ : β → α → Prop}
  {r₂₃ : β → γ → Prop} {r₁₃ : α → γ → Prop}

namespace LeftTotal

protected lemma refl (hr : ∀ a : α, r₁₁ a a) :
    LeftTotal r₁₁ :=
  fun a ↦ ⟨a, hr _⟩

protected lemma symm (hr : ∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) :
    LeftTotal r₁₂ → RightTotal r₂₁ :=
  fun h a ↦ (h a).imp (fun _ ↦ hr _ _)

protected lemma trans (hr : ∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c) :
    LeftTotal r₁₂ → LeftTotal r₂₃ → LeftTotal r₁₃ :=
  fun h₁ h₂ a ↦ let ⟨b, hab⟩ := h₁ a; let ⟨c, hbc⟩ := h₂ b; ⟨c, hr _ _ _ hab hbc⟩

end LeftTotal

namespace RightTotal

protected lemma refl (hr : ∀ a : α, r₁₁ a a) : RightTotal r₁₁ :=
  LeftTotal.refl hr

protected lemma symm (hr : ∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) :
    RightTotal r₁₂ → LeftTotal r₂₁ :=
  LeftTotal.symm (fun _ _ ↦ hr _ _)

protected lemma trans (hr : ∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c) :
    RightTotal r₁₂ → RightTotal r₂₃ → RightTotal r₁₃ :=
  swap <| LeftTotal.trans (fun _ _ _ ↦ swap <| hr _ _ _)

end RightTotal

namespace BiTotal

protected lemma refl (hr : ∀ a : α, r₁₁ a a) :
    BiTotal r₁₁ :=
  ⟨LeftTotal.refl hr, RightTotal.refl hr⟩

protected lemma symm (hr : ∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) :
    BiTotal r₁₂ → BiTotal r₂₁ :=
  fun h ↦ ⟨h.2.symm hr, h.1.symm hr⟩

protected lemma trans (hr : ∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c) :
    BiTotal r₁₂ → BiTotal r₂₃ → BiTotal r₁₃ :=
  fun h₁ h₂ ↦ ⟨h₁.1.trans hr h₂.1, h₁.2.trans hr h₂.2⟩

end BiTotal

end Relator
