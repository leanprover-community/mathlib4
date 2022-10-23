/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import Mathlib.Logic.Basic

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
    relation on functions `LiftFun : (f : α → γ) (g : β → δ) : Prop'. -/
def LiftFun (f : α → γ) (g : β → δ) : Prop :=
∀⦃a b⦄, R a b → S (f a) (g b)

/-- `(R ⇒ S) f g` means `LiftFun R S f g`. -/
infixr:40 " ⇒ " => LiftFun

end

section

variable {α : Type u₁} {β : Type u₂} (R : α → β → Prop)

/-- A relation is "right total" if every element appears on the right. -/
def RightTotal : Prop := ∀ b, ∃ a, R a b

/-- A relation is "left total" if every element appears on the left. -/
def LeftTotal : Prop := ∀ a, ∃ b, R a b

/-- A relation is "bi-total" if it is both right total and left total. -/
def BiTotal : Prop := LeftTotal R ∧ RightTotal R

/-- A relation is "left unique" if every element on the right is paired with at
    most one element on the left. -/
def LeftUnique : Prop := ∀ ⦃a b c⦄, R a c → R b c → a = b

/-- A relation is "right unique" if every element on the left is paired with at
    most one element on the right. -/
def RightUnique : Prop := ∀ ⦃a b c⦄, R a b → R a c → b = c

/-- A relation is "bi-unique" if it is both left unique and right unique. -/
def BiUnique : Prop := LeftUnique R ∧ RightUnique R

variable {R}

lemma RightTotal.rel_forall (h : RightTotal R) :
  ((R ⇒ (· → ·)) ⇒ (· → ·)) (λ p => ∀i, p i) (λ q => ∀i, q i) :=
λ _ _ Hrel H b => Exists.elim (h b) (λ _ Rab => Hrel Rab (H _))

lemma LeftTotal.rel_exists (h : LeftTotal R) :
  ((R ⇒ (· → ·)) ⇒ (· → ·)) (λ p => ∃i, p i) (λ q => ∃i, q i) :=
λ _ _ Hrel ⟨a, pa⟩ => (h a).imp $ λ _ Rab => Hrel Rab pa

lemma BiTotal.rel_forall (h : BiTotal R) :
  ((R ⇒ Iff) ⇒ Iff) (λ p => ∀i, p i) (λ q => ∀i, q i) :=
λ _ _ Hrel =>
  ⟨λ H b => Exists.elim (h.right b) (λ _ Rab => (Hrel Rab).mp (H _)),
    λ H a => Exists.elim (h.left a) (λ _ Rab => (Hrel Rab).mpr (H _))⟩

lemma BiTotal.rel_exists (h : BiTotal R) :
  ((R ⇒ Iff) ⇒ Iff) (λ p => ∃i, p i) (λ q => ∃i, q i) :=
λ _ _ Hrel =>
  ⟨λ ⟨a, pa⟩ => (h.left a).imp $ λ _ Rab => (Hrel Rab).1 pa,
    λ ⟨b, qb⟩ => (h.right b).imp $ λ _ Rab => (Hrel Rab).2 qb⟩

lemma left_unique_of_rel_eq {eq' : β → β → Prop} (he : (R ⇒ (R ⇒ Iff)) Eq eq') :
  LeftUnique R :=
λ a b c (ac : R a c) (bc : R b c) => (he ac bc).mpr ((he bc bc).mp rfl)

end

lemma rel_imp : (Iff ⇒ (Iff ⇒ Iff)) (· → ·) (· → ·) :=
λ _ _ h _ _ l => imp_congr h l

lemma rel_not : (Iff ⇒ Iff) Not Not :=
λ _ _ h => not_congr h

lemma bi_total_eq {α : Type u₁} : Relator.BiTotal (@Eq α) :=
{ left := λ a => ⟨a, rfl⟩, right := λ a => ⟨a, rfl⟩ }

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}
variable {r : α → β → Prop} {p : β → γ → Prop} {q : γ → δ → Prop}

lemma LeftUnique.flip (h : LeftUnique r) : RightUnique (flip r) :=
λ _ _ _ h₁ h₂ => h h₁ h₂

lemma rel_and : ((·↔·) ⇒ (·↔·) ⇒ (·↔·)) (·∧·) (·∧·) :=
λ _ _ h₁ _ _ h₂ => and_congr h₁ h₂

lemma rel_or : ((·↔·) ⇒ (·↔·) ⇒ (·↔·)) (·∨·) (·∨·) :=
λ _ _ h₁ _ _ h₂ => or_congr h₁ h₂

lemma rel_iff : ((·↔·) ⇒ (·↔·) ⇒ (·↔·)) (·↔·) (·↔·) :=
λ _ _ h₁ _ _ h₂ => iff_congr h₁ h₂

lemma rel_eq {r : α → β → Prop} (hr : BiUnique r) : (r ⇒ r ⇒ (·↔·)) (·=·) (·=·) :=
λ _ _ h₁ _ _ h₂ => ⟨λ h => hr.right h₁ $ h.symm ▸ h₂, λ h => hr.left h₁ $ h.symm ▸ h₂⟩

end Relator
