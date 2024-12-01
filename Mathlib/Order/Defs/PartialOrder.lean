/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Batteries.Tactic.Trans
import Mathlib.Tactic.ExtendDoc
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.TypeStar

/-!
# Orders

Defines classes for preorders and partial orders
and proves some basic lemmas about them.
-/

variable {α : Type*}

section Preorder

/-!
### Definition of `Preorder` and lemmas about types with a `Preorder`
-/

/-- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way. -/
class Preorder (α : Type*) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

variable [Preorder α] {a b c : α}

/-- The relation `≤` on a preorder is reflexive. -/
@[refl, simp] lemma le_refl : ∀ a : α, a ≤ a := Preorder.le_refl

/-- A version of `le_refl` where the argument is implicit -/
lemma le_rfl : a ≤ a := le_refl a

/-- The relation `≤` on a preorder is transitive. -/
@[trans] lemma le_trans : a ≤ b → b ≤ c → a ≤ c := Preorder.le_trans _ _ _

lemma lt_iff_le_not_le : a < b ↔ a ≤ b ∧ ¬b ≤ a := Preorder.lt_iff_le_not_le _ _

lemma lt_of_le_not_le (hab : a ≤ b) (hba : ¬ b ≤ a) : a < b := lt_iff_le_not_le.2 ⟨hab, hba⟩

@[deprecated "No deprecation message was provided." (since := "2024-07-30")]
theorem le_not_le_of_lt : ∀ {a b : α}, a < b → a ≤ b ∧ ¬b ≤ a
  | _a, _b, hab => lt_iff_le_not_le.mp hab

lemma le_of_eq (hab : a = b) : a ≤ b := by rw [hab]
lemma le_of_lt (hab : a < b) : a ≤ b := (lt_iff_le_not_le.1 hab).1
lemma not_le_of_lt (hab : a < b) : ¬ b ≤ a := (lt_iff_le_not_le.1 hab).2
lemma not_le_of_gt (hab : a > b) : ¬a ≤ b := not_le_of_lt hab
lemma not_lt_of_le (hab : a ≤ b) : ¬ b < a := imp_not_comm.1 not_le_of_lt hab
lemma not_lt_of_ge (hab : a ≥ b) : ¬a < b := not_lt_of_le hab

alias LT.lt.not_le := not_le_of_lt
alias LE.le.not_lt := not_lt_of_le

@[trans] lemma ge_trans : a ≥ b → b ≥ c → a ≥ c := fun h₁ h₂ => le_trans h₂ h₁

lemma lt_irrefl (a : α) : ¬a < a := fun h ↦ not_le_of_lt h le_rfl
lemma gt_irrefl (a : α) : ¬a > a := lt_irrefl _

@[trans] lemma lt_of_lt_of_le (hab : a < b) (hbc : b ≤ c) : a < c :=
  lt_of_le_not_le (le_trans (le_of_lt hab) hbc) fun hca ↦ not_le_of_lt hab (le_trans hbc hca)

@[trans] lemma lt_of_le_of_lt (hab : a ≤ b) (hbc : b < c) : a < c :=
  lt_of_le_not_le (le_trans hab (le_of_lt hbc)) fun hca ↦ not_le_of_lt hbc (le_trans hca hab)

@[trans] lemma gt_of_gt_of_ge (h₁ : a > b) (h₂ : b ≥ c) : a > c := lt_of_le_of_lt h₂ h₁
@[trans] lemma gt_of_ge_of_gt (h₁ : a ≥ b) (h₂ : b > c) : a > c := lt_of_lt_of_le h₂ h₁

@[trans] lemma lt_trans (hab : a < b) (hbc : b < c) : a < c := lt_of_lt_of_le hab (le_of_lt hbc)
@[trans] lemma gt_trans : a > b → b > c → a > c := fun h₁ h₂ => lt_trans h₂ h₁

lemma ne_of_lt (h : a < b) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
lemma ne_of_gt (h : b < a) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
lemma lt_asymm (h : a < b) : ¬b < a := fun h1 : b < a => lt_irrefl a (lt_trans h h1)

alias not_lt_of_gt := lt_asymm
alias not_lt_of_lt := lt_asymm

lemma le_of_lt_or_eq (h : a < b ∨ a = b) : a ≤ b := h.elim le_of_lt le_of_eq
lemma le_of_eq_or_lt (h : a = b ∨ a < b) : a ≤ b := h.elim le_of_eq le_of_lt

instance (priority := 900) : @Trans α α α LE.le LE.le LE.le := ⟨le_trans⟩
instance (priority := 900) : @Trans α α α LT.lt LT.lt LT.lt := ⟨lt_trans⟩
instance (priority := 900) : @Trans α α α LT.lt LE.le LT.lt := ⟨lt_of_lt_of_le⟩
instance (priority := 900) : @Trans α α α LE.le LT.lt LT.lt := ⟨lt_of_le_of_lt⟩
instance (priority := 900) : @Trans α α α GE.ge GE.ge GE.ge := ⟨ge_trans⟩
instance (priority := 900) : @Trans α α α GT.gt GT.gt GT.gt := ⟨gt_trans⟩
instance (priority := 900) : @Trans α α α GT.gt GE.ge GT.gt := ⟨gt_of_gt_of_ge⟩
instance (priority := 900) : @Trans α α α GE.ge GT.gt GT.gt := ⟨gt_of_ge_of_gt⟩

/-- `<` is decidable if `≤` is. -/
def decidableLTOfDecidableLE [@DecidableRel α (· ≤ ·)] : @DecidableRel α (· < ·)
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isFalse fun hab' => not_le_of_gt hab' hba
      else isTrue <| lt_of_le_not_le hab hba
    else isFalse fun hab' => hab (le_of_lt hab')

end Preorder

section PartialOrder

/-!
### Definition of `PartialOrder` and lemmas about types with a partial order
-/

/-- A partial order is a reflexive, transitive, antisymmetric relation `≤`. -/
class PartialOrder (α : Type*) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

variable [PartialOrder α] {a b : α}

lemma le_antisymm : a ≤ b → b ≤ a → a = b := PartialOrder.le_antisymm _ _

alias eq_of_le_of_le := le_antisymm

lemma le_antisymm_iff : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun e => ⟨le_of_eq e, le_of_eq e.symm⟩, fun ⟨h1, h2⟩ => le_antisymm h1 h2⟩

lemma lt_of_le_of_ne : a ≤ b → a ≠ b → a < b := fun h₁ h₂ =>
  lt_of_le_not_le h₁ <| mt (le_antisymm h₁) h₂

/-- Equality is decidable if `≤` is. -/
def decidableEqOfDecidableLE [@DecidableRel α (· ≤ ·)] : DecidableEq α
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isTrue (le_antisymm hab hba) else isFalse fun heq => hba (heq ▸ le_refl _)
    else isFalse fun heq => hab (heq ▸ le_refl _)

namespace Decidable

variable [@DecidableRel α (· ≤ ·)]

lemma lt_or_eq_of_le (hab : a ≤ b) : a < b ∨ a = b :=
  if hba : b ≤ a then Or.inr (le_antisymm hab hba) else Or.inl (lt_of_le_not_le hab hba)

lemma eq_or_lt_of_le (hab : a ≤ b) : a = b ∨ a < b :=
  (lt_or_eq_of_le hab).symm

lemma le_iff_lt_or_eq : a ≤ b ↔ a < b ∨ a = b :=
  ⟨lt_or_eq_of_le, le_of_lt_or_eq⟩

end Decidable

attribute [local instance] Classical.propDecidable

lemma lt_or_eq_of_le : a ≤ b → a < b ∨ a = b := Decidable.lt_or_eq_of_le
lemma le_iff_lt_or_eq : a ≤ b ↔ a < b ∨ a = b := Decidable.le_iff_lt_or_eq

end PartialOrder
