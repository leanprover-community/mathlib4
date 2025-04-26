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
import Mathlib.Tactic.ToAdditive

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

attribute [to_dual self (reorder := 3 4)] LE.le
attribute [to_dual self (reorder := 3 4)] LT.lt
attribute [to_dual self (reorder := 3 4)] GE.ge
attribute [to_dual self (reorder := 3 4)] GT.gt

-- Core lemmas that need to_dual tags

-- @[simp] theorem ge_iff_le [LE α] {x y : α} : x ≥ y ↔ y ≤ x := Iff.rfl
set_option linter.existingAttributeWarning false in
attribute [to_dual self (reorder := 3 4)] ge_iff_le

-- @[simp] theorem gt_iff_lt [LT α] {x y : α} : x > y ↔ y < x := Iff.rfl
set_option linter.existingAttributeWarning false in
attribute [to_dual self (reorder := 3 4)] gt_iff_lt

-- theorem le_of_eq_of_le {a b c : α} [LE α] (h₁ : a = b) (h₂ : b ≤ c) : a ≤ c := h₁ ▸ h₂
attribute [to_dual le_of_eq_of_leOD] le_of_eq_of_le

-- theorem le_of_le_of_eq {a b c : α} [LE α] (h₁ : a ≤ b) (h₂ : b = c) : a ≤ c := h₂ ▸ h₁
attribute [to_dual le_of_le_of_eqOD] le_of_le_of_eq

-- theorem lt_of_eq_of_lt {a b c : α} [LT α] (h₁ : a = b) (h₂ : b < c) : a < c := h₁ ▸ h₂
attribute [to_dual lt_of_eq_of_ltOD] lt_of_eq_of_lt

-- theorem lt_of_lt_of_eq {a b c : α} [LT α] (h₁ : a < b) (h₂ : b = c) : a < c := h₂ ▸ h₁
attribute [to_dual lt_of_lt_of_eqOD] lt_of_lt_of_eq

/-- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way. -/
class Preorder (α : Type*) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

attribute [to_dual self (reorder := 3 5, 6 7)] Preorder.le_trans
attribute [to_dual self (reorder := 3 4)] Preorder.lt_iff_le_not_le

variable [Preorder α] {a b c : α}

/-- The relation `≤` on a preorder is reflexive. -/
@[refl, simp] lemma le_refl : ∀ a : α, a ≤ a := Preorder.le_refl

/-- A version of `le_refl` where the argument is implicit -/
lemma le_rfl : a ≤ a := le_refl a

/-- The relation `≤` on a preorder is transitive. -/
@[to_dual self (attr := trans) (reorder := 3 5, 6 7)]
lemma le_trans : a ≤ b → b ≤ c → a ≤ c := Preorder.le_trans _ _ _

@[to_dual self (reorder := 3 4)]
lemma lt_iff_le_not_le : a < b ↔ a ≤ b ∧ ¬b ≤ a := Preorder.lt_iff_le_not_le _ _

@[to_dual self (reorder := 3 4)]
lemma lt_of_le_not_le (hab : a ≤ b) (hba : ¬ b ≤ a) : a < b := lt_iff_le_not_le.2 ⟨hab, hba⟩

@[to_dual le_of_eqOD]
lemma le_of_eq (hab : a = b) : a ≤ b := by rw [hab]
@[to_dual self (reorder := 3 4)]
lemma le_of_lt (hab : a < b) : a ≤ b := (lt_iff_le_not_le.1 hab).1
@[to_dual self (reorder := 3 4)]
lemma not_le_of_lt (hab : a < b) : ¬ b ≤ a := (lt_iff_le_not_le.1 hab).2
@[to_dual self (reorder := 3 4)]
lemma not_le_of_gt (hab : a > b) : ¬a ≤ b := not_le_of_lt hab
@[to_dual self (reorder := 3 4)]
lemma not_lt_of_le (hab : a ≤ b) : ¬ b < a := imp_not_comm.1 not_le_of_lt hab
@[to_dual self (reorder := 3 4)]
lemma not_lt_of_ge (hab : a ≥ b) : ¬a < b := not_lt_of_le hab

@[to_dual self (reorder := 3 4)]
alias LT.lt.not_le := not_le_of_lt
@[to_dual self (reorder := 3 4)]
alias LE.le.not_lt := not_lt_of_le

@[to_dual self (attr := trans) (reorder := 3 5, 6 7)]
lemma ge_trans : a ≥ b → b ≥ c → a ≥ c := fun h₁ h₂ => le_trans h₂ h₁

lemma lt_irrefl (a : α) : ¬a < a := fun h ↦ not_le_of_lt h le_rfl
lemma gt_irrefl (a : α) : ¬a > a := lt_irrefl _

@[to_dual (attr := trans) (reorder := 3 5, 6 7) lt_of_le_of_lt]
lemma lt_of_lt_of_le (hab : a < b) (hbc : b ≤ c) : a < c :=
  lt_of_le_not_le (le_trans (le_of_lt hab) hbc) fun hca ↦ not_le_of_lt hab (le_trans hbc hca)

@[to_dual (attr := trans) (reorder := 3 5, 6 7) gt_of_ge_of_gt]
lemma gt_of_gt_of_ge (h₁ : a > b) (h₂ : b ≥ c) : a > c := lt_of_le_of_lt h₂ h₁
#print gt_of_ge_of_gt
@[to_dual self (reorder := 3 5, 6 7)]
lemma lt_trans (hab : a < b) (hbc : b < c) : a < c := lt_of_lt_of_le hab (le_of_lt hbc)
@[to_dual self (reorder := 3 5, 6 7)]
lemma gt_trans : a > b → b > c → a > c := fun h₁ h₂ => lt_trans h₂ h₁

@[to_dual ne_of_ltOD]
lemma ne_of_lt (h : a < b) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
@[to_dual ne_of_gtOD]
lemma ne_of_gt (h : b < a) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
@[to_dual self (reorder := 3 4)]
lemma lt_asymm (h : a < b) : ¬b < a := fun h1 : b < a => lt_irrefl a (lt_trans h h1)

@[to_dual self (reorder := 3 4)]
alias not_lt_of_gt := lt_asymm
@[to_dual self (reorder := 3 4)]
alias not_lt_of_lt := lt_asymm

@[to_dual le_of_lt_or_eqOD]
lemma le_of_lt_or_eq (h : a < b ∨ a = b) : a ≤ b := h.elim le_of_lt le_of_eq
@[to_dual le_of_eq_or_ltOD]
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
def decidableLTOfDecidableLE [DecidableLE α] : DecidableLT α
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

attribute [to_dual self (reorder := 5 6)] PartialOrder.le_antisymm

variable [PartialOrder α] {a b : α}

@[to_dual self (reorder := 5 6)]
lemma le_antisymm : a ≤ b → b ≤ a → a = b := PartialOrder.le_antisymm _ _

@[to_dual self (reorder := 5 6)]
alias eq_of_le_of_le := le_antisymm

@[to_dual le_antisymm_iffOD]
lemma le_antisymm_iff : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun e => ⟨le_of_eq e, le_of_eq e.symm⟩, fun ⟨h1, h2⟩ => le_antisymm h1 h2⟩

@[to_dual lt_of_le_of_neOD]
lemma lt_of_le_of_ne : a ≤ b → a ≠ b → a < b := fun h₁ h₂ =>
  lt_of_le_not_le h₁ <| mt (le_antisymm h₁) h₂

/-- Equality is decidable if `≤` is. -/
def decidableEqOfDecidableLE [DecidableLE α] : DecidableEq α
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isTrue (le_antisymm hab hba) else isFalse fun heq => hba (heq ▸ le_refl _)
    else isFalse fun heq => hab (heq ▸ le_refl _)

-- These type classes are redundant, but they are needed for `to_dual`.
/-- Abbreviation for `DecidableRel (· > · : α → α → Prop)`. It is equivalent to `DecidableLT`. -/
@[to_dual existing DecidableLT]
abbrev DecidableGT (α : Type*) [LT α] := DecidableRel (GT.gt : α → α → Prop)
/-- Abbreviation for `DecidableRel (· ≥ · : α → α → Prop)`. It is equivalent to `DecidableLE`. -/
@[to_dual existing DecidableLE]
abbrev DecidableGE (α : Type*) [LE α] := DecidableRel (GE.ge : α → α → Prop)

namespace Decidable

variable [DecidableLE α]

@[to_dual lt_or_eq_of_leOD]
lemma lt_or_eq_of_le (hab : a ≤ b) : a < b ∨ a = b :=
  if hba : b ≤ a then Or.inr (le_antisymm hab hba) else Or.inl (lt_of_le_not_le hab hba)

@[to_dual eq_or_lt_of_leOD]
lemma eq_or_lt_of_le (hab : a ≤ b) : a = b ∨ a < b :=
  (lt_or_eq_of_le hab).symm

@[to_dual le_iff_lt_or_eqOD]
lemma le_iff_lt_or_eq : a ≤ b ↔ a < b ∨ a = b :=
  ⟨lt_or_eq_of_le, le_of_lt_or_eq⟩

end Decidable

@[to_dual lt_or_eq_of_leOD]
lemma lt_or_eq_of_le : a ≤ b → a < b ∨ a = b := open scoped Classical in Decidable.lt_or_eq_of_le
@[to_dual le_iff_lt_or_eqOD]
lemma le_iff_lt_or_eq : a ≤ b ↔ a < b ∨ a = b := open scoped Classical in Decidable.le_iff_lt_or_eq

end PartialOrder
