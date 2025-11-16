/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Batteries.Tactic.Alias
import Batteries.Tactic.Trans
import Mathlib.Tactic.ExtendDoc
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ToDual

/-!
# Orders

Defines classes for preorders and partial orders
and proves some basic lemmas about them.

We also define covering relations on a preorder.
We say that `b` *covers* `a` if `a < b` and there is no element in between.
We say that `b` *weakly covers* `a` if `a ≤ b` and there is no element between `a` and `b`.
In a partial order this is equivalent to `a ⋖ b ∨ a = b`,
in a preorder this is equivalent to `a ⋖ b ∨ (a ≤ b ∧ b ≤ a)`

## Notation

* `a ⋖ b` means that `b` covers `a`.
* `a ⩿ b` means that `b` weakly covers `a`.
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
  lt_iff_le_not_ge : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

attribute [to_dual self (reorder := 3 5, 6 7)] Preorder.le_trans
attribute [to_dual self (reorder := 3 4)] Preorder.lt_iff_le_not_ge

instance [Preorder α] : Std.LawfulOrderLT α where
  lt_iff := Preorder.lt_iff_le_not_ge

instance [Preorder α] : Std.IsPreorder α where
  le_refl := Preorder.le_refl
  le_trans := Preorder.le_trans

@[deprecated (since := "2025-05-11")] alias Preorder.lt_iff_le_not_le := Preorder.lt_iff_le_not_ge

variable [Preorder α] {a b c : α}

/-- The relation `≤` on a preorder is reflexive. -/
@[refl, simp] lemma le_refl : ∀ a : α, a ≤ a := Preorder.le_refl

/-- A version of `le_refl` where the argument is implicit -/
lemma le_rfl : a ≤ a := le_refl a

/-- The relation `≤` on a preorder is transitive. -/
@[to_dual ge_trans] lemma le_trans : a ≤ b → b ≤ c → a ≤ c := Preorder.le_trans _ _ _

@[to_dual self (reorder := 3 4)]
lemma lt_iff_le_not_ge : a < b ↔ a ≤ b ∧ ¬b ≤ a := Preorder.lt_iff_le_not_ge _ _

@[deprecated (since := "2025-05-11")] alias lt_iff_le_not_le := lt_iff_le_not_ge

@[to_dual self (reorder := 3 4)]
lemma lt_of_le_not_ge (hab : a ≤ b) (hba : ¬ b ≤ a) : a < b := lt_iff_le_not_ge.2 ⟨hab, hba⟩

@[deprecated (since := "2025-05-11")] alias lt_of_le_not_le := lt_of_le_not_ge

@[to_dual ge_of_eq]
lemma le_of_eq (hab : a = b) : a ≤ b := by rw [hab]
@[to_dual self (reorder := 3 4)]
lemma le_of_lt (hab : a < b) : a ≤ b := (lt_iff_le_not_ge.1 hab).1
@[to_dual self (reorder := 3 4)]
lemma not_le_of_gt (hab : a < b) : ¬ b ≤ a := (lt_iff_le_not_ge.1 hab).2
@[to_dual self (reorder := 3 4)]
lemma not_lt_of_ge (hab : a ≤ b) : ¬ b < a := imp_not_comm.1 not_le_of_gt hab

@[deprecated (since := "2025-05-11")] alias not_le_of_lt := not_le_of_gt
@[deprecated (since := "2025-05-11")] alias not_lt_of_le := not_lt_of_ge

@[to_dual self (reorder := 3 4)] alias LT.lt.not_ge := not_le_of_gt
@[to_dual self (reorder := 3 4)] alias LE.le.not_gt := not_lt_of_ge

@[deprecated (since := "2025-06-07")] alias LT.lt.not_le := LT.lt.not_ge
@[deprecated (since := "2025-06-07")] alias LE.le.not_lt := LE.le.not_gt

@[to_dual self] lemma lt_irrefl (a : α) : ¬a < a := fun h ↦ not_le_of_gt h le_rfl

@[deprecated (since := "2025-06-07")] alias gt_irrefl := lt_irrefl

@[to_dual lt_of_lt_of_le']
lemma lt_of_lt_of_le (hab : a < b) (hbc : b ≤ c) : a < c :=
  lt_of_le_not_ge (le_trans (le_of_lt hab) hbc) fun hca ↦ not_le_of_gt hab (le_trans hbc hca)

@[to_dual lt_of_le_of_lt']
lemma lt_of_le_of_lt (hab : a ≤ b) (hbc : b < c) : a < c :=
  lt_of_le_not_ge (le_trans hab (le_of_lt hbc)) fun hca ↦ not_le_of_gt hbc (le_trans hca hab)

@[deprecated (since := "2025-06-07")] alias gt_of_gt_of_ge := lt_of_lt_of_le'
@[deprecated (since := "2025-06-07")] alias gt_of_ge_of_gt := lt_of_le_of_lt'

@[to_dual gt_trans]
lemma lt_trans : a < b → b < c → a < c := fun h₁ h₂ => lt_of_lt_of_le h₁ (le_of_lt h₂)

@[to_dual ne_of_gt]
lemma ne_of_lt (h : a < b) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
@[to_dual self (reorder := 3 4)]
lemma lt_asymm (h : a < b) : ¬b < a := fun h1 : b < a => lt_irrefl a (lt_trans h h1)

@[to_dual self (reorder := 3 4)]
alias not_lt_of_gt := lt_asymm
@[deprecated (since := "2025-05-11")] alias not_lt_of_lt := not_lt_of_gt

@[to_dual le_of_lt_or_eq']
lemma le_of_lt_or_eq (h : a < b ∨ a = b) : a ≤ b := h.elim le_of_lt le_of_eq
@[to_dual le_of_eq_or_lt']
lemma le_of_eq_or_lt (h : a = b ∨ a < b) : a ≤ b := h.elim le_of_eq le_of_lt

instance instTransLE : @Trans α α α LE.le LE.le LE.le := ⟨le_trans⟩
instance instTransLT : @Trans α α α LT.lt LT.lt LT.lt := ⟨lt_trans⟩
instance instTransLTLE : @Trans α α α LT.lt LE.le LT.lt := ⟨lt_of_lt_of_le⟩
instance instTransLELT : @Trans α α α LE.le LT.lt LT.lt := ⟨lt_of_le_of_lt⟩
-- we have to express the following 4 instances in terms of `≥` instead of flipping the arguments
-- to `≤`, because otherwise `calc` gets confused.
@[to_dual existing instTransLE]
instance instTransGE : @Trans α α α GE.ge GE.ge GE.ge := ⟨ge_trans⟩
@[to_dual existing instTransLT]
instance instTransGT : @Trans α α α GT.gt GT.gt GT.gt := ⟨gt_trans⟩
@[to_dual existing instTransLTLE]
instance instTransGTGE : @Trans α α α GT.gt GE.ge GT.gt := ⟨lt_of_lt_of_le'⟩
@[to_dual existing instTransLELT]
instance instTransGEGT : @Trans α α α GE.ge GT.gt GT.gt := ⟨lt_of_le_of_lt'⟩

/-- `<` is decidable if `≤` is. -/
@[to_dual decidableGTOfDecidableGE /-- `<` is decidable if `≤` is. -/]
def decidableLTOfDecidableLE [DecidableLE α] : DecidableLT α :=
  fun _ _ => decidable_of_iff _ lt_iff_le_not_ge.symm

/-- `WCovBy a b` means that `a = b` or `b` covers `a`.
This means that `a ≤ b` and there is no element in between. This is denoted `a ⩿ b`.
-/
@[to_dual self (reorder := 3 4)]
def WCovBy (a b : α) : Prop :=
  a ≤ b ∧ ∀ ⦃c⦄, a < c → ¬c < b

@[inherit_doc]
infixl:50 " ⩿ " => WCovBy

/-- `CovBy a b` means that `b` covers `a`. This means that `a < b` and there is no element in
between. This is denoted `a ⋖ b`. -/
@[to_dual self (reorder := 3 4)]
def CovBy {α : Type*} [LT α] (a b : α) : Prop :=
  a < b ∧ ∀ ⦃c⦄, a < c → ¬c < b

@[inherit_doc]
infixl:50 " ⋖ " => CovBy

end Preorder

section PartialOrder

/-!
### Definition of `PartialOrder` and lemmas about types with a partial order
-/

/-- A partial order is a reflexive, transitive, antisymmetric relation `≤`. -/
class PartialOrder (α : Type*) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

attribute [to_dual self (reorder := 5 6)] PartialOrder.le_antisymm

instance [PartialOrder α] : Std.IsPartialOrder α where
  le_antisymm := PartialOrder.le_antisymm

variable [PartialOrder α] {a b : α}

@[to_dual ge_antisymm]
lemma le_antisymm : a ≤ b → b ≤ a → a = b := PartialOrder.le_antisymm _ _

@[to_dual eq_of_ge_of_le]
alias eq_of_le_of_ge := le_antisymm

@[deprecated (since := "2025-06-07")] alias eq_of_le_of_le := eq_of_le_of_ge

@[to_dual ge_antisymm_iff]
lemma le_antisymm_iff : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun e => ⟨le_of_eq e, le_of_eq e.symm⟩, fun ⟨h1, h2⟩ => le_antisymm h1 h2⟩

@[to_dual lt_of_le_of_ne']
lemma lt_of_le_of_ne : a ≤ b → a ≠ b → a < b := fun h₁ h₂ =>
  lt_of_le_not_ge h₁ <| mt (le_antisymm h₁) h₂

/-- Equality is decidable if `≤` is. -/
@[to_dual decidableEqofDecidableGE /-- Equality is decidable if `≤` is. -/]
def decidableEqOfDecidableLE [DecidableLE α] : DecidableEq α
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isTrue (le_antisymm hab hba) else isFalse fun heq => hba (heq ▸ le_refl _)
    else isFalse fun heq => hab (heq ▸ le_refl _)

-- See Note [decidable namespace]
@[to_dual Decidable.lt_or_eq_of_le']
protected lemma Decidable.lt_or_eq_of_le [DecidableLE α] (hab : a ≤ b) : a < b ∨ a = b :=
  if hba : b ≤ a then Or.inr (le_antisymm hab hba) else Or.inl (lt_of_le_not_ge hab hba)

@[to_dual Decidable.le_iff_lt_or_eq']
protected lemma Decidable.le_iff_lt_or_eq [DecidableLE α] : a ≤ b ↔ a < b ∨ a = b :=
  ⟨Decidable.lt_or_eq_of_le, le_of_lt_or_eq⟩

@[to_dual lt_or_eq_of_le']
lemma lt_or_eq_of_le : a ≤ b → a < b ∨ a = b := open scoped Classical in Decidable.lt_or_eq_of_le
@[to_dual le_iff_lt_or_eq']
lemma le_iff_lt_or_eq : a ≤ b ↔ a < b ∨ a = b := open scoped Classical in Decidable.le_iff_lt_or_eq

end PartialOrder
