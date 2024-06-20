/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Batteries.Tactic.Alias
import Mathlib.Mathport.Rename
import Mathlib.Tactic.Relation.Trans
import Mathlib.Tactic.TypeStar

#align_import init.algebra.order from "leanprover-community/lean"@"c2bcdbcbe741ed37c361a30d38e179182b989f76"

/-!
# Orders

Defines classes for preorders, partial orders, and linear orders
and proves some basic lemmas about them.
-/

universe u
variable {α : Type u}

section Preorder

/-!
### Definition of `Preorder` and lemmas about types with a `Preorder`
-/

/-- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way. -/
class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl
#align preorder Preorder
#align preorder.to_has_le Preorder.toLE
#align preorder.to_has_lt Preorder.toLT

variable [Preorder α]

/-- The relation `≤` on a preorder is reflexive. -/
@[refl]
theorem le_refl : ∀ a : α, a ≤ a :=
  Preorder.le_refl
#align le_refl le_refl

/-- A version of `le_refl` where the argument is implicit -/
theorem le_rfl {a : α} : a ≤ a :=
  le_refl a
#align le_rfl le_rfl

/-- The relation `≤` on a preorder is transitive. -/
@[trans]
theorem le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c :=
  Preorder.le_trans _ _ _
#align le_trans le_trans

theorem lt_iff_le_not_le : ∀ {a b : α}, a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  Preorder.lt_iff_le_not_le _ _
#align lt_iff_le_not_le lt_iff_le_not_le

theorem lt_of_le_not_le : ∀ {a b : α}, a ≤ b → ¬b ≤ a → a < b
  | _a, _b, hab, hba => lt_iff_le_not_le.mpr ⟨hab, hba⟩
#align lt_of_le_not_le lt_of_le_not_le

theorem le_not_le_of_lt : ∀ {a b : α}, a < b → a ≤ b ∧ ¬b ≤ a
  | _a, _b, hab => lt_iff_le_not_le.mp hab
#align le_not_le_of_lt le_not_le_of_lt

theorem le_of_eq {a b : α} : a = b → a ≤ b := fun h => h ▸ le_refl a
#align le_of_eq le_of_eq

@[trans]
theorem ge_trans : ∀ {a b c : α}, a ≥ b → b ≥ c → a ≥ c := fun h₁ h₂ => le_trans h₂ h₁
#align ge_trans ge_trans

theorem lt_irrefl : ∀ a : α, ¬a < a
  | _a, haa =>
    match le_not_le_of_lt haa with
    | ⟨h1, h2⟩ => h2 h1
#align lt_irrefl lt_irrefl

theorem gt_irrefl : ∀ a : α, ¬a > a :=
  lt_irrefl
#align gt_irrefl gt_irrefl

@[trans]
theorem lt_trans : ∀ {a b c : α}, a < b → b < c → a < c
  | _a, _b, _c, hab, hbc =>
    match le_not_le_of_lt hab, le_not_le_of_lt hbc with
    | ⟨hab, _hba⟩, ⟨hbc, hcb⟩ =>
      lt_of_le_not_le (le_trans hab hbc) fun hca => hcb (le_trans hca hab)
#align lt_trans lt_trans

@[trans]
theorem gt_trans : ∀ {a b c : α}, a > b → b > c → a > c := fun h₁ h₂ => lt_trans h₂ h₁
#align gt_trans gt_trans

theorem ne_of_lt {a b : α} (h : a < b) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
#align ne_of_lt ne_of_lt

theorem ne_of_gt {a b : α} (h : b < a) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
#align ne_of_gt ne_of_gt

theorem lt_asymm {a b : α} (h : a < b) : ¬b < a := fun h1 : b < a => lt_irrefl a (lt_trans h h1)
#align lt_asymm lt_asymm

theorem le_of_lt : ∀ {a b : α}, a < b → a ≤ b
  | _a, _b, hab => (le_not_le_of_lt hab).left
#align le_of_lt le_of_lt

@[trans]
theorem lt_of_lt_of_le : ∀ {a b c : α}, a < b → b ≤ c → a < c
  | _a, _b, _c, hab, hbc =>
    let ⟨hab, hba⟩ := le_not_le_of_lt hab
    lt_of_le_not_le (le_trans hab hbc) fun hca => hba (le_trans hbc hca)
#align lt_of_lt_of_le lt_of_lt_of_le

@[trans]
theorem lt_of_le_of_lt : ∀ {a b c : α}, a ≤ b → b < c → a < c
  | _a, _b, _c, hab, hbc =>
    let ⟨hbc, hcb⟩ := le_not_le_of_lt hbc
    lt_of_le_not_le (le_trans hab hbc) fun hca => hcb (le_trans hca hab)
#align lt_of_le_of_lt lt_of_le_of_lt

@[trans]
theorem gt_of_gt_of_ge {a b c : α} (h₁ : a > b) (h₂ : b ≥ c) : a > c :=
  lt_of_le_of_lt h₂ h₁
#align gt_of_gt_of_ge gt_of_gt_of_ge

@[trans]
theorem gt_of_ge_of_gt {a b c : α} (h₁ : a ≥ b) (h₂ : b > c) : a > c :=
  lt_of_lt_of_le h₂ h₁
#align gt_of_ge_of_gt gt_of_ge_of_gt

-- Porting note (#10754): new instance
instance (priority := 900) : @Trans α α α LE.le LE.le LE.le := ⟨le_trans⟩
instance (priority := 900) : @Trans α α α LT.lt LT.lt LT.lt := ⟨lt_trans⟩
instance (priority := 900) : @Trans α α α LT.lt LE.le LT.lt := ⟨lt_of_lt_of_le⟩
instance (priority := 900) : @Trans α α α LE.le LT.lt LT.lt := ⟨lt_of_le_of_lt⟩
instance (priority := 900) : @Trans α α α GE.ge GE.ge GE.ge := ⟨ge_trans⟩
instance (priority := 900) : @Trans α α α GT.gt GT.gt GT.gt := ⟨gt_trans⟩
instance (priority := 900) : @Trans α α α GT.gt GE.ge GT.gt := ⟨gt_of_gt_of_ge⟩
instance (priority := 900) : @Trans α α α GE.ge GT.gt GT.gt := ⟨gt_of_ge_of_gt⟩

theorem not_le_of_gt {a b : α} (h : a > b) : ¬a ≤ b :=
  (le_not_le_of_lt h).right
#align not_le_of_gt not_le_of_gt

theorem not_lt_of_ge {a b : α} (h : a ≥ b) : ¬a < b := fun hab => not_le_of_gt hab h
#align not_lt_of_ge not_lt_of_ge

theorem le_of_lt_or_eq : ∀ {a b : α}, a < b ∨ a = b → a ≤ b
  | _a, _b, Or.inl hab => le_of_lt hab
  | _a, _b, Or.inr hab => hab ▸ le_refl _
#align le_of_lt_or_eq le_of_lt_or_eq

theorem le_of_eq_or_lt {a b : α} (h : a = b ∨ a < b) : a ≤ b :=
  Or.elim h le_of_eq le_of_lt
#align le_of_eq_or_lt le_of_eq_or_lt

/-- `<` is decidable if `≤` is. -/
def decidableLTOfDecidableLE [@DecidableRel α (· ≤ ·)] : @DecidableRel α (· < ·)
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isFalse fun hab' => not_le_of_gt hab' hba
      else isTrue <| lt_of_le_not_le hab hba
    else isFalse fun hab' => hab (le_of_lt hab')
#align decidable_lt_of_decidable_le decidableLTOfDecidableLE

end Preorder

section PartialOrder

/-!
### Definition of `PartialOrder` and lemmas about types with a partial order
-/

/-- A partial order is a reflexive, transitive, antisymmetric relation `≤`. -/
class PartialOrder (α : Type u) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b
#align partial_order PartialOrder

variable [PartialOrder α]

theorem le_antisymm : ∀ {a b : α}, a ≤ b → b ≤ a → a = b :=
  PartialOrder.le_antisymm _ _
#align le_antisymm le_antisymm

alias eq_of_le_of_le := le_antisymm

theorem le_antisymm_iff {a b : α} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun e => ⟨le_of_eq e, le_of_eq e.symm⟩, fun ⟨h1, h2⟩ => le_antisymm h1 h2⟩
#align le_antisymm_iff le_antisymm_iff

theorem lt_of_le_of_ne {a b : α} : a ≤ b → a ≠ b → a < b := fun h₁ h₂ =>
  lt_of_le_not_le h₁ <| mt (le_antisymm h₁) h₂
#align lt_of_le_of_ne lt_of_le_of_ne

/-- Equality is decidable if `≤` is. -/
def decidableEqOfDecidableLE [@DecidableRel α (· ≤ ·)] : DecidableEq α
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isTrue (le_antisymm hab hba) else isFalse fun heq => hba (heq ▸ le_refl _)
    else isFalse fun heq => hab (heq ▸ le_refl _)
#align decidable_eq_of_decidable_le decidableEqOfDecidableLE

namespace Decidable

variable [@DecidableRel α (· ≤ ·)]

theorem lt_or_eq_of_le {a b : α} (hab : a ≤ b) : a < b ∨ a = b :=
  if hba : b ≤ a then Or.inr (le_antisymm hab hba) else Or.inl (lt_of_le_not_le hab hba)
#align decidable.lt_or_eq_of_le Decidable.lt_or_eq_of_le

theorem eq_or_lt_of_le {a b : α} (hab : a ≤ b) : a = b ∨ a < b :=
  (lt_or_eq_of_le hab).symm
#align decidable.eq_or_lt_of_le Decidable.eq_or_lt_of_le

theorem le_iff_lt_or_eq {a b : α} : a ≤ b ↔ a < b ∨ a = b :=
  ⟨lt_or_eq_of_le, le_of_lt_or_eq⟩
#align decidable.le_iff_lt_or_eq Decidable.le_iff_lt_or_eq

end Decidable

attribute [local instance] Classical.propDecidable

theorem lt_or_eq_of_le {a b : α} : a ≤ b → a < b ∨ a = b :=
  Decidable.lt_or_eq_of_le
#align lt_or_eq_of_le lt_or_eq_of_le

theorem le_iff_lt_or_eq {a b : α} : a ≤ b ↔ a < b ∨ a = b :=
  Decidable.le_iff_lt_or_eq
#align le_iff_lt_or_eq le_iff_lt_or_eq

end PartialOrder

section LinearOrder

/-!
### Definition of `LinearOrder` and lemmas about types with a linear order
-/

/-- Default definition of `max`. -/
def maxDefault {α : Type u} [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b : α) :=
  if a ≤ b then b else a
#align max_default maxDefault

/-- Default definition of `min`. -/
def minDefault {α : Type u} [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b : α) :=
  if a ≤ b then a else b

/-- This attempts to prove that a given instance of `compare` is equal to `compareOfLessAndEq` by
introducing the arguments and trying the following approaches in order:

1. seeing if `rfl` works
2. seeing if the `compare` at hand is nonetheless essentially `compareOfLessAndEq`, but, because of
implicit arguments, requires us to unfold the defs and split the `if`s in the definition of
`compareOfLessAndEq`
3. seeing if we can split by cases on the arguments, then see if the defs work themselves out
  (useful when `compare` is defined via a `match` statement, as it is for `Bool`) -/
macro "compareOfLessAndEq_rfl" : tactic =>
  `(tactic| (intros a b; first | rfl |
    (simp only [compare, compareOfLessAndEq]; split <;> rfl) |
    (induction a <;> induction b <;> simp (config := {decide := true}) only [])))

/-- A linear order is reflexive, transitive, antisymmetric and total relation `≤`.
We assume that every linear ordered type has decidable `(≤)`, `(<)`, and `(=)`. -/
class LinearOrder (α : Type u) extends PartialOrder α, Min α, Max α, Ord α :=
  /-- A linear order is total. -/
  le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableLE : DecidableRel (· ≤ · : α → α → Prop)
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ decidableLE
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableLT : DecidableRel (· < · : α → α → Prop) :=
    @decidableLTOfDecidableLE _ _ decidableLE
  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a
  /-- The minimum function is equivalent to the one you get from `minOfLe`. -/
  min_def : ∀ a b, min a b = if a ≤ b then a else b := by intros; rfl
  /-- The minimum function is equivalent to the one you get from `maxOfLe`. -/
  max_def : ∀ a b, max a b = if a ≤ b then b else a := by intros; rfl
  compare a b := compareOfLessAndEq a b
  /-- Comparison via `compare` is equal to the canonical comparison given decidable `<` and `=`. -/
  compare_eq_compareOfLessAndEq : ∀ a b, compare a b = compareOfLessAndEq a b := by
    compareOfLessAndEq_rfl
#align linear_order LinearOrder

variable [LinearOrder α]

attribute [local instance] LinearOrder.decidableLE

theorem le_total : ∀ a b : α, a ≤ b ∨ b ≤ a :=
  LinearOrder.le_total
#align le_total le_total

theorem le_of_not_ge {a b : α} : ¬a ≥ b → a ≤ b :=
  Or.resolve_left (le_total b a)
#align le_of_not_ge le_of_not_ge

theorem le_of_not_le {a b : α} : ¬a ≤ b → b ≤ a :=
  Or.resolve_left (le_total a b)
#align le_of_not_le le_of_not_le

theorem not_lt_of_gt {a b : α} (h : a > b) : ¬a < b :=
  lt_asymm h
#align not_lt_of_gt not_lt_of_gt

theorem lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a :=
  Or.elim (le_total a b)
    (fun h : a ≤ b =>
      Or.elim (Decidable.lt_or_eq_of_le h) (fun h : a < b => Or.inl h) fun h : a = b =>
        Or.inr (Or.inl h))
    fun h : b ≤ a =>
    Or.elim (Decidable.lt_or_eq_of_le h) (fun h : b < a => Or.inr (Or.inr h)) fun h : b = a =>
      Or.inr (Or.inl h.symm)
#align lt_trichotomy lt_trichotomy

theorem le_of_not_lt {a b : α} (h : ¬b < a) : a ≤ b :=
  match lt_trichotomy a b with
  | Or.inl hlt => le_of_lt hlt
  | Or.inr (Or.inl HEq) => HEq ▸ le_refl a
  | Or.inr (Or.inr hgt) => absurd hgt h
#align le_of_not_lt le_of_not_lt

theorem le_of_not_gt {a b : α} : ¬a > b → a ≤ b :=
  le_of_not_lt
#align le_of_not_gt le_of_not_gt

theorem lt_of_not_ge {a b : α} (h : ¬a ≥ b) : a < b :=
  lt_of_le_not_le ((le_total _ _).resolve_right h) h
#align lt_of_not_ge lt_of_not_ge

theorem lt_or_le (a b : α) : a < b ∨ b ≤ a :=
  if hba : b ≤ a then Or.inr hba else Or.inl <| lt_of_not_ge hba
#align lt_or_le lt_or_le

theorem le_or_lt (a b : α) : a ≤ b ∨ b < a :=
  (lt_or_le b a).symm
#align le_or_lt le_or_lt

theorem lt_or_ge : ∀ a b : α, a < b ∨ a ≥ b :=
  lt_or_le
#align lt_or_ge lt_or_ge

theorem le_or_gt : ∀ a b : α, a ≤ b ∨ a > b :=
  le_or_lt
#align le_or_gt le_or_gt

theorem lt_or_gt_of_ne {a b : α} (h : a ≠ b) : a < b ∨ a > b :=
  match lt_trichotomy a b with
  | Or.inl hlt => Or.inl hlt
  | Or.inr (Or.inl HEq) => absurd HEq h
  | Or.inr (Or.inr hgt) => Or.inr hgt
#align lt_or_gt_of_ne lt_or_gt_of_ne

theorem ne_iff_lt_or_gt {a b : α} : a ≠ b ↔ a < b ∨ a > b :=
  ⟨lt_or_gt_of_ne, fun o => Or.elim o ne_of_lt ne_of_gt⟩
#align ne_iff_lt_or_gt ne_iff_lt_or_gt

theorem lt_iff_not_ge (x y : α) : x < y ↔ ¬x ≥ y :=
  ⟨not_le_of_gt, lt_of_not_ge⟩
#align lt_iff_not_ge lt_iff_not_ge

@[simp]
theorem not_lt {a b : α} : ¬a < b ↔ b ≤ a :=
  ⟨le_of_not_gt, not_lt_of_ge⟩
#align not_lt not_lt

@[simp]
theorem not_le {a b : α} : ¬a ≤ b ↔ b < a :=
  (lt_iff_not_ge _ _).symm
#align not_le not_le

instance (priority := 900) (a b : α) : Decidable (a < b) :=
  LinearOrder.decidableLT a b

instance (priority := 900) (a b : α) : Decidable (a ≤ b) :=
  LinearOrder.decidableLE a b

instance (priority := 900) (a b : α) : Decidable (a = b) :=
  LinearOrder.decidableEq a b

theorem eq_or_lt_of_not_lt {a b : α} (h : ¬a < b) : a = b ∨ b < a :=
  if h₁ : a = b then Or.inl h₁ else Or.inr (lt_of_not_ge fun hge => h (lt_of_le_of_ne hge h₁))
#align eq_or_lt_of_not_lt eq_or_lt_of_not_lt

/-- Perform a case-split on the ordering of `x` and `y` in a decidable linear order. -/
def ltByCases (x y : α) {P : Sort*} (h₁ : x < y → P) (h₂ : x = y → P) (h₃ : y < x → P) : P :=
  if h : x < y then h₁ h
  else if h' : y < x then h₃ h' else h₂ (le_antisymm (le_of_not_gt h') (le_of_not_gt h))
#align lt_by_cases ltByCases

theorem le_imp_le_of_lt_imp_lt {β} [Preorder α] [LinearOrder β] {a b : α} {c d : β}
    (H : d < c → b < a) (h : a ≤ b) : c ≤ d :=
  le_of_not_lt fun h' => not_le_of_gt (H h') h
#align le_imp_le_of_lt_imp_lt le_imp_le_of_lt_imp_lt

-- Porting note: new
section Ord

theorem compare_lt_iff_lt {a b : α} : (compare a b = .lt) ↔ a < b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  split <;> simp only [*, lt_irrefl]
  split <;> simp

theorem compare_gt_iff_gt {a b : α} : (compare a b = .gt) ↔ a > b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  split
  · simp only [*, lt_irrefl, not_lt_of_gt]
  split
  · simp only [*, lt_irrefl, not_lt_of_gt]
  simp only [gt_iff_lt, true_iff]
  case _ h₁ h₂ =>
    exact lt_trichotomy a b |>.resolve_left h₁ |>.resolve_left h₂

theorem compare_eq_iff_eq {a b : α} : (compare a b = .eq) ↔ a = b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  split <;> simp [*, ne_of_lt]

theorem compare_le_iff_le {a b : α} : (compare a b ≠ .gt) ↔ a ≤ b := by
  cases h : compare a b <;> simp
  · exact le_of_lt <| compare_lt_iff_lt.1 h
  · exact le_of_eq <| compare_eq_iff_eq.1 h
  · exact compare_gt_iff_gt.1 h

theorem compare_ge_iff_ge {a b : α} : (compare a b ≠ .lt) ↔ a ≥ b := by
  cases h : compare a b <;> simp
  · exact compare_lt_iff_lt.1 h
  · exact le_of_eq <| (·.symm) <| compare_eq_iff_eq.1 h
  · exact le_of_lt <| compare_gt_iff_gt.1 h

end Ord

end LinearOrder

instance Nat.instLinearOrder : LinearOrder Nat where
  le := Nat.le
  le_refl := @Nat.le_refl
  le_trans := @Nat.le_trans
  le_antisymm := @Nat.le_antisymm
  le_total := @Nat.le_total
  lt := Nat.lt
  lt_iff_le_not_le := @Nat.lt_iff_le_not_le
  decidableLT := inferInstance
  decidableLE := inferInstance
  decidableEq := inferInstance
#align nat.linear_order Nat.instLinearOrder

section

open Decidable

variable {α : Type u} [LinearOrder α]

theorem min_def (a b : α) : min a b = if a ≤ b then a else b := by
  rw [LinearOrder.min_def a]
#align min_def min_def

theorem max_def (a b : α) : max a b = if a ≤ b then b else a := by
  rw [LinearOrder.max_def a]
#align max_def max_def

theorem min_le_left (a b : α) : min a b ≤ a := by
  -- Porting note: no `min_tac` tactic
  if h : a ≤ b
  then simp [min_def, if_pos h, le_refl]
  else simp [min_def, if_neg h]; exact le_of_not_le h
#align min_le_left min_le_left

theorem min_le_right (a b : α) : min a b ≤ b := by
  -- Porting note: no `min_tac` tactic
  if h : a ≤ b
  then simp [min_def, if_pos h]; exact h
  else simp [min_def, if_neg h, le_refl]
#align min_le_right min_le_right

theorem le_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b := by
  -- Porting note: no `min_tac` tactic
  if h : a ≤ b
  then simp [min_def, if_pos h]; exact h₁
  else simp [min_def, if_neg h]; exact h₂
#align le_min le_min

theorem le_max_left (a b : α) : a ≤ max a b := by
  -- Porting note: no `min_tac` tactic
  if h : a ≤ b
  then simp [max_def, if_pos h]; exact h
  else simp [max_def, if_neg h, le_refl]
#align le_max_left le_max_left

theorem le_max_right (a b : α) : b ≤ max a b := by
  -- Porting note: no `min_tac` tactic
  if h : a ≤ b
  then simp [max_def, if_pos h, le_refl]
  else simp [max_def, if_neg h]; exact le_of_not_le h
#align le_max_right le_max_right

theorem max_le {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c := by
  -- Porting note: no `min_tac` tactic
  if h : a ≤ b
  then simp [max_def, if_pos h]; exact h₂
  else simp [max_def, if_neg h]; exact h₁
#align max_le max_le

theorem eq_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) (h₃ : ∀ {d}, d ≤ a → d ≤ b → d ≤ c) :
    c = min a b :=
  le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))
#align eq_min eq_min

theorem min_comm (a b : α) : min a b = min b a :=
  eq_min (min_le_right a b) (min_le_left a b) fun h₁ h₂ => le_min h₂ h₁
#align min_comm min_comm

theorem min_assoc (a b c : α) : min (min a b) c = min a (min b c) := by
  apply eq_min
  · apply le_trans; apply min_le_left; apply min_le_left
  · apply le_min; apply le_trans; apply min_le_left; apply min_le_right; apply min_le_right
  · intro d h₁ h₂; apply le_min; apply le_min h₁; apply le_trans h₂; apply min_le_left
    apply le_trans h₂; apply min_le_right
#align min_assoc min_assoc

theorem min_left_comm (a b c : α) : min a (min b c) = min b (min a c) := by
  rw [← min_assoc, min_comm a, min_assoc]
#align min_left_comm min_left_comm

@[simp]
theorem min_self (a : α) : min a a = a := by simp [min_def]
#align min_self min_self

theorem min_eq_left {a b : α} (h : a ≤ b) : min a b = a := by
  apply Eq.symm; apply eq_min (le_refl _) h; intros; assumption
#align min_eq_left min_eq_left

theorem min_eq_right {a b : α} (h : b ≤ a) : min a b = b :=
  min_comm b a ▸ min_eq_left h
#align min_eq_right min_eq_right

theorem eq_max {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) (h₃ : ∀ {d}, a ≤ d → b ≤ d → c ≤ d) :
    c = max a b :=
  le_antisymm (h₃ (le_max_left a b) (le_max_right a b)) (max_le h₁ h₂)
#align eq_max eq_max

theorem max_comm (a b : α) : max a b = max b a :=
  eq_max (le_max_right a b) (le_max_left a b) fun h₁ h₂ => max_le h₂ h₁
#align max_comm max_comm

theorem max_assoc (a b c : α) : max (max a b) c = max a (max b c) := by
  apply eq_max
  · apply le_trans; apply le_max_left a b; apply le_max_left
  · apply max_le; apply le_trans; apply le_max_right a b; apply le_max_left; apply le_max_right
  · intro d h₁ h₂; apply max_le; apply max_le h₁; apply le_trans (le_max_left _ _) h₂
    apply le_trans (le_max_right _ _) h₂
#align max_assoc max_assoc

theorem max_left_comm (a b c : α) : max a (max b c) = max b (max a c) := by
  rw [← max_assoc, max_comm a, max_assoc]
#align max_left_comm max_left_comm

@[simp]
theorem max_self (a : α) : max a a = a := by simp [max_def]
#align max_self max_self

theorem max_eq_left {a b : α} (h : b ≤ a) : max a b = a := by
  apply Eq.symm; apply eq_max (le_refl _) h; intros; assumption
#align max_eq_left max_eq_left

theorem max_eq_right {a b : α} (h : a ≤ b) : max a b = b :=
  max_comm b a ▸ max_eq_left h
#align max_eq_right max_eq_right

-- these rely on lt_of_lt
theorem min_eq_left_of_lt {a b : α} (h : a < b) : min a b = a :=
  min_eq_left (le_of_lt h)
#align min_eq_left_of_lt min_eq_left_of_lt

theorem min_eq_right_of_lt {a b : α} (h : b < a) : min a b = b :=
  min_eq_right (le_of_lt h)
#align min_eq_right_of_lt min_eq_right_of_lt

theorem max_eq_left_of_lt {a b : α} (h : b < a) : max a b = a :=
  max_eq_left (le_of_lt h)
#align max_eq_left_of_lt max_eq_left_of_lt

theorem max_eq_right_of_lt {a b : α} (h : a < b) : max a b = b :=
  max_eq_right (le_of_lt h)
#align max_eq_right_of_lt max_eq_right_of_lt

-- these use the fact that it is a linear ordering
theorem lt_min {a b c : α} (h₁ : a < b) (h₂ : a < c) : a < min b c :=
  -- Porting note: no `min_tac` tactic
  Or.elim (le_or_gt b c)
    (fun h : b ≤ c ↦ by rwa [min_eq_left h])
    (fun h : b > c ↦ by rwa [min_eq_right_of_lt h])
#align lt_min lt_min

theorem max_lt {a b c : α} (h₁ : a < c) (h₂ : b < c) : max a b < c :=
  -- Porting note: no `min_tac` tactic
  Or.elim (le_or_gt a b)
    (fun h : a ≤ b ↦ by rwa [max_eq_right h])
    (fun h : a > b ↦ by rwa [max_eq_left_of_lt h])
#align max_lt max_lt

end
