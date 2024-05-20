/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename
import Mathlib.Init.Algebra.Classes
import Mathlib.Init.Data.Ordering.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.TypeStar
import Batteries.Classes.Order
import Mathlib.Tactic.GCongr.Core


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
    (simp only [compare, compareOfLessAndEq]; split_ifs <;> rfl) |
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

instance : IsTotalPreorder α (· ≤ ·) where
  trans := @le_trans _ _
  total := le_total

-- TODO(Leo): decide whether we should keep this instance or not
instance isStrictWeakOrder_of_linearOrder : IsStrictWeakOrder α (· < ·) :=
  have : IsTotalPreorder α (· ≤ ·) := by infer_instance -- Porting note: added
  isStrictWeakOrder_of_isTotalPreorder lt_iff_not_ge
#align is_strict_weak_order_of_linear_order isStrictWeakOrder_of_linearOrder

-- TODO(Leo): decide whether we should keep this instance or not
instance isStrictTotalOrder_of_linearOrder : IsStrictTotalOrder α (· < ·) where
  trichotomous := lt_trichotomy
#align is_strict_total_order_of_linear_order isStrictTotalOrder_of_linearOrder

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
  split_ifs <;> simp only [*, lt_irrefl]

theorem compare_gt_iff_gt {a b : α} : (compare a b = .gt) ↔ a > b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  split_ifs <;> simp only [*, lt_irrefl, not_lt_of_gt]
  case _ h₁ h₂ =>
    have h : b < a := lt_trichotomy a b |>.resolve_left h₁ |>.resolve_left h₂
    exact true_iff_iff.2 h

theorem compare_eq_iff_eq {a b : α} : (compare a b = .eq) ↔ a = b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  split_ifs <;> try simp only
  case _ h   => exact false_iff_iff.2 <| ne_iff_lt_or_gt.2 <| .inl h
  case _ _ h => exact true_iff_iff.2 h
  case _ _ h => exact false_iff_iff.2 h

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

theorem compare_iff (a b : α) {o : Ordering} : compare a b = o ↔ o.toRel a b := by
  cases o <;> simp only [Ordering.toRel]
  · exact compare_lt_iff_lt
  · exact compare_eq_iff_eq
  · exact compare_gt_iff_gt

instance : Batteries.TransCmp (compare (α := α)) where
  symm a b := by
    cases h : compare a b <;>
    simp only [Ordering.swap] <;> symm
    · exact compare_gt_iff_gt.2 <| compare_lt_iff_lt.1 h
    · exact compare_eq_iff_eq.2 <| compare_eq_iff_eq.1 h |>.symm
    · exact compare_lt_iff_lt.2 <| compare_gt_iff_gt.1 h
  le_trans := fun h₁ h₂ ↦
    compare_le_iff_le.2 <| le_trans (compare_le_iff_le.1 h₁) (compare_le_iff_le.1 h₂)

end Ord

end LinearOrder

open Lean Meta
/-- See if the term is `a < b` and the goal is `a ≤ b`. -/
@[gcongr_forward] def Mathlib.Tactic.GCongr.exactLeOfLt : ForwardExt where
  eval h goal := do goal.assignIfDefeq (← mkAppM ``le_of_lt #[h])
