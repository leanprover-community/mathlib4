/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.Algebra.Classes
import Mathlib.Data.Ordering.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.TypeStar
import Batteries.Classes.Order

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

variable [Preorder α] {a b c : α}

/-- The relation `≤` on a preorder is reflexive. -/
@[refl] lemma le_refl : ∀ a : α, a ≤ a := Preorder.le_refl

/-- A version of `le_refl` where the argument is implicit -/
lemma le_rfl : a ≤ a := le_refl a

/-- The relation `≤` on a preorder is transitive. -/
@[trans] lemma le_trans : a ≤ b → b ≤ c → a ≤ c := Preorder.le_trans _ _ _

lemma lt_iff_le_not_le : a < b ↔ a ≤ b ∧ ¬b ≤ a := Preorder.lt_iff_le_not_le _ _

lemma lt_of_le_not_le (hab : a ≤ b) (hba : ¬ b ≤ a) : a < b := lt_iff_le_not_le.2 ⟨hab, hba⟩

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
class PartialOrder (α : Type u) extends Preorder α where
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

section LinearOrder

/-!
### Definition of `LinearOrder` and lemmas about types with a linear order
-/

/-- Default definition of `max`. -/
def maxDefault {α : Type u} [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b : α) :=
  if a ≤ b then b else a

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

variable [LinearOrder α] {a b c : α}

attribute [local instance] LinearOrder.decidableLE

lemma le_total : ∀ a b : α, a ≤ b ∨ b ≤ a := LinearOrder.le_total

lemma le_of_not_ge : ¬a ≥ b → a ≤ b := (le_total b a).resolve_left
lemma le_of_not_le : ¬a ≤ b → b ≤ a := (le_total a b).resolve_left
lemma lt_of_not_ge (h : ¬a ≥ b) : a < b := lt_of_le_not_le (le_of_not_ge h) h

lemma lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a :=
  Or.elim (le_total a b)
    (fun h : a ≤ b =>
      Or.elim (Decidable.lt_or_eq_of_le h) (fun h : a < b => Or.inl h) fun h : a = b =>
        Or.inr (Or.inl h))
    fun h : b ≤ a =>
    Or.elim (Decidable.lt_or_eq_of_le h) (fun h : b < a => Or.inr (Or.inr h)) fun h : b = a =>
      Or.inr (Or.inl h.symm)

lemma le_of_not_lt (h : ¬b < a) : a ≤ b :=
  match lt_trichotomy a b with
  | Or.inl hlt => le_of_lt hlt
  | Or.inr (Or.inl HEq) => HEq ▸ le_refl a
  | Or.inr (Or.inr hgt) => absurd hgt h

lemma le_of_not_gt : ¬a > b → a ≤ b := le_of_not_lt

lemma lt_or_le (a b : α) : a < b ∨ b ≤ a :=
  if hba : b ≤ a then Or.inr hba else Or.inl <| lt_of_not_ge hba

lemma le_or_lt (a b : α) : a ≤ b ∨ b < a := (lt_or_le b a).symm
lemma lt_or_ge : ∀ a b : α, a < b ∨ a ≥ b := lt_or_le
lemma le_or_gt : ∀ a b : α, a ≤ b ∨ a > b := le_or_lt

lemma lt_or_gt_of_ne (h : a ≠ b) : a < b ∨ a > b := by simpa [h] using lt_trichotomy a b

lemma ne_iff_lt_or_gt : a ≠ b ↔ a < b ∨ a > b := ⟨lt_or_gt_of_ne, (Or.elim · ne_of_lt ne_of_gt)⟩

lemma lt_iff_not_ge (x y : α) : x < y ↔ ¬x ≥ y := ⟨not_le_of_gt, lt_of_not_ge⟩

@[simp] lemma not_lt : ¬a < b ↔ b ≤ a := ⟨le_of_not_gt, not_lt_of_ge⟩
@[simp] lemma not_le : ¬a ≤ b ↔ b < a := (lt_iff_not_ge _ _).symm

instance (priority := 900) (a b : α) : Decidable (a < b) := LinearOrder.decidableLT a b
instance (priority := 900) (a b : α) : Decidable (a ≤ b) := LinearOrder.decidableLE a b
instance (priority := 900) (a b : α) : Decidable (a = b) := LinearOrder.decidableEq a b

lemma eq_or_lt_of_not_lt (h : ¬a < b) : a = b ∨ b < a :=
  if h₁ : a = b then Or.inl h₁ else Or.inr (lt_of_not_ge fun hge => h (lt_of_le_of_ne hge h₁))

set_option linter.deprecated false in
@[deprecated (since := "2024-07-30")]
instance : IsTotalPreorder α (· ≤ ·) where
  trans := @le_trans _ _
  total := le_total

-- TODO(Leo): decide whether we should keep this instance or not
set_option linter.deprecated false in
@[deprecated (since := "2024-07-30")]
instance isStrictWeakOrder_of_linearOrder : IsStrictWeakOrder α (· < ·) :=
  have : IsTotalPreorder α (· ≤ ·) := by infer_instance -- Porting note: added
  isStrictWeakOrder_of_isTotalPreorder lt_iff_not_ge

-- TODO(Leo): decide whether we should keep this instance or not
instance isStrictTotalOrder_of_linearOrder : IsStrictTotalOrder α (· < ·) where
  trichotomous := lt_trichotomy

/-- Perform a case-split on the ordering of `x` and `y` in a decidable linear order. -/
def ltByCases (x y : α) {P : Sort*} (h₁ : x < y → P) (h₂ : x = y → P) (h₃ : y < x → P) : P :=
  if h : x < y then h₁ h
  else if h' : y < x then h₃ h' else h₂ (le_antisymm (le_of_not_gt h') (le_of_not_gt h))

theorem le_imp_le_of_lt_imp_lt {α β} [Preorder α] [LinearOrder β] {a b : α} {c d : β}
    (H : d < c → b < a) (h : a ≤ b) : c ≤ d :=
  le_of_not_lt fun h' => not_le_of_gt (H h') h

-- Porting note: new
section Ord
variable {o : Ordering}

lemma compare_lt_iff_lt : compare a b = .lt ↔ a < b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  split_ifs <;> simp only [*, lt_irrefl]

lemma compare_gt_iff_gt : compare a b = .gt ↔ a > b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  split_ifs <;> simp only [*, lt_irrefl, not_lt_of_gt]
  case _ h₁ h₂ =>
    have h : b < a := lt_trichotomy a b |>.resolve_left h₁ |>.resolve_left h₂
    exact true_iff_iff.2 h

lemma compare_eq_iff_eq : compare a b = .eq ↔ a = b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  split_ifs <;> try simp only
  case _ h   => exact false_iff_iff.2 <| ne_iff_lt_or_gt.2 <| .inl h
  case _ _ h => exact true_iff_iff.2 h
  case _ _ h => exact false_iff_iff.2 h

lemma compare_le_iff_le : compare a b ≠ .gt ↔ a ≤ b := by
  cases h : compare a b <;> simp
  · exact le_of_lt <| compare_lt_iff_lt.1 h
  · exact le_of_eq <| compare_eq_iff_eq.1 h
  · exact compare_gt_iff_gt.1 h

lemma compare_ge_iff_ge : compare a b ≠ .lt ↔ a ≥ b := by
  cases h : compare a b <;> simp
  · exact compare_lt_iff_lt.1 h
  · exact le_of_eq <| (·.symm) <| compare_eq_iff_eq.1 h
  · exact le_of_lt <| compare_gt_iff_gt.1 h

lemma compare_iff (a b : α) : compare a b = o ↔ o.toRel a b := by
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
