/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Batteries.Classes.Order
import Batteries.Tactic.Trans
import Mathlib.Data.Ordering.Basic
import Mathlib.Tactic.ExtendDoc
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.TypeStar
import Mathlib.Order.Defs.PartialOrder

/-!
# Orders

Defines classes for linear orders and proves some basic lemmas about them.
-/

variable {α : Type*}

section LinearOrder

/-!
### Definition of `LinearOrder` and lemmas about types with a linear order
-/

/-- Default definition of `max`. -/
def maxDefault [LE α] [DecidableLE α] (a b : α) :=
  if a ≤ b then b else a

/-- Default definition of `min`. -/
def minDefault [LE α] [DecidableLE α] (a b : α) :=
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
  `(tactic| (intro a b; first | rfl |
    (simp only [compare, compareOfLessAndEq]; split_ifs <;> rfl) |
    (induction a <;> induction b <;> simp +decide only)))

/-- A linear order is reflexive, transitive, antisymmetric and total relation `≤`.
We assume that every linear ordered type has decidable `(≤)`, `(<)`, and `(=)`. -/
class LinearOrder (α : Type*) extends PartialOrder α, Min α, Max α, Ord α where
  /-- A linear order is total. -/
  le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLE : DecidableLE α
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ toDecidableLE
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLT : DecidableLT α := @decidableLTOfDecidableLE _ _ toDecidableLE
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

attribute [instance 900] LinearOrder.toDecidableLT
attribute [instance 900] LinearOrder.toDecidableLE
attribute [instance 900] LinearOrder.toDecidableEq

instance : Std.IsLinearOrder α where
  le_total := LinearOrder.le_total

lemma le_total : ∀ a b : α, a ≤ b ∨ b ≤ a := LinearOrder.le_total

lemma le_of_not_ge : ¬a ≤ b → b ≤ a := (le_total a b).resolve_left
lemma lt_of_not_ge (h : ¬b ≤ a) : a < b := lt_of_le_not_ge (le_of_not_ge h) h

@[deprecated (since := "2025-05-11")] alias le_of_not_le := le_of_not_ge

lemma lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a := by
  grind [le_total, Decidable.lt_or_eq_of_le]

lemma le_of_not_gt (h : ¬b < a) : a ≤ b :=
  match lt_trichotomy a b with
  | Or.inl hlt => le_of_lt hlt
  | Or.inr (Or.inl HEq) => HEq ▸ le_refl a
  | Or.inr (Or.inr hgt) => absurd hgt h

@[deprecated (since := "2025-05-11")] alias le_of_not_lt := le_of_not_gt

lemma lt_or_ge (a b : α) : a < b ∨ b ≤ a :=
  if hba : b ≤ a then Or.inr hba else Or.inl <| lt_of_not_ge hba

@[deprecated (since := "2025-05-11")] alias lt_or_le := lt_or_ge

lemma le_or_gt (a b : α) : a ≤ b ∨ b < a := (lt_or_ge b a).symm

@[deprecated (since := "2025-05-11")] alias le_or_lt := le_or_gt

lemma lt_or_gt_of_ne (h : a ≠ b) : a < b ∨ b < a := by simpa [h] using lt_trichotomy a b

lemma ne_iff_lt_or_gt : a ≠ b ↔ a < b ∨ b < a := ⟨lt_or_gt_of_ne, (Or.elim · ne_of_lt ne_of_gt)⟩

lemma lt_iff_not_ge : a < b ↔ ¬b ≤ a := ⟨not_le_of_gt, lt_of_not_ge⟩

@[simp] lemma not_lt : ¬a < b ↔ b ≤ a := ⟨le_of_not_gt, not_lt_of_ge⟩
@[simp] lemma not_le : ¬a ≤ b ↔ b < a := lt_iff_not_ge.symm

lemma eq_or_gt_of_not_lt (h : ¬a < b) : a = b ∨ b < a :=
  if h₁ : a = b then Or.inl h₁ else Or.inr (lt_of_not_ge fun hge => h (lt_of_le_of_ne hge h₁))

@[deprecated (since := "2025-07-27")] alias eq_or_lt_of_not_gt := eq_or_gt_of_not_lt
@[deprecated (since := "2025-05-11")] alias eq_or_lt_of_not_lt := eq_or_gt_of_not_lt

/-- Perform a case-split on the ordering of `x` and `y` in a decidable linear order. -/
@[deprecated lt_trichotomy (since := "2025-04-21")]
def ltByCases (x y : α) {P : Sort*} (h₁ : x < y → P) (h₂ : x = y → P) (h₃ : y < x → P) : P :=
  if h : x < y then h₁ h
  else if h' : y < x then h₃ h' else h₂ (le_antisymm (le_of_not_gt h') (le_of_not_gt h))

theorem le_imp_le_of_lt_imp_lt {α β} [Preorder α] [LinearOrder β] {a b : α} {c d : β}
    (H : d < c → b < a) (h : a ≤ b) : c ≤ d :=
  le_of_not_gt fun h' => not_le_of_gt (H h') h

@[grind =]
lemma min_def (a b : α) : min a b = if a ≤ b then a else b := by rw [LinearOrder.min_def a]
@[grind =]
lemma max_def (a b : α) : max a b = if a ≤ b then b else a := by rw [LinearOrder.max_def a]

lemma min_le_left (a b : α) : min a b ≤ a := by
  if h : a ≤ b
  then simp [min_def, if_pos h, le_refl]
  else simpa [min_def, if_neg h] using le_of_not_ge h

lemma min_le_right (a b : α) : min a b ≤ b := by
  if h : a ≤ b
  then simpa [min_def, if_pos h] using h
  else simp [min_def, if_neg h, le_refl]

lemma le_min (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b := by
  if h : a ≤ b
  then simpa [min_def, if_pos h] using h₁
  else simpa [min_def, if_neg h] using h₂

lemma le_max_left (a b : α) : a ≤ max a b := by
  if h : a ≤ b
  then simpa [max_def, if_pos h] using h
  else simp [max_def, if_neg h, le_refl]

lemma le_max_right (a b : α) : b ≤ max a b := by
  if h : a ≤ b
  then simp [max_def, if_pos h, le_refl]
  else simpa [max_def, if_neg h] using le_of_not_ge h

lemma max_le (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c := by
  if h : a ≤ b
  then simpa [max_def, if_pos h] using h₂
  else simpa [max_def, if_neg h] using h₁

lemma eq_min (h₁ : c ≤ a) (h₂ : c ≤ b) (h₃ : ∀ {d}, d ≤ a → d ≤ b → d ≤ c) : c = min a b :=
  le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))

lemma min_comm (a b : α) : min a b = min b a :=
  eq_min (min_le_right a b) (min_le_left a b) fun h₁ h₂ => le_min h₂ h₁

lemma min_assoc (a b c : α) : min (min a b) c = min a (min b c) := by
  apply eq_min
  · apply le_trans (min_le_left ..) (min_le_left ..)
  · apply le_min
    · apply le_trans (min_le_left ..) (min_le_right ..)
    · apply min_le_right
  · intro d h₁ h₂; apply le_min
    · apply le_min h₁; apply le_trans h₂; apply min_le_left
    · apply le_trans h₂; apply min_le_right

lemma min_left_comm (a b c : α) : min a (min b c) = min b (min a c) := by
  rw [← min_assoc, min_comm a, min_assoc]

@[simp] lemma min_self (a : α) : min a a = a := by simp [min_def]

lemma min_eq_left (h : a ≤ b) : min a b = a := by
  apply Eq.symm; apply eq_min (le_refl _) h; intros; assumption

lemma min_eq_right (h : b ≤ a) : min a b = b := min_comm b a ▸ min_eq_left h

lemma eq_max (h₁ : a ≤ c) (h₂ : b ≤ c) (h₃ : ∀ {d}, a ≤ d → b ≤ d → c ≤ d) :
    c = max a b :=
  le_antisymm (h₃ (le_max_left a b) (le_max_right a b)) (max_le h₁ h₂)

lemma max_comm (a b : α) : max a b = max b a :=
  eq_max (le_max_right a b) (le_max_left a b) fun h₁ h₂ => max_le h₂ h₁

lemma max_assoc (a b c : α) : max (max a b) c = max a (max b c) := by
  apply eq_max
  · apply le_trans (le_max_left a b) (le_max_left ..)
  · apply max_le
    · apply le_trans (le_max_right a b) (le_max_left ..)
    · apply le_max_right
  · intro d h₁ h₂; apply max_le
    · apply max_le h₁; apply le_trans (le_max_left _ _) h₂
    · apply le_trans (le_max_right _ _) h₂

lemma max_left_comm (a b c : α) : max a (max b c) = max b (max a c) := by
  rw [← max_assoc, max_comm a, max_assoc]

@[simp] lemma max_self (a : α) : max a a = a := by simp [max_def]

lemma max_eq_left (h : b ≤ a) : max a b = a := by
  apply Eq.symm; apply eq_max (le_refl _) h; intros; assumption

lemma max_eq_right (h : a ≤ b) : max a b = b := max_comm b a ▸ max_eq_left h

lemma min_eq_left_of_lt (h : a < b) : min a b = a := min_eq_left (le_of_lt h)
lemma min_eq_right_of_lt (h : b < a) : min a b = b := min_eq_right (le_of_lt h)
lemma max_eq_left_of_lt (h : b < a) : max a b = a := max_eq_left (le_of_lt h)
lemma max_eq_right_of_lt (h : a < b) : max a b = b := max_eq_right (le_of_lt h)

lemma lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c := by
  cases le_total b c <;> simp [min_eq_left, min_eq_right, *]

lemma max_lt (h₁ : a < c) (h₂ : b < c) : max a b < c := by
  cases le_total a b <;> simp [max_eq_left, max_eq_right, *]

section Ord

lemma compare_lt_iff_lt : compare a b = .lt ↔ a < b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  split_ifs <;> simp only [*, lt_irrefl]

lemma compare_gt_iff_gt : compare a b = .gt ↔ b < a := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  split_ifs <;> simp only [*, lt_irrefl, not_lt_of_gt]
  case _ h₁ h₂ =>
    have h : b < a := lt_trichotomy a b |>.resolve_left h₁ |>.resolve_left h₂
    rwa [true_iff]

lemma compare_eq_iff_eq : compare a b = .eq ↔ a = b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  split_ifs <;> try simp only
  case _ h => rw [false_iff]; exact ne_iff_lt_or_gt.2 <| .inl h
  case _ _ h => rwa [true_iff]
  case _ _ h => rwa [false_iff]

lemma compare_le_iff_le : compare a b ≠ .gt ↔ a ≤ b := by
  cases h : compare a b
  · simpa using le_of_lt <| compare_lt_iff_lt.1 h
  · simpa using le_of_eq <| compare_eq_iff_eq.1 h
  · simpa using compare_gt_iff_gt.1 h

lemma compare_ge_iff_ge : compare a b ≠ .lt ↔ b ≤ a := by
  cases h : compare a b
  · simpa using compare_lt_iff_lt.1 h
  · simpa using le_of_eq <| (·.symm) <| compare_eq_iff_eq.1 h
  · simpa using le_of_lt <| compare_gt_iff_gt.1 h

lemma compare_iff (a b : α) {o : Ordering} : compare a b = o ↔ o.Compares a b := by
  cases o <;> simp only [Ordering.Compares]
  · exact compare_lt_iff_lt
  · exact compare_eq_iff_eq
  · exact compare_gt_iff_gt

theorem cmp_eq_compare (a b : α) : cmp a b = compare a b := by
  refine ((compare_iff ..).2 ?_).symm
  unfold cmp cmpUsing; split_ifs with h1 h2
  · exact h1
  · exact h2
  · exact le_antisymm (not_lt.1 h2) (not_lt.1 h1)

theorem cmp_eq_compareOfLessAndEq (a b : α) : cmp a b = compareOfLessAndEq a b :=
  (cmp_eq_compare ..).trans (LinearOrder.compare_eq_compareOfLessAndEq ..)

instance : Std.LawfulBCmp (compare (α := α)) where
  eq_swap {a b} := by
    cases _ : compare b a <;>
      simp_all [Ordering.swap, compare_eq_iff_eq, compare_lt_iff_lt, compare_gt_iff_gt]
  isLE_trans h₁ h₂ := by
    simp only [← Ordering.ne_gt_iff_isLE, compare_le_iff_le] at *
    exact le_trans h₁ h₂
  compare_eq_iff_beq := by simp [compare_eq_iff_eq]
  eq_lt_iff_lt := by simp [compare_lt_iff_lt]
  isLE_iff_le := by simp [← Ordering.ne_gt_iff_isLE, compare_le_iff_le]

end Ord

end LinearOrder
