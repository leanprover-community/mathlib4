/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Batteries.Classes.Order
public import Batteries.Tactic.Trans
public import Mathlib.Data.Ordering.Basic
public import Mathlib.Tactic.ExtendDoc
public import Mathlib.Tactic.Lemma
public import Mathlib.Tactic.Push.Attr
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.TypeStar
public import Mathlib.Order.Defs.PartialOrder

/-!
# Orders

Defines classes for linear orders and proves some basic lemmas about them.
-/

@[expose] public section

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
  protected le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLE : DecidableLE α
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ toDecidableLE
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLT : DecidableLT α := @decidableLTOfDecidableLE _ _ toDecidableLE
  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a
  /-- The minimum function is equivalent to the one you get from `minOfLe`. -/
  protected min_def : ∀ a b, min a b = if a ≤ b then a else b := by intros; rfl
  /-- The minimum function is equivalent to the one you get from `maxOfLe`. -/
  protected max_def : ∀ a b, max a b = if a ≤ b then b else a := by intros; rfl
  compare a b := compareOfLessAndEq a b
  /-- Comparison via `compare` is equal to the canonical comparison given decidable `<` and `=`. -/
  compare_eq_compareOfLessAndEq : ∀ a b, compare a b = compareOfLessAndEq a b := by
    compareOfLessAndEq_rfl

attribute [to_dual existing] LinearOrder.toMax

variable [LinearOrder α] {a b c : α}

attribute [instance 900] LinearOrder.toDecidableLT
attribute [instance 900] LinearOrder.toDecidableLE
attribute [instance 900] LinearOrder.toDecidableEq

instance : Std.IsLinearOrder α where
  le_total := LinearOrder.le_total

@[to_dual self] lemma le_total : ∀ a b : α, a ≤ b ∨ b ≤ a := LinearOrder.le_total

@[to_dual self] lemma le_of_not_ge : ¬a ≤ b → b ≤ a := (le_total a b).resolve_left
@[to_dual self] lemma lt_of_not_ge (h : ¬b ≤ a) : a < b := lt_of_le_not_ge (le_of_not_ge h) h

@[to_dual gt_trichotomy]
lemma lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a := by grind

@[to_dual self]
lemma le_of_not_gt (h : ¬b < a) : a ≤ b :=
  match lt_trichotomy a b with
  | Or.inl hlt => le_of_lt hlt
  | Or.inr (Or.inl HEq) => HEq ▸ le_refl a
  | Or.inr (Or.inr hgt) => absurd hgt h

@[to_dual self] lemma lt_or_ge (a b : α) : a < b ∨ b ≤ a :=
  if hba : b ≤ a then Or.inr hba else Or.inl <| lt_of_not_ge hba

@[to_dual self] lemma le_or_gt (a b : α) : a ≤ b ∨ b < a := (lt_or_ge b a).symm

@[to_dual gt_or_lt_of_ne]
lemma lt_or_gt_of_ne (h : a ≠ b) : a < b ∨ b < a := by grind

@[to_dual ne_iff_gt_or_lt]
lemma ne_iff_lt_or_gt : a ≠ b ↔ a < b ∨ b < a := ⟨lt_or_gt_of_ne, (Or.elim · ne_of_lt ne_of_gt)⟩

@[to_dual self] lemma lt_iff_not_ge : a < b ↔ ¬b ≤ a := ⟨not_le_of_gt, lt_of_not_ge⟩

@[simp, push, to_dual self] lemma not_lt : ¬a < b ↔ b ≤ a := ⟨le_of_not_gt, not_lt_of_ge⟩
@[simp, push, to_dual self] lemma not_le : ¬a ≤ b ↔ b < a := lt_iff_not_ge.symm

@[to_dual eq_or_lt_of_not_gt]
lemma eq_or_gt_of_not_lt (h : ¬a < b) : a = b ∨ b < a :=
  if h₁ : a = b then Or.inl h₁ else Or.inr (lt_of_not_ge fun hge => h (lt_of_le_of_ne hge h₁))

@[to_dual self]
theorem le_imp_le_of_lt_imp_lt {α β} [Preorder α] [LinearOrder β] {a b : α} {c d : β}
    (H : d < c → b < a) (h : a ≤ b) : c ≤ d :=
  le_of_not_gt fun h' => not_le_of_gt (H h') h

@[grind =]
lemma min_def (a b : α) : min a b = if a ≤ b then a else b := LinearOrder.min_def a b
@[grind =]
lemma max_def (a b : α) : max a b = if a ≤ b then b else a := LinearOrder.max_def a b

@[to_dual existing max_def]
theorem min_def' (a b : α) : min a b = if b ≤ a then b else a := by grind

@[to_dual existing min_def]
theorem max_def' (a b : α) : max a b = if b ≤ a then a else b := by grind

@[to_dual le_max_left]
lemma min_le_left (a b : α) : min a b ≤ a := by grind

@[to_dual le_max_right]
lemma min_le_right (a b : α) : min a b ≤ b := by grind

@[to_dual max_le]
lemma le_min (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b := by grind

@[to_dual]
lemma eq_min (h₁ : c ≤ a) (h₂ : c ≤ b) (h₃ : ∀ {d}, d ≤ a → d ≤ b → d ≤ c) : c = min a b :=
  le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))

@[to_dual]
lemma min_comm (a b : α) : min a b = min b a :=
  eq_min (min_le_right a b) (min_le_left a b) fun h₁ h₂ => le_min h₂ h₁

@[to_dual]
lemma min_assoc (a b c : α) : min (min a b) c = min a (min b c) := by grind

@[to_dual]
lemma min_left_comm (a b c : α) : min a (min b c) = min b (min a c) := by grind

@[to_dual (attr := simp)] lemma min_self (a : α) : min a a = a := by grind

@[to_dual]
lemma min_eq_left (h : a ≤ b) : min a b = a := by grind

@[to_dual]
lemma min_eq_right (h : b ≤ a) : min a b = b := min_comm b a ▸ min_eq_left h

@[to_dual] lemma min_eq_left_of_lt (h : a < b) : min a b = a := min_eq_left (le_of_lt h)
@[to_dual] lemma min_eq_right_of_lt (h : b < a) : min a b = b := min_eq_right (le_of_lt h)

@[to_dual max_lt]
lemma lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c := by
  cases le_total b c <;> simp [min_eq_left, min_eq_right, *]

section Ord

lemma compare_lt_iff_lt : compare a b = .lt ↔ a < b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  grind

lemma compare_gt_iff_gt : compare a b = .gt ↔ b < a := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  grind

lemma compare_eq_iff_eq : compare a b = .eq ↔ a = b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  grind

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

/-- The category of linear orders.

This will get reused to define `OrderType`. -/
structure LinOrd where
  /-- Construct a bundled `LinOrd` from the underlying type and typeclass. -/
  of ::
  /-- The underlying linearly ordered type. -/
  (carrier : Type*)
  [str : LinearOrder carrier]

attribute [instance] LinOrd.str

initialize_simps_projections LinOrd (carrier → coe, -str)

namespace LinOrd

instance : CoeSort LinOrd (Type _) :=
  ⟨LinOrd.carrier⟩

attribute [coe] LinOrd.carrier

end LinOrd

end LinearOrder
