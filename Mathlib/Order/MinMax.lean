/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.OpClass
public import Mathlib.Order.Lattice

/-!
# `max` and `min`

This file proves basic properties about maxima and minima on a `LinearOrder`.

## Tags

min, max
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe u v

variable {α : Type u} {β : Type v}

section

variable [LinearOrder α] [LinearOrder β] {f : α → β} {s : Set α} {a b c d : α}

-- translate from lattices to linear orders (sup → max, inf → min)
@[to_dual max_le_iff]
theorem le_min_iff : c ≤ min a b ↔ c ≤ a ∧ c ≤ b :=
  le_inf_iff

@[to_dual min_le_iff]
theorem le_max_iff : a ≤ max b c ↔ a ≤ b ∨ a ≤ c :=
  le_sup_iff

@[to_dual]
instance [LinearOrder α] : Std.LawfulOrderSup α where
  max_le_iff _ _ _ := max_le_iff

@[to_dual max_lt_iff]
theorem lt_min_iff : a < min b c ↔ a < b ∧ a < c :=
  lt_inf_iff

@[to_dual min_lt_iff]
theorem lt_max_iff : a < max b c ↔ a < b ∨ a < c :=
  lt_sup_iff

@[to_dual]
theorem max_le_max : a ≤ c → b ≤ d → max a b ≤ max c d :=
  sup_le_sup

@[to_dual]
theorem max_le_max_left (c) (h : a ≤ b) : max c a ≤ max c b := sup_le_sup_left h c

@[to_dual]
theorem max_le_max_right (c) (h : a ≤ b) : max a c ≤ max b c := sup_le_sup_right h c

@[to_dual min_le_of_left_le]
theorem le_max_of_le_left : a ≤ b → a ≤ max b c :=
  le_sup_of_le_left

@[to_dual min_le_of_right_le]
theorem le_max_of_le_right : a ≤ c → a ≤ max b c :=
  le_sup_of_le_right

@[to_dual min_lt_of_left_lt]
theorem lt_max_of_lt_left (h : a < b) : a < max b c :=
  h.trans_le (le_max_left b c)

@[to_dual min_lt_of_right_lt]
theorem lt_max_of_lt_right (h : a < c) : a < max b c :=
  h.trans_le (le_max_right b c)

@[to_dual]
lemma max_min_distrib_left (a b c : α) : max a (min b c) = min (max a b) (max a c) :=
  sup_inf_left _ _ _

@[to_dual]
lemma max_min_distrib_right (a b c : α) : max (min a b) c = min (max a c) (max b c) :=
  sup_inf_right _ _ _

theorem min_le_max : min a b ≤ max a b :=
  le_trans (min_le_left a b) (le_max_left a b)

@[to_dual]
theorem min_eq_left_iff : min a b = a ↔ a ≤ b :=
  inf_eq_left

@[to_dual]
theorem min_eq_right_iff : min a b = b ↔ b ≤ a :=
  inf_eq_right

/-- For elements `a` and `b` of a linear order, either `min a b = a` and `a ≤ b`,
or `min a b = b` and `b < a`.
Use cases on this lemma to automate linarith in inequalities -/
@[to_dual
/-- For elements `a` and `b` of a linear order, either `max a b = a` and `b ≤ a`,
or `max a b = b` and `a < b`.
Use cases on this lemma to automate linarith in inequalities -/]
theorem min_cases (a b : α) : min a b = a ∧ a ≤ b ∨ min a b = b ∧ b < a := by
  grind

@[to_dual]
theorem min_eq_iff : min a b = c ↔ a = c ∧ a ≤ b ∨ b = c ∧ b ≤ a := by
  grind

@[to_dual]
theorem min_lt_min_left_iff : min a c < min b c ↔ a < b ∧ a < c := by
  grind

@[to_dual]
theorem min_lt_min_right_iff : min a b < min a c ↔ b < c ∧ b < a := by
  grind

/-- An instance asserting that `max a a = a` -/
@[to_dual /-- An instance asserting that `min a a = a` -/]
instance max_idem : Std.IdempotentOp (α := α) max where
  idempotent := by simp

theorem min_lt_max : min a b < max a b ↔ a ≠ b :=
  inf_lt_sup

@[to_dual]
theorem max_lt_max (h₁ : a < c) (h₂ : b < d) : max a b < max c d :=
  max_lt (lt_max_of_lt_left h₁) (lt_max_of_lt_right h₂)

@[to_dual]
lemma min_right_comm (a b c : α) : min (min a b) c = min (min a c) b := by
  rw [min_assoc, min_comm b, ← min_assoc]

@[deprecated (since := "2026-03-22")] alias Max.left_comm := max_left_comm
@[deprecated (since := "2026-03-22")] alias Max.right_comm := max_right_comm

@[to_dual]
theorem MonotoneOn.map_max (hf : MonotoneOn f s) (ha : a ∈ s) (hb : b ∈ s) : f (max a b) =
    max (f a) (f b) := by
  rcases le_total a b with h | h <;>
    simp only [max_eq_right, max_eq_left, hf ha hb, hf hb ha, h]

@[to_dual]
theorem AntitoneOn.map_max (hf : AntitoneOn f s) (ha : a ∈ s) (hb : b ∈ s) : f (max a b) =
    min (f a) (f b) := hf.dual_right.map_max ha hb

@[to_dual]
theorem Monotone.map_max (hf : Monotone f) : f (max a b) = max (f a) (f b) := by
  rcases le_total a b with h | h <;> simp [h, hf h]

@[to_dual]
theorem Antitone.map_max (hf : Antitone f) : f (max a b) = min (f a) (f b) := by
  rcases le_total a b with h | h <;> simp [h, hf h]

@[to_dual]
theorem min_choice (a b : α) : min a b = a ∨ min a b = b := by cases le_total a b <;> simp [*]

@[to_dual le_of_le_min_left]
theorem le_of_max_le_left {a b c : α} (h : max a b ≤ c) : a ≤ c :=
  le_trans (le_max_left _ _) h

@[to_dual le_of_le_min_right]
theorem le_of_max_le_right {a b c : α} (h : max a b ≤ c) : b ≤ c :=
  le_trans (le_max_right _ _) h

@[to_dual] instance instCommutativeMax : Std.Commutative (α := α) max where comm := max_comm
@[to_dual] instance instAssociativeMax : Std.Associative (α := α) max where assoc := max_assoc

@[to_dual]
theorem max_left_commutative : LeftCommutative (max : α → α → α) := ⟨max_left_comm⟩

end
