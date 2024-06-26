/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Order.Lattice

#align_import order.min_max from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# `max` and `min`

This file proves basic properties about maxima and minima on a `LinearOrder`.

## Tags

min, max
-/


universe u v

variable {α : Type u} {β : Type v}

attribute [simp] max_eq_left max_eq_right min_eq_left min_eq_right

section

variable [LinearOrder α] [LinearOrder β] {f : α → β} {s : Set α} {a b c d : α}

-- translate from lattices to linear orders (sup → max, inf → min)
@[simp]
theorem le_min_iff : c ≤ min a b ↔ c ≤ a ∧ c ≤ b :=
  le_inf_iff
#align le_min_iff le_min_iff

@[simp]
theorem le_max_iff : a ≤ max b c ↔ a ≤ b ∨ a ≤ c :=
  le_sup_iff
#align le_max_iff le_max_iff

@[simp]
theorem min_le_iff : min a b ≤ c ↔ a ≤ c ∨ b ≤ c :=
  inf_le_iff
#align min_le_iff min_le_iff

@[simp]
theorem max_le_iff : max a b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  sup_le_iff
#align max_le_iff max_le_iff

@[simp]
theorem lt_min_iff : a < min b c ↔ a < b ∧ a < c :=
  lt_inf_iff
#align lt_min_iff lt_min_iff

@[simp]
theorem lt_max_iff : a < max b c ↔ a < b ∨ a < c :=
  lt_sup_iff
#align lt_max_iff lt_max_iff

@[simp]
theorem min_lt_iff : min a b < c ↔ a < c ∨ b < c :=
  inf_lt_iff
#align min_lt_iff min_lt_iff

@[simp]
theorem max_lt_iff : max a b < c ↔ a < c ∧ b < c :=
  sup_lt_iff
#align max_lt_iff max_lt_iff

@[gcongr]
theorem max_le_max : a ≤ c → b ≤ d → max a b ≤ max c d :=
  sup_le_sup
#align max_le_max max_le_max

@[gcongr] theorem max_le_max_left (c) (h : a ≤ b) : max c a ≤ max c b := sup_le_sup_left h c

@[gcongr] theorem max_le_max_right (c) (h : a ≤ b) : max a c ≤ max b c := sup_le_sup_right h c

@[gcongr]
theorem min_le_min : a ≤ c → b ≤ d → min a b ≤ min c d :=
  inf_le_inf
#align min_le_min min_le_min

@[gcongr] theorem min_le_min_left (c) (h : a ≤ b) : min c a ≤ min c b := inf_le_inf_left c h

@[gcongr] theorem min_le_min_right (c) (h : a ≤ b) : min a c ≤ min b c := inf_le_inf_right c h

theorem le_max_of_le_left : a ≤ b → a ≤ max b c :=
  le_sup_of_le_left
#align le_max_of_le_left le_max_of_le_left

theorem le_max_of_le_right : a ≤ c → a ≤ max b c :=
  le_sup_of_le_right
#align le_max_of_le_right le_max_of_le_right

theorem lt_max_of_lt_left (h : a < b) : a < max b c :=
  h.trans_le (le_max_left b c)
#align lt_max_of_lt_left lt_max_of_lt_left

theorem lt_max_of_lt_right (h : a < c) : a < max b c :=
  h.trans_le (le_max_right b c)
#align lt_max_of_lt_right lt_max_of_lt_right

theorem min_le_of_left_le : a ≤ c → min a b ≤ c :=
  inf_le_of_left_le
#align min_le_of_left_le min_le_of_left_le

theorem min_le_of_right_le : b ≤ c → min a b ≤ c :=
  inf_le_of_right_le
#align min_le_of_right_le min_le_of_right_le

theorem min_lt_of_left_lt (h : a < c) : min a b < c :=
  (min_le_left a b).trans_lt h
#align min_lt_of_left_lt min_lt_of_left_lt

theorem min_lt_of_right_lt (h : b < c) : min a b < c :=
  (min_le_right a b).trans_lt h
#align min_lt_of_right_lt min_lt_of_right_lt

lemma max_min_distrib_left (a b c : α) : max a (min b c) = min (max a b) (max a c) :=
  sup_inf_left _ _ _
#align max_min_distrib_left max_min_distrib_left

lemma max_min_distrib_right (a b c : α) : max (min a b) c = min (max a c) (max b c) :=
  sup_inf_right _ _ _
#align max_min_distrib_right max_min_distrib_right

lemma min_max_distrib_left (a b c : α) : min a (max b c) = max (min a b) (min a c) :=
  inf_sup_left _ _ _
#align min_max_distrib_left min_max_distrib_left

lemma min_max_distrib_right (a b c : α) : min (max a b) c = max (min a c) (min b c) :=
  inf_sup_right _ _ _
#align min_max_distrib_right min_max_distrib_right

theorem min_le_max : min a b ≤ max a b :=
  le_trans (min_le_left a b) (le_max_left a b)
#align min_le_max min_le_max

@[simp]
theorem min_eq_left_iff : min a b = a ↔ a ≤ b :=
  inf_eq_left
#align min_eq_left_iff min_eq_left_iff

@[simp]
theorem min_eq_right_iff : min a b = b ↔ b ≤ a :=
  inf_eq_right
#align min_eq_right_iff min_eq_right_iff

@[simp]
theorem max_eq_left_iff : max a b = a ↔ b ≤ a :=
  sup_eq_left
#align max_eq_left_iff max_eq_left_iff

@[simp]
theorem max_eq_right_iff : max a b = b ↔ a ≤ b :=
  sup_eq_right
#align max_eq_right_iff max_eq_right_iff

/-- For elements `a` and `b` of a linear order, either `min a b = a` and `a ≤ b`,
    or `min a b = b` and `b < a`.
    Use cases on this lemma to automate linarith in inequalities -/
theorem min_cases (a b : α) : min a b = a ∧ a ≤ b ∨ min a b = b ∧ b < a := by
  by_cases h : a ≤ b
  · left
    exact ⟨min_eq_left h, h⟩
  · right
    exact ⟨min_eq_right (le_of_lt (not_le.mp h)), not_le.mp h⟩
#align min_cases min_cases

/-- For elements `a` and `b` of a linear order, either `max a b = a` and `b ≤ a`,
    or `max a b = b` and `a < b`.
    Use cases on this lemma to automate linarith in inequalities -/
theorem max_cases (a b : α) : max a b = a ∧ b ≤ a ∨ max a b = b ∧ a < b :=
  @min_cases αᵒᵈ _ a b
#align max_cases max_cases

theorem min_eq_iff : min a b = c ↔ a = c ∧ a ≤ b ∨ b = c ∧ b ≤ a := by
  constructor
  · intro h
    refine Or.imp (fun h' => ?_) (fun h' => ?_) (le_total a b) <;> exact ⟨by simpa [h'] using h, h'⟩
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩) <;> simp [h]
#align min_eq_iff min_eq_iff

theorem max_eq_iff : max a b = c ↔ a = c ∧ b ≤ a ∨ b = c ∧ a ≤ b :=
  @min_eq_iff αᵒᵈ _ a b c
#align max_eq_iff max_eq_iff

theorem min_lt_min_left_iff : min a c < min b c ↔ a < b ∧ a < c := by
  simp_rw [lt_min_iff, min_lt_iff, or_iff_left (lt_irrefl _)]
  exact and_congr_left fun h => or_iff_left_of_imp h.trans
#align min_lt_min_left_iff min_lt_min_left_iff

theorem min_lt_min_right_iff : min a b < min a c ↔ b < c ∧ b < a := by
  simp_rw [min_comm a, min_lt_min_left_iff]
#align min_lt_min_right_iff min_lt_min_right_iff

theorem max_lt_max_left_iff : max a c < max b c ↔ a < b ∧ c < b :=
  @min_lt_min_left_iff αᵒᵈ _ _ _ _
#align max_lt_max_left_iff max_lt_max_left_iff

theorem max_lt_max_right_iff : max a b < max a c ↔ b < c ∧ a < c :=
  @min_lt_min_right_iff αᵒᵈ _ _ _ _
#align max_lt_max_right_iff max_lt_max_right_iff

/-- An instance asserting that `max a a = a` -/
instance max_idem : Std.IdempotentOp (α := α) max where
  idempotent := by simp
#align max_idem max_idem

-- short-circuit type class inference
/-- An instance asserting that `min a a = a` -/
instance min_idem : Std.IdempotentOp (α := α) min where
  idempotent := by simp
#align min_idem min_idem

-- short-circuit type class inference
theorem min_lt_max : min a b < max a b ↔ a ≠ b :=
  inf_lt_sup
#align min_lt_max min_lt_max

-- Porting note: was `by simp [lt_max_iff, max_lt_iff, *]`
theorem max_lt_max (h₁ : a < c) (h₂ : b < d) : max a b < max c d :=
  max_lt (lt_max_of_lt_left h₁) (lt_max_of_lt_right h₂)
#align max_lt_max max_lt_max

theorem min_lt_min (h₁ : a < c) (h₂ : b < d) : min a b < min c d :=
  @max_lt_max αᵒᵈ _ _ _ _ _ h₁ h₂
#align min_lt_min min_lt_min

theorem min_right_comm (a b c : α) : min (min a b) c = min (min a c) b :=
  right_comm min min_comm min_assoc a b c
#align min_right_comm min_right_comm

theorem Max.left_comm (a b c : α) : max a (max b c) = max b (max a c) :=
  _root_.left_comm max max_comm max_assoc a b c
#align max.left_comm Max.left_comm

theorem Max.right_comm (a b c : α) : max (max a b) c = max (max a c) b :=
  _root_.right_comm max max_comm max_assoc a b c
#align max.right_comm Max.right_comm

theorem MonotoneOn.map_max (hf : MonotoneOn f s) (ha : a ∈ s) (hb : b ∈ s) : f (max a b) =
    max (f a) (f b) := by
  rcases le_total a b with h | h <;>
    simp only [max_eq_right, max_eq_left, hf ha hb, hf hb ha, h]
#align monotone_on.map_max MonotoneOn.map_max

theorem MonotoneOn.map_min (hf : MonotoneOn f s) (ha : a ∈ s) (hb : b ∈ s) : f (min a b) =
    min (f a) (f b) := hf.dual.map_max ha hb
#align monotone_on.map_min MonotoneOn.map_min

theorem AntitoneOn.map_max (hf : AntitoneOn f s) (ha : a ∈ s) (hb : b ∈ s) : f (max a b) =
    min (f a) (f b) := hf.dual_right.map_max ha hb
#align antitone_on.map_max AntitoneOn.map_max

theorem AntitoneOn.map_min (hf : AntitoneOn f s) (ha : a ∈ s) (hb : b ∈ s) : f (min a b) =
    max (f a) (f b) := hf.dual.map_max ha hb
#align antitone_on.map_min AntitoneOn.map_min

theorem Monotone.map_max (hf : Monotone f) : f (max a b) = max (f a) (f b) := by
  rcases le_total a b with h | h <;> simp [h, hf h]
#align monotone.map_max Monotone.map_max

theorem Monotone.map_min (hf : Monotone f) : f (min a b) = min (f a) (f b) :=
  hf.dual.map_max
#align monotone.map_min Monotone.map_min

theorem Antitone.map_max (hf : Antitone f) : f (max a b) = min (f a) (f b) := by
  rcases le_total a b with h | h <;> simp [h, hf h]
#align antitone.map_max Antitone.map_max

theorem Antitone.map_min (hf : Antitone f) : f (min a b) = max (f a) (f b) :=
  hf.dual.map_max
#align antitone.map_min Antitone.map_min

theorem min_choice (a b : α) : min a b = a ∨ min a b = b := by cases le_total a b <;> simp [*]
#align min_choice min_choice

theorem max_choice (a b : α) : max a b = a ∨ max a b = b :=
  @min_choice αᵒᵈ _ a b
#align max_choice max_choice

theorem le_of_max_le_left {a b c : α} (h : max a b ≤ c) : a ≤ c :=
  le_trans (le_max_left _ _) h
#align le_of_max_le_left le_of_max_le_left

theorem le_of_max_le_right {a b c : α} (h : max a b ≤ c) : b ≤ c :=
  le_trans (le_max_right _ _) h
#align le_of_max_le_right le_of_max_le_right

theorem max_commutative : Commutative (max : α → α → α) :=
  max_comm
#align max_commutative max_commutative

theorem max_associative : Associative (max : α → α → α) :=
  max_assoc
#align max_associative max_associative

instance : Std.Commutative (α := α) max where
  comm := max_comm

instance : Std.Associative (α := α) max where
  assoc := max_assoc

theorem max_left_commutative : LeftCommutative (max : α → α → α) :=
  max_left_comm
#align max_left_commutative max_left_commutative

theorem min_commutative : Commutative (min : α → α → α) :=
  min_comm
#align min_commutative min_commutative

theorem min_associative : Associative (α := α) min :=
  min_assoc
#align min_associative min_associative

instance : Std.Commutative (α := α) min where
  comm := min_comm

instance : Std.Associative (α := α) min where
  assoc := min_assoc

theorem min_left_commutative : LeftCommutative (min : α → α → α) :=
  min_left_comm
#align min_left_commutative min_left_commutative

end
