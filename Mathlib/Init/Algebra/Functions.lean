/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/

import Mathlib.Init.Algebra.Order

universe u

section

variable {α : Type u} [LinearOrder α]

lemma min_def (a b : α) : min a b = if a ≤ b then a else b := LinearOrder.min_def ..

lemma min_le_left (a b : α) : min a b ≤ a := by
  if h : a ≤ b
  then simp [min_def, if_pos h, le_refl]
  else simp [min_def, if_neg h]; exact le_of_not_le h

lemma min_le_right (a b : α) : min a b ≤ b := by
  if h : a ≤ b
  then simp [min_def, if_pos h]; exact h
  else simp [min_def, if_neg h, le_refl]

lemma le_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b := by
  if h : a ≤ b
  then simp [min_def, if_pos h]; exact h₁
  else simp [min_def, if_neg h]; exact h₂

lemma max_def (a b : α) : max a b = if a ≤ b then b else a := LinearOrder.max_def ..

lemma le_max_left (a b : α) : a ≤ max a b := by
  if h : a ≤ b
  then simp [max_def, if_pos h]; exact h
  else simp [max_def, if_neg h, le_refl]

lemma le_max_right (a b : α) : b ≤ max a b := by
  if h : a ≤ b
  then simp [max_def, if_pos h, le_refl]
  else simp [max_def, if_neg h]; exact le_of_not_le h

lemma max_le {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c := by
  if h : a ≤ b
  then simp [max_def, if_pos h]; exact h₂
  else simp [max_def, if_neg h]; exact h₁

lemma eq_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) (h₃ : ∀{d}, d ≤ a → d ≤ b → d ≤ c) :
  c = min a b :=
le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))

lemma min_comm (a b : α) : min a b = min b a :=
  eq_min (min_le_right a b) (min_le_left a b) (λ {_} h₁ h₂ => le_min h₂ h₁)

lemma min_assoc (a b c : α) : min (min a b) c = min a (min b c) := by
  apply eq_min
  · apply le_trans; apply min_le_left; apply min_le_left
  · apply le_min; apply le_trans; apply min_le_left; apply min_le_right; apply min_le_right
  · intros d h₁ h₂; apply le_min; apply le_min h₁; apply le_trans h₂; apply min_le_left
    apply le_trans h₂; apply min_le_right

lemma min_left_comm : @LeftCommutative α α min :=
  left_comm min (@min_comm α _) (@min_assoc α _)

@[simp]
lemma min_self (a : α) : min a a = a := by simp [min_def]

lemma min_eq_left {a b : α} (h : a ≤ b) : min a b = a := by
  apply Eq.symm; apply eq_min (le_refl _) h; intros; assumption

lemma min_eq_right {a b : α} (h : b ≤ a) : min a b = b := by
  rw [min_comm]
  exact min_eq_left h

lemma eq_max {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) (h₃ : ∀{d}, a ≤ d → b ≤ d → c ≤ d) :
    c = max a b :=
le_antisymm (h₃ (le_max_left a b) (le_max_right a b)) (max_le h₁ h₂)

lemma max_comm (a b : α) : max a b = max b a :=
  eq_max (le_max_right a b) (le_max_left a b) (λ {_} h₁ h₂ => max_le h₂ h₁)

lemma max_assoc (a b c : α) : max (max a b) c = max a (max b c) := by
  apply eq_max
  · apply le_trans; apply le_max_left a b; apply le_max_left
  · apply max_le; apply le_trans; apply le_max_right a b; apply le_max_left; apply le_max_right
  · intros d h₁ h₂; apply max_le; apply max_le h₁; apply le_trans (le_max_left _ _) h₂
    apply le_trans (le_max_right _ _) h₂

lemma max_left_comm : ∀ (a b c : α), max a (max b c) = max b (max a c) :=
  left_comm max (@max_comm α _) (@max_assoc α _)

@[simp] lemma max_self (a : α) : max a a = a := by simp [max_def]

lemma max_eq_left {a b : α} (h : b ≤ a) : max a b = a := by
  apply Eq.symm; apply eq_max (le_refl _) h; intros; assumption

lemma max_eq_right {a b : α} (h : a ≤ b) : max a b = b := by
  rw [←max_comm b a]; exact max_eq_left h

/- these rely on lt_of_lt -/

lemma min_eq_left_of_lt {a b : α} (h : a < b) : min a b = a :=
  min_eq_left (le_of_lt h)

lemma min_eq_right_of_lt {a b : α} (h : b < a) : min a b = b :=
  min_eq_right (le_of_lt h)

lemma max_eq_left_of_lt {a b : α} (h : b < a) : max a b = a :=
  max_eq_left (le_of_lt h)

lemma max_eq_right_of_lt {a b : α} (h : a < b) : max a b = b :=
  max_eq_right (le_of_lt h)

/- these use the fact that it is a linear ordering -/

lemma lt_min {a b c : α} (h₁ : a < b) (h₂ : a < c) : a < min b c :=
  Or.elim (le_or_gt b c)
    (λ h : b ≤ c => by rwa [min_eq_left h])
    (λ h : b > c => by rwa [min_eq_right_of_lt h])

lemma max_lt {a b c : α} (h₁ : a < c) (h₂ : b < c) : max a b < c :=
  Or.elim (le_or_gt a b)
    (λ h : a ≤ b => by rwa [max_eq_right h])
    (λ h : a > b => by rwa [max_eq_left_of_lt h])

end
