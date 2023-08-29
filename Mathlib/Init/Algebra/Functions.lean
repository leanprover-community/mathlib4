/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Init.Algebra.Order

#align_import init.algebra.functions from "leanprover-community/lean"@"c2bcdbcbe741ed37c361a30d38e179182b989f76"

universe u

section

open Decidable

variable {α : Type u} [LinearOrder α]

theorem min_def (a b : α) : min a b = if a ≤ b then a else b := by
  rw [LinearOrder.min_def a]
  -- 🎉 no goals
#align min_def min_def

theorem max_def (a b : α) : max a b = if a ≤ b then b else a := by
  rw [LinearOrder.max_def a]
  -- 🎉 no goals
#align max_def max_def

theorem min_le_left (a b : α) : min a b ≤ a := by
  -- porting note: no `min_tac` tactic
  if h : a ≤ b
  then simp [min_def, if_pos h, le_refl]
  else simp [min_def, if_neg h]; exact le_of_not_le h
#align min_le_left min_le_left

theorem min_le_right (a b : α) : min a b ≤ b := by
  -- porting note: no `min_tac` tactic
  if h : a ≤ b
  then simp [min_def, if_pos h]; exact h
  else simp [min_def, if_neg h, le_refl]
#align min_le_right min_le_right

theorem le_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b := by
  -- porting note: no `min_tac` tactic
  if h : a ≤ b
  then simp [min_def, if_pos h]; exact h₁
  else simp [min_def, if_neg h]; exact h₂
#align le_min le_min

theorem le_max_left (a b : α) : a ≤ max a b := by
  -- porting note: no `min_tac` tactic
  if h : a ≤ b
  then simp [max_def, if_pos h]; exact h
  else simp [max_def, if_neg h, le_refl]
#align le_max_left le_max_left

theorem le_max_right (a b : α) : b ≤ max a b := by
  -- porting note: no `min_tac` tactic
  if h : a ≤ b
  then simp [max_def, if_pos h, le_refl]
  else simp [max_def, if_neg h]; exact le_of_not_le h
#align le_max_right le_max_right

theorem max_le {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c := by
  -- porting note: no `min_tac` tactic
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
                    -- ⊢ min a b ≤ a
                                       -- 🎉 no goals
  · apply le_min; apply le_trans; apply min_le_left; apply min_le_right; apply min_le_right
    -- ⊢ min (min a b) c ≤ b
                                  -- ⊢ min a b ≤ b
                                                     -- ⊢ min (min a b) c ≤ c
                                                                         -- 🎉 no goals
  · intro d h₁ h₂; apply le_min; apply le_min h₁; apply le_trans h₂; apply min_le_left
    -- ⊢ d ≤ min (min a b) c
                   -- ⊢ d ≤ min a b
                                 -- ⊢ d ≤ b
                                                  -- ⊢ min b c ≤ b
                                                                     -- ⊢ d ≤ c
    apply le_trans h₂; apply min_le_right
    -- ⊢ min b c ≤ c
                       -- 🎉 no goals
#align min_assoc min_assoc

theorem min_left_comm : ∀ a b c : α, min a (min b c) = min b (min a c) :=
  left_comm (@min α _) (@min_comm α _) (@min_assoc α _)
#align min_left_comm min_left_comm

@[simp]
theorem min_self (a : α) : min a a = a := by simp [min_def]
                                             -- 🎉 no goals
#align min_self min_self

theorem min_eq_left {a b : α} (h : a ≤ b) : min a b = a := by
  apply Eq.symm; apply eq_min (le_refl _) h; intros; assumption
  -- ⊢ a = min a b
                 -- ⊢ ∀ {d : α}, d ≤ a → d ≤ b → d ≤ a
                                             -- ⊢ d✝ ≤ a
                                                     -- 🎉 no goals
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
                    -- ⊢ max a b ≤ max (max a b) c
                                           -- 🎉 no goals
  · apply max_le; apply le_trans; apply le_max_right a b; apply le_max_left; apply le_max_right
    -- ⊢ b ≤ max (max a b) c
                                  -- ⊢ max a b ≤ max (max a b) c
                                                          -- ⊢ c ≤ max (max a b) c
                                                                             -- 🎉 no goals
  · intro d h₁ h₂; apply max_le; apply max_le h₁; apply le_trans (le_max_left _ _) h₂
    -- ⊢ max (max a b) c ≤ d
                   -- ⊢ max a b ≤ d
                                 -- ⊢ b ≤ d
                                                  -- ⊢ c ≤ d
    apply le_trans (le_max_right _ _) h₂
    -- 🎉 no goals
#align max_assoc max_assoc

theorem max_left_comm : ∀ a b c : α, max a (max b c) = max b (max a c) :=
  left_comm (@max α _) (@max_comm α _) (@max_assoc α _)
#align max_left_comm max_left_comm

@[simp]
theorem max_self (a : α) : max a a = a := by simp [max_def]
                                             -- 🎉 no goals
#align max_self max_self

theorem max_eq_left {a b : α} (h : b ≤ a) : max a b = a := by
  apply Eq.symm; apply eq_max (le_refl _) h; intros; assumption
  -- ⊢ a = max a b
                 -- ⊢ ∀ {d : α}, a ≤ d → b ≤ d → a ≤ d
                                             -- ⊢ a ≤ d✝
                                                     -- 🎉 no goals
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
  -- porting note: no `min_tac` tactic
  Or.elim (le_or_gt b c)
    (λ h : b ≤ c => by rwa [min_eq_left h])
                       -- 🎉 no goals
    (λ h : b > c => by rwa [min_eq_right_of_lt h])
                       -- 🎉 no goals
#align lt_min lt_min

theorem max_lt {a b c : α} (h₁ : a < c) (h₂ : b < c) : max a b < c :=
  -- porting note: no `min_tac` tactic
  Or.elim (le_or_gt a b)
    (λ h : a ≤ b => by rwa [max_eq_right h])
                       -- 🎉 no goals
    (λ h : a > b => by rwa [max_eq_left_of_lt h])
                       -- 🎉 no goals
#align max_lt max_lt

end
