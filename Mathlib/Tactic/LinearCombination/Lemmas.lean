/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# Lemmas for the linear_combination tactic

These should not be used directly in user code.
-/

namespace Mathlib.Tactic.LinearCombination
open Lean

variable {α : Type*} {a a' a₁ a₂ b b' b₁ b₂ c : α}

theorem add_pf [Add α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂ := p₁ ▸ p₂ ▸ rfl
theorem pf_mul_c [Mul α] (p : a = b) (c : α) : a * c = b * c := p ▸ rfl
theorem c_mul_pf [Mul α] (p : b = c) (a : α) : a * b = a * c := p ▸ rfl
theorem pf_div_c [Div α] (p : a = b) (c : α) : a / c = b / c := p ▸ rfl

theorem eq_of_sub [AddGroup α] (p : (a:α) = b) (H : (a' - b') - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; rwa [sub_eq_zero, p] at H

theorem eq_of_add [Add α] [IsRightCancelAdd α] (p : (a:α) = b) (H : a' + b = b' + a) : a' = b' := by
  rw [p] at H
  exact add_right_cancel H

theorem eq_of_add_pow [Ring α] [NoZeroDivisors α] (n : ℕ) (p : (a:α) = b)
    (H : (a' - b')^n - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; apply pow_eq_zero (n := n); rwa [sub_eq_zero, p] at H

end Mathlib.Tactic.LinearCombination
