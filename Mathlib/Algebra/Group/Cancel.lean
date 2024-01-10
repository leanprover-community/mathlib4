/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Function.Basic

/-!
# Facts about injectivity of cancellative multiplication.
-/

#align_import algebra.group.defs from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

universe u v w

open Function

variable {G : Type*} [Mul G]

section IsLeftCancelMul

variable [IsLeftCancelMul G] {a b c : G}

@[to_additive]
theorem mul_right_injective (a : G) : Injective (a * ·) := fun _ _ ↦ mul_left_cancel
#align mul_right_injective mul_right_injective
#align add_right_injective add_right_injective

@[to_additive (attr := simp)]
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
  (mul_right_injective a).eq_iff
#align mul_right_inj mul_right_inj
#align add_right_inj add_right_inj

@[to_additive]
theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
  (mul_right_injective a).ne_iff
#align mul_ne_mul_right mul_ne_mul_right
#align add_ne_add_right add_ne_add_right

end IsLeftCancelMul

section IsRightCancelMul

variable [IsRightCancelMul G] {a b c : G}

@[to_additive]
theorem mul_left_injective (a : G) : Function.Injective (· * a) := fun _ _ ↦ mul_right_cancel
#align mul_left_injective mul_left_injective
#align add_left_injective add_left_injective

@[to_additive (attr := simp)]
theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
  (mul_left_injective a).eq_iff
#align mul_left_inj mul_left_inj
#align add_left_inj add_left_inj

@[to_additive]
theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c :=
  (mul_left_injective a).ne_iff
#align mul_ne_mul_left mul_ne_mul_left
#align add_ne_add_left add_ne_add_left

end IsRightCancelMul
