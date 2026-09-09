/-
Copyright (c) 2026 metakunt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Ring.GrindInstances


/-!
# Some basic algebraic results regarding reduced semirings.
-/

variable {R : Type*} [Semiring R] [IsReduced R]

variable {a b : R}

public section

namespace IsReduced

/-- In a reduced semiring, annihilation is symmetric. -/
theorem mul_eq_zero_comm (h : a * b = 0) : b * a = 0 := by
  refine IsReduced.eq_zero _ ⟨2, ?_⟩
  grind => have : (b * a) ^ 2 = b * (a * b) * a

/-- A reduced semiring is semicommutative: `a * b = 0` implies `a * r * b = 0` for all `r`. -/
theorem mul_mid_eq_zero (h : a * b = 0) (r : R) : a * r * b = 0 := by
  have hba : b * a = 0 := IsReduced.mul_eq_zero_comm h
  refine IsReduced.eq_zero _ ⟨2, ?_⟩
  have h2 : (a * r * b) ^ 2 = a * r * (b * a) * (r * b) := by simp [pow_two, mul_assoc]
  simp [h2, hba]

/-- In a reduced semiring, `a * b * b = 0` implies `a * b = 0`. -/
theorem mul_eq_zero_of_mul_sq_eq_zero (h : a * b * b = 0) : a * b = 0 := by
  have h2 : b * (a * b) = 0 := IsReduced.mul_eq_zero_comm (a := a * b) (b := b) h
  refine IsReduced.eq_zero _ ⟨2, ?_⟩
  simp [pow_two, mul_assoc, h2]

end IsReduced

end
