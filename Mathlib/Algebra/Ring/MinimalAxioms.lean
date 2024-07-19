/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Minimal Axioms for a Ring

This file defines constructors to define a `Ring` or `CommRing` structure on a Type, while proving
a minimum number of equalities.

## Main Definitions

* `Ring.ofMinimalAxioms`: Define a `Ring` structure on a Type by proving a minimized set of axioms
* `CommRing.ofMinimalAxioms`: Define a `CommRing` structure on a Type by proving a minimized set of
  axioms

-/

universe u

/-- Define a `Ring` structure on a Type by proving a minimized set of axioms.
Note that this uses the default definitions for `npow`, `nsmul`, `zsmul` and `sub`
See note [reducible non-instances]. -/
abbrev Ring.ofMinimalAxioms {R : Type u}
    [Add R] [Mul R] [Neg R] [Zero R] [One R]
    (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
    (zero_add : ∀ a : R, 0 + a = a)
    (add_left_neg : ∀ a : R, -a + a = 0)
    (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
    (one_mul : ∀ a : R, 1 * a = a)
    (mul_one : ∀ a : R, a * 1 = a)
    (left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c)
    (right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c) : Ring R :=
  letI := AddGroup.ofLeftAxioms add_assoc zero_add add_left_neg
  haveI add_comm : ∀ a b, a + b = b + a := by
    intro a b
    have h₁ : (1 + 1 : R) * (a + b) = a + (a + b) + b := by
      rw [left_distrib]
      simp only [right_distrib, one_mul, add_assoc]
    have h₂ : (1 + 1 : R) * (a + b) = a + (b + a) + b := by
      rw [right_distrib]
      simp only [left_distrib, one_mul, add_assoc]
    have := h₁.symm.trans h₂
    rwa [add_left_inj, add_right_inj] at this
  haveI zero_mul : ∀ a, (0 : R) * a = 0 := fun a => by
    have : 0 * a = 0 * a + 0 * a :=
      calc 0 * a = (0 + 0) * a := by rw [zero_add]
      _ = 0 * a + 0 * a := by rw [right_distrib]
    rwa [self_eq_add_right] at this
  haveI mul_zero : ∀ a, a * (0 : R) = 0 := fun a => by
    have : a * 0 = a * 0 + a * 0 :=
      calc a * 0 = a * (0 + 0) := by rw [zero_add]
      _ = a * 0 + a * 0 := by rw [left_distrib]
    rwa [self_eq_add_right] at this
  { add_comm := add_comm
    left_distrib := left_distrib
    right_distrib := right_distrib
    zero_mul := zero_mul
    mul_zero := mul_zero
    mul_assoc := mul_assoc
    one_mul := one_mul
    mul_one := mul_one
    add_left_neg := add_left_neg
    zsmul := (· • ·) }

/-- Define a `CommRing` structure on a Type by proving a minimized set of axioms.
Note that this uses the default definitions for `npow`, `nsmul`, `zsmul` and `sub`
See note [reducible non-instances]. -/
abbrev CommRing.ofMinimalAxioms {R : Type u}
    [Add R] [Mul R] [Neg R] [Zero R] [One R]
    (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
    (zero_add : ∀ a : R, 0 + a = a)
    (add_left_neg : ∀ a : R, -a + a = 0)
    (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
    (mul_comm : ∀ a b : R, a * b = b * a)
    (one_mul : ∀ a : R, 1 * a = a)
    (left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c) : CommRing R :=
  haveI mul_one : ∀ a : R, a * 1 = a := fun a => by
    rw [mul_comm, one_mul]
  haveI right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c := fun a b c => by
    rw [mul_comm, left_distrib, mul_comm, mul_comm b c]
  letI := Ring.ofMinimalAxioms add_assoc zero_add add_left_neg mul_assoc
    one_mul mul_one left_distrib right_distrib
  { mul_comm := mul_comm }
