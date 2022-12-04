/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Data.Nat.Basic

/-!
# Cast of natural numbers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`nat.cast`).

This is an ad-hoc port file.

## Main declarations

* `cast_add_monoid_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.
-/

section Semiring

@[simp, norm_cast]
lemma Nat.cast_mul [Semiring R] {m n : ℕ} : (m * n).cast = (m.cast * n.cast : R) := by
  induction n generalizing m <;> simp_all [mul_succ, mul_add]

@[simp, norm_cast]
lemma Nat.cast_pow [Semiring R] {m n : ℕ} : (m ^ n).cast = (m.cast ^ n : R) := by
  induction n generalizing m <;> simp_all [Nat.pow_succ', _root_.pow_succ'', pow_zero]

theorem Nat.cast_commute [Semiring α] (n : ℕ) (x : α) : Commute (↑n) x := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Commute.zero_left x
  | succ n ihn => rw [Nat.cast_succ]; exact ihn.add_left (Commute.one_left x)

end Semiring

@[simp] lemma Nat.cast_id : (Nat.cast n : ℕ) = n := rfl
