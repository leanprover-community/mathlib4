/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Data.Polynomial.Degree.Definitions

/-!
###  Simple lemmas about `natDegree` and `degree`

The lemmas in this section deduce inequalities of the form `natDegree f ≤ d` and `degree f ≤ d`,
using inequalities of the same shape.
This allows a recursive application of the `compute_degree_le` tactic on a goal,
and on all the resulting subgoals.
-/

open Polynomial

namespace Mathlib.Tactic.ComputeDegree

section mylemmas

variable {R : Type _}

section semiring
variable [Semiring R]

theorem add {a b : Nat} {f g : R[X]} (hf : natDegree f ≤ a) (hg : natDegree g ≤ b) :
    natDegree (f + g) ≤ max a b :=
(f.natDegree_add_le g).trans $ max_le_max ‹_› ‹_›

theorem mul {a b : Nat} {f g : R[X]} (hf : natDegree f ≤ a) (hg : natDegree g ≤ b) :
    natDegree (f * g) ≤ a + b :=
natDegree_mul_le.trans $ add_le_add ‹_› ‹_›

theorem pow {a : Nat} (b : Nat) {f : R[X]} (hf : natDegree f ≤ a) :
    natDegree (f ^ b) ≤ b * a :=
natDegree_pow_le.trans (Nat.mul_le_mul rfl.le ‹_›)

theorem C_le (a : R) : natDegree (C a) ≤ 0 := (natDegree_C a).le
theorem nat_cast_le (n : Nat) : natDegree (n : R[X]) ≤ 0 := (natDegree_nat_cast _).le
theorem zero_le : natDegree (0 : R[X]) ≤ 0 := natDegree_zero.le
theorem one_le : natDegree (1 : R[X]) ≤ 0 := natDegree_one.le

theorem addD {a b : WithBot Nat} {f g : R[X]} (hf : degree f ≤ a) (hg : degree g ≤ b) :
    degree (f + g) ≤ max a b :=
(f.degree_add_le g).trans $ max_le_max ‹_› ‹_›

theorem mulD {a b : WithBot Nat} {f g : R[X]} (hf : degree f ≤ a) (hg : degree g ≤ b) :
    degree (f * g) ≤ a + b :=
(f.degree_mul_le _).trans $ add_le_add ‹_› ‹_›

theorem powD {a : WithBot Nat} (b : Nat) {f : R[X]} (hf : degree f ≤ a) :
    degree (f ^ b) ≤ b * a := by
  apply (degree_pow_le _ _).trans
  rw [nsmul_eq_mul]
  induction b with
    | zero => simp [degree_one_le]
    | succ n hn =>
      rw [Nat.cast_succ, add_mul, add_mul, one_mul, one_mul]
      exact (add_le_add_left hf _).trans (add_le_add_right hn _)

theorem nat_cast_leD (n : Nat) : degree (n : R[X]) ≤ 0 := degree_le_of_natDegree_le (by simp)
theorem zero_leD : degree (0 : R[X]) ≤ 0 := natDegree_eq_zero_iff_degree_le_zero.mp rfl

end semiring

section ring
variable [Ring R]

theorem neg {a : Nat} {f : R[X]} (hf : natDegree f ≤ a) : natDegree (- f) ≤ a :=
(natDegree_neg f).le.trans ‹_›

theorem sub {a b : Nat} {f g : R[X]} (hf : natDegree f ≤ a) (hg : natDegree g ≤ b) :
    natDegree (f - g) ≤ max a b :=
(f.natDegree_sub_le g).trans $ max_le_max ‹_› ‹_›

theorem int_cast_le (n : Int) : natDegree (n : R[X]) ≤ 0 := (natDegree_int_cast _).le

theorem negD {a : WithBot Nat} {f : R[X]} (hf : degree f ≤ a) : degree (- f) ≤ a :=
(degree_neg f).le.trans ‹_›

theorem subD {a b : WithBot Nat} {f g : R[X]} (hf : degree f ≤ a) (hg : degree g ≤ b) :
    degree (f - g) ≤ max a b :=
(f.degree_sub_le g).trans $ max_le_max ‹_› ‹_›

theorem int_cast_leD (n : Int) : degree (n : R[X]) ≤ 0 := degree_le_of_natDegree_le (by simp)

end ring

end mylemmas

end Mathlib.Tactic.ComputeDegree
