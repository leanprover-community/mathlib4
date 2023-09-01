/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Data.Polynomial.Degree.Definitions

/-!
###  Simple lemmas about `natDegree`

The lemmas in this section all have the form `natDegree <some form of cast> ≤ 0`.
Their proofs are weakenings of the stronger lemmas `natDegree <same> = 0`.
These are the lemmas called by `compute_degree_le` on (almost) all the leaves of its recursion.
-/

open Polynomial

namespace Mathlib.Tactic.ComputeDegree

section leaf_lemmas

variable {R : Type*}

section semiring
variable [Semiring R]

theorem natDegree_C_le (a : R) : natDegree (C a) ≤ 0 := (natDegree_C a).le
theorem natDegree_nat_cast_le (n : ℕ) : natDegree (n : R[X]) ≤ 0 := (natDegree_nat_cast _).le
theorem natDegree_zero_le : natDegree (0 : R[X]) ≤ 0 := natDegree_zero.le
theorem natDegree_one_le : natDegree (1 : R[X]) ≤ 0 := natDegree_one.le

end semiring

variable [Ring R] in
theorem natDegree_int_cast_le (n : ℤ) : natDegree (n : R[X]) ≤ 0 := (natDegree_int_cast _).le

end leaf_lemmas

end Mathlib.Tactic.ComputeDegree
