/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Star

/-! # `unitary R` is a topological group

In a topological star monoid, the unitary group is a topological group.
-/

variable {R : Type*} [Monoid R] [StarMul R] [TopologicalSpace R]

instance [ContinuousMul R] : ContinuousMul (unitary R) where
  continuous_mul := continuous_induced_rng.mpr <| by fun_prop

instance [ContinuousStar R] : ContinuousStar (unitary R) where
  continuous_star := continuous_induced_rng.mpr <| by fun_prop

instance [ContinuousStar R] : ContinuousInv (unitary R) where
  continuous_inv := by simp_rw [← unitary.star_eq_inv]; fun_prop

instance [ContinuousMul R] [ContinuousStar R] : IsTopologicalGroup (unitary R) where
