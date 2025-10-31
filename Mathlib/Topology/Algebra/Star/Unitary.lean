/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Bhavik Mehta
-/
import Mathlib.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Star
import Mathlib.Topology.Algebra.Monoid

/-! # Topological properties of the unitary (sub)group

* In a topological star monoid `R`, `unitary R` is a topological group
* In a topological star monoid `R` which is T1, `unitary R` is closed as a subset of `R`.
-/

variable {R : Type*} [Monoid R] [StarMul R] [TopologicalSpace R]

instance [ContinuousStar R] : ContinuousStar (unitary R) where
  continuous_star := continuous_induced_rng.mpr continuous_subtype_val.star

instance [ContinuousStar R] : ContinuousInv (unitary R) where
  continuous_inv := continuous_star

instance [ContinuousMul R] [ContinuousStar R] : IsTopologicalGroup (unitary R) where

lemma isClosed_unitary [T1Space R] [ContinuousStar R] [ContinuousMul R] :
    IsClosed (unitary R : Set R) := by
  let f (u : R) : R × R := (star u * u, u * star u)
  have hf : f ⁻¹' {(1, 1)} = unitary R := by ext u; simp [f, Unitary.mem_iff]
  rw [← hf]
  exact isClosed_singleton.preimage (by fun_prop)
