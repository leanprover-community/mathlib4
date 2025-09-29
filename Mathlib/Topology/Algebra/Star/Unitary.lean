/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Algebra.Monoid

@[expose] public section

/-! # `unitary R` is a topological group

In a topological star monoid, the unitary group is a topological group.
-/

variable {R : Type*} [Monoid R] [StarMul R] [TopologicalSpace R]

instance [ContinuousStar R] : ContinuousStar (unitary R) where
  continuous_star := continuous_induced_rng.mpr continuous_subtype_val.star

instance [ContinuousStar R] : ContinuousInv (unitary R) where
  continuous_inv := continuous_star

instance [ContinuousMul R] [ContinuousStar R] : IsTopologicalGroup (unitary R) where
