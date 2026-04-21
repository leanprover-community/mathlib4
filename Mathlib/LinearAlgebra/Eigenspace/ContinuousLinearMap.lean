/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Topology.Algebra.Module.LinearMap

/-!
# Eigenspaces of continuous linear maps

This file provides some basic properties of eigenspaces of continuous linear maps.

These results are in a separate file to avoid heavy topology imports.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace ContinuousLinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [T0Space M]
  [ContinuousConstSMul R M] [IsTopologicalAddGroup M] (f : M →L[R] M) (μ : R) (n : ℕ)

open Module End

instance isClosed_genEigenspace : IsClosed (genEigenspace (f : End R M) μ n : Set M) := by
  rw [genEigenspace_nat, one_eq_id, ← coe_id, ← coe_smul, ← coe_sub, ← coe_pow]
  apply isClosed_ker

instance isClosed_eigenspace : IsClosed (eigenspace (f : End R M) μ : Set M) :=
  isClosed_genEigenspace f μ 1

end ContinuousLinearMap
