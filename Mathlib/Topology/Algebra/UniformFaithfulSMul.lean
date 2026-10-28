/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.Algebra.Algebra.IsSimpleRing
public import Mathlib.Topology.Algebra.UniformField

/-!
# Faithfulness of Scalar Multiplication on Completions

Given a field `K` with an `R`-scalar multiplication, if the scalar action of `R` on `K`
is faithful, then the induced scalar action of `R` on the completion of `K`
is also faithful.
-/

public section

instance UniformSpace.Completion.faithfulSMul {R K : Type*} [CommSemiring R] [Field K] [Algebra R K]
    [UniformSpace K] [UniformContinuousConstSMul R K] [IsUniformAddGroup K]
    [IsTopologicalRing K] [Nontrivial (Completion K)] [FaithfulSMul R K] :
    FaithfulSMul R (Completion K) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact (FaithfulSMul.algebraMap_injective K _).comp (FaithfulSMul.algebraMap_injective R K)
