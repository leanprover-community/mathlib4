/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Topology.Algebra.UniformField

/-!
# Faithful Scalar Multiplication Induces Faithful Scalar Multiplication on Completion

If the `R`-scalar multiplication on a field `K` is faithful, then its canonical
induced `R`-scalar multiplication on `Completion K` is also faithful.
-/

@[expose] public section

-- `[T0Space K]` can be replace by any condition that implies `Nontrivial (Completion K)`
instance UniformSpace.Completion.faithfulSMul {R K : Type*} [CommSemiring R] [Field K] [Algebra R K]
    [UniformSpace K] [UniformContinuousConstSMul R K] [IsUniformAddGroup K]
    [IsTopologicalRing K] [T0Space K] [FaithfulSMul R K] :
    FaithfulSMul R (Completion K) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact (FaithfulSMul.algebraMap_injective K _).comp (FaithfulSMul.algebraMap_injective R K)
