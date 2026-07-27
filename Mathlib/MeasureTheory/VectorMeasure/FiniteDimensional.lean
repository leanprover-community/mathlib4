/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# TODO

## Main results

TODO
-/

public section

open Module LinearMap
open scoped ENNReal NNReal

namespace MeasureTheory.VectorMeasure

variable {X : Type*} {mX : MeasurableSpace X}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! For a basis `b` in `V` indexed by `ι`, `i : ι` and a vector measure `μ`, `μ.coeff b i` gives the
`i`-th component of `μ` as a `ℝ`-valued vector measure, which is `SignedMeasure V`. -/
noncomputable def coeff (b : Basis ι ℝ V) (μ : VectorMeasure X V) : ι → SignedMeasure X :=
  fun i ↦ mapRangeₗ (b.dualBasis i) (b.dualBasis i).continuous_of_finiteDimensional μ

@[simp]
lemma coeff_apply (b : Basis ι ℝ V) (μ : VectorMeasure X V) (i : ι) (E : Set X) :
    μ.coeff b i E = b.dualBasis i (μ E) := by simp [coeff]

theorem sum_coeff_smul_eq (b : Basis ι ℝ V) (μ : VectorMeasure X V) :
    ∑ i, mapRangeₗ (toSpanSingleton ℝ V (b i))
      ((toSpanSingleton ℝ V (b i)).continuous_of_finiteDimensional) (μ.coeff b i) = μ := by
  ext; simp

end MeasureTheory.VectorMeasure
