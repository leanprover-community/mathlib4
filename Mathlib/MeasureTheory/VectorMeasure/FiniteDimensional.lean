/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Decomposition of a vector measure in a finite-dimensional `ℝ`-vector space with respect to a basis

## Main results

* `coeff` : for a `ℝ`-basis `b` in an `R`-vector space `V` and a `V`-valued vector measure `μ`, one
  has the equality `μ E = ∑ i, a i E • b i` for each `E : Set X`. Then the coefficients `a i E` is
  an `ℝ`-valued vector measure (`SignedMeasure`), which we call `μ.coeff b`.
* `sum_coeff_smul_eq` : the characterizing equality `∑ i, (μ.coeff b i E) • b i = μ E ` for `coeff`.
* `sum_toSpanSingleton_coeff_eq` : `μ` as a linear combination of vector measures.

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
    μ.coeff b i E = b.coord i (μ E) := by simp [coeff]

theorem sum_coeff_smul_eq (b : Basis ι ℝ V) (μ : VectorMeasure X V) (E : Set X) :
    ∑ i, (μ.coeff b i E) • b i = μ E := by
  simp

theorem sum_toSpanSingleton_coeff_eq (b : Basis ι ℝ V) (μ : VectorMeasure X V) :
    ∑ i, mapRangeₗ (toSpanSingleton ℝ V (b i))
      ((toSpanSingleton ℝ V (b i)).continuous_of_finiteDimensional) (μ.coeff b i) = μ := by
  ext; simp

end MeasureTheory.VectorMeasure
