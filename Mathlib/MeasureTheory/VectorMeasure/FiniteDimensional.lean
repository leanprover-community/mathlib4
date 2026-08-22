/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Decomposition of a vector measure in a finite-dimensional `ℝ`-vector space with respect to a basis

## Main results

* `coord` : for a `𝕜`-Schauder basis `b` in a `𝕜`-vector space `V` and a `V`-valued vector measure
  `μ`, one has the equality `μ E = ∑ i, a i E • b i` for each `E : Set X`. Then the coordinate
  `a i E` is a `𝕜`-valued vector measure, which we call `μ.coord b i`.
* `sum_toSpanSingleton_coord_eq` : `μ` as a linear combination of vector measures.

-/

public section

open Module ContinuousLinearMap

namespace MeasureTheory.VectorMeasure

variable {X : Type*} {mX : MeasurableSpace X}
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {ι : Type*} {L : SummationFilter ι}

/-- For a Schauder basis `b` in `V` indexed by `ι`, `i : ι` and a vector measure `μ`, `μ.coord b i`
gives the `i`-th component of `μ` as a `𝕜`-valued vector measure. -/
protected noncomputable def coord (b : GeneralSchauderBasis ι 𝕜 V L) (μ : VectorMeasure X V)
    (i : ι) : VectorMeasure X 𝕜 := μ.mapRangeL (b.coord i)

@[simp]
lemma coord_apply (b : GeneralSchauderBasis ι 𝕜 V L) (μ : VectorMeasure X V) (i : ι) (E : Set X) :
    μ.coord b i E = b.coord i (μ E) := by simp [VectorMeasure.coord]

lemma hasSum_coord (b : GeneralSchauderBasis ι 𝕜 V L) (μ : VectorMeasure X V) (E : Set X) :
    HasSum (fun i ↦ μ.coord b i E • b i)  (μ E) L := by simpa using b.expansion _

lemma sum_coord_toUnconditionalSchauderBasis [Finite ι] [CompleteSpace 𝕜] (b : Basis ι 𝕜 V)
    (μ : VectorMeasure X V) (E : Set X) :
    letI : Fintype ι := Fintype.ofFinite ι
    ∑ i, μ.coord b.toUnconditionalSchauderBasis i E • b i = μ E := by simp

theorem eq_sum_toSpanSingleton_coord [CompleteSpace 𝕜] [Fintype ι] [L.LeAtTop] [L.NeBot]
    (b : GeneralSchauderBasis ι 𝕜 V L) (μ : VectorMeasure X V) :
    μ = ∑ i, (μ.coord b i).mapRangeL (toSpanSingleton 𝕜 (b i)) := by ext; simp

end MeasureTheory.VectorMeasure
