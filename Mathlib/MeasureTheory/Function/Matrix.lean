/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Matrices as a measurable space

In this file we provide a measurable space structure on matrices (the one induced by the product
measurable space). We also provide a Borel space structure on matrices when the underlying type is
a second countable topological space.

## Main results
* `Matrix.measurable_cfcSqrt_matrix`: the function `CFC.sqrt` on real matrices is measurable.
-/

@[expose] public section

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {m n α : Type*} [MeasurableSpace α]

instance : MeasurableSpace (Matrix m n α) := inferInstanceAs <| MeasurableSpace (m → n → α)

instance [Countable m] [Countable n] [TopologicalSpace α] [SecondCountableTopology α]
    [BorelSpace α] : BorelSpace (Matrix m n α) := inferInstanceAs <| BorelSpace (m → n → α)

open Classical in
@[fun_prop]
lemma measurable_cfcSqrt_matrix [Fintype m] :
    Measurable (CFC.sqrt : Matrix m m ℝ → Matrix m m ℝ) := by
  have h_measurable : MeasurableSet {S : Matrix m m ℝ | 0 ≤ S} := by
    apply IsClosed.measurableSet
    convert IsClosed.isClosed_le (α := Matrix m m ℝ) (f := 0) (g := id) isClosed_univ ?_ ?_
    · simp
    · exact continuous_const.continuousOn
    · exact continuous_id.continuousOn
  convert CFC.continuousOn_sqrt.measurable_piecewise continuousOn_const h_measurable using 1
  rotate_left
  · exact 0
  · ext S : 1
    by_cases hS : 0 ≤ S
    · simp [hS]
    · simp [hS, CFC.sqrt_of_not_nonneg]

end Matrix
