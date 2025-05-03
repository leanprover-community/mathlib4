/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Pfaffelhuber
-/

import Mathlib.LinearAlgebra.Matrix.Gram

/-! # Brownian Motion

In this file we define Brownian Motion using the Kolmogorov extension theorem, and the Kolmogorov-Chentsov criterion for a continuous modification.

## Main definition

*
## Main results

*
-/

section covariance

/- Here, we describe the covariance matrix of the finite dimensional distributions of
Brownian Motion, i.e. `s t ↦ s ∧ t`. Identifying this as a Gram Matrix gives that it is
positive semi-definite. This section will be moved to the section on stochastic processes once
we define Brownian Motion.
-/

variable {E n : Type*}
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open MeasureTheory L2 NNReal ENNReal

namespace brownianMotion

/-- This is the covariance matrix of Brownian Motion. -/
def covMatrix (t : n → ℝ≥0) : Matrix n n ℝ := fun i j ↦ ((t i) ⊓ (t j)).toReal

namespace covMatrix

theorem posSemidef [Fintype n] (t : n → ℝ≥0) :
    PosSemidef (covMatrix t) := by
  let v : n → (Set ℝ) := fun i ↦ Set.Icc 0 (t i)
  have h : covMatrix t = interMatrix volume (fun i ↦ Set.Icc 0 (t i).toReal) := by
    ext i j
    rw [covMatrix, interMatrix, Set.Icc_inter_Icc]
    simp
  apply h ▸ posSemidef_interMatrix _ v  (fun j ↦ measurableSet_Icc)
    (fun j ↦ IsCompact.measure_ne_top isCompact_Icc)

end covMatrix

end brownianMotion

end covariance
