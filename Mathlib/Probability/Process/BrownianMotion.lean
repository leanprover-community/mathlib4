/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Brownian Motion

In this file we will eventually define Brownian Motion using the Kolmogorov extension theorem, and
the Kolmogorov-Chentsov criterion for a continuous modification.

At the moment, it only contains positive semidefiniteness of the covariance matrices for the
finite-dimensional distributions.

## Main definition

## Main results

* `Probability.BrownianMotion.CovMatrix.posSemidef`:
The matrix with `(s t : ℝ) ↦ s ∧ t` is positive semidefinite.

-/

section covariance

open MeasureTheory NNReal Matrix Set

variable {n : Type*}
variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

namespace MeasureTheory

namespace L2

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- In an `L2` space, the matrix of intersections of pairs of sets is positive semi-definite. -/
theorem posSemidef_interMatrix [Fintype n] (μ : Measure α) (v : n → (Set α))
    (hv₁ : ∀ j, MeasurableSet (v j)) (hv₂ : ∀ j, μ (v j) ≠ ⊤) :
      PosSemidef (of fun i j : n ↦ μ.real (v i ∩ v j)) := by
  conv =>
    right; right; intro i j;
    rw [← inner_indicatorConstLp_one_indicatorConstLp_one (hv₁ i) (hv₁ j) (hv₂ i) (hv₂ j)]
  rw [← gram]
  exact gram_posSemidef

end L2

end MeasureTheory

namespace Probability

namespace BrownianMotion

/-- The covariance matrix of Brownian Motion. -/
def covMatrix (t : n → ℝ≥0) : Matrix n n ℝ := fun i j ↦ min (t i) (t j)

namespace CovMatrix

/-- The covariance matrix of Brownian Motion is positive semi-definite. -/
theorem posSemidef [Fintype n] (t : n → ℝ≥0) :
    PosSemidef (covMatrix t) := by
  let v : n → (Set ℝ) := fun i ↦ Set.Icc 0 (t i)
  have h : covMatrix t = fun i j ↦ (volume.real ((Icc 0 (t i).toReal) ∩ (Icc 0 (t j)))) := by
    simp [Set.Icc_inter_Icc]
    rfl
  apply h ▸ L2.posSemidef_interMatrix _ v  (fun j ↦ measurableSet_Icc)
    (fun j ↦ IsCompact.measure_ne_top isCompact_Icc)

end CovMatrix

end BrownianMotion

end Probability

end covariance
