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

* `Probability.BrownianMotion.covMatrix.posSemidef`:
The matrix with `(s t : ℝ) ↦ s ∧ t` is positive semidefinite.

-/

section covariance

open MeasureTheory NNReal Matrix Set

variable {n : Type*}
variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

namespace MeasureTheory

namespace L2

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

lemma innerProduct_eq_inter {v w : (Set α)} (hv₁ : MeasurableSet v)
  (hw₁ : MeasurableSet w) (hv₂ : μ v ≠ ⊤ := by finiteness) (hw₂ : μ w ≠ ⊤ := by finiteness) :
  ⟪((indicatorConstLp 2 hv₁ hv₂ (1 : ℝ))), (indicatorConstLp 2 hw₁ hw₂ (1 : ℝ))⟫ =
    (μ.real (v ∩ w)) := by
  rw [inner_indicatorConstLp_one]
  have h : ((indicatorConstLp 2 hw₁ hw₂ (1 : ℝ)) : α → ℝ) =ᶠ[ae μ] w.indicator fun x ↦ (1 : ℝ) :=
    indicatorConstLp_coeFn (hs := hw₁) (hμs := hw₂)
  have g : ∀ᵐ (x : α) ∂μ, x ∈ v → ((indicatorConstLp 2 hw₁ hw₂ (1 : ℝ)) : α → ℝ) x =
      w.indicator (fun x ↦ (1 : ℝ)) x := Filter.Eventually.mono h fun x a a_1 ↦ a
  rw [setIntegral_congr_ae hv₁ g, setIntegral_indicator hw₁]
  simp

theorem posSemidef_interMatrix [Fintype n] (μ : Measure α) (v : n → (Set α))
    (hv₁ : ∀ j, MeasurableSet (v j)) (hv₂ : ∀ j, μ (v j) ≠ ⊤) :
      PosSemidef (fun (i j : n) ↦ (μ.real (v i ∩ v j))) := by
  conv => right ; intro i j ; rw [← innerProduct_eq_inter (hv₁ i) (hv₁ j) (hv₂ i) (hv₂ j)]
  exact IsGram.PosSemidef

end L2

end MeasureTheory

namespace Probability

namespace BrownianMotion

/-- This is the covariance matrix of Brownian Motion. -/
def covMatrix (t : n → ℝ≥0) : Matrix n n ℝ := fun i j ↦ min (t i) (t j)

namespace covMatrix

theorem posSemidef [Fintype n] (t : n → ℝ≥0) :
    PosSemidef (covMatrix t) := by
  let v : n → (Set ℝ) := fun i ↦ Set.Icc 0 (t i)
  have h : covMatrix t = fun i j ↦ (volume.real ((Icc 0 (t i).toReal) ∩ (Icc 0 (t j)))) := by
    simp [Set.Icc_inter_Icc]
    rfl
  apply h ▸ L2.posSemidef_interMatrix _ v  (fun j ↦ measurableSet_Icc)
    (fun j ↦ IsCompact.measure_ne_top isCompact_Icc)

end covMatrix

end BrownianMotion

end Probability

end covariance
