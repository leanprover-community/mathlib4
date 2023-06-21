/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import Mathlib.Probability.Notation

/-!
# Rényi Divergence

FIXME

## Main definitions

* `renyiDivergence α μ ν`: The Rényi α-divergence between measures μ and ν. When
  `α=1`, this is the Kullback-Leibler divergence, and when `(α : ℝ≥0∞) = ∞`, this becomes
  the max-divergence.

## References

* Yury Polyanskiy and Yihong Wu, Information Theory From Coding to Learning
-/

set_option autoImplicit false
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

open scoped Classical ENNReal ProbabilityTheory NNReal

open MeasureTheory

variable {Ω : Type _} {m : MeasurableSpace Ω}

noncomputable def renyiDivergence (α : ℝ≥0∞) (μ ν : Measure Ω) : ℝ :=
  if μ ≪ ν then
    if α = ∞ then -- α = ∞: max-divergence
      Real.log <| essSup (ENNReal.toReal ∘ (μ.rnDeriv ν)) ν
    else
      if α = 1 then  -- α = 1: Kullback-Leibler divergence
        ∫ x, ((μ.rnDeriv ν x).toReal * (Real.log (μ.rnDeriv ν x).toReal)) ∂ν
      else                -- Standard Rényi divergence
        Real.log <| ∫ x, ((μ.rnDeriv ν x).toReal^(α.toReal)) ∂ν
  else 0

namespace InformationTheory

scoped notation "𝓓[" α "](" μ "‖" ν ")" => renyiDivergence α μ ν

end InformationTheory

open scoped InformationTheory

lemma renyiDivergence_one_def (μ ν : MeasureTheory.Measure Ω) (h : μ ≪ ν) :
    𝓓[1](μ‖ν) = ∫ x, ((μ.rnDeriv ν x).toReal * (Real.log (μ.rnDeriv ν x).toReal)) ∂ν := by
  simp [renyiDivergence, h]

lemma renyiDivergence_infty_def (μ ν : MeasureTheory.Measure Ω) (h : μ ≪ ν) :
    𝓓[∞](μ‖ν) = Real.log (essSup (ENNReal.toReal ∘ (μ.rnDeriv ν)) ν) := by
  simp [renyiDivergence, h]

lemma renyiDivergence_def (α : ℝ≥0) (hα : α ≠ 1) (μ ν : MeasureTheory.Measure Ω) (h : μ ≪ ν) :
    𝓓[α](μ‖ν) = Real.log (∫ x, ((μ.rnDeriv ν x).toReal^(α.toReal)) ∂ν) := by
  simp [renyiDivergence, h, hα]

lemma renyiDivergence_one_eq_zero (μ ν : MeasureTheory.Measure Ω) (hμν : μ ≪ ν) :
    𝓓[1](μ‖ν) = 0 ↔ μ = ν := by
  sorry
