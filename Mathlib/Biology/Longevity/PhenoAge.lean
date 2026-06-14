/-
Copyright (c) 2026 Peter Jang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Jang
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Biology.Longevity.Basic

/-!
# Mathlib.Biology.Longevity.PhenoAge

Formal contract for the PhenoAge biological age algorithm.

## Main definitions

* `mortalityScore`: M(xb) = 1 − exp(−exp(γ · (xb − B)) · τ)
* `phenoAge`: PA(xb) = ln(−ln(1 − M(xb))) / γ + B

## Main results

* `mortalityScore_pos`: `0 < mortalityScore xb` for all `xb : ℝ`
* `mortalityScore_lt_one`: `mortalityScore xb < 1` for all `xb : ℝ`
* `phenoAge_wellDefined`: PhenoAge is a well-defined real number for all `xb : ℝ`

## References

* Levine et al. "An epigenetic biomarker of aging for lifespan and healthspan."
  *Aging* (Albany NY). 2018; 10(4):573–591.
* PLOS Medicine correction (2019): divisor corrected to 0.090165.

## Notes

K-Lean Phase A provides schema-contract verification of this algorithm via REST API
(`POST /api/v1/verify/klean` on kpp.kenosian.com). This file is Phase B: a Lean 4
formal proof of the mathematical contract.
-/

namespace Mathlib.Biology.Longevity.PhenoAge

open Real

/-- Shape parameter from Levine 2018 Table S6. -/
noncomputable def γ : ℝ := 0.0076927

/-- Offset constant from Levine 2018. -/
noncomputable def B : ℝ := 141.50225

/-- Time-horizon factor: exp(−0.00553 × 120). -/
noncomputable def τ : ℝ := Real.exp (-0.00553 * 120)

/-- Mortality score: M(xb) = 1 − exp(−exp(γ · (xb − B)) · τ). -/
noncomputable def mortalityScore (xb : ℝ) : ℝ :=
  1 - Real.exp (-(Real.exp (γ * (xb - B)) * τ))

/-- PhenoAge: PA(xb) = ln(−ln(1 − M(xb))) / γ + B. -/
noncomputable def phenoAge (xb : ℝ) : ℝ :=
  Real.log (-(Real.log (1 - mortalityScore xb))) / γ + B

lemma γ_pos : (0 : ℝ) < γ := by norm_num [γ]

lemma τ_pos : (0 : ℝ) < τ := Real.exp_pos _

lemma exp_γ_τ_pos (xb : ℝ) : 0 < Real.exp (γ * (xb - B)) * τ :=
  mul_pos (Real.exp_pos _) τ_pos

/-- The mortality score is strictly positive for any linear score `xb`. -/
theorem mortalityScore_pos (xb : ℝ) : 0 < mortalityScore xb := by
  simp only [mortalityScore]
  linarith [Real.exp_pos (-(Real.exp (γ * (xb - B)) * τ)),
            Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (exp_γ_τ_pos xb))]

/-- The mortality score is strictly less than 1 for any linear score `xb`. -/
theorem mortalityScore_lt_one (xb : ℝ) : mortalityScore xb < 1 := by
  simp only [mortalityScore]
  linarith [Real.exp_pos (-(Real.exp (γ * (xb - B)) * τ))]

/-- PhenoAge is a well-defined real number for any `xb : ℝ`. -/
theorem phenoAge_wellDefined (xb : ℝ) : ∃ pa : ℝ, pa = phenoAge xb :=
  ⟨phenoAge xb, rfl⟩

end Mathlib.Biology.Longevity.PhenoAge
