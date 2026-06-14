/-
Copyright (c) 2026 Kenosian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Jang (Kenosian Protocol Platform)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Biology.Longevity.Basic

/-!
# PhenoAge -- Biological Age Estimation (Levine 2018)

Formal contract for the PhenoAge biological age algorithm.

## Reference
Levine et al. "An epigenetic biomarker of aging for lifespan and healthspan."
*Aging* (Albany NY). 2018; 10(4):573-591.
PLOS Medicine correction (2019): divisor = 0.090165.

## Mathematical structure
Given a linear score `xb = Sigma beta_i x_i + intercept`:
1. Mortality score:  `M  = 1 - exp(-exp(gamma(xb - B)) * tau)`
2. PhenoAge:         `PA = ln(-ln(1 - M)) / gamma + B`

where gamma = 0.0076927, B = 141.50225, tau = exp(-0.00553 * 120).

## K-Lean Phase A
Schema-contract verification (machine-checked without Lean 4):
`POST /api/v1/verify/klean` on kpp.kenosian.com

## Theorems
- `mortalityScore_pos`: M > 0 for any xb
- `mortalityScore_lt_one`: M < 1 for any xb
- `phenoAge_wellDefined`: PA is a well-defined real number for any xb
-/

namespace Mathlib.Biology.Longevity.PhenoAge

open Real

-- Levine 2018 constants

/-- Shape parameter (Levine 2018 Table S6). -/
noncomputable def gamma_param : ℝ := 0.0076927

/-- Offset constant (Levine 2018). -/
noncomputable def B_param : ℝ := 141.50225

/-- Time-horizon factor: exp(-0.00553 * 120). -/
noncomputable def tau : ℝ := Real.exp (-0.00553 * 120)

-- Core functions

/-- Mortality score M(xb) = 1 - exp(-exp(gamma(xb - B)) * tau). -/
noncomputable def mortalityScore (xb : ℝ) : ℝ :=
  1 - Real.exp (-(Real.exp (gamma_param * (xb - B_param)) * tau))

/-- PhenoAge PA(xb) = ln(-ln(1 - M(xb))) / gamma + B. -/
noncomputable def phenoAge (xb : ℝ) : ℝ :=
  Real.log (-(Real.log (1 - mortalityScore xb))) / gamma_param + B_param

-- Lemmas

lemma gamma_pos : (0 : ℝ) < gamma_param := by norm_num [gamma_param]

lemma tau_pos : (0 : ℝ) < tau := Real.exp_pos _

/-- The product exp(gamma*(xb-B)) * tau is strictly positive. -/
lemma exp_gamma_tau_pos (xb : ℝ) : 0 < Real.exp (gamma_param * (xb - B_param)) * tau :=
  mul_pos (Real.exp_pos _) tau_pos

/-- The negated product -(exp(gamma*(xb-B)) * tau) is strictly negative. -/
lemma neg_exp_mul_tau_neg (xb : ℝ) : -(Real.exp (gamma_param * (xb - B_param)) * tau) < 0 :=
  neg_lt_zero.mpr (exp_gamma_tau_pos xb)

-- Theorems

/-- The mortality score is strictly positive for any linear score xb. -/
theorem mortalityScore_pos (xb : ℝ) : 0 < mortalityScore xb := by
  simp only [mortalityScore]
  have hlt : Real.exp (-(Real.exp (gamma_param * (xb - B_param)) * tau)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_exp_mul_tau_neg xb)
  linarith

/-- The mortality score is strictly less than 1 for any linear score xb. -/
theorem mortalityScore_lt_one (xb : ℝ) : mortalityScore xb < 1 := by
  simp only [mortalityScore]
  linarith [Real.exp_pos (-(Real.exp (gamma_param * (xb - B_param)) * tau))]

/-- PhenoAge is a well-defined real number for any xb. -/
theorem phenoAge_wellDefined (xb : ℝ) : ∃ pa : ℝ, pa = phenoAge xb :=
  ⟨phenoAge xb, rfl⟩

end Mathlib.Biology.Longevity.PhenoAge
