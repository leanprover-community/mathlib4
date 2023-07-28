/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Patrick Massot
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ReImTopology

/-!
# A collection of specific limit computations for is_R_or_C
-/

open Set Algebra Filter

variable (𝕜 : Type _) [IsROrC 𝕜]

theorem IsROrC.tendsto_inverse_atTop_nhds_0_nat : Tendsto (fun n : ℕ => (n : 𝕜)⁻¹) atTop (nhds 0) := by
  rw [show (fun n : ℕ => (n : 𝕜)⁻¹) = (↑) ∘ fun n : ℕ => (n : ℝ)⁻¹ by ext1 n; simp]
  exact tendsto_algebraMap_inverse_atTop_nhds_0_nat 𝕜
