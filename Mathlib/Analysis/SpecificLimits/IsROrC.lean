/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Patrick Massot
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.IsROrC.Basic

/-!
# A collection of specific limit computations for `IsROrC`

-/

open Set Algebra Filter
open scoped Topology

variable (𝕜 : Type*) [IsROrC 𝕜]

theorem IsROrC.tendsto_inverse_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => (n : 𝕜)⁻¹) atTop (𝓝 0) := by
  convert tendsto_algebraMap_inverse_atTop_nhds_zero_nat 𝕜
  simp
@[deprecated] alias IsROrC.tendsto_inverse_atTop_nhds_0_nat :=
  IsROrC.tendsto_inverse_atTop_nhds_zero_nat
