/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude)
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

import Mathlib.Tactic

/-!
# The residue of `Gamma` at zero

Mathlib defines `Gamma 0 = 0` by convention, so the mathematically meaningful
statement at the pole is a punctured-neighbourhood limit. Euler's recurrence

`Gamma (ε + 1) = ε * Gamma ε`

turns the residue limit `ε * Gamma ε → 1` into ordinary continuity of `Gamma` at `1`.
-/

public section

namespace Real

open Filter Set
open scoped Topology

/-- Real `Gamma` is continuous at `1`, as an immediate consequence of Mathlib's
real differentiability theorem away from the nonpositive integer poles. -/
theorem continuousAt_Gamma_one : ContinuousAt Real.Gamma 1 := by
  apply (Real.differentiableAt_Gamma ?_).continuousAt
  intro m h
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  linarith

/-- **The residue of `Gamma` at the origin.** In the punctured real neighbourhood
of zero, `ε * Gamma ε` tends to `1`. -/
theorem tendsto_mul_Gamma_zero :
    Tendsto (fun ε : ℝ => ε * Real.Gamma ε)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hadd0 : Tendsto (fun ε : ℝ => ε + 1) (nhds 0) (nhds 1) := by
    simpa using (tendsto_id.add tendsto_const_nhds :
      Tendsto (fun ε : ℝ => ε + 1) (nhds 0) (nhds (0 + 1)))
  have hadd : Tendsto (fun ε : ℝ => ε + 1)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hadd0.mono_left inf_le_left
  have hshift :
      Tendsto (fun ε : ℝ => Real.Gamma (ε + 1))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [Function.comp_def] using continuousAt_Gamma_one.tendsto.comp hadd
  apply hshift.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := by simpa using hε
  exact Real.Gamma_add_one hε0

/-- The same residue limit on the right-hand neighbourhood `ε → 0⁺`. -/
theorem tendsto_mul_Gamma_zero_nhdsGT :
    Tendsto (fun ε : ℝ => ε * Real.Gamma ε)
      (𝓝[>] 0) (nhds 1) := by
  apply tendsto_mul_Gamma_zero.mono_left
  apply nhdsWithin_mono
  intro ε hε
  simp only [mem_compl_iff, mem_singleton_iff]
  exact ne_of_gt hε

end Real
