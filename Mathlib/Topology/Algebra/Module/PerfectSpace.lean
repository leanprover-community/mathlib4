/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Perfect

/-! # Vector spaces over nontrivially normed fields are perfect spaces -/

open Filter Set
open scoped Topology

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nontrivial E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]

include 𝕜 in
lemma perfectSpace_of_module : PerfectSpace E := by
  refine ⟨fun x hx ↦ ?_⟩
  let ⟨r, hr₀, hr⟩ := NormedField.exists_norm_lt_one 𝕜
  obtain ⟨c, hc⟩ : ∃ (c : E), c ≠ 0 := exists_ne 0
  have A : Tendsto (fun (n : ℕ) ↦ x + r ^ n • c) atTop (𝓝 (x + (0 : 𝕜) • c)) := by
    apply Tendsto.add tendsto_const_nhds
    exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).smul tendsto_const_nhds
  have B : Tendsto (fun (n : ℕ) ↦ x + r ^ n • c) atTop (𝓝[univ \ {x}] x) := by
    simp only [zero_smul, add_zero] at A
    simp [tendsto_nhdsWithin_iff, A, hc, norm_pos_iff.mp hr₀]
  exact accPt_principal_iff_nhdsWithin.mpr ((atTop_neBot.map _).mono B)

instance : PerfectSpace 𝕜 := perfectSpace_of_module 𝕜 𝕜
