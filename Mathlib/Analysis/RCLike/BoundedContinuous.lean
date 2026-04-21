/-
Copyright (c) 2025 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Star

/-! # Results on bounded continuous functions with `RCLike` values -/
set_option backward.defeqAttrib.useBackward true

public section

open Filter Real RCLike BoundedContinuousFunction

open scoped Topology

variable (𝕜 E : Type*) [RCLike 𝕜] [PseudoEMetricSpace E]

namespace RCLike

/-- On a star subalgebra of bounded continuous functions, the operations "restrict scalars to ℝ"
and "forget that a bounded continuous function is a bounded" commute. -/
theorem restrict_toContinuousMap_eq_toContinuousMapStar_restrict
    {A : StarSubalgebra 𝕜 (E →ᵇ 𝕜)} :
    ((A.restrictScalars ℝ).comap
    (AlgHom.compLeftContinuousBounded ℝ ofRealAm lipschitzWith_ofReal)).map (toContinuousMapₐ ℝ) =
    ((A.map (toContinuousMapStarₐ 𝕜)).restrictScalars ℝ).comap
    (ofRealAm.compLeftContinuous ℝ continuous_ofReal) := by
  ext g
  simp only [Subalgebra.mem_map, Subalgebra.mem_comap, Subalgebra.mem_restrictScalars,
    StarSubalgebra.mem_toSubalgebra, toContinuousMapₐ_apply, StarSubalgebra.mem_map]
  constructor
  · intro ⟨x, hxA, hxg⟩
    use (@ofRealAm 𝕜 _).compLeftContinuousBounded ℝ lipschitzWith_ofReal x, hxA
    ext a
    simp only [toContinuousMapStarₐ_apply_apply, AlgHom.compLeftContinuousBounded_apply_apply,
      ofRealAm_coe, AlgHom.compLeftContinuous_apply_apply, algebraMap.coe_inj]
    exact DFunLike.congr_fun hxg a
  · intro ⟨x, hxA, hxg⟩
    have hg_apply (a : E) := DFunLike.congr_fun hxg a
    simp only [toContinuousMapStarₐ_apply_apply, AlgHom.compLeftContinuous_apply_apply,
      ofRealAm_coe] at hg_apply
    have h_comp_eq : (@ofRealAm 𝕜 _).compLeftContinuousBounded ℝ lipschitzWith_ofReal
        (x.comp reCLM (@reCLM 𝕜 _).lipschitz) = x := by
      ext a
      simp [hg_apply]
    use x.comp reCLM (@reCLM 𝕜 _).lipschitz
    refine ⟨by rwa [h_comp_eq], ?_⟩
    ext a
    simp [hg_apply]

end RCLike
