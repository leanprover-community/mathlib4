/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.Baire.CompleteMetrizable

#align_import analysis.normed_space.banach_steinhaus from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# The Banach-Steinhaus theorem: Uniform Boundedness Principle

Herein we prove the Banach-Steinhaus theorem for normed spaces: any collection of bounded linear
maps from a Banach space into a normed space which is pointwise bounded is uniformly bounded.

Note that we prove the more general version about barrelled spaces in
`Analysis.LocallyConvex.Barrelled`, and the usual version below is indeed deduced from the
more general setup.
-/

open Set

variable {E F 𝕜 𝕜₂ : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

/-- This is the standard Banach-Steinhaus theorem, or Uniform Boundedness Principle.
If a family of continuous linear maps from a Banach space into a normed space is pointwise
bounded, then the norms of these linear maps are uniformly bounded.

See also `WithSeminorms.banach_steinhaus` for the general statement in barrelled spaces. -/
theorem banach_steinhaus {ι : Type*} [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) : ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  rw [show (∃ C, ∀ i, ‖g i‖ ≤ C) ↔ _ from (NormedSpace.equicontinuous_TFAE g).out 5 2]
  refine (norm_withSeminorms 𝕜₂ F).banach_steinhaus (fun _ x ↦ ?_)
  simpa [bddAbove_def, forall_mem_range] using h x
#align banach_steinhaus banach_steinhaus

open ENNReal

open ENNReal

/-- This version of Banach-Steinhaus is stated in terms of suprema of `↑‖·‖₊ : ℝ≥0∞`
for convenience. -/
theorem banach_steinhaus_iSup_nnnorm {ι : Type*} [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ x, (⨆ i, ↑‖g i x‖₊) < ∞) : (⨆ i, ↑‖g i‖₊) < ∞ := by
  rw [show ((⨆ i, ↑‖g i‖₊) < ∞) ↔ _ from (NormedSpace.equicontinuous_TFAE g).out 8 2]
  refine (norm_withSeminorms 𝕜₂ F).banach_steinhaus (fun _ x ↦ ?_)
  simpa [← NNReal.bddAbove_coe, ← Set.range_comp] using ENNReal.iSup_coe_lt_top.1 (h x)
#align banach_steinhaus_supr_nnnorm banach_steinhaus_iSup_nnnorm

open Topology

open Filter

/-- Given a *sequence* of continuous linear maps which converges pointwise and for which the
domain is complete, the Banach-Steinhaus theorem is used to guarantee that the limit map
is a *continuous* linear map as well. -/
abbrev continuousLinearMapOfTendsto {α : Type*} [CompleteSpace E] [T2Space F] {l : Filter α}
    [l.IsCountablyGenerated] [l.NeBot] (g : α → E →SL[σ₁₂] F) {f : E → F}
    (h : Tendsto (fun n x ↦ g n x) l (𝓝 f)) :
    E →SL[σ₁₂] F :=
  (norm_withSeminorms 𝕜₂ F).continuousLinearMapOfTendsto g h
#align continuous_linear_map_of_tendsto continuousLinearMapOfTendsto
