/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module analysis.normed_space.banach_steinhaus
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Analysis.LocallyConvex.Barrelled

/-!
# The Banach-Steinhaus theorem: Uniform Boundedness Principle

Herein we prove the Banach-Steinhaus theorem: any collection of bounded linear maps
from a Banach space into a normed space which is pointwise bounded is uniformly bounded.

## TODO

For now, we only prove the standard version by appeal to the Baire category theorem.
Much more general versions exist (in particular, for maps from barrelled spaces to locally
convex spaces), but these are not yet in `mathlib`.
-/


open Set

variable {E F 𝕜 𝕜₂ : Type _} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

/-- This is the standard Banach-Steinhaus theorem, or Uniform Boundedness Principle.
If a family of continuous linear maps from a Banach space into a normed space is pointwise
bounded, then the norms of these linear maps are uniformly bounded. -/
theorem banach_steinhaus {ι : Type _} [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) : ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  rw [show (∃ C, ∀ i, ‖g i‖ ≤ C) ↔ _ from (NormedSpace.equicontinuous_TFAE g).out 5 2]
  refine (norm_withSeminorms 𝕜₂ F).banach_steinhaus (fun _ x ↦ ?_)
  simpa [bddAbove_def, forall_range_iff] using h x
#align banach_steinhaus banach_steinhaus

open ENNReal

open ENNReal

/-- This version of Banach-Steinhaus is stated in terms of suprema of `↑‖⬝‖₊ : ℝ≥0∞`
for convenience. -/
theorem banach_steinhaus_iSup_nnnorm {ι : Type _} [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ x, (⨆ i, ↑‖g i x‖₊) < ∞) : (⨆ i, ↑‖g i‖₊) < ∞ := by
  rw [show ((⨆ i, ↑‖g i‖₊) < ∞) ↔ _ from (NormedSpace.equicontinuous_TFAE g).out 8 2]
  refine (norm_withSeminorms 𝕜₂ F).banach_steinhaus (fun _ x ↦ ?_)
  simpa [← NNReal.bddAbove_coe, ← Set.range_comp] using
    (WithTop.iSup_coe_lt_top (fun i ↦ ‖g i x‖₊)).mp (h x)
#align banach_steinhaus_supr_nnnorm banach_steinhaus_iSup_nnnorm

open Topology

open Filter

/-- Given a *sequence* of continuous linear maps which converges pointwise and for which the
domain is complete, the Banach-Steinhaus theorem is used to guarantee that the limit map
is a *continuous* linear map as well. -/
def continuousLinearMapOfTendsto [CompleteSpace E] [T2Space F] (g : ℕ → E →SL[σ₁₂] F) {f : E → F}
    (h : Tendsto (fun n x => g n x) atTop (𝓝 f)) : E →SL[σ₁₂] F where
  toFun := f
  map_add' := (linearMapOfTendsto _ _ h).map_add'
  map_smul' := (linearMapOfTendsto _ _ h).map_smul'
  cont := by
    -- show that the maps are pointwise bounded and apply `banach_steinhaus`
    have h_point_bdd : ∀ x : E, ∃ C : ℝ, ∀ n : ℕ, ‖g n x‖ ≤ C := by
      intro x
      rcases cauchySeq_bdd (tendsto_pi_nhds.mp h x).cauchySeq with ⟨C, -, hC⟩
      refine' ⟨C + ‖g 0 x‖, fun n => _⟩
      simp_rw [dist_eq_norm] at hC
      calc
        ‖g n x‖ ≤ ‖g 0 x‖ + ‖g n x - g 0 x‖ := norm_le_insert' _ _
        _ ≤ C + ‖g 0 x‖ := by linarith [hC n 0]
    cases' banach_steinhaus h_point_bdd with C' hC'
    /- show the uniform bound from `banach_steinhaus` is a norm bound of the limit map
             by allowing "an `ε` of room." -/
    refine'
      AddMonoidHomClass.continuous_of_bound (linearMapOfTendsto _ _ h) C' fun x =>
        le_of_forall_pos_lt_add fun ε ε_pos => _
    cases' Metric.tendsto_atTop.mp (tendsto_pi_nhds.mp h x) ε ε_pos with n hn
    have lt_ε : ‖g n x - f x‖ < ε := by
      rw [← dist_eq_norm]
      exact hn n (le_refl n)
    calc
      ‖f x‖ ≤ ‖g n x‖ + ‖g n x - f x‖ := norm_le_insert _ _
      _ < ‖g n‖ * ‖x‖ + ε := by linarith [lt_ε, (g n).le_op_norm x]
      _ ≤ C' * ‖x‖ + ε := by nlinarith [hC' n, norm_nonneg x]
#align continuous_linear_map_of_tendsto continuousLinearMapOfTendsto
