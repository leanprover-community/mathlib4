/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# The Schwartz space on a finite-dimensional space is second countable

We show that `𝓢(E, F)` is second countable (hence separable) whenever `E` is a
finite-dimensional real normed space and `F` is second countable.

For `f : 𝓢(E, F)` and `k n : ℕ`, the function `x ↦ ‖x‖ ^ k • iteratedFDeriv ℝ n f x` tends to
zero at infinity, so it extends by zero to a continuous function on the one-point
compactification `OnePoint E`, whose sup norm is exactly the Schwartz seminorm
`SchwartzMap.seminorm ℝ k n f`. Hence the continuous linear map sending `f` to the family of
these extensions is an inducing map into a countable product of spaces of the form
`C(OnePoint E, E [×n]→L[ℝ] F)`, which are second countable since `OnePoint E` is compact and
second countable.

## Main statements

* `ContinuousMultilinearMap.instSecondCountableTopologyFin`: the space `E [×n]→L[𝕜] F` of
  continuous multilinear maps is second countable if `E` is finite-dimensional and `F` is second
  countable.
* `SchwartzMap.instSecondCountableTopology`: `𝓢(E, F)` is second countable if `E` is a
  finite-dimensional real normed space and `F` is second countable. In particular, `𝓢(E, F)` is a
  separable space.
-/

public noncomputable section

open Filter Set Topology TopologicalSpace
open scoped OnePoint

namespace ContinuousMultilinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The space of continuous `n`-multilinear maps on a finite-dimensional space with values in a
second countable space is second countable. -/
instance instSecondCountableTopologyFin [FiniteDimensional 𝕜 E] [SecondCountableTopology F]
    (n : ℕ) : SecondCountableTopology (E [×n]→L[𝕜] F) := by
  induction n with
  | zero => exact (continuousMultilinearCurryFin0 𝕜 E F).toHomeomorph.secondCountableTopology
  | succ n ih =>
    exact (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E)
      F).toHomeomorph.secondCountableTopology

end ContinuousMultilinearMap

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

section ProperSpace

variable [ProperSpace E]

private theorem tendsto_norm_pow_smul_iteratedFDeriv_cocompact (k n : ℕ) (f : 𝓢(E, F)) :
    Tendsto (fun x ↦ ‖x‖ ^ k • iteratedFDeriv ℝ n f x) (cocompact E) (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun x ↦ ‖x‖⁻¹ * SchwartzMap.seminorm ℝ (k + 1) n f) ?_ ?_
  · filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop 0] with x hx
    rw [norm_smul, norm_pow, norm_norm, inv_mul_eq_div, le_div_iff₀' hx, ← mul_assoc, ← pow_succ']
    exact le_seminorm ℝ (k + 1) n f x
  · simpa using (tendsto_inv_atTop_zero.comp tendsto_norm_cocompact_atTop).mul_const
      (SchwartzMap.seminorm ℝ (k + 1) n f)

/-- The function `x ↦ ‖x‖ ^ k • iteratedFDeriv ℝ n f x`, extended by zero to the one-point
compactification. -/
private def weightedDeriv (k n : ℕ) (f : 𝓢(E, F)) : C(OnePoint E, E [×n]→L[ℝ] F) :=
  OnePoint.continuousMapMk
    ⟨fun x ↦ ‖x‖ ^ k • iteratedFDeriv ℝ n f x,
      (continuous_norm.pow k).smul ((f.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top))⟩
    0 (by simpa [coclosedCompact_eq_cocompact] using
      tendsto_norm_pow_smul_iteratedFDeriv_cocompact k n f)

private theorem weightedDeriv_infty (k n : ℕ) (f : 𝓢(E, F)) : weightedDeriv k n f ∞ = 0 := rfl

private theorem weightedDeriv_coe (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    weightedDeriv k n f x = ‖x‖ ^ k • iteratedFDeriv ℝ n f x := rfl

private theorem norm_weightedDeriv (k n : ℕ) (f : 𝓢(E, F)) :
    ‖weightedDeriv k n f‖ = SchwartzMap.seminorm ℝ k n f := by
  refine le_antisymm ((ContinuousMap.norm_le _ (by positivity)).2 fun x ↦ ?_) <|
    seminorm_le_bound ℝ k n f (norm_nonneg (weightedDeriv k n f)) fun x ↦ ?_
  · induction x using OnePoint.rec with
    | infty => simp [weightedDeriv_infty]
    | coe x =>
      rw [weightedDeriv_coe, norm_smul, norm_pow, norm_norm]
      exact le_seminorm ℝ k n f x
  · simpa [weightedDeriv_coe, norm_smul] using (weightedDeriv k n f).norm_coe_le_norm x

/-- The map sending `f` to the family of the functions `x ↦ ‖x‖ ^ k • iteratedFDeriv ℝ n f x`,
seen as continuous functions on the one-point compactification. -/
private def embedding : 𝓢(E, F) →L[ℝ] ((c : ℕ × ℕ) → C(OnePoint E, E [×c.2]→L[ℝ] F)) :=
  ContinuousLinearMap.pi fun c ↦ mkCLMtoNormedSpace (𝕜 := ℝ) (σ := RingHom.id ℝ)
    (weightedDeriv c.1 c.2 : 𝓢(E, F) → C(OnePoint E, E [×c.2]→L[ℝ] F))
    (fun f g ↦ ContinuousMap.ext fun x ↦ by
      induction x using OnePoint.rec with
      | infty => simp [weightedDeriv_infty]
      | coe x =>
        simp [weightedDeriv_coe,
          iteratedFDeriv_add_apply (f.smooth _).contDiffAt (g.smooth _).contDiffAt])
    (fun a f ↦ ContinuousMap.ext fun x ↦ by
      induction x using OnePoint.rec with
      | infty => simp [weightedDeriv_infty]
      | coe x =>
        simp [weightedDeriv_coe, iteratedFDeriv_const_smul_apply (f.smooth _).contDiffAt,
          smul_comm a])
    ⟨{c}, 1, zero_le_one, fun f ↦ by simp [norm_weightedDeriv, schwartzSeminormFamily]⟩

private theorem isInducing_embedding : IsInducing (embedding (E := E) (F := F)) := by
  refine isInducing_iff_nhds.2 fun f ↦ le_antisymm (embedding.continuous.tendsto f).le_comap ?_
  intro U hU
  obtain ⟨s, r, hr, hsub⟩ := ((schwartz_withSeminorms ℝ E F).mem_nhds_iff f U).1 hU
  refine ⟨⋂ c ∈ s, (fun v ↦ v c) ⁻¹' Metric.ball (embedding f c) r,
    (biInter_finset_mem s).2 fun c _ ↦
      (continuous_apply c).continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (embedding f c) hr),
    fun g hg ↦ hsub ?_⟩
  simp only [mem_preimage, mem_iInter, Metric.mem_ball] at hg
  rw [Seminorm.mem_ball]
  refine Seminorm.finset_sup_apply_lt hr fun c hc ↦ ?_
  calc schwartzSeminormFamily ℝ E F c (g - f) = ‖embedding (g - f) c‖ :=
        (norm_weightedDeriv c.1 c.2 (g - f)).symm
    _ = dist (embedding g c) (embedding f c) := by
      rw [map_sub, Pi.sub_apply]
      exact (dist_eq_norm (embedding g c) (embedding f c)).symm
    _ < r := hg c hc

end ProperSpace

/-- The Schwartz space `𝓢(E, F)` on a finite-dimensional real normed space `E` is second countable
(hence separable) when `F` is. -/
instance instSecondCountableTopology [FiniteDimensional ℝ E] [SecondCountableTopology F] :
    SecondCountableTopology 𝓢(E, F) :=
  isInducing_embedding.secondCountableTopology

end SchwartzMap
