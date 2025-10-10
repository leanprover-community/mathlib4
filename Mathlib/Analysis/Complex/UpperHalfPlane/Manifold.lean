/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Manifold structure on the upper half plane.

In this file we define the complex manifold structure on the upper half-plane.
-/

open Filter

open scoped Manifold ContDiff MatrixGroups

variable {n : WithTop ℕ∞}

namespace UpperHalfPlane

noncomputable instance : ChartedSpace ℂ ℍ :=
  UpperHalfPlane.isOpenEmbedding_coe.singletonChartedSpace

instance : IsManifold 𝓘(ℂ) ω ℍ :=
  UpperHalfPlane.isOpenEmbedding_coe.isManifold_singleton

/-- The inclusion map `ℍ → ℂ` is a map of `C^n` manifolds. -/
theorem contMDiff_coe : CMDiff n ((↑) : ℍ → ℂ) :=
  fun _ => contMDiffAt_extChartAt

/-- The inclusion map `ℍ → ℂ` is a differentiable map of manifolds. -/
theorem mdifferentiable_coe : MDiff ((↑) : ℍ → ℂ) :=
  contMDiff_coe.mdifferentiable le_top

lemma contMDiffAt_ofComplex {z : ℂ} (hz : 0 < z.im) : CMDiffAt n ofComplex z := by
  rw [contMDiffAt_iff]
  constructor
  · -- continuity at z
    rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
    refine Tendsto.congr' (eventuallyEq_coe_comp_ofComplex hz).symm ?_
    simpa [ofComplex_apply_of_im_pos hz] using tendsto_id
  · -- smoothness in local chart
    simpa using contDiffAt_id.congr_of_eventuallyEq (eventuallyEq_coe_comp_ofComplex hz)

lemma mdifferentiableAt_ofComplex {z : ℂ} (hz : 0 < z.im) : MDiffAt ofComplex z :=
  (contMDiffAt_ofComplex hz).mdifferentiableAt le_top

lemma contMDiffAt_iff {f : ℍ → ℂ} {τ : ℍ} :
    CMDiffAt n f τ ↔ ContDiffAt ℂ n (f ∘ ofComplex) τ := by
  rw [← contMDiffAt_iff_contDiffAt]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (contMDiffAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (contMDiff_coe τ)

lemma mdifferentiableAt_iff {f : ℍ → ℂ} {τ : ℍ} :
    MDiffAt f τ ↔ DifferentiableAt ℂ (f ∘ ofComplex) ↑τ := by
  rw [← mdifferentiableAt_iff_differentiableAt]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (mdifferentiableAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (mdifferentiable_coe τ)

lemma mdifferentiable_iff {f : ℍ → ℂ} :
    MDiff f ↔ DifferentiableOn ℂ (f ∘ ofComplex) {z | 0 < z.im} :=
  ⟨fun h z hz ↦ (mdifferentiableAt_iff.mp (h ⟨z, hz⟩)).differentiableWithinAt,
    fun h ⟨z, hz⟩ ↦ mdifferentiableAt_iff.mpr <| (h z hz).differentiableAt
     <| isOpen_upperHalfPlaneSet.mem_nhds hz⟩

lemma contMDiff_num (g : GL (Fin 2) ℝ) : CMDiff n (fun τ : ℍ ↦ num g τ) :=
  (contMDiff_const.smul contMDiff_coe).add contMDiff_const

lemma contMDiff_denom (g : GL (Fin 2) ℝ) : CMDiff n (fun τ : ℍ ↦ denom g τ) :=
  (contMDiff_const.smul contMDiff_coe).add contMDiff_const

lemma contMDiff_denom_zpow (g : GL (Fin 2) ℝ) (k : ℤ) : CMDiff n (denom g · ^ k : ℍ → ℂ) := by
  intro τ
  have : AnalyticAt ℂ (· ^ k) (denom g τ) := (differentiableOn_zpow k _ (by tauto)).analyticOnNhd
    isOpen_compl_singleton _ (denom_ne_zero g τ)
  exact this.contDiffAt.contMDiffAt.comp τ (contMDiff_denom g τ)

lemma contMDiff_inv_denom (g : GL (Fin 2) ℝ) : CMDiff n (fun τ : ℍ ↦ (denom g τ)⁻¹) := by
  simpa using contMDiff_denom_zpow g (-1)

/-- Each element of `GL(2, ℝ)⁺` defines a map of `C ^ n` manifolds `ℍ → ℍ`. -/
lemma contMDiff_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) : CMDiff n (fun τ : ℍ ↦ g • τ) := by
  intro τ
  refine contMDiffAt_iff_target.mpr ⟨(continuous_const_smul g).continuousAt, ?_⟩
  simpa [glPos_smul_def hg] using (contMDiff_num g τ).mul (contMDiff_inv_denom g τ)

lemma mdifferentiable_num (g : GL (Fin 2) ℝ) : MDiff (fun τ : ℍ ↦ num g τ) :=
  (contMDiff_num g).mdifferentiable le_top

lemma mdifferentiable_denom (g : GL (Fin 2) ℝ) : MDiff (fun τ : ℍ ↦ denom g τ) :=
  (contMDiff_denom g).mdifferentiable le_top

lemma mdifferentiable_denom_zpow (g : GL (Fin 2) ℝ) (k : ℤ) : MDiff (denom g · ^ k : ℍ → ℂ) :=
  (contMDiff_denom_zpow g k).mdifferentiable le_top

lemma mdifferentiable_inv_denom (g : GL (Fin 2) ℝ) : MDiff (fun τ : ℍ ↦ (denom g τ)⁻¹) :=
  (contMDiff_inv_denom g).mdifferentiable le_top

/-- Each element of `GL(2, ℝ)⁺` defines a complex-differentiable map `ℍ → ℍ`. -/
lemma mdifferentiable_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) : MDiff (fun τ : ℍ ↦ g • τ) :=
  (contMDiff_smul hg).mdifferentiable le_top

end UpperHalfPlane
