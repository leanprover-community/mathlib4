/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Manifold structure on the upper half plane.

In this file we define the complex manifold structure on the upper half-plane.
-/

open Filter

open scoped Manifold ContDiff MatrixGroups

namespace UpperHalfPlane

noncomputable instance : ChartedSpace ℂ ℍ :=
  UpperHalfPlane.isOpenEmbedding_coe.singletonChartedSpace

instance : IsManifold 𝓘(ℂ) ω ℍ :=
  UpperHalfPlane.isOpenEmbedding_coe.isManifold_singleton

/-- The inclusion map `ℍ → ℂ` is an analytic map of manifolds. -/
theorem contMDiff_coe {n : WithTop ℕ∞} : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n ((↑) : ℍ → ℂ) :=
  fun _ => contMDiffAt_extChartAt

@[deprecated (since := "2024-11-20")] alias smooth_coe := contMDiff_coe

/-- The inclusion map `ℍ → ℂ` is a differentiable map of manifolds. -/
theorem mdifferentiable_coe : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((↑) : ℍ → ℂ) :=
  contMDiff_coe.mdifferentiable le_top

lemma contMDiffAt_ofComplex {n : WithTop ℕ∞} {z : ℂ} (hz : 0 < z.im) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n ofComplex z := by
  rw [contMDiffAt_iff]
  constructor
  · -- continuity at z
    rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
    refine Tendsto.congr' (eventuallyEq_coe_comp_ofComplex hz).symm ?_
    simpa only [ofComplex_apply_of_im_pos hz, Subtype.coe_mk] using tendsto_id
  · -- smoothness in local chart
    simp only [extChartAt, PartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.refl_partialEquiv,
      PartialEquiv.refl_source, PartialHomeomorph.singletonChartedSpace_chartAt_eq,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, CompTriple.comp_eq, modelWithCornersSelf_coe,
      Set.range_id, id_eq, contDiffWithinAt_univ]
    exact contDiffAt_id.congr_of_eventuallyEq (eventuallyEq_coe_comp_ofComplex hz)

@[deprecated (since := "2024-11-20")] alias smoothAt_ofComplex := contMDiffAt_ofComplex

lemma mdifferentiableAt_ofComplex {z : ℂ} (hz : 0 < z.im) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ofComplex z :=
  (contMDiffAt_ofComplex hz).mdifferentiableAt le_top

lemma mdifferentiableAt_iff {f : ℍ → ℂ} {τ : ℍ} :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f τ ↔ DifferentiableAt ℂ (f ∘ ofComplex) ↑τ := by
  rw [← mdifferentiableAt_iff_differentiableAt]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (mdifferentiableAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (mdifferentiable_coe τ)

lemma mdifferentiable_iff {f : ℍ → ℂ} :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ↔ DifferentiableOn ℂ (f ∘ ofComplex) {z | 0 < z.im} :=
  ⟨fun h z hz ↦ (mdifferentiableAt_iff.mp (h ⟨z, hz⟩)).differentiableWithinAt,
    fun h ⟨z, hz⟩ ↦ mdifferentiableAt_iff.mpr <| (h z hz).differentiableAt
      <| (Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds hz⟩

lemma mdifferentiable_num (g : GL(2, ℝ)⁺) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (num g) :=
  (mdifferentiable_coe.const_smul _).add mdifferentiable_const

lemma mdifferentiable_denom (g : GL(2, ℝ)⁺) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (denom g) :=
  (mdifferentiable_coe.const_smul _).add mdifferentiable_const

lemma mdifferentiable_denom_zpow (g : GL(2, ℝ)⁺) (k : ℤ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (denom g · ^ k) := fun τ ↦ by
  have := (differentiableAt_zpow (m := k)).mpr (Or.inl <| denom_ne_zero g τ)
  exact this.mdifferentiableAt.comp τ (mdifferentiable_denom g τ)

lemma mdifferentiable_inv_denom (g : GL(2, ℝ)⁺) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ ↦ (denom g τ)⁻¹) := by
  simpa using mdifferentiable_denom_zpow g (-1)

/-- Each element of `GL(2, ℝ)⁺` defines a complex-differentiable map `ℍ → ℍ`. -/
lemma mdifferentiable_smul (g : GL(2, ℝ)⁺) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ g • τ) := fun τ ↦ by
  refine mdifferentiableAt_iff_target.mpr ⟨(continuous_const_smul g).continuousAt, ?_⟩
  simpa [smulAux, Function.comp_def] using
    (mdifferentiable_num g τ).mul (mdifferentiable_inv_denom g τ)

end UpperHalfPlane
