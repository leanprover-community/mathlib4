/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Manifold structure on the upper half plane.

In this file we define the complex manifold structure on the upper half-plane.
-/

@[expose] public section

open Filter

open scoped Manifold ContDiff MatrixGroups Topology

variable {n : WithTop ℕ∞}

namespace UpperHalfPlane

noncomputable instance : ChartedSpace ℂ ℍ :=
  UpperHalfPlane.isOpenEmbedding_coe.singletonChartedSpace

instance : IsManifold 𝓘(ℂ) ω ℍ :=
  UpperHalfPlane.isOpenEmbedding_coe.isManifold_singleton

/-- The inclusion map `ℍ → ℂ` is a map of `C^n` manifolds. -/
theorem contMDiff_coe : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n ((↑) : ℍ → ℂ) :=
  fun _ => contMDiffAt_extChartAt

/-- The inclusion map `ℍ → ℂ` is a differentiable map of manifolds. -/
theorem mdifferentiable_coe : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((↑) : ℍ → ℂ) :=
  contMDiff_coe.mdifferentiable le_top

lemma contMDiffAt_ofComplex {z : ℂ} (hz : 0 < z.im) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n ofComplex z := by
  rw [contMDiffAt_iff]
  constructor
  · -- continuity at z
    rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
    refine Tendsto.congr' (eventuallyEq_coe_comp_ofComplex hz).symm ?_
    simpa [ofComplex_apply_of_im_pos hz] using tendsto_id
  · -- smoothness in local chart
    simpa using contDiffAt_id.congr_of_eventuallyEq (eventuallyEq_coe_comp_ofComplex hz)

lemma mdifferentiableAt_ofComplex {z : ℂ} (hz : 0 < z.im) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ofComplex z :=
  (contMDiffAt_ofComplex hz).mdifferentiableAt le_top

lemma contMDiffAt_iff {f : ℍ → ℂ} {τ : ℍ} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n f τ ↔ ContDiffAt ℂ n (f ∘ ofComplex) τ := by
  rw [← contMDiffAt_iff_contDiffAt]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (contMDiffAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (contMDiff_coe τ)

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
     <| isOpen_upperHalfPlaneSet.mem_nhds hz⟩

lemma contMDiff_num (g : GL (Fin 2) ℝ) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (fun τ : ℍ ↦ num g τ) :=
  (contMDiff_const.smul contMDiff_coe).add contMDiff_const

lemma contMDiff_denom (g : GL (Fin 2) ℝ) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (fun τ : ℍ ↦ denom g τ) :=
  (contMDiff_const.smul contMDiff_coe).add contMDiff_const

lemma contMDiff_denom_zpow (g : GL (Fin 2) ℝ) (k : ℤ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (denom g · ^ k : ℍ → ℂ) := fun τ ↦ by
  have : AnalyticAt ℂ (· ^ k) (denom g τ) := (differentiableOn_zpow k _ (by tauto)).analyticOnNhd
    isOpen_compl_singleton _ (denom_ne_zero g τ)
  exact this.contDiffAt.contMDiffAt.comp τ (contMDiff_denom g τ)

lemma contMDiff_inv_denom (g : GL (Fin 2) ℝ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (fun τ : ℍ ↦ (denom g τ)⁻¹) := by
  simpa using contMDiff_denom_zpow g (-1)

/-- Each element of `GL(2, ℝ)⁺` defines a map of `C ^ n` manifolds `ℍ → ℍ`. -/
lemma contMDiff_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (fun τ : ℍ ↦ g • τ) := fun τ ↦ by
  refine contMDiffAt_iff_target.mpr ⟨(continuous_const_smul g).continuousAt, ?_⟩
  simpa [glPos_smul_def hg] using (contMDiff_num g τ).mul (contMDiff_inv_denom g τ)

lemma mdifferentiable_num (g : GL (Fin 2) ℝ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ num g τ) :=
  (contMDiff_num g).mdifferentiable le_top

lemma mdifferentiable_denom (g : GL (Fin 2) ℝ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ denom g τ) :=
  (contMDiff_denom g).mdifferentiable le_top

lemma mdifferentiable_denom_zpow (g : GL (Fin 2) ℝ) (k : ℤ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (denom g · ^ k : ℍ → ℂ) :=
  (contMDiff_denom_zpow g k).mdifferentiable le_top

lemma mdifferentiable_inv_denom (g : GL (Fin 2) ℝ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ (denom g τ)⁻¹) :=
  (contMDiff_inv_denom g).mdifferentiable le_top

/-- Each element of `GL(2, ℝ)⁺` defines a complex-differentiable map `ℍ → ℍ`. -/
lemma mdifferentiable_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ g • τ) :=
  (contMDiff_smul hg).mdifferentiable le_top

lemma eq_zero_of_frequently {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {τ : ℍ} (hτ : ∃ᶠ z in 𝓝[≠] τ, f z = 0) : f = 0 := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf
  have := hf.analyticOnNhd isOpen_upperHalfPlaneSet
  ext w
  convert this.eqOn_zero_of_preconnected_of_frequently_eq_zero (z₀ := ↑τ) ?_ τ.2 ?_ w.property
  · rw [Function.comp_apply, ofComplex_apply_of_im_pos w.property]
    rfl
  · exact (Complex.isConnected_of_upperHalfPlane subset_rfl (by grind)).isPreconnected
  · contrapose! hτ
    rw [eventually_nhdsWithin_iff, ← isOpenEmbedding_coe.map_nhds_eq, eventually_map] at hτ
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hτ] with a ha
    simpa using ha

lemma mul_eq_zero_iff {f g : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) : f * g = 0 ↔ f = 0 ∨ g = 0 :=
  ⟨fun hfg ↦ (frequently_or_distrib.mp <| .of_forall <| by simpa using congrFun hfg).imp
    (eq_zero_of_frequently (τ := I) hf) (eq_zero_of_frequently hg), by grind⟩

lemma prod_eq_zero_iff {ι : Type*} {f : ι → ℍ → ℂ} {s : Finset ι}
    (hf : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i)) :
    ∏ i ∈ s, f i = 0 ↔ ∃ i ∈ s, f i = 0 := by
  refine ⟨fun h0 ↦ ?_, fun ⟨i, hi, hi'⟩ ↦ Finset.prod_eq_zero hi hi'⟩
  have : ∃ᶠ τ in 𝓝[≠] I, ∏ i ∈ s, f i τ = 0 := .of_forall <| by simpa using congrFun h0
  simp only [Finset.prod_eq_zero_iff, Finset.frequently_exists] at this
  exact this.imp fun i hi ↦ ⟨hi.1, eq_zero_of_frequently (hf i hi.1) hi.2⟩

end UpperHalfPlane
