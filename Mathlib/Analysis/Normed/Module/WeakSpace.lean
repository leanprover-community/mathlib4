/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Normed space instances for `WeakSpace`

This file provides basic instances for `WeakSpace 𝕜 E` in the setting of normed spaces.

## Main definitions

* `WeakSpace.instBornology`: The norm bornology on `WeakSpace 𝕜 E`, inherited from `E`.
* `WeakSpace.instT2Space`: The weak topology on a normed space over `RCLike` is Hausdorff,
  via Hahn–Banach separation.
-/

@[expose] public section

noncomputable section

open Bornology Topology

namespace WeakSpace

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The norm bornology on `WeakSpace 𝕜 E`, inherited from `E`. -/
instance instBornology : Bornology (WeakSpace 𝕜 E) := inferInstanceAs (Bornology E)

/-- A set in `WeakSpace 𝕜 E` is bounded iff its image in `E` is bounded. -/
@[simp]
theorem isBounded_toE_preimage {s : Set E} :
    IsBounded (⇑(toWeakSpace 𝕜 E).symm ⁻¹' s) ↔ IsBounded s :=
  Iff.rfl

/-- A set in `E` is bounded iff its image in `WeakSpace 𝕜 E` is bounded. -/
@[simp]
theorem isBounded_toWeakSpace_preimage {s : Set (WeakSpace 𝕜 E)} :
    IsBounded (⇑(toWeakSpace 𝕜 E) ⁻¹' s) ↔ IsBounded s :=
  Iff.rfl

end NontriviallyNormedField

section RCLike

variable (𝕜 : Type*) [RCLike 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The weak topology on a normed space over `RCLike` is T2 (Hausdorff). This follows from
Hahn–Banach: the continuous linear functionals separate points. -/
instance instT2Space : T2Space (WeakSpace 𝕜 F) :=
  (WeakBilin.isEmbedding (B := (topDualPairing 𝕜 F).flip) fun x y h => by
    obtain ⟨g, _, hg⟩ := exists_dual_vector'' 𝕜 (x - y)
    rw [map_sub, show g x = g y from LinearMap.ext_iff.mp h g, sub_self] at hg
    exact sub_eq_zero.mp (norm_eq_zero.mp (by exact_mod_cast hg.symm))).t2Space

/-- A set in `WeakSpace 𝕜 F` is von Neumann bounded iff it is bounded under
every continuous linear functional. -/
theorem isVonNBounded_iff_forall_eval_bounded {s : Set (WeakSpace 𝕜 F)} :
    Bornology.IsVonNBounded 𝕜 s ↔ ∀ f : StrongDual 𝕜 F, ∃ r : ℝ, ∀ x ∈ s, ‖f x‖ ≤ r := by
  constructor
  · -- Forward: vonN bounded → each eval is bounded
    intro hs f
    -- f is continuous on WeakSpace
    have hcont : Continuous fun x : WeakSpace 𝕜 F => f x :=
      WeakBilin.eval_continuous _ f
    -- f⁻¹'(ball 0 1) is a weak neighborhood of 0
    have hmem : (fun x : WeakSpace 𝕜 F => f x) ⁻¹' Metric.ball 0 1 ∈
        𝓝 (0 : WeakSpace 𝕜 F) :=
      hcont.continuousAt.preimage_mem_nhds (by
        change Metric.ball 0 1 ∈ 𝓝 ((f : F →L[𝕜] 𝕜) 0)
        rw [map_zero]; exact Metric.ball_mem_nhds 0 one_pos)
    -- This neighborhood absorbs s
    obtain ⟨r, hr, hab⟩ := (hs hmem).exists_pos
    refine ⟨r, fun x hx => ?_⟩
    -- Use (r : 𝕜) which has norm r
    have hr_norm : ‖(↑r : 𝕜)‖ = r := by rw [RCLike.norm_ofReal, abs_of_pos hr]
    have hr_ne : (↑r : 𝕜) ≠ 0 := by exact_mod_cast hr.ne'
    have hxV := hab (↑r : 𝕜) (by rw [hr_norm]) hx
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr_ne] at hxV
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hxV
    have hfsmul : f ((↑r : 𝕜)⁻¹ • x) = (↑r : 𝕜)⁻¹ • f x := map_smul f (↑r : 𝕜)⁻¹ (x : F)
    rw [hfsmul, norm_smul, norm_inv, hr_norm] at hxV
    linarith [inv_mul_lt_iff₀ hr |>.mp hxV]
  · -- Backward: each eval bounded → vonN bounded
    intro h V hV
    -- V ∈ nhds 0 in the weak topology (= induced topology from pi)
    let φ : WeakSpace 𝕜 F → (StrongDual 𝕜 F → 𝕜) := fun x f => f x
    have hφ0 : φ 0 = 0 := funext fun f => map_zero f
    -- nhds 0 in WeakSpace = comap φ (nhds 0) in pi
    rw [show 𝓝 (0 : WeakSpace 𝕜 F) = Filter.comap φ (𝓝 0) from
      hφ0 ▸ nhds_induced φ 0, Filter.mem_comap] at hV
    obtain ⟨U, hU, hUV⟩ := hV
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hI, t, ht, htU⟩ := hU
    -- Suffices to show the smaller preimage absorbs s
    apply Absorbs.mono_left _ (Set.Subset.trans (Set.preimage_mono htU) hUV)
    -- Convert preimage of Set.pi to biInter of preimages
    have hpi : φ ⁻¹' I.pi t = ⋂ f ∈ I, (fun (x : WeakSpace 𝕜 F) => f x) ⁻¹' t f := by
      ext x; simp [Set.mem_pi, φ]
    rw [hpi, hI.absorbs_biInter]
    intro f hf
    -- Show each preimage absorbs s via the image being vonN bounded
    obtain ⟨r, hr⟩ := h f
    have h_vonN : Bornology.IsVonNBounded 𝕜 ((fun x : WeakSpace 𝕜 F => f x) '' s) :=
      NormedSpace.image_isVonNBounded_iff (𝕜 := 𝕜).mpr ⟨r, hr⟩
    have h_abs := h_vonN (ht f)
    -- Convert: Absorbs 𝕜 (t f) (f '' s) → Absorbs 𝕜 (f⁻¹' t f) s
    rw [absorbs_iff_eventually_cobounded_mapsTo] at h_abs ⊢
    exact h_abs.mono fun c hc x hx => by
      simp only [Set.mem_preimage]
      have : f (c⁻¹ • x) = c⁻¹ • f x := map_smul f c⁻¹ (x : F)
      rw [this]
      exact hc (Set.mem_image_of_mem _ hx)



end RCLike

end WeakSpace
