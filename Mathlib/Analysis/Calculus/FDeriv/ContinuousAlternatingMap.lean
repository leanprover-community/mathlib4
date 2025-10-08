/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import Mathlib.Analysis.NormedSpace.Alternating.Basic

/-!
TODO
-/

variable {𝕜 ι E F G H : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {f : E → G [⋀^ι]→L[𝕜] H} {f' : E →L[𝕜] G [⋀^ι]→L[𝕜] H}
  {g : E → F →L[𝕜] G} {g' : E →L[𝕜] F →L[𝕜] G}
  {s : Set E} {x : E}

open ContinuousAlternatingMap
open scoped Topology

theorem ContinuousAlternatingMap.hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff
    [Finite ι] :
    HasStrictFDerivAt (toContinuousMultilinearMap ∘ f) (toContinuousMultilinearMapCLM 𝕜 ∘L f') x ↔
      HasStrictFDerivAt f f' x := by
  cases nonempty_fintype ι
  constructor <;> intro h
  · rw [hasStrictFDerivAt_iff_isLittleOTVS] at h ⊢
    refine Asymptotics.IsBigOTVS.trans_isLittleOTVS ?_ h
    simp only [Function.comp_apply, ← toContinuousMultilinearMapCLM_apply 𝕜,
      ContinuousLinearMap.comp_apply, ← map_sub]
    apply LinearMap.isBigOTVS_rev_comp
    simp [isEmbedding_toContinuousMultilinearMap.nhds_eq_comap]
  · exact (toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt.comp x h

section HasFDerivAt

variable [Fintype ι] [DecidableEq ι]

theorem ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg : (G [⋀^ι]→L[𝕜] H) × (F →L[𝕜] G)) :
    HasStrictFDerivAt
      (fun fg : (G [⋀^ι]→L[𝕜] H) × (F →L[𝕜] G) ↦ fg.1.compContinuousLinearMap fg.2)
      (compContinuousLinearMapCLM fg.2 ∘L .fst _ _ _ +
        fg.1.fderivCompContinuousLinearMap fg.2 ∘L .snd _ _ _)
      fg := by
  rw [← hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff]
  have H₁ := ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg.1.1, fun _ : ι ↦ fg.2)
  have H₂ := ((toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt (x := fg.1))
  have H₃ := hasStrictFDerivAt_pi.mpr fun i : ι ↦ hasStrictFDerivAt_id (𝕜 := 𝕜) fg.2
  exact H₁.comp fg (H₂.prodMap fg H₃)

theorem HasStrictFDerivAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun x ↦ (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') x :=
  hasStrictFDerivAt_compContinuousLinearMap (f x, g x) |>.comp x (hf.prodMk hg)

theorem HasFDerivAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun x ↦ (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') x := by
  convert hasStrictFDerivAt_compContinuousLinearMap (f x, (g x)) |>.hasFDerivAt
    |>.comp x (hf.prodMk hg)

theorem HasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x) :
    HasFDerivWithinAt (fun x ↦ (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') s x := by
  convert hasStrictFDerivAt_compContinuousLinearMap (f x, (g x)) |>.hasFDerivAt
    |>.comp_hasFDerivWithinAt x (hf.prodMk hg)

theorem fderivWithin_continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) s x =
      compContinuousLinearMapCLM (g x) ∘L fderivWithin 𝕜 f s x +
        (f x).fderivCompContinuousLinearMap (g x) ∘L fderivWithin 𝕜 g s x :=
  hf.hasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap (hg.hasFDerivWithinAt)
    |>.fderivWithin hs

theorem fderiv_continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) x =
      compContinuousLinearMapCLM (g x) ∘L fderiv 𝕜 f x +
        (f x).fderivCompContinuousLinearMap (g x) ∘L fderiv 𝕜 g x :=
  hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap (hg.hasFDerivAt) |>.fderiv

end HasFDerivAt

variable [Finite ι]

theorem DifferentiableWithinAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) :
    DifferentiableWithinAt 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) s x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap hg.hasFDerivWithinAt
    |>.differentiableWithinAt

theorem DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap hg.hasFDerivAt
    |>.differentiableAt
