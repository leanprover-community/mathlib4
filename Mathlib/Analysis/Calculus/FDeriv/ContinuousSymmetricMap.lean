/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
public import Mathlib.Analysis.Normed.Module.Symmetric.Basic

/-!
# Derivatives of operations on continuous symmetric maps

In this file we prove formulas for the derivatives of

- `ContinuousSymmetricMap.compContinuousLinearMap`, the pullback of a continuous symmetric map
  along a continuous linear map;
- application of a `ContinuousSymmetricMap` as a function of both the map and the vectors.
-/

public section

variable {𝕜 ι E F G H : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

open ContinuousSymmetricMap
open scoped Topology

section CompContinuousLinearMap

variable
  {f : E → G [Sym^ι]→L[𝕜] H} {f' : E →L[𝕜] G [Sym^ι]→L[𝕜] H}
  {g : E → F →L[𝕜] G} {g' : E →L[𝕜] F →L[𝕜] G}
  {s : Set E} {x : E}

/-!
### Derivative of the pullback

In this section we prove a formula for the derivative
of the pullback of a continuous symmetric map along a continuous linear map,
as a function of both maps.
-/

theorem ContinuousSymmetricMap.hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff [Finite ι] :
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

theorem ContinuousSymmetricMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg : (G [Sym^ι]→L[𝕜] H) × (F →L[𝕜] G)) :
    HasStrictFDerivAt
      (fun fg : (G [Sym^ι]→L[𝕜] H) × (F →L[𝕜] G) ↦ fg.1.compContinuousLinearMap fg.2)
      (compContinuousLinearMapCLM fg.2 ∘L .fst _ _ _ +
        fg.1.fderivCompContinuousLinearMap fg.2 ∘L .snd _ _ _)
      fg := by
  rw [← hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff]
  have H₁ := ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg.1.1, fun _ : ι ↦ fg.2)
  have H₂ := ((toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt (x := fg.1))
  have H₃ := hasStrictFDerivAt_pi.mpr fun i : ι ↦ hasStrictFDerivAt_id (𝕜 := 𝕜) fg.2
  exact H₁.comp fg (H₂.prodMap fg H₃)

theorem HasStrictFDerivAt.continuousSymmetricMapCompContinuousLinearMap
    (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun x ↦ (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') x :=
  hasStrictFDerivAt_compContinuousLinearMap (f x, g x) |>.comp x (hf.prodMk hg)

theorem HasFDerivAt.continuousSymmetricMapCompContinuousLinearMap
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun x ↦ (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') x := by
  convert hasStrictFDerivAt_compContinuousLinearMap (f x, (g x)) |>.hasFDerivAt
    |>.comp x (hf.prodMk hg)

theorem HasFDerivWithinAt.continuousSymmetricMapCompContinuousLinearMap
    (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x) :
    HasFDerivWithinAt (fun x ↦ (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') s x := by
  convert hasStrictFDerivAt_compContinuousLinearMap (f x, (g x)) |>.hasFDerivAt
    |>.comp_hasFDerivWithinAt x (hf.prodMk hg)

theorem fderivWithin_continuousSymmetricMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) s x =
      compContinuousLinearMapCLM (g x) ∘L fderivWithin 𝕜 f s x +
        (f x).fderivCompContinuousLinearMap (g x) ∘L fderivWithin 𝕜 g s x :=
  hf.hasFDerivWithinAt.continuousSymmetricMapCompContinuousLinearMap (hg.hasFDerivWithinAt)
    |>.fderivWithin hs

theorem fderiv_continuousSymmetricMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) x =
      compContinuousLinearMapCLM (g x) ∘L fderiv 𝕜 f x +
        (f x).fderivCompContinuousLinearMap (g x) ∘L fderiv 𝕜 g x :=
  hf.hasFDerivAt.continuousSymmetricMapCompContinuousLinearMap (hg.hasFDerivAt) |>.fderiv

end HasFDerivAt

/-!
### Differentiability of the pullback

In this section we prove that the pullback of a continuous symmetric map
along a continuous linear map is differentiable with respect to a parameter,
provided that both maps are differentiable.
-/

variable [Finite ι]

theorem DifferentiableWithinAt.continuousSymmetricMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) :
    DifferentiableWithinAt 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) s x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousSymmetricMapCompContinuousLinearMap hg.hasFDerivWithinAt
    |>.differentiableWithinAt

theorem DifferentiableAt.continuousSymmetricMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousSymmetricMapCompContinuousLinearMap hg.hasFDerivAt
    |>.differentiableAt

end CompContinuousLinearMap

/-!
### Derivative of a continuous symmetric map applied to a tuple of vectors

In this section we prove the formula for the derivative `D_xf(x; g_0(x), ..., g_n(x))`.
-/

section Apply

variable {f : E → F [Sym^ι]→L[𝕜] G} {f' : E →L[𝕜] F [Sym^ι]→L[𝕜] G}
  {g : ι → E → F} {g' : ι → E →L[𝕜] F}
  {s : Set E} {x : E}

section HasFDerivAt

variable [Fintype ι] [DecidableEq ι]

namespace ContinuousSymmetricMap

theorem hasStrictFDerivAt (f : E [Sym^ι]→L[𝕜] F) (x : ι → E) :
    HasStrictFDerivAt f (f.1.linearDeriv x) x :=
  f.1.hasStrictFDerivAt x

theorem hasFDerivAt (f : E [Sym^ι]→L[𝕜] F) (x : ι → E) : HasFDerivAt f (f.1.linearDeriv x) x :=
  f.1.hasFDerivAt x

theorem hasFDerivWithinAt (f : E [Sym^ι]→L[𝕜] F) (s : Set (ι → E)) (x : ι → E) :
    HasFDerivWithinAt f (f.1.linearDeriv x) s x :=
  (f.hasFDerivAt x).hasFDerivWithinAt

end ContinuousSymmetricMap

theorem HasStrictFDerivAt.continuousSymmetricMap_apply (hf : HasStrictFDerivAt f f' x)
    (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) x) :
    HasStrictFDerivAt
      (fun x ↦ f x (g · x))
      (apply 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i)
      x :=
  (toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt.comp x hf
    |>.continuousMultilinearMap_apply hg

theorem HasFDerivAt.continuousSymmetricMap_apply (hf : HasFDerivAt f f' x)
    (hg : ∀ i, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt
      (fun x ↦ f x (g · x))
      (apply 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i)
      x :=
  (toContinuousMultilinearMapCLM 𝕜).hasFDerivAt.comp x hf
    |>.continuousMultilinearMap_apply hg

theorem HasFDerivWithinAt.continuousSymmetricMap_apply (hf : HasFDerivWithinAt f f' s x)
    (hg : ∀ i, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt
      (fun x ↦ f x (g · x))
      (apply 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i)
      s x :=
  (toContinuousMultilinearMapCLM 𝕜).hasFDerivAt.comp_hasFDerivWithinAt x hf
    |>.continuousMultilinearMap_apply hg

theorem fderivWithin_continuousSymmetricMap_apply (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : ∀ i, DifferentiableWithinAt 𝕜 (g i) s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x ↦ f x (g · x)) s x =
      apply 𝕜 F G (g · x) ∘L fderivWithin 𝕜 f s x +
        ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L fderivWithin 𝕜 (g i) s x :=
  hf.hasFDerivWithinAt.continuousSymmetricMap_apply (fun i ↦ (hg i).hasFDerivWithinAt)
    |>.fderivWithin hs

theorem fderivWithin_continuousSymmetricMap_apply_apply (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : ∀ i, DifferentiableWithinAt 𝕜 (g i) s x) (hs : UniqueDiffWithinAt 𝕜 s x) (dx : E) :
    fderivWithin 𝕜 (fun x ↦ f x (g · x)) s x dx =
      fderivWithin 𝕜 f s x dx (g · x) +
        ∑ i, f x (Function.update (g · x) i (fderivWithin 𝕜 (g i) s x dx)) := by
  simp [fderivWithin_continuousSymmetricMap_apply, *]

theorem fderiv_continuousSymmetricMap_apply (hf : DifferentiableAt 𝕜 f x)
    (hg : ∀ i, DifferentiableAt 𝕜 (g i) x) :
    fderiv 𝕜 (fun x ↦ f x (g · x)) x =
      apply 𝕜 F G (g · x) ∘L fderiv 𝕜 f x +
        ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L fderiv 𝕜 (g i) x :=
  hf.hasFDerivAt.continuousSymmetricMap_apply (fun i ↦ (hg i).hasFDerivAt) |>.fderiv

theorem fderiv_continuousSymmetricMap_apply_apply (hf : DifferentiableAt 𝕜 f x)
    (hg : ∀ i, DifferentiableAt 𝕜 (g i) x) (dx : E) :
    fderiv 𝕜 (fun x ↦ f x (g · x)) x dx =
      fderiv 𝕜 f x dx (g · x) +
        ∑ i, f x (Function.update (g · x) i (fderiv 𝕜 (g i) x dx)) := by
  simp [fderiv_continuousSymmetricMap_apply, *]

end HasFDerivAt

variable [Finite ι]

theorem DifferentiableWithinAt.continuousSymmetricMap_apply (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : ∀ i, DifferentiableWithinAt 𝕜 (g i) s x) :
    DifferentiableWithinAt 𝕜 (fun x ↦ f x (g · x)) s x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousSymmetricMap_apply (fun i ↦ (hg i).hasFDerivWithinAt)
    |>.differentiableWithinAt

theorem DifferentiableAt.continuousSymmetricMap_apply (hf : DifferentiableAt 𝕜 f x)
    (hg : ∀ i, DifferentiableAt 𝕜 (g i) x) : DifferentiableAt 𝕜 (fun x ↦ f x (g · x)) x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousSymmetricMap_apply (fun i ↦ (hg i).hasFDerivAt)
    |>.differentiableAt

theorem DifferentiableOn.continuousSymmetricMap_apply (hf : DifferentiableOn 𝕜 f s)
    (hg : ∀ i, DifferentiableOn 𝕜 (g i) s) : DifferentiableOn 𝕜 (fun x ↦ f x (g · x)) s :=
  fun x hx ↦ (hf x hx).continuousSymmetricMap_apply (hg · x hx)

theorem Differentiable.continuousSymmetricMap_apply (hf : Differentiable 𝕜 f)
    (hg : ∀ i, Differentiable 𝕜 (g i)) : Differentiable 𝕜 (fun x ↦ f x (g · x)) :=
  fun x ↦ (hf x).continuousSymmetricMap_apply (hg · x)

theorem ContinuousSymmetricMap.differentiable (f : E [Sym^ι]→L[𝕜] F) : Differentiable 𝕜 f := by
  cases nonempty_fintype ι
  apply Differentiable.continuousSymmetricMap_apply <;> fun_prop

end Apply
