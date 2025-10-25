/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Derivatives of operations on continuous multilinear maps

In this file we prove a formula
for the derivative of `fun x ↦ (f x).compContinuousLinearMap (g · x)`,
where `f x` is a continuous multilinear map
and `g i x`, `i : ι`, is a family of continuous linear maps.
-/

variable {𝕜 ι E : Type*} {F G : ι → Type*} {H : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {f : E → ContinuousMultilinearMap 𝕜 G H} {f' : E →L[𝕜] ContinuousMultilinearMap 𝕜 G H}
  {g : ∀ i, E → F i →L[𝕜] G i} {g' : ∀ i, E →L[𝕜] F i →L[𝕜] G i}
  {s : Set E} {x : E}

open ContinuousMultilinearMap

section HasFDerivAt

variable [Fintype ι] [DecidableEq ι]

theorem ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg : ContinuousMultilinearMap 𝕜 G H × ∀ i, F i →L[𝕜] G i) :
    HasStrictFDerivAt
      (fun fg : ContinuousMultilinearMap 𝕜 G H × ∀ i, F i →L[𝕜] G i ↦
        fg.1.compContinuousLinearMap fg.2)
      (compContinuousLinearMapL fg.2 ∘L .fst _ _ _ +
        fg.1.fderivCompContinuousLinearMap fg.2 ∘L .snd _ _ _)
      fg := by
  have := (compContinuousLinearMapContinuousMultilinear 𝕜 F G H).hasStrictFDerivAt fg.2
  convert this.comp fg hasStrictFDerivAt_snd |>.clm_apply hasStrictFDerivAt_fst
  ext <;> simp [fderivCompContinuousLinearMap]

theorem HasStrictFDerivAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : HasStrictFDerivAt f f' x) (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) x) :
    HasStrictFDerivAt (fun x ↦ (f x).compContinuousLinearMap (g · x))
      (compContinuousLinearMapL (g · x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi g') x :=
  hasStrictFDerivAt_compContinuousLinearMap (f x, (g · x))
    |>.comp x (hf.prodMk (hasStrictFDerivAt_pi.2 hg))

theorem HasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : HasFDerivAt f f' x) (hg : ∀ i, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt (fun x ↦ (f x).compContinuousLinearMap (g · x))
      (compContinuousLinearMapL (g · x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi g') x := by
  convert hasStrictFDerivAt_compContinuousLinearMap (f x, (g · x)) |>.hasFDerivAt
    |>.comp x (hf.prodMk (hasFDerivAt_pi.2 hg))

theorem HasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : HasFDerivWithinAt f f' s x) (hg : ∀ i, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt (fun x ↦ (f x).compContinuousLinearMap (g · x))
      (compContinuousLinearMapL (g · x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi g') s x := by
  convert hasStrictFDerivAt_compContinuousLinearMap (f x, (g · x)) |>.hasFDerivAt
    |>.comp_hasFDerivWithinAt x (hf.prodMk (hasFDerivWithinAt_pi.2 hg))

theorem fderivWithin_continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : ∀ i, DifferentiableWithinAt 𝕜 (g i) s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g · x)) s x =
      compContinuousLinearMapL (g · x) ∘L fderivWithin 𝕜 f s x +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi fun i ↦ fderivWithin 𝕜 (g i) s x :=
  hf.hasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
    (fun i ↦ (hg i).hasFDerivWithinAt) |>.fderivWithin hs

theorem fderiv_continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : ∀ i, DifferentiableAt 𝕜 (g i) x) :
    fderiv 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g · x)) x =
      compContinuousLinearMapL (g · x) ∘L fderiv 𝕜 f x +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi fun i ↦ fderiv 𝕜 (g i) x :=
  hf.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
    (fun i ↦ (hg i).hasFDerivAt) |>.fderiv

end HasFDerivAt

variable [Finite ι]

theorem DifferentiableWithinAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : ∀ i, DifferentiableWithinAt 𝕜 (g i) s x) :
    DifferentiableWithinAt 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g · x)) s x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
    (fun i ↦ (hg i).hasFDerivWithinAt) |>.differentiableWithinAt

theorem DifferentiableAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : ∀ i, DifferentiableAt 𝕜 (g i) x) :
    DifferentiableAt 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g · x)) x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
    (fun i ↦ (hg i).hasFDerivAt) |>.differentiableAt

theorem DifferentiableOn.continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableOn 𝕜 f s) (hg : ∀ i, DifferentiableOn 𝕜 (g i) s) :
    DifferentiableOn 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g · x)) s := fun x hx ↦
  (hf x hx).continuousMultilinearMapCompContinuousLinearMap (hg · x hx)

theorem Differentiable.continuousMultilinearMapCompContinuousLinearMap
    (hf : Differentiable 𝕜 f) (hg : ∀ i, Differentiable 𝕜 (g i)) :
    Differentiable 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g · x)) := fun x ↦
  (hf x).continuousMultilinearMapCompContinuousLinearMap (hg · x)
