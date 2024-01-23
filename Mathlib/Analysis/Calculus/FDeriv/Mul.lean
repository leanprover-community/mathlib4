/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

#align_import analysis.calculus.fderiv.mul from "leanprover-community/mathlib"@"d608fc5d4e69d4cc21885913fb573a88b0deb521"

/-!
# Multiplicative operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* multiplication of a function by a scalar function
* multiplication of two scalar functions
* taking the pointwise multiplicative inverse (i.e. `Inv.inv` or `Ring.inverse`) of a function
-/


open Filter Asymptotics ContinuousLinearMap Set Metric Topology Classical NNReal ENNReal

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

variable {f f₀ f₁ g : E → F}

variable {f' f₀' f₁' g' : E →L[𝕜] F}

variable (e : E →L[𝕜] F)

variable {x : E}

variable {s t : Set E}

variable {L L₁ L₂ : Filter E}

section ClmCompApply

/-! ### Derivative of the pointwise composition/application of continuous linear maps -/


variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] {c : E → G →L[𝕜] H}
  {c' : E →L[𝕜] G →L[𝕜] H} {d : E → F →L[𝕜] G} {d' : E →L[𝕜] F →L[𝕜] G} {u : E → G} {u' : E →L[𝕜] G}

theorem HasStrictFDerivAt.clm_comp (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
    HasStrictFDerivAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x :=
  (isBoundedBilinearMap_comp.hasStrictFDerivAt (c x, d x)).comp x <| hc.prod hd
#align has_strict_fderiv_at.clm_comp HasStrictFDerivAt.clm_comp

theorem HasFDerivWithinAt.clm_comp (hc : HasFDerivWithinAt c c' s x)
    (hd : HasFDerivWithinAt d d' s x) :
    HasFDerivWithinAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') s x :=
  (isBoundedBilinearMap_comp.hasFDerivAt (c x, d x)).comp_hasFDerivWithinAt x <| hc.prod hd
#align has_fderiv_within_at.clm_comp HasFDerivWithinAt.clm_comp

theorem HasFDerivAt.clm_comp (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) :
    HasFDerivAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x :=
  (isBoundedBilinearMap_comp.hasFDerivAt (c x, d x)).comp x <| hc.prod hd
#align has_fderiv_at.clm_comp HasFDerivAt.clm_comp

theorem DifferentiableWithinAt.clm_comp (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    DifferentiableWithinAt 𝕜 (fun y => (c y).comp (d y)) s x :=
  (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).differentiableWithinAt
#align differentiable_within_at.clm_comp DifferentiableWithinAt.clm_comp

theorem DifferentiableAt.clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    DifferentiableAt 𝕜 (fun y => (c y).comp (d y)) x :=
  (hc.hasFDerivAt.clm_comp hd.hasFDerivAt).differentiableAt
#align differentiable_at.clm_comp DifferentiableAt.clm_comp

theorem DifferentiableOn.clm_comp (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s) :
    DifferentiableOn 𝕜 (fun y => (c y).comp (d y)) s := fun x hx => (hc x hx).clm_comp (hd x hx)
#align differentiable_on.clm_comp DifferentiableOn.clm_comp

theorem Differentiable.clm_comp (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) :
    Differentiable 𝕜 fun y => (c y).comp (d y) := fun x => (hc x).clm_comp (hd x)
#align differentiable.clm_comp Differentiable.clm_comp

theorem fderivWithin_clm_comp (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (fun y => (c y).comp (d y)) s x =
      (compL 𝕜 F G H (c x)).comp (fderivWithin 𝕜 d s x) +
        ((compL 𝕜 F G H).flip (d x)).comp (fderivWithin 𝕜 c s x) :=
  (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).fderivWithin hxs
#align fderiv_within_clm_comp fderivWithin_clm_comp

theorem fderiv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (fun y => (c y).comp (d y)) x =
      (compL 𝕜 F G H (c x)).comp (fderiv 𝕜 d x) +
        ((compL 𝕜 F G H).flip (d x)).comp (fderiv 𝕜 c x) :=
  (hc.hasFDerivAt.clm_comp hd.hasFDerivAt).fderiv
#align fderiv_clm_comp fderiv_clm_comp

theorem HasStrictFDerivAt.clm_apply (hc : HasStrictFDerivAt c c' x)
    (hu : HasStrictFDerivAt u u' x) :
    HasStrictFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
  (isBoundedBilinearMap_apply.hasStrictFDerivAt (c x, u x)).comp x (hc.prod hu)
#align has_strict_fderiv_at.clm_apply HasStrictFDerivAt.clm_apply

theorem HasFDerivWithinAt.clm_apply (hc : HasFDerivWithinAt c c' s x)
    (hu : HasFDerivWithinAt u u' s x) :
    HasFDerivWithinAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) s x :=
  (isBoundedBilinearMap_apply.hasFDerivAt (c x, u x)).comp_hasFDerivWithinAt x (hc.prod hu)
#align has_fderiv_within_at.clm_apply HasFDerivWithinAt.clm_apply

theorem HasFDerivAt.clm_apply (hc : HasFDerivAt c c' x) (hu : HasFDerivAt u u' x) :
    HasFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
  (isBoundedBilinearMap_apply.hasFDerivAt (c x, u x)).comp x (hc.prod hu)
#align has_fderiv_at.clm_apply HasFDerivAt.clm_apply

theorem DifferentiableWithinAt.clm_apply (hc : DifferentiableWithinAt 𝕜 c s x)
    (hu : DifferentiableWithinAt 𝕜 u s x) : DifferentiableWithinAt 𝕜 (fun y => (c y) (u y)) s x :=
  (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).differentiableWithinAt
#align differentiable_within_at.clm_apply DifferentiableWithinAt.clm_apply

theorem DifferentiableAt.clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    DifferentiableAt 𝕜 (fun y => (c y) (u y)) x :=
  (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).differentiableAt
#align differentiable_at.clm_apply DifferentiableAt.clm_apply

theorem DifferentiableOn.clm_apply (hc : DifferentiableOn 𝕜 c s) (hu : DifferentiableOn 𝕜 u s) :
    DifferentiableOn 𝕜 (fun y => (c y) (u y)) s := fun x hx => (hc x hx).clm_apply (hu x hx)
#align differentiable_on.clm_apply DifferentiableOn.clm_apply

theorem Differentiable.clm_apply (hc : Differentiable 𝕜 c) (hu : Differentiable 𝕜 u) :
    Differentiable 𝕜 fun y => (c y) (u y) := fun x => (hc x).clm_apply (hu x)
#align differentiable.clm_apply Differentiable.clm_apply

theorem fderivWithin_clm_apply (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s x) :
    fderivWithin 𝕜 (fun y => (c y) (u y)) s x =
      (c x).comp (fderivWithin 𝕜 u s x) + (fderivWithin 𝕜 c s x).flip (u x) :=
  (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).fderivWithin hxs
#align fderiv_within_clm_apply fderivWithin_clm_apply

theorem fderiv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    fderiv 𝕜 (fun y => (c y) (u y)) x = (c x).comp (fderiv 𝕜 u x) + (fderiv 𝕜 c x).flip (u x) :=
  (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).fderiv
#align fderiv_clm_apply fderiv_clm_apply

end ClmCompApply

section ContinuousMultilinearApplyConst

/-! ### Derivative of the application of continuous multilinear maps to a constant -/

variable {ι : Type*} [Fintype ι]
  {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {c : E → ContinuousMultilinearMap 𝕜 M H}
  {c' : E →L[𝕜] ContinuousMultilinearMap 𝕜 M H}

theorem HasStrictFDerivAt.continuousMultilinear_apply_const (hc : HasStrictFDerivAt c c' x)
    (u : ∀ i, M i) : HasStrictFDerivAt (fun y ↦ (c y) u) (c'.flipMultilinear u) x :=
  (ContinuousMultilinearMap.apply 𝕜 M H u).hasStrictFDerivAt.comp x hc

theorem HasFDerivWithinAt.continuousMultilinear_apply_const (hc : HasFDerivWithinAt c c' s x)
    (u : ∀ i, M i) :
    HasFDerivWithinAt (fun y ↦ (c y) u) (c'.flipMultilinear u) s x :=
  (ContinuousMultilinearMap.apply 𝕜 M H u).hasFDerivAt.comp_hasFDerivWithinAt x hc

theorem HasFDerivAt.continuousMultilinear_apply_const (hc : HasFDerivAt c c' x) (u : ∀ i, M i) :
    HasFDerivAt (fun y ↦ (c y) u) (c'.flipMultilinear u) x :=
  (ContinuousMultilinearMap.apply 𝕜 M H u).hasFDerivAt.comp x hc

theorem DifferentiableWithinAt.continuousMultilinear_apply_const
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : ∀ i, M i) :
    DifferentiableWithinAt 𝕜 (fun y ↦ (c y) u) s x :=
  (hc.hasFDerivWithinAt.continuousMultilinear_apply_const u).differentiableWithinAt

theorem DifferentiableAt.continuousMultilinear_apply_const (hc : DifferentiableAt 𝕜 c x)
    (u : ∀ i, M i) :
    DifferentiableAt 𝕜 (fun y ↦ (c y) u) x :=
  (hc.hasFDerivAt.continuousMultilinear_apply_const u).differentiableAt

theorem DifferentiableOn.continuousMultilinear_apply_const (hc : DifferentiableOn 𝕜 c s)
    (u : ∀ i, M i) : DifferentiableOn 𝕜 (fun y ↦ (c y) u) s :=
  fun x hx ↦ (hc x hx).continuousMultilinear_apply_const u

theorem Differentiable.continuousMultilinear_apply_const (hc : Differentiable 𝕜 c) (u : ∀ i, M i) :
    Differentiable 𝕜 fun y ↦ (c y) u := fun x ↦ (hc x).continuousMultilinear_apply_const u

theorem fderivWithin_continuousMultilinear_apply_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : ∀ i, M i) :
    fderivWithin 𝕜 (fun y ↦ (c y) u) s x = ((fderivWithin 𝕜 c s x).flipMultilinear u) :=
  (hc.hasFDerivWithinAt.continuousMultilinear_apply_const u).fderivWithin hxs

theorem fderiv_continuousMultilinear_apply_const (hc : DifferentiableAt 𝕜 c x) (u : ∀ i, M i) :
    (fderiv 𝕜 (fun y ↦ (c y) u) x) = (fderiv 𝕜 c x).flipMultilinear u :=
  (hc.hasFDerivAt.continuousMultilinear_apply_const u).fderiv

/-- Application of a `ContinuousMultilinearMap` to a constant commutes with `fderivWithin`. -/
theorem fderivWithin_continuousMultilinear_apply_const_apply (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : ∀ i, M i) (m : E) :
    (fderivWithin 𝕜 (fun y ↦ (c y) u) s x) m = (fderivWithin 𝕜 c s x) m u := by
  simp [fderivWithin_continuousMultilinear_apply_const hxs hc]

/-- Application of a `ContinuousMultilinearMap` to a constant commutes with `fderiv`. -/
theorem fderiv_continuousMultilinear_apply_const_apply (hc : DifferentiableAt 𝕜 c x)
    (u : ∀ i, M i) (m : E) :
    (fderiv 𝕜 (fun y ↦ (c y) u) x) m = (fderiv 𝕜 c x) m u := by
  simp [fderiv_continuousMultilinear_apply_const hc]

end ContinuousMultilinearApplyConst

section SMul

/-! ### Derivative of the product of a scalar-valued function and a vector-valued function

If `c` is a differentiable scalar-valued function and `f` is a differentiable vector-valued
function, then `fun x ↦ c x • f x` is differentiable as well. Lemmas in this section works for
function `c` taking values in the base field, as well as in a normed algebra over the base
field: e.g., they work for `c : E → ℂ` and `f : E → F` provided that `F` is a complex
normed vector space.
-/


variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]

variable {c : E → 𝕜'} {c' : E →L[𝕜] 𝕜'}

theorem HasStrictFDerivAt.smul (hc : HasStrictFDerivAt c c' x) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun y => c y • f y) (c x • f' + c'.smulRight (f x)) x :=
  (isBoundedBilinearMap_smul.hasStrictFDerivAt (c x, f x)).comp x <| hc.prod hf
#align has_strict_fderiv_at.smul HasStrictFDerivAt.smul

theorem HasFDerivWithinAt.smul (hc : HasFDerivWithinAt c c' s x) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun y => c y • f y) (c x • f' + c'.smulRight (f x)) s x :=
  (isBoundedBilinearMap_smul.hasFDerivAt (c x, f x)).comp_hasFDerivWithinAt x <| hc.prod hf
#align has_fderiv_within_at.smul HasFDerivWithinAt.smul

theorem HasFDerivAt.smul (hc : HasFDerivAt c c' x) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => c y • f y) (c x • f' + c'.smulRight (f x)) x :=
  (isBoundedBilinearMap_smul.hasFDerivAt (c x, f x)).comp x <| hc.prod hf
#align has_fderiv_at.smul HasFDerivAt.smul

theorem DifferentiableWithinAt.smul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (fun y => c y • f y) s x :=
  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).differentiableWithinAt
#align differentiable_within_at.smul DifferentiableWithinAt.smul

@[simp]
theorem DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y => c y • f y) x :=
  (hc.hasFDerivAt.smul hf.hasFDerivAt).differentiableAt
#align differentiable_at.smul DifferentiableAt.smul

theorem DifferentiableOn.smul (hc : DifferentiableOn 𝕜 c s) (hf : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun y => c y • f y) s := fun x hx => (hc x hx).smul (hf x hx)
#align differentiable_on.smul DifferentiableOn.smul

@[simp]
theorem Differentiable.smul (hc : Differentiable 𝕜 c) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 fun y => c y • f y := fun x => (hc x).smul (hf x)
#align differentiable.smul Differentiable.smul

theorem fderivWithin_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (fun y => c y • f y) s x =
      c x • fderivWithin 𝕜 f s x + (fderivWithin 𝕜 c s x).smulRight (f x) :=
  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs
#align fderiv_within_smul fderivWithin_smul

theorem fderiv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun y => c y • f y) x = c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smulRight (f x) :=
  (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv
#align fderiv_smul fderiv_smul

theorem HasStrictFDerivAt.smul_const (hc : HasStrictFDerivAt c c' x) (f : F) :
    HasStrictFDerivAt (fun y => c y • f) (c'.smulRight f) x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasStrictFDerivAt_const f x)
#align has_strict_fderiv_at.smul_const HasStrictFDerivAt.smul_const

theorem HasFDerivWithinAt.smul_const (hc : HasFDerivWithinAt c c' s x) (f : F) :
    HasFDerivWithinAt (fun y => c y • f) (c'.smulRight f) s x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasFDerivWithinAt_const f x s)
#align has_fderiv_within_at.smul_const HasFDerivWithinAt.smul_const

theorem HasFDerivAt.smul_const (hc : HasFDerivAt c c' x) (f : F) :
    HasFDerivAt (fun y => c y • f) (c'.smulRight f) x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasFDerivAt_const f x)
#align has_fderiv_at.smul_const HasFDerivAt.smul_const

theorem DifferentiableWithinAt.smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    DifferentiableWithinAt 𝕜 (fun y => c y • f) s x :=
  (hc.hasFDerivWithinAt.smul_const f).differentiableWithinAt
#align differentiable_within_at.smul_const DifferentiableWithinAt.smul_const

theorem DifferentiableAt.smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    DifferentiableAt 𝕜 (fun y => c y • f) x :=
  (hc.hasFDerivAt.smul_const f).differentiableAt
#align differentiable_at.smul_const DifferentiableAt.smul_const

theorem DifferentiableOn.smul_const (hc : DifferentiableOn 𝕜 c s) (f : F) :
    DifferentiableOn 𝕜 (fun y => c y • f) s := fun x hx => (hc x hx).smul_const f
#align differentiable_on.smul_const DifferentiableOn.smul_const

theorem Differentiable.smul_const (hc : Differentiable 𝕜 c) (f : F) :
    Differentiable 𝕜 fun y => c y • f := fun x => (hc x).smul_const f
#align differentiable.smul_const Differentiable.smul_const

theorem fderivWithin_smul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    fderivWithin 𝕜 (fun y => c y • f) s x = (fderivWithin 𝕜 c s x).smulRight f :=
  (hc.hasFDerivWithinAt.smul_const f).fderivWithin hxs
#align fderiv_within_smul_const fderivWithin_smul_const

theorem fderiv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    fderiv 𝕜 (fun y => c y • f) x = (fderiv 𝕜 c x).smulRight f :=
  (hc.hasFDerivAt.smul_const f).fderiv
#align fderiv_smul_const fderiv_smul_const

end SMul

section Mul

/-! ### Derivative of the product of two functions -/


variable {𝔸 𝔸' : Type*} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸] [NormedAlgebra 𝕜 𝔸']
  {a b : E → 𝔸} {a' b' : E →L[𝕜] 𝔸} {c d : E → 𝔸'} {c' d' : E →L[𝕜] 𝔸'}

theorem HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFDerivAt a a' x)
    (hb : HasStrictFDerivAt b b' x) :
    HasStrictFDerivAt (fun y => a y * b y) (a x • b' + a'.smulRight (b x)) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasStrictFDerivAt (a x, b x)).comp x
    (ha.prod hb)
#align has_strict_fderiv_at.mul' HasStrictFDerivAt.mul'

theorem HasStrictFDerivAt.mul (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
    HasStrictFDerivAt (fun y => c y * d y) (c x • d' + d x • c') x := by
  convert hc.mul' hd
  ext z
  apply mul_comm
#align has_strict_fderiv_at.mul HasStrictFDerivAt.mul

theorem HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a a' s x) (hb : HasFDerivWithinAt b b' s x) :
    HasFDerivWithinAt (fun y => a y * b y) (a x • b' + a'.smulRight (b x)) s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt (a x, b x)).comp_hasFDerivWithinAt
    x (ha.prod hb)
#align has_fderiv_within_at.mul' HasFDerivWithinAt.mul'

theorem HasFDerivWithinAt.mul (hc : HasFDerivWithinAt c c' s x) (hd : HasFDerivWithinAt d d' s x) :
    HasFDerivWithinAt (fun y => c y * d y) (c x • d' + d x • c') s x := by
  convert hc.mul' hd
  ext z
  apply mul_comm
#align has_fderiv_within_at.mul HasFDerivWithinAt.mul

theorem HasFDerivAt.mul' (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
    HasFDerivAt (fun y => a y * b y) (a x • b' + a'.smulRight (b x)) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt (a x, b x)).comp x (ha.prod hb)
#align has_fderiv_at.mul' HasFDerivAt.mul'

theorem HasFDerivAt.mul (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) :
    HasFDerivAt (fun y => c y * d y) (c x • d' + d x • c') x := by
  convert hc.mul' hd
  ext z
  apply mul_comm
#align has_fderiv_at.mul HasFDerivAt.mul

theorem DifferentiableWithinAt.mul (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) : DifferentiableWithinAt 𝕜 (fun y => a y * b y) s x :=
  (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).differentiableWithinAt
#align differentiable_within_at.mul DifferentiableWithinAt.mul

@[simp]
theorem DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    DifferentiableAt 𝕜 (fun y => a y * b y) x :=
  (ha.hasFDerivAt.mul' hb.hasFDerivAt).differentiableAt
#align differentiable_at.mul DifferentiableAt.mul

theorem DifferentiableOn.mul (ha : DifferentiableOn 𝕜 a s) (hb : DifferentiableOn 𝕜 b s) :
    DifferentiableOn 𝕜 (fun y => a y * b y) s := fun x hx => (ha x hx).mul (hb x hx)
#align differentiable_on.mul DifferentiableOn.mul

@[simp]
theorem Differentiable.mul (ha : Differentiable 𝕜 a) (hb : Differentiable 𝕜 b) :
    Differentiable 𝕜 fun y => a y * b y := fun x => (ha x).mul (hb x)
#align differentiable.mul Differentiable.mul

theorem DifferentiableWithinAt.pow (ha : DifferentiableWithinAt 𝕜 a s x) :
    ∀ n : ℕ, DifferentiableWithinAt 𝕜 (fun x => a x ^ n) s x
  | 0 => by simp only [pow_zero, differentiableWithinAt_const]
  | n + 1 => by simp only [pow_succ, DifferentiableWithinAt.pow ha n, ha.mul]
#align differentiable_within_at.pow DifferentiableWithinAt.pow

@[simp]
theorem DifferentiableAt.pow (ha : DifferentiableAt 𝕜 a x) (n : ℕ) :
    DifferentiableAt 𝕜 (fun x => a x ^ n) x :=
  differentiableWithinAt_univ.mp <| ha.differentiableWithinAt.pow n
#align differentiable_at.pow DifferentiableAt.pow

theorem DifferentiableOn.pow (ha : DifferentiableOn 𝕜 a s) (n : ℕ) :
    DifferentiableOn 𝕜 (fun x => a x ^ n) s := fun x h => (ha x h).pow n
#align differentiable_on.pow DifferentiableOn.pow

@[simp]
theorem Differentiable.pow (ha : Differentiable 𝕜 a) (n : ℕ) : Differentiable 𝕜 fun x => a x ^ n :=
  fun x => (ha x).pow n
#align differentiable.pow Differentiable.pow

theorem fderivWithin_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) :
    fderivWithin 𝕜 (fun y => a y * b y) s x =
      a x • fderivWithin 𝕜 b s x + (fderivWithin 𝕜 a s x).smulRight (b x) :=
  (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).fderivWithin hxs
#align fderiv_within_mul' fderivWithin_mul'

theorem fderivWithin_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (fun y => c y * d y) s x =
      c x • fderivWithin 𝕜 d s x + d x • fderivWithin 𝕜 c s x :=
  (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs
#align fderiv_within_mul fderivWithin_mul

theorem fderiv_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    fderiv 𝕜 (fun y => a y * b y) x = a x • fderiv 𝕜 b x + (fderiv 𝕜 a x).smulRight (b x) :=
  (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv
#align fderiv_mul' fderiv_mul'

theorem fderiv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (fun y => c y * d y) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
  (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv
#align fderiv_mul fderiv_mul

theorem HasStrictFDerivAt.mul_const' (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
    HasStrictFDerivAt (fun y => a y * b) (a'.smulRight b) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasStrictFDerivAt.comp x ha
#align has_strict_fderiv_at.mul_const' HasStrictFDerivAt.mul_const'

theorem HasStrictFDerivAt.mul_const (hc : HasStrictFDerivAt c c' x) (d : 𝔸') :
    HasStrictFDerivAt (fun y => c y * d) (d • c') x := by
  convert hc.mul_const' d
  ext z
  apply mul_comm
#align has_strict_fderiv_at.mul_const HasStrictFDerivAt.mul_const

theorem HasFDerivWithinAt.mul_const' (ha : HasFDerivWithinAt a a' s x) (b : 𝔸) :
    HasFDerivWithinAt (fun y => a y * b) (a'.smulRight b) s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasFDerivAt.comp_hasFDerivWithinAt x ha
#align has_fderiv_within_at.mul_const' HasFDerivWithinAt.mul_const'

theorem HasFDerivWithinAt.mul_const (hc : HasFDerivWithinAt c c' s x) (d : 𝔸') :
    HasFDerivWithinAt (fun y => c y * d) (d • c') s x := by
  convert hc.mul_const' d
  ext z
  apply mul_comm
#align has_fderiv_within_at.mul_const HasFDerivWithinAt.mul_const

theorem HasFDerivAt.mul_const' (ha : HasFDerivAt a a' x) (b : 𝔸) :
    HasFDerivAt (fun y => a y * b) (a'.smulRight b) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasFDerivAt.comp x ha
#align has_fderiv_at.mul_const' HasFDerivAt.mul_const'

theorem HasFDerivAt.mul_const (hc : HasFDerivAt c c' x) (d : 𝔸') :
    HasFDerivAt (fun y => c y * d) (d • c') x := by
  convert hc.mul_const' d
  ext z
  apply mul_comm
#align has_fderiv_at.mul_const HasFDerivAt.mul_const

theorem DifferentiableWithinAt.mul_const (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    DifferentiableWithinAt 𝕜 (fun y => a y * b) s x :=
  (ha.hasFDerivWithinAt.mul_const' b).differentiableWithinAt
#align differentiable_within_at.mul_const DifferentiableWithinAt.mul_const

theorem DifferentiableAt.mul_const (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    DifferentiableAt 𝕜 (fun y => a y * b) x :=
  (ha.hasFDerivAt.mul_const' b).differentiableAt
#align differentiable_at.mul_const DifferentiableAt.mul_const

theorem DifferentiableOn.mul_const (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) :
    DifferentiableOn 𝕜 (fun y => a y * b) s := fun x hx => (ha x hx).mul_const b
#align differentiable_on.mul_const DifferentiableOn.mul_const

theorem Differentiable.mul_const (ha : Differentiable 𝕜 a) (b : 𝔸) :
    Differentiable 𝕜 fun y => a y * b := fun x => (ha x).mul_const b
#align differentiable.mul_const Differentiable.mul_const

theorem fderivWithin_mul_const' (hxs : UniqueDiffWithinAt 𝕜 s x)
    (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    fderivWithin 𝕜 (fun y => a y * b) s x = (fderivWithin 𝕜 a s x).smulRight b :=
  (ha.hasFDerivWithinAt.mul_const' b).fderivWithin hxs
#align fderiv_within_mul_const' fderivWithin_mul_const'

theorem fderivWithin_mul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸') :
    fderivWithin 𝕜 (fun y => c y * d) s x = d • fderivWithin 𝕜 c s x :=
  (hc.hasFDerivWithinAt.mul_const d).fderivWithin hxs
#align fderiv_within_mul_const fderivWithin_mul_const

theorem fderiv_mul_const' (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    fderiv 𝕜 (fun y => a y * b) x = (fderiv 𝕜 a x).smulRight b :=
  (ha.hasFDerivAt.mul_const' b).fderiv
#align fderiv_mul_const' fderiv_mul_const'

theorem fderiv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸') :
    fderiv 𝕜 (fun y => c y * d) x = d • fderiv 𝕜 c x :=
  (hc.hasFDerivAt.mul_const d).fderiv
#align fderiv_mul_const fderiv_mul_const

theorem HasStrictFDerivAt.const_mul (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
    HasStrictFDerivAt (fun y => b * a y) (b • a') x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasStrictFDerivAt.comp x ha
#align has_strict_fderiv_at.const_mul HasStrictFDerivAt.const_mul

theorem HasFDerivWithinAt.const_mul (ha : HasFDerivWithinAt a a' s x) (b : 𝔸) :
    HasFDerivWithinAt (fun y => b * a y) (b • a') s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasFDerivAt.comp_hasFDerivWithinAt x ha
#align has_fderiv_within_at.const_mul HasFDerivWithinAt.const_mul

theorem HasFDerivAt.const_mul (ha : HasFDerivAt a a' x) (b : 𝔸) :
    HasFDerivAt (fun y => b * a y) (b • a') x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasFDerivAt.comp x ha
#align has_fderiv_at.const_mul HasFDerivAt.const_mul

theorem DifferentiableWithinAt.const_mul (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    DifferentiableWithinAt 𝕜 (fun y => b * a y) s x :=
  (ha.hasFDerivWithinAt.const_mul b).differentiableWithinAt
#align differentiable_within_at.const_mul DifferentiableWithinAt.const_mul

theorem DifferentiableAt.const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    DifferentiableAt 𝕜 (fun y => b * a y) x :=
  (ha.hasFDerivAt.const_mul b).differentiableAt
#align differentiable_at.const_mul DifferentiableAt.const_mul

theorem DifferentiableOn.const_mul (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) :
    DifferentiableOn 𝕜 (fun y => b * a y) s := fun x hx => (ha x hx).const_mul b
#align differentiable_on.const_mul DifferentiableOn.const_mul

theorem Differentiable.const_mul (ha : Differentiable 𝕜 a) (b : 𝔸) :
    Differentiable 𝕜 fun y => b * a y := fun x => (ha x).const_mul b
#align differentiable.const_mul Differentiable.const_mul

theorem fderivWithin_const_mul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    fderivWithin 𝕜 (fun y => b * a y) s x = b • fderivWithin 𝕜 a s x :=
  (ha.hasFDerivWithinAt.const_mul b).fderivWithin hxs
#align fderiv_within_const_mul fderivWithin_const_mul

theorem fderiv_const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    fderiv 𝕜 (fun y => b * a y) x = b • fderiv 𝕜 a x :=
  (ha.hasFDerivAt.const_mul b).fderiv
#align fderiv_const_mul fderiv_const_mul

end Mul

section AlgebraInverse

variable {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]

open NormedRing ContinuousLinearMap Ring

/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
operation is the linear map `fun t ↦ - x⁻¹ * t * x⁻¹`.

TODO: prove that `Ring.inverse` is analytic and use it to prove a `HasStrictFDerivAt` lemma.
TODO (low prio): prove a version without assumption `[CompleteSpace R]` but within the set of
units. -/
theorem hasFDerivAt_ring_inverse (x : Rˣ) :
    HasFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x :=
  have : (fun t : R => Ring.inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =o[𝓝 0] id :=
    (inverse_add_norm_diff_second_order x).trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  by simpa [hasFDerivAt_iff_isLittleO_nhds_zero] using this
#align has_fderiv_at_ring_inverse hasFDerivAt_ring_inverse

theorem differentiableAt_inverse {x : R} (hx : IsUnit x) :
    DifferentiableAt 𝕜 (@Ring.inverse R _) x :=
  let ⟨u, hu⟩ := hx; hu ▸ (hasFDerivAt_ring_inverse u).differentiableAt

theorem differentiableWithinAt_inverse {x : R} (hx : IsUnit x) (s : Set R) :
    DifferentiableWithinAt 𝕜 (@Ring.inverse R _) s x :=
  (differentiableAt_inverse hx).differentiableWithinAt
#align differentiable_within_at_inverse differentiableWithinAt_inverse

theorem differentiableOn_inverse : DifferentiableOn 𝕜 (@Ring.inverse R _) {x | IsUnit x} :=
  fun _x hx => differentiableWithinAt_inverse hx _
#align differentiable_on_inverse differentiableOn_inverse

theorem fderiv_inverse (x : Rˣ) : fderiv 𝕜 (@Ring.inverse R _) x = -mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹ :=
  (hasFDerivAt_ring_inverse x).fderiv
#align fderiv_inverse fderiv_inverse

variable {h : E → R} {z : E} {S : Set E}

theorem DifferentiableWithinAt.inverse (hf : DifferentiableWithinAt 𝕜 h S z) (hz : IsUnit (h z)) :
    DifferentiableWithinAt 𝕜 (fun x => Ring.inverse (h x)) S z :=
  (differentiableAt_inverse hz).comp_differentiableWithinAt z hf
#align differentiable_within_at.inverse DifferentiableWithinAt.inverse

@[simp]
theorem DifferentiableAt.inverse (hf : DifferentiableAt 𝕜 h z) (hz : IsUnit (h z)) :
    DifferentiableAt 𝕜 (fun x => Ring.inverse (h x)) z :=
  (differentiableAt_inverse hz).comp z hf
#align differentiable_at.inverse DifferentiableAt.inverse

theorem DifferentiableOn.inverse (hf : DifferentiableOn 𝕜 h S) (hz : ∀ x ∈ S, IsUnit (h x)) :
    DifferentiableOn 𝕜 (fun x => Ring.inverse (h x)) S := fun x h => (hf x h).inverse (hz x h)
#align differentiable_on.inverse DifferentiableOn.inverse

@[simp]
theorem Differentiable.inverse (hf : Differentiable 𝕜 h) (hz : ∀ x, IsUnit (h x)) :
    Differentiable 𝕜 fun x => Ring.inverse (h x) := fun x => (hf x).inverse (hz x)
#align differentiable.inverse Differentiable.inverse

end AlgebraInverse

/-! ### Derivative of the inverse in a division ring

Note these lemmas are primed as they need `CompleteSpace R`, whereas the other lemmas in
`Mathlib/Analysis/Calculus/Deriv/Inv.lean` do not, but instead need `NontriviallyNormedField R`.
-/

section DivisionRingInverse

variable {R : Type*} [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]

open NormedRing ContinuousLinearMap Ring

/-- At an invertible element `x` of a normed division algebra `R`, the Fréchet derivative of the
inversion operation is the linear map `λ t, - x⁻¹ * t * x⁻¹`. -/
theorem hasFDerivAt_inv' {x : R} (hx : x ≠ 0) : HasFDerivAt Inv.inv (-mulLeftRight 𝕜 R x⁻¹ x⁻¹) x :=
  by simpa using hasFDerivAt_ring_inverse (Units.mk0 _ hx)
#align has_fderiv_at_inv' hasFDerivAt_inv'

theorem differentiableAt_inv' {x : R} (hx : x ≠ 0) : DifferentiableAt 𝕜 Inv.inv x :=
  (hasFDerivAt_inv' hx).differentiableAt
#align differentiable_at_inv' differentiableAt_inv'

theorem differentiableWithinAt_inv' {x : R} (hx : x ≠ 0) (s : Set R) :
    DifferentiableWithinAt 𝕜 (fun x => x⁻¹) s x :=
  (differentiableAt_inv' hx).differentiableWithinAt
#align differentiable_within_at_inv' differentiableWithinAt_inv'

theorem differentiableOn_inv' : DifferentiableOn 𝕜 (fun x : R => x⁻¹) {x | x ≠ 0} := fun _x hx =>
  differentiableWithinAt_inv' hx _
#align differentiable_on_inv' differentiableOn_inv'

/-- Non-commutative version of `fderiv_inv` -/
theorem fderiv_inv' {x : R} (hx : x ≠ 0) : fderiv 𝕜 Inv.inv x = -mulLeftRight 𝕜 R x⁻¹ x⁻¹ :=
  (hasFDerivAt_inv' hx).fderiv
#align fderiv_inv' fderiv_inv'

/-- Non-commutative version of `fderivWithin_inv` -/
theorem fderivWithin_inv' {s : Set R} {x : R} (hx : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => x⁻¹) s x = -mulLeftRight 𝕜 R x⁻¹ x⁻¹ := by
  rw [DifferentiableAt.fderivWithin (differentiableAt_inv' hx) hxs]
  exact fderiv_inv' hx
#align fderiv_within_inv' fderivWithin_inv'

variable {h : E → R} {z : E} {S : Set E}

theorem DifferentiableWithinAt.inv' (hf : DifferentiableWithinAt 𝕜 h S z) (hz : h z ≠ 0) :
    DifferentiableWithinAt 𝕜 (fun x => (h x)⁻¹) S z :=
  (differentiableAt_inv' hz).comp_differentiableWithinAt z hf
#align differentiable_within_at.inv' DifferentiableWithinAt.inv'

@[simp]
theorem DifferentiableAt.inv' (hf : DifferentiableAt 𝕜 h z) (hz : h z ≠ 0) :
    DifferentiableAt 𝕜 (fun x => (h x)⁻¹) z :=
  (differentiableAt_inv' hz).comp z hf
#align differentiable_at.inv' DifferentiableAt.inv'

theorem DifferentiableOn.inv' (hf : DifferentiableOn 𝕜 h S) (hz : ∀ x ∈ S, h x ≠ 0) :
    DifferentiableOn 𝕜 (fun x => (h x)⁻¹) S := fun x h => (hf x h).inv' (hz x h)
#align differentiable_on.inv' DifferentiableOn.inv'

@[simp]
theorem Differentiable.inv' (hf : Differentiable 𝕜 h) (hz : ∀ x, h x ≠ 0) :
    Differentiable 𝕜 fun x => (h x)⁻¹ := fun x => (hf x).inv' (hz x)
#align differentiable.inv' Differentiable.inv'

end DivisionRingInverse

end
