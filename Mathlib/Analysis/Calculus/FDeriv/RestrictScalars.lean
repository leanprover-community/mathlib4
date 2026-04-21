/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The derivative of the scalar restriction of a linear map

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
the scalar restriction of a linear map.
-/
set_option backward.defeqAttrib.useBackward true

public section


open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section RestrictScalars

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is differentiable over `ℂ`, then it is differentiable over `ℝ`. In this paragraph,
we give variants of this statement, in the general situation where `ℂ` and `ℝ` are replaced
respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra over `𝕜`.
-/


variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
variable [IsScalarTower 𝕜 𝕜' E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
variable [IsScalarTower 𝕜 𝕜' F]
variable {f : E → F} {f' : E →L[𝕜'] F} {s : Set E} {x : E}

theorem HasFDerivAtFilter.restrictScalars {L} (h : HasFDerivAtFilter f f' L) :
    HasFDerivAtFilter f (f'.restrictScalars 𝕜) L :=
  .of_isLittleO h.isLittleO

@[fun_prop]
theorem HasStrictFDerivAt.restrictScalars (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt f (f'.restrictScalars 𝕜) x :=
  HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]
theorem HasFDerivAt.restrictScalars (h : HasFDerivAt f f' x) :
    HasFDerivAt f (f'.restrictScalars 𝕜) x :=
  HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]
theorem HasFDerivWithinAt.restrictScalars (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt f (f'.restrictScalars 𝕜) s x :=
  HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]
theorem DifferentiableAt.restrictScalars (h : DifferentiableAt 𝕜' f x) : DifferentiableAt 𝕜 f x :=
  (h.hasFDerivAt.restrictScalars 𝕜).differentiableAt

@[fun_prop]
theorem DifferentiableWithinAt.restrictScalars (h : DifferentiableWithinAt 𝕜' f s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  (h.hasFDerivWithinAt.restrictScalars 𝕜).differentiableWithinAt

@[fun_prop]
theorem DifferentiableOn.restrictScalars (h : DifferentiableOn 𝕜' f s) : DifferentiableOn 𝕜 f s :=
  fun x hx => (h x hx).restrictScalars 𝕜

@[fun_prop]
theorem Differentiable.restrictScalars (h : Differentiable 𝕜' f) : Differentiable 𝕜 f := fun x =>
  (h x).restrictScalars 𝕜

@[fun_prop]
theorem HasFDerivWithinAt.of_restrictScalars {g' : E →L[𝕜] F} (h : HasFDerivWithinAt f g' s x)
    (H : f'.restrictScalars 𝕜 = g') : HasFDerivWithinAt f f' s x := by
  rw [← H] at h
  exact .of_isLittleO h.isLittleO

@[fun_prop]
theorem hasFDerivAt_of_restrictScalars {g' : E →L[𝕜] F} (h : HasFDerivAt f g' x)
    (H : f'.restrictScalars 𝕜 = g') : HasFDerivAt f f' x := by
  rw [← H] at h
  exact .of_isLittleO h.isLittleO

theorem DifferentiableAt.fderiv_restrictScalars (h : DifferentiableAt 𝕜' f x) :
    fderiv 𝕜 f x = (fderiv 𝕜' f x).restrictScalars 𝕜 :=
  (h.hasFDerivAt.restrictScalars 𝕜).fderiv

theorem DifferentiableWithinAt.restrictScalars_fderivWithin (hf : DifferentiableWithinAt 𝕜' f s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    (fderivWithin 𝕜' f s x).restrictScalars 𝕜 = fderivWithin 𝕜 f s x :=
  ((hf.hasFDerivWithinAt.restrictScalars 𝕜).fderivWithin hs).symm

theorem differentiableWithinAt_iff_restrictScalars (hf : DifferentiableWithinAt 𝕜 f s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) : DifferentiableWithinAt 𝕜' f s x ↔
      ∃ g' : E →L[𝕜'] F, g'.restrictScalars 𝕜 = fderivWithin 𝕜 f s x := by
  constructor
  · rintro ⟨g', hg'⟩
    exact ⟨g', hs.eq (hg'.restrictScalars 𝕜) hf.hasFDerivWithinAt⟩
  · rintro ⟨f', hf'⟩
    exact ⟨f', hf.hasFDerivWithinAt.of_restrictScalars 𝕜 hf'⟩

theorem differentiableAt_iff_restrictScalars (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜' f x ↔ ∃ g' : E →L[𝕜'] F, g'.restrictScalars 𝕜 = fderiv 𝕜 f x := by
  rw [← differentiableWithinAt_univ, ← fderivWithin_univ]
  exact
    differentiableWithinAt_iff_restrictScalars 𝕜 hf.differentiableWithinAt uniqueDiffWithinAt_univ

end RestrictScalars
