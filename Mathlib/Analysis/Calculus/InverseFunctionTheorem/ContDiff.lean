/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Inverse function theorem, `C^r` case

In this file we specialize the inverse function theorem to `C^r`-smooth functions.
-/

@[expose] public section

noncomputable section

section

variable {𝕂 : Type*} [NontriviallyNormedField 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  [CompleteSpace E] {f : E → F} {f' : E ≃L[𝕂] F} {a : E} {n : WithTop ℕ∞}

/-- Given a `ContDiff` function with an invertible strict derivative at `a`, the inverse function
(produced by `ContDiff.toOpenPartialHomeomorph`) is also `ContDiff`.

See also `ContDiffAt.to_localInverse` for a specialisation to functions over `ℝ` or `ℂ`,
requiring `n ≠ 0` but no strict Fréchet derivative. -/
theorem ContDiffAt.to_localInverse'
    (hf : ContDiffAt 𝕂 n f a) (hf' : HasStrictFDerivAt f (f' : E →L[𝕂] F) a) :
    ContDiffAt 𝕂 n hf'.localInverse (f a) := by
  apply (hf'.toOpenPartialHomeomorph (f' := f')).contDiffAt_symm
    hf'.image_mem_toOpenPartialHomeomorph_target
  · rw [hf'.toOpenPartialHomeomorph_coe, ← hf'.localInverse_def, hf'.localInverse_apply_image]
    exact hf'.hasFDerivAt
  · rwa [hf'.toOpenPartialHomeomorph_coe, ← hf'.localInverse_def, hf'.localInverse_apply_image]

end

namespace ContDiffAt

variable {𝕂 : Type*} [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  [CompleteSpace E] (f : E → F) {f' : E ≃L[𝕂] F} {a : E} {n : WithTop ℕ∞}

/-- Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible
derivative at `a`, returns an `OpenPartialHomeomorph` with `to_fun = f` and `a ∈ source`. -/
def toOpenPartialHomeomorph (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a)
    (hn : n ≠ 0) : OpenPartialHomeomorph E F :=
  (hf.hasStrictFDerivAt' hf' hn).toOpenPartialHomeomorph f

variable {f}

@[simp]
theorem toOpenPartialHomeomorph_coe (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) :
    (hf.toOpenPartialHomeomorph f hf' hn : E → F) = f :=
  rfl

theorem mem_toOpenPartialHomeomorph_source (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) :
    a ∈ (hf.toOpenPartialHomeomorph f hf' hn).source :=
  (hf.hasStrictFDerivAt' hf' hn).mem_toOpenPartialHomeomorph_source

theorem image_mem_toOpenPartialHomeomorph_target (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) :
    f a ∈ (hf.toOpenPartialHomeomorph f hf' hn).target :=
  (hf.hasStrictFDerivAt' hf' hn).image_mem_toOpenPartialHomeomorph_target

/-- Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, returns a function that is locally inverse to `f`. -/
def localInverse (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a)
    (hn : n ≠ 0) : F → E :=
  (hf.hasStrictFDerivAt' hf' hn).localInverse f f' a

theorem localInverse_apply_image (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) : hf.localInverse hf' hn (f a) = a :=
  (hf.hasStrictFDerivAt' hf' hn).localInverse_apply_image

/-- Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, the inverse function (produced by `ContDiff.toOpenPartialHomeomorph`) is also `ContDiff`.

See also `ContDiffAt.to_localInverse'` for a specialisation over any field, assuming a strict
derivative (and no condition on `n`). -/
theorem to_localInverse (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) :
    ContDiffAt 𝕂 n (hf.localInverse hf' hn) (f a) := by
  have := hf.localInverse_apply_image hf' hn
  apply (hf.toOpenPartialHomeomorph f hf' hn).contDiffAt_symm
    (image_mem_toOpenPartialHomeomorph_target hf hf' hn)
  · convert! hf'
  · convert! hf

end ContDiffAt
