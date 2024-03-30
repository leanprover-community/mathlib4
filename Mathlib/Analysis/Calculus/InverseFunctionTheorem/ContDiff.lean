/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Inverse function theorem, smooth case

In this file we specialize the inverse function theorem to `C^r`-smooth functions.
-/

noncomputable section

namespace ContDiffAt

variable {𝕂 : Type*} [RCLike 𝕂]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
variable [CompleteSpace E] (f : E → F) {f' : E ≃L[𝕂] F} {a : E}

/-- Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible
derivative at `a`, returns a `PartialHomeomorph` with `to_fun = f` and `a ∈ source`. -/
def toPartialHomeomorph {n : ℕ∞} (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a)
    (hn : 1 ≤ n) : PartialHomeomorph E F :=
  (hf.hasStrictFDerivAt' hf' hn).toPartialHomeomorph f
#align cont_diff_at.to_local_homeomorph ContDiffAt.toPartialHomeomorph

variable {f}

@[simp]
theorem toPartialHomeomorph_coe {n : ℕ∞} (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : 1 ≤ n) :
    (hf.toPartialHomeomorph f hf' hn : E → F) = f :=
  rfl
#align cont_diff_at.to_local_homeomorph_coe ContDiffAt.toPartialHomeomorph_coe

theorem mem_toPartialHomeomorph_source {n : ℕ∞} (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : 1 ≤ n) :
    a ∈ (hf.toPartialHomeomorph f hf' hn).source :=
  (hf.hasStrictFDerivAt' hf' hn).mem_toPartialHomeomorph_source
#align cont_diff_at.mem_to_local_homeomorph_source ContDiffAt.mem_toPartialHomeomorph_source

theorem image_mem_toPartialHomeomorph_target {n : ℕ∞} (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : 1 ≤ n) :
    f a ∈ (hf.toPartialHomeomorph f hf' hn).target :=
  (hf.hasStrictFDerivAt' hf' hn).image_mem_toPartialHomeomorph_target
#align cont_diff_at.image_mem_to_local_homeomorph_target ContDiffAt.image_mem_toPartialHomeomorph_target

/-- Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, returns a function that is locally inverse to `f`. -/
def localInverse {n : ℕ∞} (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a)
    (hn : 1 ≤ n) : F → E :=
  (hf.hasStrictFDerivAt' hf' hn).localInverse f f' a
#align cont_diff_at.local_inverse ContDiffAt.localInverse

theorem localInverse_apply_image {n : ℕ∞} (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : 1 ≤ n) : hf.localInverse hf' hn (f a) = a :=
  (hf.hasStrictFDerivAt' hf' hn).localInverse_apply_image
#align cont_diff_at.local_inverse_apply_image ContDiffAt.localInverse_apply_image

/-- Given a `ContDiff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, the inverse function (produced by `ContDiff.toPartialHomeomorph`) is
also `ContDiff`. -/
theorem to_localInverse {n : ℕ∞} (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : 1 ≤ n) :
    ContDiffAt 𝕂 n (hf.localInverse hf' hn) (f a) := by
  have := hf.localInverse_apply_image hf' hn
  apply (hf.toPartialHomeomorph f hf' hn).contDiffAt_symm
    (image_mem_toPartialHomeomorph_target hf hf' hn)
  · convert hf'
  · convert hf
#align cont_diff_at.to_local_inverse ContDiffAt.to_localInverse

end ContDiffAt
