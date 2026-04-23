/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Inverse function theorem, `C^r` case

In this file we specialize the inverse function theorem to `C^r`-smooth functions.
-/

@[expose] public section

noncomputable section

namespace ContDiffAt

variable {𝕂 : Type*} [RCLike 𝕂]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
variable [CompleteSpace E] (f : E → F) {f' : E ≃L[𝕂] F} {a : E} {n : WithTop ℕ∞}

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
at `a`, the inverse function (produced by `ContDiff.toOpenPartialHomeomorph`) is
also `ContDiff`. -/
theorem to_localInverse (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) :
    ContDiffAt 𝕂 n (hf.localInverse hf' hn) (f a) := by
  have := hf.localInverse_apply_image hf' hn
  apply (hf.toOpenPartialHomeomorph f hf' hn).contDiffAt_symm
    (image_mem_toOpenPartialHomeomorph_target hf hf' hn)
  · convert hf'
  · convert hf

end ContDiffAt
