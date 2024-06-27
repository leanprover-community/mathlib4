/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

#align_import analysis.special_functions.sqrt from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Smoothness of `Real.sqrt`

In this file we prove that `Real.sqrt` is infinitely smooth at all points `x ≠ 0` and provide some
dot-notation lemmas.

## Tags

sqrt, differentiable
-/


open Set

open scoped Topology

namespace Real

/-- Local homeomorph between `(0, +∞)` and `(0, +∞)` with `toFun = (· ^ 2)` and
`invFun = Real.sqrt`. -/
noncomputable def sqPartialHomeomorph : PartialHomeomorph ℝ ℝ where
  toFun x := x ^ 2
  invFun := (√·)
  source := Ioi 0
  target := Ioi 0
  map_source' _ h := mem_Ioi.2 (pow_pos (mem_Ioi.1 h) _)
  map_target' _ h := mem_Ioi.2 (sqrt_pos.2 h)
  left_inv' _ h := sqrt_sq (le_of_lt h)
  right_inv' _ h := sq_sqrt (le_of_lt h)
  open_source := isOpen_Ioi
  open_target := isOpen_Ioi
  continuousOn_toFun := (continuous_pow 2).continuousOn
  continuousOn_invFun := continuousOn_id.sqrt
#align real.sq_local_homeomorph Real.sqPartialHomeomorph

theorem deriv_sqrt_aux {x : ℝ} (hx : x ≠ 0) :
    HasStrictDerivAt (√·) (1 / (2 * √x)) x ∧ ∀ n, ContDiffAt ℝ n (√·) x := by
  cases' hx.lt_or_lt with hx hx
  · rw [sqrt_eq_zero_of_nonpos hx.le, mul_zero, div_zero]
    have : (√·) =ᶠ[𝓝 x] fun _ => 0 := (gt_mem_nhds hx).mono fun x hx => sqrt_eq_zero_of_nonpos hx.le
    exact
      ⟨(hasStrictDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq this.symm, fun n =>
        contDiffAt_const.congr_of_eventuallyEq this⟩
  · have : ↑2 * √x ^ (2 - 1) ≠ 0 := by simp [(sqrt_pos.2 hx).ne', @two_ne_zero ℝ]
    constructor
    · simpa using sqPartialHomeomorph.hasStrictDerivAt_symm hx this (hasStrictDerivAt_pow 2 _)
    · exact fun n => sqPartialHomeomorph.contDiffAt_symm_deriv this hx (hasDerivAt_pow 2 (√x))
        (contDiffAt_id.pow 2)
#align real.deriv_sqrt_aux Real.deriv_sqrt_aux

theorem hasStrictDerivAt_sqrt {x : ℝ} (hx : x ≠ 0) : HasStrictDerivAt (√·) (1 / (2 * √x)) x :=
  (deriv_sqrt_aux hx).1
#align real.has_strict_deriv_at_sqrt Real.hasStrictDerivAt_sqrt

theorem contDiffAt_sqrt {x : ℝ} {n : ℕ∞} (hx : x ≠ 0) : ContDiffAt ℝ n (√·) x :=
  (deriv_sqrt_aux hx).2 n
#align real.cont_diff_at_sqrt Real.contDiffAt_sqrt

theorem hasDerivAt_sqrt {x : ℝ} (hx : x ≠ 0) : HasDerivAt (√·) (1 / (2 * √x)) x :=
  (hasStrictDerivAt_sqrt hx).hasDerivAt
#align real.has_deriv_at_sqrt Real.hasDerivAt_sqrt

end Real

open Real

section deriv

variable {f : ℝ → ℝ} {s : Set ℝ} {f' x : ℝ}

theorem HasDerivWithinAt.sqrt (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasDerivWithinAt (fun y => √(f y)) (f' / (2 * √(f x))) s x := by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using
    (hasDerivAt_sqrt hx).comp_hasDerivWithinAt x hf
#align has_deriv_within_at.sqrt HasDerivWithinAt.sqrt

theorem HasDerivAt.sqrt (hf : HasDerivAt f f' x) (hx : f x ≠ 0) :
    HasDerivAt (fun y => √(f y)) (f' / (2 * √(f x))) x := by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using (hasDerivAt_sqrt hx).comp x hf
#align has_deriv_at.sqrt HasDerivAt.sqrt

theorem HasStrictDerivAt.sqrt (hf : HasStrictDerivAt f f' x) (hx : f x ≠ 0) :
    HasStrictDerivAt (fun t => √(f t)) (f' / (2 * √(f x))) x := by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using (hasStrictDerivAt_sqrt hx).comp x hf
#align has_strict_deriv_at.sqrt HasStrictDerivAt.sqrt

theorem derivWithin_sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0)
    (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => √(f x)) s x = derivWithin f s x / (2 * √(f x)) :=
  (hf.hasDerivWithinAt.sqrt hx).derivWithin hxs
#align deriv_within_sqrt derivWithin_sqrt

@[simp]
theorem deriv_sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    deriv (fun x => √(f x)) x = deriv f x / (2 * √(f x)) :=
  (hf.hasDerivAt.sqrt hx).deriv
#align deriv_sqrt deriv_sqrt

end deriv

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {n : ℕ∞} {s : Set E}
  {x : E} {f' : E →L[ℝ] ℝ}

theorem HasFDerivAt.sqrt (hf : HasFDerivAt f f' x) (hx : f x ≠ 0) :
    HasFDerivAt (fun y => √(f y)) ((1 / (2 * √(f x))) • f') x :=
  (hasDerivAt_sqrt hx).comp_hasFDerivAt x hf
#align has_fderiv_at.sqrt HasFDerivAt.sqrt

theorem HasStrictFDerivAt.sqrt (hf : HasStrictFDerivAt f f' x) (hx : f x ≠ 0) :
    HasStrictFDerivAt (fun y => √(f y)) ((1 / (2 * √(f x))) • f') x :=
  (hasStrictDerivAt_sqrt hx).comp_hasStrictFDerivAt x hf
#align has_strict_fderiv_at.sqrt HasStrictFDerivAt.sqrt

theorem HasFDerivWithinAt.sqrt (hf : HasFDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasFDerivWithinAt (fun y => √(f y)) ((1 / (2 * √(f x))) • f') s x :=
  (hasDerivAt_sqrt hx).comp_hasFDerivWithinAt x hf
#align has_fderiv_within_at.sqrt HasFDerivWithinAt.sqrt

theorem DifferentiableWithinAt.sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun y => √(f y)) s x :=
  (hf.hasFDerivWithinAt.sqrt hx).differentiableWithinAt
#align differentiable_within_at.sqrt DifferentiableWithinAt.sqrt

theorem DifferentiableAt.sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    DifferentiableAt ℝ (fun y => √(f y)) x :=
  (hf.hasFDerivAt.sqrt hx).differentiableAt
#align differentiable_at.sqrt DifferentiableAt.sqrt

theorem DifferentiableOn.sqrt (hf : DifferentiableOn ℝ f s) (hs : ∀ x ∈ s, f x ≠ 0) :
    DifferentiableOn ℝ (fun y => √(f y)) s := fun x hx => (hf x hx).sqrt (hs x hx)
#align differentiable_on.sqrt DifferentiableOn.sqrt

theorem Differentiable.sqrt (hf : Differentiable ℝ f) (hs : ∀ x, f x ≠ 0) :
    Differentiable ℝ fun y => √(f y) := fun x => (hf x).sqrt (hs x)
#align differentiable.sqrt Differentiable.sqrt

theorem fderivWithin_sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0)
    (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => √(f x)) s x = (1 / (2 * √(f x))) • fderivWithin ℝ f s x :=
  (hf.hasFDerivWithinAt.sqrt hx).fderivWithin hxs
#align fderiv_within_sqrt fderivWithin_sqrt

@[simp]
theorem fderiv_sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    fderiv ℝ (fun x => √(f x)) x = (1 / (2 * √(f x))) • fderiv ℝ f x :=
  (hf.hasFDerivAt.sqrt hx).fderiv
#align fderiv_sqrt fderiv_sqrt

theorem ContDiffAt.sqrt (hf : ContDiffAt ℝ n f x) (hx : f x ≠ 0) :
    ContDiffAt ℝ n (fun y => √(f y)) x :=
  (contDiffAt_sqrt hx).comp x hf
#align cont_diff_at.sqrt ContDiffAt.sqrt

theorem ContDiffWithinAt.sqrt (hf : ContDiffWithinAt ℝ n f s x) (hx : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun y => √(f y)) s x :=
  (contDiffAt_sqrt hx).comp_contDiffWithinAt x hf
#align cont_diff_within_at.sqrt ContDiffWithinAt.sqrt

theorem ContDiffOn.sqrt (hf : ContDiffOn ℝ n f s) (hs : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun y => √(f y)) s := fun x hx => (hf x hx).sqrt (hs x hx)
#align cont_diff_on.sqrt ContDiffOn.sqrt

theorem ContDiff.sqrt (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y => √(f y) :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.sqrt (h x)
#align cont_diff.sqrt ContDiff.sqrt

end fderiv
