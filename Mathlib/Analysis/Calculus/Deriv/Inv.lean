/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

#align_import analysis.calculus.deriv.inv from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Derivatives of `x ↦ x⁻¹` and `f x / g x`

In this file we prove `(x⁻¹)' = -1 / x ^ 2`, `((f x)⁻¹)' = -f' x / (f x) ^ 2`, and
`(f x / g x)' = (f' x * g x - f x * g' x) / (g x) ^ 2` for different notions of derivative.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative
-/


universe u v w

open scoped Classical
open Topology Filter ENNReal

open Filter Asymptotics Set

open ContinuousLinearMap (smulRight smulRight_one_eq_iff)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L : Filter 𝕜}

section Inverse

/-! ### Derivative of `x ↦ x⁻¹` -/

theorem hasStrictDerivAt_inv (hx : x ≠ 0) : HasStrictDerivAt Inv.inv (-(x ^ 2)⁻¹) x := by
  suffices
    (fun p : 𝕜 × 𝕜 => (p.1 - p.2) * ((x * x)⁻¹ - (p.1 * p.2)⁻¹)) =o[𝓝 (x, x)] fun p =>
      (p.1 - p.2) * 1 by
    refine this.congr' ?_ (eventually_of_forall fun _ => mul_one _)
    refine Eventually.mono ((isOpen_ne.prod isOpen_ne).mem_nhds ⟨hx, hx⟩) ?_
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    simp only [mem_setOf_eq] at hy hz
    -- hy : y ≠ 0, hz : z ≠ 0
    field_simp [hx, hy, hz]
    ring
  refine (isBigO_refl (fun p : 𝕜 × 𝕜 => p.1 - p.2) _).mul_isLittleO ((isLittleO_one_iff 𝕜).2 ?_)
  rw [← sub_self (x * x)⁻¹]
  exact tendsto_const_nhds.sub ((continuous_mul.tendsto (x, x)).inv₀ <| mul_ne_zero hx hx)
#align has_strict_deriv_at_inv hasStrictDerivAt_inv

theorem hasDerivAt_inv (x_ne_zero : x ≠ 0) : HasDerivAt (fun y => y⁻¹) (-(x ^ 2)⁻¹) x :=
  (hasStrictDerivAt_inv x_ne_zero).hasDerivAt
#align has_deriv_at_inv hasDerivAt_inv

theorem hasDerivWithinAt_inv (x_ne_zero : x ≠ 0) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => x⁻¹) (-(x ^ 2)⁻¹) s x :=
  (hasDerivAt_inv x_ne_zero).hasDerivWithinAt
#align has_deriv_within_at_inv hasDerivWithinAt_inv

theorem differentiableAt_inv : DifferentiableAt 𝕜 (fun x => x⁻¹) x ↔ x ≠ 0 :=
  ⟨fun H => NormedField.continuousAt_inv.1 H.continuousAt, fun H =>
    (hasDerivAt_inv H).differentiableAt⟩
#align differentiable_at_inv differentiableAt_inv

theorem differentiableWithinAt_inv (x_ne_zero : x ≠ 0) :
    DifferentiableWithinAt 𝕜 (fun x => x⁻¹) s x :=
  (differentiableAt_inv.2 x_ne_zero).differentiableWithinAt
#align differentiable_within_at_inv differentiableWithinAt_inv

theorem differentiableOn_inv : DifferentiableOn 𝕜 (fun x : 𝕜 => x⁻¹) { x | x ≠ 0 } := fun _x hx =>
  differentiableWithinAt_inv hx
#align differentiable_on_inv differentiableOn_inv

theorem deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹ := by
  rcases eq_or_ne x 0 with (rfl | hne)
  · simp [deriv_zero_of_not_differentiableAt (mt differentiableAt_inv.1 (not_not.2 rfl))]
  · exact (hasDerivAt_inv hne).deriv
#align deriv_inv deriv_inv

@[simp]
theorem deriv_inv' : (deriv fun x : 𝕜 => x⁻¹) = fun x => -(x ^ 2)⁻¹ :=
  funext fun _ => deriv_inv
#align deriv_inv' deriv_inv'

theorem derivWithin_inv (x_ne_zero : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => x⁻¹) s x = -(x ^ 2)⁻¹ := by
  rw [DifferentiableAt.derivWithin (differentiableAt_inv.2 x_ne_zero) hxs]
  exact deriv_inv
#align deriv_within_inv derivWithin_inv

theorem hasFDerivAt_inv (x_ne_zero : x ≠ 0) :
    HasFDerivAt (fun x => x⁻¹) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) : 𝕜 →L[𝕜] 𝕜) x :=
  hasDerivAt_inv x_ne_zero
#align has_fderiv_at_inv hasFDerivAt_inv

theorem hasFDerivWithinAt_inv (x_ne_zero : x ≠ 0) :
    HasFDerivWithinAt (fun x => x⁻¹) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) : 𝕜 →L[𝕜] 𝕜) s x :=
  (hasFDerivAt_inv x_ne_zero).hasFDerivWithinAt
#align has_fderiv_within_at_inv hasFDerivWithinAt_inv

theorem fderiv_inv : fderiv 𝕜 (fun x => x⁻¹) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) := by
  rw [← deriv_fderiv, deriv_inv]
#align fderiv_inv fderiv_inv

theorem fderivWithin_inv (x_ne_zero : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => x⁻¹) s x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) := by
  rw [DifferentiableAt.fderivWithin (differentiableAt_inv.2 x_ne_zero) hxs]
  exact fderiv_inv
#align fderiv_within_inv fderivWithin_inv

variable {c : 𝕜 → 𝕜} {h : E → 𝕜} {c' : 𝕜} {z : E} {S : Set E}

theorem HasDerivWithinAt.inv (hc : HasDerivWithinAt c c' s x) (hx : c x ≠ 0) :
    HasDerivWithinAt (fun y => (c y)⁻¹) (-c' / c x ^ 2) s x := by
  convert (hasDerivAt_inv hx).comp_hasDerivWithinAt x hc using 1
  field_simp
#align has_deriv_within_at.inv HasDerivWithinAt.inv

theorem HasDerivAt.inv (hc : HasDerivAt c c' x) (hx : c x ≠ 0) :
    HasDerivAt (fun y => (c y)⁻¹) (-c' / c x ^ 2) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.inv hx
#align has_deriv_at.inv HasDerivAt.inv

theorem DifferentiableWithinAt.inv (hf : DifferentiableWithinAt 𝕜 h S z) (hz : h z ≠ 0) :
    DifferentiableWithinAt 𝕜 (fun x => (h x)⁻¹) S z :=
  (differentiableAt_inv.mpr hz).comp_differentiableWithinAt z hf
#align differentiable_within_at.inv DifferentiableWithinAt.inv

@[simp]
theorem DifferentiableAt.inv (hf : DifferentiableAt 𝕜 h z) (hz : h z ≠ 0) :
    DifferentiableAt 𝕜 (fun x => (h x)⁻¹) z :=
  (differentiableAt_inv.mpr hz).comp z hf
#align differentiable_at.inv DifferentiableAt.inv

theorem DifferentiableOn.inv (hf : DifferentiableOn 𝕜 h S) (hz : ∀ x ∈ S, h x ≠ 0) :
    DifferentiableOn 𝕜 (fun x => (h x)⁻¹) S := fun x h => (hf x h).inv (hz x h)
#align differentiable_on.inv DifferentiableOn.inv

@[simp]
theorem Differentiable.inv (hf : Differentiable 𝕜 h) (hz : ∀ x, h x ≠ 0) :
    Differentiable 𝕜 fun x => (h x)⁻¹ := fun x => (hf x).inv (hz x)
#align differentiable.inv Differentiable.inv

theorem derivWithin_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0)
    (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => (c x)⁻¹) s x = -derivWithin c s x / c x ^ 2 :=
  (hc.hasDerivWithinAt.inv hx).derivWithin hxs
#align deriv_within_inv' derivWithin_inv'

@[simp]
theorem deriv_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) :
    deriv (fun x => (c x)⁻¹) x = -deriv c x / c x ^ 2 :=
  (hc.hasDerivAt.inv hx).deriv
#align deriv_inv'' deriv_inv''

end Inverse

section Division

/-! ### Derivative of `x ↦ c x / d x` -/

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {c d : 𝕜 → 𝕜'} {c' d' : 𝕜'}

theorem HasDerivWithinAt.div (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
    (hx : d x ≠ 0) :
    HasDerivWithinAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) s x := by
  convert hc.mul ((hasDerivAt_inv hx).comp_hasDerivWithinAt x hd) using 1
  · simp only [div_eq_mul_inv, (· ∘ ·)]
  · field_simp
    ring
#align has_deriv_within_at.div HasDerivWithinAt.div

theorem HasStrictDerivAt.div (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
    (hx : d x ≠ 0) : HasStrictDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x := by
  convert hc.mul ((hasStrictDerivAt_inv hx).comp x hd) using 1
  · simp only [div_eq_mul_inv, (· ∘ ·)]
  · field_simp
    ring
#align has_strict_deriv_at.div HasStrictDerivAt.div

theorem HasDerivAt.div (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx : d x ≠ 0) :
    HasDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.div hd hx
#align has_deriv_at.div HasDerivAt.div

theorem DifferentiableWithinAt.div (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x ≠ 0) :
    DifferentiableWithinAt 𝕜 (fun x => c x / d x) s x :=
  (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).differentiableWithinAt
#align differentiable_within_at.div DifferentiableWithinAt.div

@[simp]
theorem DifferentiableAt.div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
    (hx : d x ≠ 0) : DifferentiableAt 𝕜 (fun x => c x / d x) x :=
  (hc.hasDerivAt.div hd.hasDerivAt hx).differentiableAt
#align differentiable_at.div DifferentiableAt.div

theorem DifferentiableOn.div (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s)
    (hx : ∀ x ∈ s, d x ≠ 0) : DifferentiableOn 𝕜 (fun x => c x / d x) s := fun x h =>
  (hc x h).div (hd x h) (hx x h)
#align differentiable_on.div DifferentiableOn.div

@[simp]
theorem Differentiable.div (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) (hx : ∀ x, d x ≠ 0) :
    Differentiable 𝕜 fun x => c x / d x := fun x => (hc x).div (hd x) (hx x)
#align differentiable.div Differentiable.div

theorem derivWithin_div (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x)
    (hx : d x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => c x / d x) s x =
      (derivWithin c s x * d x - c x * derivWithin d s x) / d x ^ 2 :=
  (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).derivWithin hxs
#align deriv_within_div derivWithin_div

@[simp]
theorem deriv_div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x ≠ 0) :
    deriv (fun x => c x / d x) x = (deriv c x * d x - c x * deriv d x) / d x ^ 2 :=
  (hc.hasDerivAt.div hd.hasDerivAt hx).deriv
#align deriv_div deriv_div

end Division
