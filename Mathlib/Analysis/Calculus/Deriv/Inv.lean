/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Derivatives of `x ↦ x⁻¹` and `f x / g x`

In this file we prove `(x⁻¹)' = -1 / x ^ 2`, `((f x)⁻¹)' = -f' x / (f x) ^ 2`, and
`(f x / g x)' = (f' x * g x - f x * g' x) / (g x) ^ 2` for different notions of derivative.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative
-/

public section


universe u

open scoped Topology
open Filter Asymptotics Set

open ContinuousLinearMap (toSpanSingleton)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜}

section Inverse

/-! ### Derivative of `x ↦ x⁻¹` -/

theorem hasStrictDerivAt_inv (hx : x ≠ 0) : HasStrictDerivAt Inv.inv (-(x ^ 2)⁻¹) x := by
  suffices
    (fun p : 𝕜 × 𝕜 => (p.1 - p.2) * ((x * x)⁻¹ - (p.1 * p.2)⁻¹)) =o[𝓝 (x, x)] fun p =>
      (p.1 - p.2) * 1 by
    refine .of_isLittleO <| this.congr' ?_ (Eventually.of_forall fun _ => mul_one _)
    refine Eventually.mono ((isOpen_ne.prod isOpen_ne).mem_nhds ⟨hx, hx⟩) ?_
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    simp only [mem_setOf_eq] at hy hz
    simp [field]
    ring
  refine (isBigO_refl (fun p : 𝕜 × 𝕜 => p.1 - p.2) _).mul_isLittleO ((isLittleO_one_iff 𝕜).2 ?_)
  rw [← sub_self (x * x)⁻¹]
  exact tendsto_const_nhds.sub ((continuous_mul.tendsto (x, x)).inv₀ <| mul_ne_zero hx hx)

theorem hasDerivAt_inv (x_ne_zero : x ≠ 0) : HasDerivAt (fun y => y⁻¹) (-(x ^ 2)⁻¹) x :=
  (hasStrictDerivAt_inv x_ne_zero).hasDerivAt

theorem hasDerivWithinAt_inv (x_ne_zero : x ≠ 0) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => x⁻¹) (-(x ^ 2)⁻¹) s x :=
  (hasDerivAt_inv x_ne_zero).hasDerivWithinAt

theorem differentiableAt_inv_iff : DifferentiableAt 𝕜 (fun x => x⁻¹) x ↔ x ≠ 0 :=
  ⟨fun H => NormedField.continuousAt_inv.1 H.continuousAt, fun H =>
    (hasDerivAt_inv H).differentiableAt⟩

theorem deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹ := by
  rcases eq_or_ne x 0 with (rfl | hne)
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_inv_iff.1 (not_not.2 rfl))]
    simp
  · exact (hasDerivAt_inv hne).deriv

@[simp]
theorem deriv_inv' : (deriv fun x : 𝕜 => x⁻¹) = fun x => -(x ^ 2)⁻¹ :=
  funext fun _ => deriv_inv

theorem derivWithin_inv (x_ne_zero : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => x⁻¹) s x = -(x ^ 2)⁻¹ := by
  rw [DifferentiableAt.derivWithin (differentiableAt_inv x_ne_zero) hxs]
  exact deriv_inv

theorem hasFDerivAt_inv (x_ne_zero : x ≠ 0) :
    HasFDerivAt (fun x => x⁻¹) (toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) : 𝕜 →L[𝕜] 𝕜) x :=
  hasDerivAt_inv x_ne_zero

theorem hasStrictFDerivAt_inv (x_ne_zero : x ≠ 0) :
    HasStrictFDerivAt (fun x => x⁻¹) (toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) : 𝕜 →L[𝕜] 𝕜) x :=
  hasStrictDerivAt_inv x_ne_zero

theorem hasFDerivWithinAt_inv (x_ne_zero : x ≠ 0) :
    HasFDerivWithinAt (fun x => x⁻¹) (toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) : 𝕜 →L[𝕜] 𝕜) s x :=
  (hasFDerivAt_inv x_ne_zero).hasFDerivWithinAt

theorem fderiv_inv : fderiv 𝕜 (fun x => x⁻¹) x = toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) := by
  rw [← toSpanSingleton_deriv, deriv_inv]

theorem fderivWithin_inv (x_ne_zero : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => x⁻¹) s x = toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) := by
  rw [DifferentiableAt.fderivWithin (differentiableAt_inv x_ne_zero) hxs]
  exact fderiv_inv

variable {c : 𝕜 → 𝕜} {c' : 𝕜}

@[to_fun]
theorem HasDerivWithinAt.inv (hc : HasDerivWithinAt c c' s x) (hx : c x ≠ 0) :
    HasDerivWithinAt (c⁻¹) (-c' / c x ^ 2) s x := by
  convert (hasDerivAt_inv hx).comp_hasDerivWithinAt x hc using 1
  ring

@[to_fun]
theorem HasDerivAt.inv (hc : HasDerivAt c c' x) (hx : c x ≠ 0) :
    HasDerivAt (c⁻¹) (-c' / c x ^ 2) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.inv hx

theorem derivWithin_fun_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0) :
    derivWithin (fun x => (c x)⁻¹) s x = -derivWithin c s x / c x ^ 2 := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.inv hx).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

theorem derivWithin_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0) :
    derivWithin (c⁻¹) s x = -derivWithin c s x / c x ^ 2 :=
  derivWithin_fun_inv' hc hx

@[simp]
theorem deriv_fun_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) :
    deriv (fun x => (c x)⁻¹) x = -deriv c x / c x ^ 2 :=
  (hc.hasDerivAt.inv hx).deriv

@[simp]
theorem deriv_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) :
    deriv (c⁻¹) x = -deriv c x / c x ^ 2 :=
  (hc.hasDerivAt.inv hx).deriv

end Inverse

section Division

/-! ### Derivative of `x ↦ c x / d x` -/

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {c d : 𝕜 → 𝕜'} {c' d' : 𝕜'}

theorem HasDerivWithinAt.fun_div (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
    (hx : d x ≠ 0) :
    HasDerivWithinAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) s x := by
  convert hc.fun_mul ((hasDerivAt_inv hx).comp_hasDerivWithinAt x hd) using 1
  · simp only [div_eq_mul_inv, (· ∘ ·)]
  · simp [field]
    ring

theorem HasDerivWithinAt.div (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
    (hx : d x ≠ 0) :
    HasDerivWithinAt (c / d) ((c' * d x - c x * d') / d x ^ 2) s x :=
  hc.fun_div hd hx

theorem HasStrictDerivAt.fun_div (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
    (hx : d x ≠ 0) : HasStrictDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x := by
  convert hc.fun_mul ((hasStrictDerivAt_inv hx).comp x hd) using 1
  · simp only [div_eq_mul_inv, (· ∘ ·)]
  · simp [field]
    ring

theorem HasStrictDerivAt.div (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
    (hx : d x ≠ 0) : HasStrictDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x :=
  hc.fun_div hd hx

theorem HasDerivAt.fun_div (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx : d x ≠ 0) :
    HasDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.div hd hx

theorem HasDerivAt.div (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx : d x ≠ 0) :
    HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x :=
  hc.fun_div hd hx

theorem DifferentiableWithinAt.fun_div (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x ≠ 0) :
    DifferentiableWithinAt 𝕜 (fun x => c x / d x) s x :=
  (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).differentiableWithinAt

theorem DifferentiableWithinAt.div (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x ≠ 0) :
    DifferentiableWithinAt 𝕜 (c / d) s x :=
  hc.fun_div hd hx

@[simp, fun_prop]
theorem DifferentiableAt.fun_div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
    (hx : d x ≠ 0) : DifferentiableAt 𝕜 (fun x => c x / d x) x :=
  (hc.hasDerivAt.div hd.hasDerivAt hx).differentiableAt

@[simp, fun_prop]
theorem DifferentiableAt.div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
    (hx : d x ≠ 0) : DifferentiableAt 𝕜 (c / d) x :=
  hc.fun_div hd hx

@[fun_prop]
theorem DifferentiableOn.fun_div (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s)
    (hx : ∀ x ∈ s, d x ≠ 0) : DifferentiableOn 𝕜 (fun x => c x / d x) s := fun x h =>
  (hc x h).div (hd x h) (hx x h)

@[fun_prop]
theorem DifferentiableOn.div (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s)
    (hx : ∀ x ∈ s, d x ≠ 0) : DifferentiableOn 𝕜 (c / d) s := fun x h =>
  (hc x h).div (hd x h) (hx x h)

@[simp, fun_prop]
theorem Differentiable.fun_div (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d)
    (hx : ∀ x, d x ≠ 0) :
    Differentiable 𝕜 (fun x => c x / d x) := fun x => (hc x).div (hd x) (hx x)

@[simp, fun_prop]
theorem Differentiable.div (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) (hx : ∀ x, d x ≠ 0) :
    Differentiable 𝕜 (c / d) := fun x => (hc x).div (hd x) (hx x)

theorem derivWithin_fun_div
    (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x ≠ 0) :
    derivWithin (fun x => c x / d x) s x =
      (derivWithin c s x * d x - c x * derivWithin d s x) / d x ^ 2 := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

theorem derivWithin_div (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x)
    (hx : d x ≠ 0) :
    derivWithin (c / d) s x = (derivWithin c s x * d x - c x * derivWithin d s x) / d x ^ 2 :=
  derivWithin_fun_div hc hd hx

@[simp]
theorem deriv_fun_div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x ≠ 0) :
    deriv (fun x => c x / d x) x = (deriv c x * d x - c x * deriv d x) / d x ^ 2 :=
  (hc.hasDerivAt.div hd.hasDerivAt hx).deriv

@[simp]
theorem deriv_div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x ≠ 0) :
    deriv (c / d) x = (deriv c x * d x - c x * deriv d x) / d x ^ 2 :=
  (hc.hasDerivAt.div hd.hasDerivAt hx).deriv

end Division
