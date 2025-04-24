/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Derivative of `(f x) ^ n`, `n : ℕ`

In this file we prove that `(x ^ n)' = n * x ^ (n - 1)`, where `n` is a natural number.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative, power
-/

universe u

variable {𝕜 𝔸 E : Type*}

section NormedRing
variable [NontriviallyNormedField 𝕜] [NormedRing 𝔸] [NormedAddCommGroup E]
variable [NormedAlgebra 𝕜 𝔸] [NormedSpace 𝕜 E] {f : E → 𝔸} {f' : E →L[𝕜] 𝔸} {x : E} {s : Set E}

open scoped RightActions

private theorem aux (f : E → 𝔸) (f' : E →L[𝕜] 𝔸) (x : E) (n : ℕ) :
    f x •> ∑ i ∈ Finset.range (n + 1), f x ^ ((n + 1).pred - i) •> f' <• f x ^ i
      + f' <• (f x ^ (n + 1)) =
    ∑ i ∈ Finset.range (n + 1 + 1), f x ^ ((n + 1 + 1).pred - i) •> f' <• f x ^ i := by
  rw [Finset.sum_range_succ _ (n + 1), Finset.smul_sum]
  simp only [Nat.pred_eq_sub_one, add_tsub_cancel_right, tsub_self, pow_zero, one_smul]
  simp_rw [smul_comm (_ : 𝔸) (_ : 𝔸ᵐᵒᵖ), smul_smul, ← pow_succ']
  congr! 5 with x hx
  simp [Nat.lt_succ_iff] at hx
  rw [tsub_add_eq_add_tsub hx]

theorem HasStrictFDerivAt.pow' (h : HasStrictFDerivAt f f' x) (n : ℕ) :
    HasStrictFDerivAt (fun x ↦ f x ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) x :=
  match n with
  | 0 => by simpa using hasStrictFDerivAt_const 1 x
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
    refine this.congr_fderiv <| aux _ _ _ _

theorem HasFDerivWithinAt.pow' (h : HasFDerivWithinAt f f' s x) (n : ℕ) :
    HasFDerivWithinAt (fun x ↦ f x ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i) s x :=
  match n with
  | 0 => by simpa using hasFDerivWithinAt_const 1 x s
  | 1 => by simpa using h
  | n + 1 + 1 => by
    have := h.mul' (h.pow' (n + 1))
    simp_rw [pow_succ' _ (n + 1)]
    exact this.congr_fderiv <| aux _ _ _ _

@[fun_prop]
theorem DifferentiableWithinAt.pow (hf : DifferentiableWithinAt 𝕜 f s x) (n : ℕ) :
    DifferentiableWithinAt 𝕜 (fun x => f x ^ n) s x :=
  let ⟨_, hf'⟩ := hf; ⟨_, hf'.pow' n⟩

@[simp, fun_prop]
theorem DifferentiableAt.pow (hf : DifferentiableAt 𝕜 f x) (n : ℕ) :
    DifferentiableAt 𝕜 (fun x => f x ^ n) x :=
  differentiableWithinAt_univ.mp <| hf.differentiableWithinAt.pow n

@[fun_prop]
theorem DifferentiableOn.pow (ha : DifferentiableOn 𝕜 f s) (n : ℕ) :
    DifferentiableOn 𝕜 (fun x => f x ^ n) s := fun x h => (ha x h).pow n

@[simp, fun_prop]
theorem Differentiable.pow (ha : Differentiable 𝕜 f) (n : ℕ) : Differentiable 𝕜 fun x => f x ^ n :=
  fun x => (ha x).pow n

theorem differentiableAt_pow (n : ℕ) {x : 𝔸} : DifferentiableAt 𝕜 (fun x : 𝔸 => x ^ n) x :=
  differentiableAt_id.pow _

theorem differentiableWithinAt_pow (n : ℕ) {x : 𝔸} : DifferentiableWithinAt 𝕜 (fun x : 𝔸 => x ^ n) s x :=
  (differentiableAt_pow n).differentiableWithinAt

theorem differentiable_pow (n : ℕ) : Differentiable 𝕜 fun x : 𝔸 => x ^ n :=
  fun _ => differentiableAt_pow n

theorem differentiableOn_pow (n : ℕ) {s : Set 𝔸} : DifferentiableOn 𝕜 (fun x : 𝔸 => x ^ n) s :=
  (differentiable_pow n).differentiableOn

end NormedRing

variable {c : 𝕜 → 𝕜} {c' : 𝕜}
variable (n : ℕ)

theorem hasStrictDerivAt_pow :
    ∀ (n : ℕ) (x : 𝕜), HasStrictDerivAt (fun x : 𝕜 ↦ x ^ n) ((n : 𝕜) * x ^ (n - 1)) x
  | 0, x => by simp [hasStrictDerivAt_const]
  | 1, x => by simpa using hasStrictDerivAt_id x
  | n + 1 + 1, x => by
    simpa [pow_succ, add_mul, mul_assoc] using
      (hasStrictDerivAt_pow (n + 1) x).mul (hasStrictDerivAt_id x)

theorem hasDerivAt_pow (n : ℕ) (x : 𝕜) :
    HasDerivAt (fun x : 𝕜 => x ^ n) ((n : 𝕜) * x ^ (n - 1)) x :=
  (hasStrictDerivAt_pow n x).hasDerivAt

theorem hasDerivWithinAt_pow (n : ℕ) (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x : 𝕜 => x ^ n) ((n : 𝕜) * x ^ (n - 1)) s x :=
  (hasDerivAt_pow n x).hasDerivWithinAt


theorem deriv_pow : deriv (fun x : 𝕜 => x ^ n) x = (n : 𝕜) * x ^ (n - 1) :=
  (hasDerivAt_pow n x).deriv

@[simp]
theorem deriv_pow' : (deriv fun x : 𝕜 => x ^ n) = fun x => (n : 𝕜) * x ^ (n - 1) :=
  funext fun _ => deriv_pow n

theorem derivWithin_pow (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x : 𝕜 => x ^ n) s x = (n : 𝕜) * x ^ (n - 1) :=
  (hasDerivWithinAt_pow n x s).derivWithin hxs

theorem HasDerivWithinAt.pow (hc : HasDerivWithinAt c c' s x) :
    HasDerivWithinAt (fun y => c y ^ n) ((n : 𝕜) * c x ^ (n - 1) * c') s x :=
  (hasDerivAt_pow n (c x)).comp_hasDerivWithinAt x hc

theorem HasDerivAt.pow (hc : HasDerivAt c c' x) :
    HasDerivAt (fun y => c y ^ n) ((n : 𝕜) * c x ^ (n - 1) * c') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.pow n

theorem derivWithin_pow' (hc : DifferentiableWithinAt 𝕜 c s x) :
    derivWithin (fun x => c x ^ n) s x = (n : 𝕜) * c x ^ (n - 1) * derivWithin c s x := by
  rcases uniqueDiffWithinAt_or_nhdsWithin_eq_bot s x with hxs | hxs
  · exact (hc.hasDerivWithinAt.pow n).derivWithin hxs
  · simp [derivWithin_zero_of_isolated hxs]

@[simp]
theorem deriv_pow'' (hc : DifferentiableAt 𝕜 c x) :
    deriv (fun x => c x ^ n) x = (n : 𝕜) * c x ^ (n - 1) * deriv c x :=
  (hc.hasDerivAt.pow n).deriv
