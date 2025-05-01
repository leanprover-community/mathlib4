/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Derivative of `(f x) ^ n`, `n : ℕ`

In this file we prove that `(x ^ n)' = n * x ^ (n - 1)`, where `n` is a natural number.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative, power
-/

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜}

/-! ### Derivative of `x ↦ x^n` for `n : ℕ` -/

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

theorem differentiableAt_pow : DifferentiableAt 𝕜 (fun x : 𝕜 => x ^ n) x :=
  (hasDerivAt_pow n x).differentiableAt

theorem differentiableWithinAt_pow :
    DifferentiableWithinAt 𝕜 (fun x : 𝕜 => x ^ n) s x :=
  (differentiableAt_pow n).differentiableWithinAt

theorem differentiable_pow : Differentiable 𝕜 fun x : 𝕜 => x ^ n := fun _ => differentiableAt_pow n

theorem differentiableOn_pow : DifferentiableOn 𝕜 (fun x : 𝕜 => x ^ n) s :=
  (differentiable_pow n).differentiableOn

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
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.pow n).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[simp]
theorem deriv_pow'' (hc : DifferentiableAt 𝕜 c x) :
    deriv (fun x => c x ^ n) x = (n : 𝕜) * c x ^ (n - 1) * deriv c x :=
  (hc.hasDerivAt.pow n).deriv
