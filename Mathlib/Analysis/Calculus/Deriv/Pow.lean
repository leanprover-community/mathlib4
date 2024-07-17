/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

#align_import analysis.calculus.deriv.pow from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Derivative of `(f x) ^ n`, `n : ℕ`

In this file we prove that `(x ^ n)' = n * x ^ (n - 1)`, where `n` is a natural number.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative, power
-/

universe u v w

open scoped Classical
open Topology Filter ENNReal

open Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}

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
#align has_strict_deriv_at_pow hasStrictDerivAt_pow

theorem hasDerivAt_pow (n : ℕ) (x : 𝕜) :
    HasDerivAt (fun x : 𝕜 => x ^ n) ((n : 𝕜) * x ^ (n - 1)) x :=
  (hasStrictDerivAt_pow n x).hasDerivAt
#align has_deriv_at_pow hasDerivAt_pow

theorem hasDerivWithinAt_pow (n : ℕ) (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x : 𝕜 => x ^ n) ((n : 𝕜) * x ^ (n - 1)) s x :=
  (hasDerivAt_pow n x).hasDerivWithinAt
#align has_deriv_within_at_pow hasDerivWithinAt_pow

theorem differentiableAt_pow : DifferentiableAt 𝕜 (fun x : 𝕜 => x ^ n) x :=
  (hasDerivAt_pow n x).differentiableAt
#align differentiable_at_pow differentiableAt_pow

theorem differentiableWithinAt_pow :
    DifferentiableWithinAt 𝕜 (fun x : 𝕜 => x ^ n) s x :=
  (differentiableAt_pow n).differentiableWithinAt
#align differentiable_within_at_pow differentiableWithinAt_pow

theorem differentiable_pow : Differentiable 𝕜 fun x : 𝕜 => x ^ n := fun _ => differentiableAt_pow n
#align differentiable_pow differentiable_pow

theorem differentiableOn_pow : DifferentiableOn 𝕜 (fun x : 𝕜 => x ^ n) s :=
  (differentiable_pow n).differentiableOn
#align differentiable_on_pow differentiableOn_pow

theorem deriv_pow : deriv (fun x : 𝕜 => x ^ n) x = (n : 𝕜) * x ^ (n - 1) :=
  (hasDerivAt_pow n x).deriv
#align deriv_pow deriv_pow

@[simp]
theorem deriv_pow' : (deriv fun x : 𝕜 => x ^ n) = fun x => (n : 𝕜) * x ^ (n - 1) :=
  funext fun _ => deriv_pow n
#align deriv_pow' deriv_pow'

theorem derivWithin_pow (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x : 𝕜 => x ^ n) s x = (n : 𝕜) * x ^ (n - 1) :=
  (hasDerivWithinAt_pow n x s).derivWithin hxs
#align deriv_within_pow derivWithin_pow

theorem HasDerivWithinAt.pow (hc : HasDerivWithinAt c c' s x) :
    HasDerivWithinAt (fun y => c y ^ n) ((n : 𝕜) * c x ^ (n - 1) * c') s x :=
  (hasDerivAt_pow n (c x)).comp_hasDerivWithinAt x hc
#align has_deriv_within_at.pow HasDerivWithinAt.pow

theorem HasDerivAt.pow (hc : HasDerivAt c c' x) :
    HasDerivAt (fun y => c y ^ n) ((n : 𝕜) * c x ^ (n - 1) * c') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.pow n
#align has_deriv_at.pow HasDerivAt.pow

theorem derivWithin_pow' (hc : DifferentiableWithinAt 𝕜 c s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => c x ^ n) s x = (n : 𝕜) * c x ^ (n - 1) * derivWithin c s x :=
  (hc.hasDerivWithinAt.pow n).derivWithin hxs
#align deriv_within_pow' derivWithin_pow'

@[simp]
theorem deriv_pow'' (hc : DifferentiableAt 𝕜 c x) :
    deriv (fun x => c x ^ n) x = (n : 𝕜) * c x ^ (n - 1) * deriv c x :=
  (hc.hasDerivAt.pow n).deriv
#align deriv_pow'' deriv_pow''
