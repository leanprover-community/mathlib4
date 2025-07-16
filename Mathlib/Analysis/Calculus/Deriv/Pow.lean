/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Derivative of `(f x) ^ n`, `n : ℕ`

In this file we prove that `(x ^ n)' = n * x ^ (n - 1)`, where `n` is a natural number.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative, power
-/

variable {𝕜 𝔸 : Type*}

section NormedRing
variable [NontriviallyNormedField 𝕜] [NormedRing 𝔸]
variable [NormedAlgebra 𝕜 𝔸] {f : 𝕜 → 𝔸} {f' : 𝔸} {x : 𝕜} {s : Set 𝕜}

nonrec theorem HasStrictDerivAt.pow' (h : HasStrictDerivAt f f' x) (n : ℕ) :
    HasStrictDerivAt (fun x ↦ f x ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x := by
  unfold HasStrictDerivAt
  convert h.pow' n
  ext
  simp

nonrec theorem HasDerivWithinAt.pow' (h : HasDerivWithinAt f f' s x) (n : ℕ) :
    HasDerivWithinAt (fun x ↦ f x ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) s x := by
  simpa using h.hasFDerivWithinAt.pow' n |>.hasDerivWithinAt

theorem HasDerivAt.pow' (h : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun x ↦ f x ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x := by
  simpa using h.hasFDerivAt.pow' n |>.hasDerivAt

@[simp low]
theorem derivWithin_fun_pow'
    (h : DifferentiableWithinAt 𝕜 f s x) (hu : UniqueDiffWithinAt 𝕜 s x) (n : ℕ) :
    derivWithin (fun x => f x ^ n) s x =
      ∑ i ∈ Finset.range n, f x ^ (n.pred - i) * derivWithin f s x * f x ^ i :=
  (h.hasDerivWithinAt.pow' n).derivWithin hu

@[simp low]
theorem derivWithin_pow'
    (h : DifferentiableWithinAt 𝕜 f s x) (hu : UniqueDiffWithinAt 𝕜 s x) (n : ℕ) :
    derivWithin (f ^ n) s x =
      ∑ i ∈ Finset.range n, f x ^ (n.pred - i) * derivWithin f s x * f x ^ i :=
  derivWithin_fun_pow' h hu n

@[simp low]
theorem deriv_fun_pow' (h : DifferentiableAt 𝕜 f x) (n : ℕ) :
    deriv (fun x => f x ^ n) x = ∑ i ∈ Finset.range n, f x ^ (n.pred - i) * deriv f x * f x ^ i :=
  (h.hasDerivAt.pow' n).deriv

@[simp low]
theorem deriv_pow' (h : DifferentiableAt 𝕜 f x) (n : ℕ) :
    deriv (f ^ n) x = ∑ i ∈ Finset.range n, f x ^ (n.pred - i) * deriv f x * f x ^ i :=
  deriv_fun_pow' h n

end NormedRing

section NormedCommRing
variable [NontriviallyNormedField 𝕜] [NormedCommRing 𝔸]
variable [NormedAlgebra 𝕜 𝔸] {f : 𝕜 → 𝔸} {f' : 𝔸} {x : 𝕜} {s : Set 𝕜}

open scoped RightActions

nonrec theorem HasStrictDerivAt.fun_pow (h : HasStrictDerivAt f f' x) (n : ℕ) :
    HasStrictDerivAt (fun x ↦ f x ^ n) (n * f x ^ (n - 1) * f') x := by
  unfold HasStrictDerivAt
  convert h.pow n
  ext
  simp [mul_assoc]

nonrec theorem HasStrictDerivAt.pow (h : HasStrictDerivAt f f' x) (n : ℕ) :
    HasStrictDerivAt (f ^ n) (n * f x ^ (n - 1) * f') x := h.fun_pow n

nonrec theorem HasDerivWithinAt.fun_pow (h : HasDerivWithinAt f f' s x) (n : ℕ) :
    HasDerivWithinAt (fun x ↦ f x ^ n) (n * f x ^ (n - 1) * f') s x := by
  simpa using h.hasFDerivWithinAt.pow n |>.hasDerivWithinAt

nonrec theorem HasDerivWithinAt.pow (h : HasDerivWithinAt f f' s x) (n : ℕ) :
    HasDerivWithinAt (f ^ n) (n * f x ^ (n - 1) * f') s x := h.fun_pow n

theorem HasDerivAt.fun_pow (h : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun x ↦ f x ^ n) (n * f x ^ (n - 1) * f') x := by
  simpa using h.hasFDerivAt.pow n |>.hasDerivAt

theorem HasDerivAt.pow (h : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (f ^ n) (n * f x ^ (n - 1) * f') x := h.fun_pow n

@[simp]
theorem derivWithin_fun_pow
    (h : DifferentiableWithinAt 𝕜 f s x) (hu : UniqueDiffWithinAt 𝕜 s x) (n : ℕ) :
    derivWithin (fun x => f x ^ n) s x = n * f x ^ (n - 1) * derivWithin f s x :=
  (h.hasDerivWithinAt.pow n).derivWithin hu

@[simp]
theorem derivWithin_pow
    (h : DifferentiableWithinAt 𝕜 f s x) (hu : UniqueDiffWithinAt 𝕜 s x) (n : ℕ) :
    derivWithin (f ^ n) s x = n * f x ^ (n - 1) * derivWithin f s x :=
  derivWithin_fun_pow h hu n

@[simp]
theorem deriv_fun_pow (h : DifferentiableAt 𝕜 f x) (n : ℕ) :
    deriv (fun x => f x ^ n) x = n * f x ^ (n - 1) * deriv f x  :=
  (h.hasDerivAt.pow n).deriv

@[simp]
theorem deriv_pow (h : DifferentiableAt 𝕜 f x) (n : ℕ) :
    deriv (f ^ n) x = n * f x ^ (n - 1) * deriv f x := deriv_fun_pow h n

end NormedCommRing

section NontriviallyNormedField
variable [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜} {c : 𝕜 → 𝕜}

theorem deriv_pow_field (n : ℕ) : deriv (fun x => x ^ n) x = (n : 𝕜) * x ^ (n - 1) := by
  simp

theorem derivWithin_pow_field (h : UniqueDiffWithinAt 𝕜 s x) (n : ℕ) :
    derivWithin (fun x => x ^ n) s x = (n : 𝕜) * x ^ (n - 1) := by
  rw [derivWithin_pow (differentiableWithinAt_id' (s := s)) h n, derivWithin_id' _ _ h, mul_one]

theorem derivWithin_fun_pow_field' (hc : DifferentiableWithinAt 𝕜 c s x) (n : ℕ) :
    derivWithin (fun x => c x ^ n) s x = (n : 𝕜) * c x ^ (n - 1) * derivWithin c s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact derivWithin_pow hc hsx n
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

theorem derivWithin_pow_field' (hc : DifferentiableWithinAt 𝕜 c s x) (n : ℕ) :
    derivWithin (c ^ n) s x = (n : 𝕜) * c x ^ (n - 1) * derivWithin c s x :=
  derivWithin_fun_pow_field' hc n

theorem hasStrictDerivAt_pow (n : ℕ) (x : 𝕜) :
    HasStrictDerivAt (fun x : 𝕜 ↦ x ^ n) (n * x ^ (n - 1)) x := by
  simpa using (hasStrictDerivAt_id x).pow n

theorem hasDerivWithinAt_pow (n : ℕ) (x : 𝕜) :
    HasDerivWithinAt (fun x : 𝕜 ↦ x ^ n) (n * x ^ (n - 1)) s x := by
  simpa using (hasDerivWithinAt_id x s).pow n

theorem hasDerivAt_pow (n : ℕ) (x : 𝕜) :
    HasDerivAt (fun x : 𝕜 => x ^ n) ((n : 𝕜) * x ^ (n - 1)) x := by
  simpa using (hasStrictDerivAt_pow n x).hasDerivAt

end NontriviallyNormedField
