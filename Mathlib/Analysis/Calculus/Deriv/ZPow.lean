/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Derivatives of `x ^ m`, `m : ℤ`

In this file we prove theorems about (iterated) derivatives of `x ^ m`, `m : ℤ`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`analysis/calculus/deriv/basic`.

## Keywords

derivative, power
-/

universe u v w

open Topology Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {m : ℤ}

/-! ### Derivative of `x ↦ x^m` for `m : ℤ` -/

theorem hasStrictDerivAt_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
    HasStrictDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x := by
  have : ∀ m : ℤ, 0 < m → HasStrictDerivAt (· ^ m) ((m : 𝕜) * x ^ (m - 1)) x := fun m hm ↦ by
    lift m to ℕ using hm.le
    simp only [zpow_natCast, Int.cast_natCast]
    convert hasStrictDerivAt_pow m x using 2
    rw [← Int.ofNat_one, ← Int.ofNat_sub, zpow_natCast]
    norm_cast at hm
  rcases lt_trichotomy m 0 with (hm | hm | hm)
  · have hx : x ≠ 0 := h.resolve_right hm.not_le
    have := (hasStrictDerivAt_inv ?_).scomp _ (this (-m) (neg_pos.2 hm)) <;>
      [skip; exact zpow_ne_zero _ hx]
    simp only [Function.comp_def, zpow_neg, one_div, inv_inv, smul_eq_mul] at this
    convert this using 1
    rw [sq, mul_inv, inv_inv, Int.cast_neg, neg_mul, neg_mul_neg, ← zpow_add₀ hx, mul_assoc, ←
      zpow_add₀ hx]
    congr
    abel
  · simp only [hm, zpow_zero, Int.cast_zero, zero_mul, hasStrictDerivAt_const]
  · exact this m hm

theorem hasDerivAt_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
    HasDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x :=
  (hasStrictDerivAt_zpow m x h).hasDerivAt

theorem hasDerivWithinAt_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) s x :=
  (hasDerivAt_zpow m x h).hasDerivWithinAt

theorem differentiableAt_zpow : DifferentiableAt 𝕜 (fun x => x ^ m) x ↔ x ≠ 0 ∨ 0 ≤ m :=
  ⟨fun H => NormedField.continuousAt_zpow.1 H.continuousAt, fun H =>
    (hasDerivAt_zpow m x H).differentiableAt⟩

theorem differentiableWithinAt_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
    DifferentiableWithinAt 𝕜 (fun x => x ^ m) s x :=
  (differentiableAt_zpow.mpr h).differentiableWithinAt

theorem differentiableOn_zpow (m : ℤ) (s : Set 𝕜) (h : (0 : 𝕜) ∉ s ∨ 0 ≤ m) :
    DifferentiableOn 𝕜 (fun x => x ^ m) s := fun x hxs =>
  differentiableWithinAt_zpow m x <| h.imp_left <| ne_of_mem_of_not_mem hxs

theorem deriv_zpow (m : ℤ) (x : 𝕜) : deriv (fun x => x ^ m) x = m * x ^ (m - 1) := by
  by_cases H : x ≠ 0 ∨ 0 ≤ m
  · exact (hasDerivAt_zpow m x H).deriv
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_zpow.1 H)]
    push_neg at H
    rcases H with ⟨rfl, hm⟩
    rw [zero_zpow _ ((sub_one_lt _).trans hm).ne, mul_zero]

@[simp]
theorem deriv_zpow' (m : ℤ) : (deriv fun x : 𝕜 => x ^ m) = fun x => (m : 𝕜) * x ^ (m - 1) :=
  funext <| deriv_zpow m

theorem derivWithin_zpow (hxs : UniqueDiffWithinAt 𝕜 s x) (h : x ≠ 0 ∨ 0 ≤ m) :
    derivWithin (fun x => x ^ m) s x = (m : 𝕜) * x ^ (m - 1) :=
  (hasDerivWithinAt_zpow m x h s).derivWithin hxs

@[simp]
theorem iter_deriv_zpow' (m : ℤ) (k : ℕ) :
    (deriv^[k] fun x : 𝕜 => x ^ m) =
      fun x => (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k) := by
  induction k with
  | zero =>
    simp only [one_mul, Int.ofNat_zero, id, sub_zero, Finset.prod_range_zero, Function.iterate_zero]
  | succ k ihk =>
    simp only [Function.iterate_succ_apply', ihk, deriv_const_mul_field', deriv_zpow',
      Finset.prod_range_succ, Int.ofNat_succ, ← sub_sub, Int.cast_sub, Int.cast_natCast, mul_assoc]

theorem iter_deriv_zpow (m : ℤ) (x : 𝕜) (k : ℕ) :
    deriv^[k] (fun y => y ^ m) x = (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k) :=
  congr_fun (iter_deriv_zpow' m k) x

theorem iter_deriv_pow (n : ℕ) (x : 𝕜) (k : ℕ) :
    deriv^[k] (fun x : 𝕜 => x ^ n) x = (∏ i ∈ Finset.range k, ((n : 𝕜) - i)) * x ^ (n - k) := by
  simp only [← zpow_natCast, iter_deriv_zpow, Int.cast_natCast]
  rcases le_or_lt k n with hkn | hnk
  · rw [Int.ofNat_sub hkn]
  · have : (∏ i ∈ Finset.range k, (n - i : 𝕜)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hnk) (sub_self _)
    simp only [this, zero_mul]

@[simp]
theorem iter_deriv_pow' (n k : ℕ) :
    (deriv^[k] fun x : 𝕜 => x ^ n) =
      fun x => (∏ i ∈ Finset.range k, ((n : 𝕜) - i)) * x ^ (n - k) :=
  funext fun x => iter_deriv_pow n x k

theorem iter_deriv_inv (k : ℕ) (x : 𝕜) :
    deriv^[k] Inv.inv x = (∏ i ∈ Finset.range k, (-1 - i : 𝕜)) * x ^ (-1 - k : ℤ) := by
  simpa only [zpow_neg_one, Int.cast_neg, Int.cast_one] using iter_deriv_zpow (-1) x k

@[simp]
theorem iter_deriv_inv' (k : ℕ) :
    deriv^[k] Inv.inv = fun x : 𝕜 => (∏ i ∈ Finset.range k, (-1 - i : 𝕜)) * x ^ (-1 - k : ℤ) :=
  funext (iter_deriv_inv k)

variable {f : E → 𝕜} {t : Set E} {a : E}

theorem DifferentiableWithinAt.zpow (hf : DifferentiableWithinAt 𝕜 f t a) (h : f a ≠ 0 ∨ 0 ≤ m) :
    DifferentiableWithinAt 𝕜 (fun x => f x ^ m) t a :=
  (differentiableAt_zpow.2 h).comp_differentiableWithinAt a hf

theorem DifferentiableAt.zpow (hf : DifferentiableAt 𝕜 f a) (h : f a ≠ 0 ∨ 0 ≤ m) :
    DifferentiableAt 𝕜 (fun x => f x ^ m) a :=
  (differentiableAt_zpow.2 h).comp a hf

theorem DifferentiableOn.zpow (hf : DifferentiableOn 𝕜 f t) (h : (∀ x ∈ t, f x ≠ 0) ∨ 0 ≤ m) :
    DifferentiableOn 𝕜 (fun x => f x ^ m) t := fun x hx =>
  (hf x hx).zpow <| h.imp_left fun h => h x hx

theorem Differentiable.zpow (hf : Differentiable 𝕜 f) (h : (∀ x, f x ≠ 0) ∨ 0 ≤ m) :
    Differentiable 𝕜 fun x => f x ^ m := fun x => (hf x).zpow <| h.imp_left fun h => h x
