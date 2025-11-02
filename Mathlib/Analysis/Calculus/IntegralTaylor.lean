/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib

/-!
# Taylor's formula with an integral remainder

-/

open Nat

variable {𝕜 E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

variable {f : E → F} {x y : E} (t : 𝕜) {n : ℕ}

/-- The iterated derivative is given by the derivative of the `n-1` iterated derivative. -/
theorem bar {m : Fin (n + 1) → E} (hf : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n f) x) :
    iteratedFDeriv 𝕜 (n + 1) f x m =
    fderiv 𝕜 (fun y ↦ iteratedFDeriv 𝕜 n f y (Fin.tail m)) x (m 0) := by
  convert iteratedFDeriv_succ_apply_left m
  simp [fderiv_continuousMultilinear_apply_const hf]

theorem foo_zero (hf : DifferentiableAt 𝕜 f (x + t • y)) :
    deriv (fun (s : 𝕜) ↦ f (x + s • y)) t = fderiv 𝕜 f (x + t • y) y := by
  have hg : Differentiable 𝕜 (fun (s : 𝕜) ↦ (x + s • y)) := by fun_prop
  convert fderiv_comp_deriv t hf hg.differentiableAt
  simpa using (deriv_smul_const (x := t) differentiableAt_id y).symm

theorem foo (hf : ContDiffAt 𝕜 (n + 1) f (x + t • y)) :
    deriv (fun (s : 𝕜) ↦ iteratedFDeriv 𝕜 n f (x + s • y) (fun _ ↦ y)) t =
    iteratedFDeriv 𝕜 (n + 1) f (x + t • y) (fun _ ↦ y) := by
  have hf' : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n f) (x + t • y) := by
    apply hf.differentiableAt_iteratedFDeriv
    norm_cast
    grind
  convert foo_zero t (hf'.continuousMultilinear_apply_const _)
  exact bar hf'

end NontriviallyNormedField

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

variable {f : E → F} {x y : E} {n : ℕ}

example {a b c : ℝ} : a + b = c ↔ b = (-a) + c := by
  exact Iff.symm eq_neg_add_iff_add_eq

--#exit

#check intervalIntegral.integral_smul_deriv_eq_deriv_smul

variable [CompleteSpace F]

theorem baz (hf : ∀ (t : ℝ) (ht : t ∈ Set.uIcc 0 1), ContDiffAt ℝ (n + 1) f (x + t • y)) :
    f (x + y) = ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • (iteratedFDeriv ℝ k f x (fun _ ↦ y)) +
    (n ! : ℝ)⁻¹ • ∫ t in 0..1, (1 - t)^n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ ↦ y) := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, factorial_zero, cast_one, inv_one,
    iteratedFDeriv_zero_apply, one_smul, pow_zero, reduceAdd, iteratedFDeriv_one_apply]
    rw [← sub_eq_iff_eq_add', Eq.comm]
    have hf' : ∀ (t : ℝ) (ht : t ∈ Set.uIcc 0 1), DifferentiableAt ℝ (fun s ↦ f (x + s • y)) t :=
      fun t ht ↦ ((hf t ht).differentiableAt (by simp)).comp t (by fun_prop)
    have hint : IntervalIntegrable (deriv (fun s ↦ f (x + s • y))) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      have : ContDiffOn ℝ 1 (fun (s : ℝ) ↦ f (x + s • y)) (Set.uIcc 0 1) := sorry
      intro t ht
      specialize hf t ht
      simp only [CharP.cast_eq_zero, zero_add] at hf

      sorry
    have := intervalIntegral.integral_deriv_eq_sub hf' hint
    simp only [one_smul, zero_smul, add_zero] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [foo_zero]
    apply (hf t ht).differentiableAt
    simp
  | succ n ih =>
    specialize ih (fun t ht ↦ (hf t ht).of_le (by simp))
    rw [Finset.sum_range_succ, add_assoc]
    convert ih using 2
    set u := fun (k : ℕ) (t : ℝ) ↦ (k ! : ℝ)⁻¹ * (1 - t) ^ k
    have hu : ∀ (k : ℕ) (t : ℝ), HasDerivAt (u k) (-u (k - 1) t) t := by
      intro k t
      unfold u
      sorry
    have hu' : ∀ (k : ℕ), IntervalIntegrable (u k) MeasureTheory.volume 0 1 := by
      sorry
    set v := fun (k : ℕ) (t : ℝ) ↦ iteratedFDeriv ℝ k f (x + t • y) (fun _ ↦ y)
    have hv : ∀ (k : ℕ) (t : ℝ), HasDerivAt (v k) (v (k + 1) t) t := by
      sorry
    have hv' : ∀ (k : ℕ), IntervalIntegrable (v k) MeasureTheory.volume 0 1 := by
      sorry
    -- We rest of the proof is integration by parts
    have := intervalIntegral.integral_smul_deriv_eq_deriv_smul
      (fun t _ ↦ hu (n + 1) t) (fun t _ ↦ hv (n + 1) t) (hu' n).neg (hv' _)
    simp only [← eq_neg_add_iff_add_eq, ← intervalIntegral.integral_smul, smul_smul]
    nth_rw 1 [sub_eq_add_neg] at this
    simp only [← intervalIntegral.integral_neg, add_tsub_cancel_right, neg_smul, neg_neg] at this
    convert this using 1
    congr 1
    simp [u, v]
