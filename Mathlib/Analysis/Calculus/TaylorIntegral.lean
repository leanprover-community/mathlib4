/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Taylor's formula with an integral remainder

In this file we prove Taylor's formula with the remainder term in integral form.

* `add_eq_sum_add_integral_iteratedFDeriv`: version for higher dimensions with `iteratedFDeriv`
* `add_eq_sum_add_integral_iteratedDeriv`: one-dimensional version with `iteratedDeriv`
-/

open Nat

variable {𝕜 E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

variable {f : E → F} {x y : E} {t : 𝕜} {n : ℕ}

/-- The iterated derivative is given by the derivative of the `n-1` iterated derivative. -/
theorem DifferentiableAt.iteratedFDeriv_succ_apply_left' {m : Fin (n + 1) → E}
    (hf : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n f) x) :
    iteratedFDeriv 𝕜 (n + 1) f x m =
    fderiv 𝕜 (fun y ↦ iteratedFDeriv 𝕜 n f y (Fin.tail m)) x (m 0) := by
  convert iteratedFDeriv_succ_apply_left m
  simp [fderiv_continuousMultilinear_apply_const hf]

theorem DifferentiableAt.deriv_comp_add_smul (hf : DifferentiableAt 𝕜 f (x + t • y)) :
    deriv (fun (s : 𝕜) ↦ f (x + s • y)) t = fderiv 𝕜 f (x + t • y) y := by
  have hg : Differentiable 𝕜 (fun (s : 𝕜) ↦ (x + s • y)) := by fun_prop
  convert fderiv_comp_deriv t hf hg.differentiableAt
  simpa using (deriv_smul_const (x := t) differentiableAt_id y).symm

theorem ContDiffAt.deriv_fderiv_add_smul (hf : ContDiffAt 𝕜 (n + 1) f (x + t • y)) :
    deriv (fun (s : 𝕜) ↦ iteratedFDeriv 𝕜 n f (x + s • y) (fun _ ↦ y)) t =
    iteratedFDeriv 𝕜 (n + 1) f (x + t • y) (fun _ ↦ y) := by
  have hf' : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n f) (x + t • y) := by
    apply hf.differentiableAt_iteratedFDeriv
    norm_cast
    exact lt_add_one n
  convert (hf'.continuousMultilinear_apply_const _).deriv_comp_add_smul
  exact hf'.iteratedFDeriv_succ_apply_left'

end NontriviallyNormedField

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

variable {f : E → F} {x y : E} {n : ℕ}

variable [CompleteSpace F]

/-- *Taylor's theorem with remainder in integral form*.

Version for higher dimensions. -/
theorem add_eq_sum_add_integral_iteratedFDeriv (hf : ∀ (t : ℝ) (_ht : t ∈ Set.Icc 0 1),
    ContDiffAt ℝ (n + 1) f (x + t • y)) :
    f (x + y) = ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • (iteratedFDeriv ℝ k f x (fun _ ↦ y)) +
    (n ! : ℝ)⁻¹ • ∫ t in 0..1, (1 - t)^n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ ↦ y) := by
  simp_rw [← Set.uIcc_of_le zero_le_one] at hf
  induction n with
  | zero =>
    -- The base case follows from the fundamental theorem of calculus
    have h_eq : Set.EqOn (fun t ↦ (fderiv ℝ f (x + t • y)) y) (deriv fun (s : ℝ) ↦ f (x + s • y))
        (Set.uIcc 0 1) := by
      intro t ht
      rw [DifferentiableAt.deriv_comp_add_smul]
      exact (hf t ht).differentiableAt (le_refl _)
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, factorial_zero, cast_one, inv_one,
      iteratedFDeriv_zero_apply, one_smul, pow_zero, reduceAdd, iteratedFDeriv_one_apply]
    rw [← sub_eq_iff_eq_add', Eq.comm, intervalIntegral.integral_congr h_eq]
    have hf' : ∀ (t : ℝ) (ht : t ∈ Set.uIcc 0 1), DifferentiableAt ℝ (fun s ↦ f (x + s • y)) t :=
      fun t ht ↦ ((hf t ht).differentiableAt (by simp)).comp t (by fun_prop)
    have hint : IntervalIntegrable (deriv (fun s ↦ f (x + s • y))) MeasureTheory.volume 0 1 := by
      have h₁ : ContinuousOn (fderiv ℝ f) ((fun t ↦ x + t • y) '' Set.uIcc (0 : ℝ) 1) := by
        intro z ⟨t, ht, hz⟩
        rw [← hz]
        exact (((hf t ht).fderiv_right (le_refl _)).continuousAt (n := 0)).continuousWithinAt
      have h₂ : ContinuousOn (fun x_1 ↦ fderiv ℝ f (x + x_1 • y)) (Set.uIcc (0 : ℝ) 1) := by
        apply h₁.comp (t := (fun t ↦ x + t • y) '' (Set.uIcc (0 : ℝ) 1)) (by fun_prop)
        intro t ht
        use t
      apply (ContinuousOn.congr _ h_eq.symm).intervalIntegrable
      fun_prop
    simpa using intervalIntegral.integral_deriv_eq_sub hf' hint
  | succ n ih =>
    -- We use the inductive hypothesis to cancel all lower order terms
    specialize ih (fun t ht ↦ (hf t ht).of_le (by simp))
    rw [Finset.sum_range_succ, add_assoc]
    convert ih using 2
    -- We define the functions u and v that we will integrate by parts
    set u := fun (k : ℕ) (t : ℝ) ↦ (k ! : ℝ)⁻¹ * (1 - t) ^ k
    have hu : ∀ (t : ℝ), HasDerivAt (u (n + 1)) (-u n t) t := by
      intro t
      unfold u
      have : (-((n ! : ℝ)⁻¹ * (1 - t) ^ n)) =
          ((n + 1) ! : ℝ)⁻¹ * ((n + 1) * (1 - t) ^ n * (-1)) := by
        field_simp
        congr 1
        rw [Nat.factorial_succ]
        grind
      rw [this]
      convert (((hasDerivAt_id t).const_sub 1).pow _).const_mul _
      norm_cast
    have hu' : Continuous (u n) := by fun_prop
    set v := fun (k : ℕ) (t : ℝ) ↦ iteratedFDeriv ℝ k f (x + t • y) (fun _ ↦ y)
    have hv : ∀ (t : ℝ) (ht : t ∈ Set.uIcc 0 1), HasDerivAt (v (n + 1)) (v (n + 1 + 1) t) t := by
      intro t ht
      unfold v
      rw [← (hf t ht).deriv_fderiv_add_smul]
      have h_diff : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 1) f) (x + t • y) := by
        apply (hf t ht).differentiableAt_iteratedFDeriv
        norm_cast
        grind
      refine DifferentiableAt.hasDerivAt ?_
      fun_prop
    have hv' : ContinuousOn (v (n + 1 + 1)) (Set.uIcc 0 1) := by
      intro t ht
      have h_cont : ContinuousAt (iteratedFDeriv ℝ (n + 1 + 1) f) (x + t • y) :=
        ((hf t ht).iteratedFDeriv_right (i := n + 1 + 1) (m := 0) (by simp)).continuousAt
      exact (h_cont.comp (x := t) (by fun_prop)).continuousWithinAt.eval_const _
    -- Now we apply integration by parts and simplify
    simpa [← eq_neg_add_iff_add_eq, ← intervalIntegral.integral_smul, smul_smul, u, v] using
      intervalIntegral.integral_smul_deriv_eq_deriv_smul (fun t _ ↦ hu t) hv
      (hu'.neg.intervalIntegrable _ _) hv'.intervalIntegrable

/-- *Taylor's theorem with remainder in integral form*.

Version for the 1-dimensional derivative. -/
theorem add_eq_sum_add_integral_iteratedDeriv {f : ℝ → F} {x y : ℝ}
    (hf : ∀ (t : ℝ) (_ht : t ∈ Set.uIcc x (x + y)), ContDiffAt ℝ (n + 1) f t) :
    f (x + y) = ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • y ^ k • iteratedDeriv k f x +
    (n ! : ℝ)⁻¹ • ∫ t in 0..1, (1 - t)^n • y ^ (n + 1) • iteratedDeriv (n + 1) f (x + t * y) := by
  have hf' : ∀ (t : ℝ) (_ht : t ∈ Set.Icc 0 1), ContDiffAt ℝ (n + 1) f (x + t * y) := by
    intro t ⟨ht₁, ht₂⟩
    apply hf (x + t * y)
    by_cases h : 0 ≤ y
    · refine Set.mem_uIcc_of_le ?_ ?_
      · simp only [le_add_iff_nonneg_right]
        positivity
      simp only [add_le_add_iff_left]
      exact mul_le_of_le_one_left h ht₂
    · simp only [not_le] at h
      refine Set.mem_uIcc_of_ge ?_ ?_
      · simp only [add_le_add_iff_left]
        exact le_mul_of_le_one_left h.le ht₂
      simp only [add_le_iff_nonpos_right]
      exact mul_nonpos_of_nonneg_of_nonpos ht₁ h.le
  simpa [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] using
    add_eq_sum_add_integral_iteratedFDeriv hf'
