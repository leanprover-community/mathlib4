/-
Copyright (c) 2026 Julian Rolfes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Rolfes, Luke Schleef, Philipp Svinger, Paul Niessner, Florian Grube
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Peano Existence Theorem

This files concerns ODE theory involving a continuous time-dependent vector field on a
finite-dimensional real normed vector space. The assumptions are collected in `IsPeano`.

This file constructs Tonelli approximations with a delayed input
which prepares for Peano existence theorem.

## Main definitions

- `IsPeano`: the hypotheses on the vector field and its cylinder of definition.
- `IsPeano.stepSize`: the time-step size of a Tonelli approximation.
- `IsPeano.delayedInput`: the delayed time argument used in the Tonelli approximations.
- `IsPeano.tonelliIterate`: the recursively defined curves used in the construction.
- `IsPeano.tonelliApproximation`: the diagonal sequence of Tonelli approximations.

## Tags

differential equation, initial value problem, Tonelli approximation
-/

@[expose] public section

open Metric Set
open scoped NNReal

/-! ### Assumptions of Peano's existence theorem -/

/-- The hypotheses for Peano's existence theorem on a closed time interval and a closed ball. -/
structure IsPeano {E : Type*} [NormedAddCommGroup E]
    (f : ℝ × E → E) (tmin tmax t₀ : ℝ) (x₀ : E) (r L : ℝ≥0) : Prop where
  /-- The initial time belongs to the time interval. -/
  t₀_mem : t₀ ∈ Icc tmin tmax
  /-- The vector field is continuous on the set product of a time interval and a closed ball. -/
  continuousOn : ContinuousOn f (Icc tmin tmax ×ˢ closedBall x₀ r)
  /-- `L` is an upper bound of the norm of the vector field. -/
  norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ r, ‖f (t, x)‖ ≤ L
  /-- The time interval of validity. -/
  mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ r

namespace IsPeano

variable {E : Type*} [NormedAddCommGroup E]
  {f : ℝ × E → E} {α : ℝ → E} {tmin tmax t₀ : ℝ} {x₀ : E} {r L : ℝ≥0}

variable [NormedSpace ℝ E]

/-! ### Tonelli approximations -/

section TonelliApproximation

/-- The time-step size of the `n`th Tonelli approximation. -/
noncomputable def stepSize (t₀ tmax : ℝ) (n : ℕ) : ℝ := (tmax - t₀) / n

lemma stepSize_nonneg {t₀ tmax : ℝ} (n : ℕ) (ht₀ : t₀ ≤ tmax) :
    0 ≤ stepSize t₀ tmax n :=
  div_nonneg (sub_nonneg.mpr ht₀) (Nat.cast_nonneg n)

lemma add_mul_stepSize_eq_tmax {t₀ tmax : ℝ} (n : ℕ) :
    t₀ + ((n : ℝ) + 1) * stepSize t₀ tmax (n + 1) = tmax := by
  rw [stepSize]
  grind

/-- The delayed time input used in the Tonelli approximations. -/
noncomputable def delayedInput (t₀ tmax : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun t ↦ max (t - stepSize t₀ tmax n) t₀

/-- The delayed input maps the first `k + 1` time steps into the first `k` time steps. -/
lemma mapsTo_delayedInput_previous_interval
    {t₀ tmax : ℝ} (n k : ℕ) (ht₀ : t₀ ≤ tmax) :
    MapsTo (delayedInput t₀ tmax n)
      (Icc t₀ (t₀ + (k + 1 : ℝ) * stepSize t₀ tmax n))
      (Icc t₀ (t₀ + (k : ℝ) * stepSize t₀ tmax n)) := by
  intro s hs
  rw [mem_Icc] at hs ⊢
  have h_mul_nonneg : 0 ≤ (k : ℝ) * stepSize t₀ tmax n :=
    mul_nonneg (Nat.cast_nonneg k) (stepSize_nonneg n ht₀)
  exact ⟨le_max_right _ _, max_le (by linarith) (by linarith)⟩

lemma mapsTo_delayedInput {t₀ tmax : ℝ} (n : ℕ) (ht₀ : t₀ ≤ tmax) :
    MapsTo (delayedInput t₀ tmax n) (Icc t₀ tmax) (Icc t₀ tmax) := by
  intro s hs
  rw [mem_Icc] at hs ⊢
  have := stepSize_nonneg n ht₀
  exact ⟨le_max_right _ _, max_le (by linarith) ht₀⟩

lemma lipschitzWith_delayedInput {t₀ tmax : ℝ} (n : ℕ) :
    LipschitzWith 1 (delayedInput t₀ tmax n) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa [delayedInput, Real.dist_eq, sub_sub_sub_cancel_right] using
    abs_max_sub_max_le_abs (x - stepSize t₀ tmax n) (y - stepSize t₀ tmax n) t₀

/-- The recursively defined curves used to build the Tonelli approximations. -/
noncomputable def tonelliIterate (f : ℝ × E → E) (t₀ tmax : ℝ) (x₀ : E) (n : ℕ) :
    ℕ → ℝ → E
  | 0 => fun _ ↦ x₀
  | k + 1 =>
      fun t ↦ x₀ + ∫ s in t₀..t,
        f (s, tonelliIterate f t₀ tmax x₀ n k (delayedInput t₀ tmax n s))

/-- Every recursively defined curve takes the value `x₀` at `t₀`. -/
lemma tonelliIterate_apply_t₀
    (f : ℝ × E → E) {t₀ tmax : ℝ} (x₀ : E) (n : ℕ) (k : ℕ) :
    tonelliIterate f t₀ tmax x₀ n k t₀ = x₀ := by
  induction k <;> simp [tonelliIterate]

/-- Consecutive recursive curves agree on the first `k` time steps. -/
lemma tonelliIterate_eq_succ_on_Icc (n : ℕ) (k : ℕ) (ht₀ : t₀ ≤ tmax) (t : ℝ)
    (ht : t ∈ Icc t₀ (t₀ + k * stepSize t₀ tmax n)) :
    tonelliIterate f t₀ tmax x₀ n k t = tonelliIterate f t₀ tmax x₀ n (k + 1) t := by
  induction k generalizing t with
  | zero =>
    obtain rfl : t = t₀ := by simp_all
    unfold tonelliIterate
    simp
  | succ k ih =>
    push_cast at ht
    unfold tonelliIterate
    simp only [add_right_inj]
    apply intervalIntegral.integral_congr
    intro s hs
    simp only [ih _ (mapsTo_delayedInput_previous_interval n k ht₀
      (uIcc_subset_Icc (left_mem_Icc.mpr (ht.1.trans ht.2)) ht hs))]

/-- The diagonal sequence of Tonelli approximations. -/
noncomputable def tonelliApproximation
    (f : ℝ × E → E) (t₀ tmax : ℝ) (x₀ : E) (n : ℕ) : ℝ → E :=
  fun t ↦ tonelliIterate f t₀ tmax x₀ (n + 1) (n + 1) t

/-- Every diagonal Tonelli approximation satisfies the integral equation with delayed input. -/
lemma tonelliApproximation_eq_integral (n : ℕ) (t : ℝ) (ht : t ∈ Icc t₀ tmax) :
    tonelliApproximation f t₀ tmax x₀ n t =
      x₀ + ∫ s in t₀..t,
        f (s, tonelliApproximation f t₀ tmax x₀ n (delayedInput t₀ tmax (n + 1) s)) := by
  have h_succ : ∀ t ∈ Icc t₀ tmax, tonelliApproximation f t₀ tmax x₀ n t =
      tonelliIterate f t₀ tmax x₀ (n + 1) (n + 2) t := by
    intro t ht
    apply tonelliIterate_eq_succ_on_Icc (n + 1) (n + 1) (ht.1.trans ht.2)
    simpa only [Nat.cast_add, Nat.cast_one, add_mul_stepSize_eq_tmax] using ht
  simp_rw [h_succ t ht, tonelliApproximation, tonelliIterate]

end TonelliApproximation

end IsPeano
