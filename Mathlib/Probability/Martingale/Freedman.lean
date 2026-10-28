/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib.Probability.Martingale.Exponential
public import Mathlib.Probability.Martingale.Ville

/-!
# Freedman's inequality

Freedman's inequality bounds the probability that a real martingale crosses a level while its
predictable quadratic variation remains small. Unlike a bound expressed in terms of deterministic
increment bounds alone, it takes account of the conditional variances of the increments.

We assume only a one-sided upper bound on the increments. The proof applies Ville's inequality to
an exponential supermartingale with the standard Bernstein choice of parameter.

## Main results

* `MeasureTheory.Martingale.freedman_ineq`: the bound over all natural-number times.
* `MeasureTheory.Martingale.freedman_ineq_finite`: the bound up to a fixed time.
* `MeasureTheory.Martingale.freedman_ineq_of_variation_le`: a fixed-time bound when the predictable
  quadratic variation has a deterministic upper bound.

## References

* [D. A. Freedman, *On tail probabilities for martingales*][freedman1975]
-/

public section

open Filter Real
open scoped ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ} {b t v : ℝ}

namespace Martingale

/-- **Freedman's inequality** for a square-integrable real martingale with increments bounded
above by `b`: at any time, crossing `t` before the predictable quadratic variation exceeds `v`
has probability at most `exp (-t² / (2 * (v + b * t / 3)))`. -/
theorem freedman_ineq (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    (hM2 : ∀ n, MemLp (M n) 2 μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, M (n + 1) ω - M n ω ≤ b)
    (hb : 0 < b) (ht : 0 ≤ t) (hv : 0 < v) :
    μ.real {ω | ∃ n, t ≤ M n ω ∧ predictableQuadraticVariation M ℱ μ n ω ≤ v}
      ≤ exp (-t ^ 2 / (2 * (v + b * t / 3))) := by
  obtain rfl | ht := ht.eq_or_lt
  · simp
  let θ := t / (v + b * t / 3)
  let ψ := θ ^ 2 / (2 * (1 - θ * b / 3))
  have hd : 0 < v + b * t / 3 := by positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθb : θ * b < 3 := by
    dsimp [θ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    nlinarith
  have hψ : 0 ≤ ψ := by
    dsimp [ψ]
    exact div_nonneg (sq_nonneg _) (by linarith)
  let Z : ℕ → Ω → ℝ := fun n ω ↦
    exp (θ * M n ω - ψ * predictableQuadraticVariation M ℱ μ n ω)
  have hZ : Supermartingale Z ℱ μ :=
    hM.exponential_supermartingale hM0 hM2 hbound hb hθ.le hθb
  have hZ0 : μ[Z 0] = 1 := by
    have hz : Z 0 =ᵐ[μ] fun _ ↦ (1 : ℝ) := by
      filter_upwards [hM0] with ω hω
      simp [Z, hω]
    simpa using integral_congr_ae hz
  have hcross : μ.real {ω | ∃ n,
      exp (θ * t - ψ * v) ≤ Z n ω} ≤ exp (ψ * v - θ * t) := by
    have h := hZ.ville_ineq (fun n ↦ ae_of_all _ fun ω ↦ (exp_pos _).le)
      (exp_pos (θ * t - ψ * v))
    rw [hZ0, one_div, ← exp_neg] at h
    simpa [neg_sub] using h
  calc
    μ.real {ω | ∃ n, t ≤ M n ω ∧ predictableQuadraticVariation M ℱ μ n ω ≤ v}
      ≤ μ.real {ω | ∃ n, exp (θ * t - ψ * v) ≤ Z n ω} := by
        refine measureReal_mono ?_ (measure_ne_top _ _)
        rintro ω ⟨n, hn, hV⟩
        exact ⟨n, exp_le_exp.mpr <| sub_le_sub (mul_le_mul_of_nonneg_left hn hθ.le)
          (mul_le_mul_of_nonneg_left hV hψ)⟩
    _ ≤ exp (ψ * v - θ * t) := hcross
    _ = exp (-t ^ 2 / (2 * (v + b * t / 3))) := by
      congr 1
      dsimp [ψ, θ]
      field_simp
      ring

/-- Freedman's inequality up to a fixed natural-number time. -/
theorem freedman_ineq_finite (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    (hM2 : ∀ n, MemLp (M n) 2 μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, M (n + 1) ω - M n ω ≤ b)
    (hb : 0 < b) (ht : 0 ≤ t) (hv : 0 < v) (N : ℕ) :
    μ.real {ω | ∃ n ≤ N, t ≤ M n ω ∧ predictableQuadraticVariation M ℱ μ n ω ≤ v}
      ≤ exp (-t ^ 2 / (2 * (v + b * t / 3))) :=
  (measureReal_mono (by rintro ω ⟨n, _, hn⟩; exact ⟨n, hn⟩)).trans
    (hM.freedman_ineq hM0 hM2 hbound hb ht hv)

/-- At a fixed time, Freedman's inequality gives a Bernstein bound whenever the predictable
quadratic variation is almost surely bounded by a deterministic constant. -/
theorem freedman_ineq_of_variation_le (hM : Martingale M ℱ μ) (hM0 : M 0 =ᵐ[μ] 0)
    (hM2 : ∀ n, MemLp (M n) 2 μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, M (n + 1) ω - M n ω ≤ b)
    (hb : 0 < b) (ht : 0 ≤ t) (hv : 0 < v) (N : ℕ)
    (hV : ∀ᵐ ω ∂μ, predictableQuadraticVariation M ℱ μ N ω ≤ v) :
    μ.real {ω | t ≤ M N ω} ≤ exp (-t ^ 2 / (2 * (v + b * t / 3))) := by
  refine (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)).trans
    (hM.freedman_ineq hM0 hM2 hbound hb ht hv)
  filter_upwards [hV] with ω hω hMt
  exact ⟨N, hMt, hω⟩

end Martingale

end MeasureTheory
