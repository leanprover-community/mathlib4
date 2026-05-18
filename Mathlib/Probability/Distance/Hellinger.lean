/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Probability.Distance.TotalVariation

/-!
# Bretagnolle–Huber bridge via Hellinger / Bhattacharyya affinity

The classical Bretagnolle–Huber inequality bounds the total variation distance
between two probability measures by their Kullback–Leibler divergence:

  `tvDist² μ ν ≤ 1 - exp (-KL μ ν)`.

The standard proof factors through the **Bhattacharyya affinity**
`ρ μ ν := ∫ √(dμ/dτ · dν/dτ) dτ ∈ [0, 1]` (or equivalently the squared
Hellinger distance `H² := 2 (1 - ρ)`) and a two-step chain:

1. `tvDist²(μ, ν) ≤ 1 - ρ(μ, ν)²` (Le Cam / Cauchy–Schwarz),
2. `ρ(μ, ν) ≥ exp (-KL(μ‖ν) / 2)` (Jensen on `-log`).

Combining (1) with the square of (2) yields the Bretagnolle–Huber bound.

Mathlib does not yet expose `bhattacharyya` or `hellingerSquared` directly,
so this file gives the **algebraic bridge** that consumes the two characteristic
hypotheses as inputs and produces the squared-distance bound on `tvDist`.
Once the Hellinger / Bhattacharyya infrastructure is in place, the hypotheses
become standalone theorems and the parametric statement collapses to the
textbook Bretagnolle–Huber inequality.

## Main results

* `MeasureTheory.exp_neg_le_sq_of_exp_neg_half_le` : `exp (-D / 2) ≤ ρ`
  implies `exp (-D) ≤ ρ²` for nonnegative `ρ`.
* `MeasureTheory.tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya` : given the
  Le Cam estimate `tvDist² ≤ 1 - ρ²` and the Jensen-style bound
  `exp (-D / 2) ≤ ρ`, the bridge `tvDist² ≤ 1 - exp (-D)` holds.
* `MeasureTheory.tvDist_sq_le_one_sub_exp_neg_of_hellinger` : Hellinger-form
  variant parametrized by the squared Hellinger distance `H² = 2 (1 - ρ)`.

## References

* J. Bretagnolle and C. Huber, *Estimation des densités: risque minimax*,
  Z. Wahrscheinlichkeitstheorie verw. Gebiete **47** (1979), 119–137.
* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer,
  2009, Section 2.4.
* L. Devroye, L. Györfi, G. Lugosi, *A Probabilistic Theory of Pattern
  Recognition*, Springer, 1996, Chapter 8.

## Tags

Bretagnolle-Huber, Hellinger, Bhattacharyya, total variation, KL divergence
-/

@[expose] public section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- **Squaring the Bhattacharyya lower bound.**

If `Real.exp (-D / 2) ≤ ρ` and `0 ≤ ρ`, then squaring both sides gives
`Real.exp (-D) ≤ ρ ^ 2`. This is the elementary monotonicity step that
upgrades the Jensen-on-`log` bound `ρ ≥ exp (-D / 2)` to its squared form,
ready for use against the Le Cam estimate `tvDist² ≤ 1 - ρ²`. -/
theorem exp_neg_le_sq_of_exp_neg_half_le {D ρ : ℝ}
    (_hρ_nonneg : 0 ≤ ρ) (h : Real.exp (-D / 2) ≤ ρ) :
    Real.exp (-D) ≤ ρ ^ 2 := by
  have h_exp_nonneg : 0 ≤ Real.exp (-D / 2) := (Real.exp_pos _).le
  have h_sq : Real.exp (-D / 2) ^ 2 ≤ ρ ^ 2 :=
    pow_le_pow_left₀ h_exp_nonneg h 2
  have h_rewrite : Real.exp (-D / 2) ^ 2 = Real.exp (-D) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [h_rewrite] at h_sq
  exact h_sq

/-- **Bhattacharyya-affinity discharge of the Bretagnolle–Huber bridge.**

If a real number `ρ` plays the role of the Bhattacharyya affinity between
two measures `μ` and `ν`, satisfying

* `0 ≤ ρ` (the affinity is nonnegative),
* `tvDist² μ ν ≤ 1 - ρ²` (Le Cam / Cauchy–Schwarz step), and
* `Real.exp (-D / 2) ≤ ρ` (Jensen on `-log`, with `D` standing in for KL),

then the **Bretagnolle–Huber bridge** holds:

  `tvDist² μ ν ≤ 1 - Real.exp (-D)`.

The proof is the algebraic chain `tvDist² ≤ 1 - ρ² ≤ 1 - exp (-D)`. -/
theorem tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya
    (μ ν : Measure α) {ρ D : ℝ} (hρ_nonneg : 0 ≤ ρ)
    (h_lecam : (tvDist μ ν).toReal ^ 2 ≤ 1 - ρ ^ 2)
    (h_kl_bridge : Real.exp (-D / 2) ≤ ρ) :
    (tvDist μ ν).toReal ^ 2 ≤ 1 - Real.exp (-D) := by
  have h_sq : Real.exp (-D) ≤ ρ ^ 2 :=
    exp_neg_le_sq_of_exp_neg_half_le hρ_nonneg h_kl_bridge
  have h_chain : 1 - ρ ^ 2 ≤ 1 - Real.exp (-D) := by linarith
  exact h_lecam.trans h_chain

/-- **Hellinger-distance variant of the Bretagnolle–Huber bridge.**

If the squared Hellinger distance `Hsq` between two measures `μ` and `ν`
satisfies

* `0 ≤ Hsq` and `Hsq ≤ 2` (the natural range for probability measures),
* `tvDist² μ ν ≤ Hsq · (1 - Hsq / 4)` (Le Cam in Hellinger form), and
* `Hsq ≤ 2 · (1 - Real.exp (-D / 2))` (Bhattacharyya–KL on `Hsq = 2 (1 - ρ)`),

then `tvDist² μ ν ≤ 1 - Real.exp (-D)`.

The proof reduces to `tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya` via
the identity `ρ = 1 - Hsq / 2`. -/
theorem tvDist_sq_le_one_sub_exp_neg_of_hellinger
    (μ ν : Measure α) {Hsq D : ℝ}
    (_hH_nonneg : 0 ≤ Hsq) (hH_le_two : Hsq ≤ 2)
    (h_lecam : (tvDist μ ν).toReal ^ 2 ≤ Hsq * (1 - Hsq / 4))
    (h_kl_bridge : Hsq ≤ 2 * (1 - Real.exp (-D / 2))) :
    (tvDist μ ν).toReal ^ 2 ≤ 1 - Real.exp (-D) := by
  -- Set `ρ = 1 - Hsq / 2`. Then `0 ≤ ρ` (from `Hsq ≤ 2`) and the two
  -- Hellinger hypotheses translate to the Bhattacharyya hypotheses.
  set ρ : ℝ := 1 - Hsq / 2 with hρ_def
  have hρ_nonneg : 0 ≤ ρ := by simp [hρ_def]; linarith
  have h_lecam' : (tvDist μ ν).toReal ^ 2 ≤ 1 - ρ ^ 2 := by
    have h_eq : Hsq * (1 - Hsq / 4) = 1 - ρ ^ 2 := by
      simp only [hρ_def]; ring
    rw [← h_eq]
    exact h_lecam
  have h_kl_bridge' : Real.exp (-D / 2) ≤ ρ := by
    simp only [hρ_def]; linarith
  exact tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya μ ν
    hρ_nonneg h_lecam' h_kl_bridge'

end MeasureTheory
