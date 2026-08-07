/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Sets with bounded covering exponent

A property of sets in a pseudoemetric space that bounds the growth of their covering numbers as the
radius of the balls goes to zero.
This will be used in the proof of the Kolmogorov-Chentsov theorem, that gives a sufficient condition
for a stochastic process to have a modification with Hölder continuous paths.

## Main definitions

* `HasCoveringExponent A c d` : a set `A` in a pseudoemetric space has bounded covering number with
  constant `c` and exponent `d` if it has finite diameter and for all `ε ∈ (0, diam(A)]`,
  the covering number of `A` at scale `ε` is bounded by `c * ε^{-d}`.

## Main statements

* `HasCoveringExponent.subset`: if `A` has bounded covering exponent with constant `c` and
  exponent `d`, then any subset of `A` has bounded covering exponent with constant `2^d * c` and
  exponent `d`.

-/

@[expose] public section

open scoped ENNReal NNReal

namespace Metric

variable {T : Type*} [PseudoEMetricSpace T] {A B : Set T} {c : ℝ≥0∞} {ε : ℝ≥0} {d : ℝ}

/-- A set `A` in a pseudoemetric space has bounded covering number with constant `c` and exponent
`d` if it has finite diameter and for all `ε ∈ (0, diam(A)]`, the covering number of `A`
at scale `ε` is bounded by `c * ε^{-d}`. -/
structure HasCoveringExponent (A : Set T) (c : ℝ≥0∞) (d : ℝ) : Prop where
  ediam_lt_top : Metric.ediam A < ∞
  coveringNumber_le : ∀ ε : ℝ≥0, ε ≤ Metric.ediam A → coveringNumber ε A ≤ c * (ε : ℝ≥0∞)⁻¹ ^ d

lemma HasCoveringExponent.coveringNumber_lt_top (h : HasCoveringExponent A c d) (hε_ne : ε ≠ 0)
    (hc : c ≠ ∞) (hd : 0 ≤ d) :
    coveringNumber ε A < ⊤ := by
  by_cases hε_le : ε ≤ Metric.ediam A
  · suffices (coveringNumber ε A : ℝ≥0∞) < ∞ by norm_cast at this
    calc (coveringNumber ε A : ℝ≥0∞)
    _ ≤ c * (ε : ℝ≥0∞)⁻¹ ^ d := h.coveringNumber_le _ hε_le
    _ < ∞ := by
      refine ENNReal.mul_lt_top hc.lt_top ?_
      exact ENNReal.rpow_lt_top_of_nonneg hd (by simp [hε_ne])
  · calc coveringNumber ε A
    _ ≤ 1 := coveringNumber_le_one_of_ediam_le (not_le.mp hε_le).le
    _ < ⊤ := by simp

lemma HasCoveringExponent.coveringNumber_ne_top (h : HasCoveringExponent A c d) (hε_ne : ε ≠ 0)
    (hc : c ≠ ∞) (hd : 0 ≤ d) :
    coveringNumber ε A ≠ ⊤ :=
  (h.coveringNumber_lt_top hε_ne hc hd).ne

lemma HasCoveringExponent.subset (h : HasCoveringExponent A c d) (hBA : B ⊆ A) (hd : 0 ≤ d) :
    HasCoveringExponent B (2 ^ d * c) d := by
  constructor
  · exact lt_of_le_of_lt (Metric.ediam_mono hBA) h.ediam_lt_top
  intro ε hε_le
  by_cases hdA : d = 0 ∧ Metric.ediam A = ∞
  · simp only [hdA.1, ENNReal.rpow_zero, one_mul, mul_one]
    replace h := h.coveringNumber_le 0 (by simp)
    simp only [hdA.1, ENNReal.rpow_zero, mul_one] at h
    calc (coveringNumber ε B : ℝ≥0∞)
    _ ≤ coveringNumber 0 B := mod_cast coveringNumber_anti zero_le
    _ ≤ coveringNumber (0 / 2) A := mod_cast coveringNumber_subset_le hBA
    _ = coveringNumber 0 A := by simp
    _ ≤ c := h
  push Not at hdA
  calc (coveringNumber ε B : ℝ≥0∞)
  _ ≤ coveringNumber (ε / 2) A := mod_cast coveringNumber_subset_le hBA
  _ ≤ c * (ε / 2 : ℝ≥0∞)⁻¹ ^ d := by
    replace h := h.coveringNumber_le (ε / 2) ?_
    · simpa using h
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_ofNat]
      calc (ε / 2 : ℝ≥0∞) ≤ ε := ENNReal.half_le_self
      _ ≤ Metric.ediam B := hε_le
      _ ≤ Metric.ediam A := Metric.ediam_mono hBA
  _ = 2 ^ d * c * (ε : ℝ≥0∞)⁻¹ ^ d := by
    rw [div_eq_mul_inv, ENNReal.mul_inv (by simp) (by simp), inv_inv,
      ENNReal.mul_rpow_of_nonneg _ _ hd]
    ring

end Metric
