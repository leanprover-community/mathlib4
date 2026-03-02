/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# HasBoundedCoveringNumber

-/

@[expose] public section

open Metric
open scoped ENNReal NNReal

variable {T : Type*} [PseudoEMetricSpace T] {A : Set T} {c : ℝ≥0∞} {ε : ℝ≥0} {d : ℝ}

/-- A set `A` in a pseudoemetric space has bounded covering number with constant `c` and exponent
`d` if it has finite diameter and for all `ε ∈ (0, diam(A)]`, the covering number of `A`
at scale `ε` is bounded by `c * ε^{-d}`. -/
structure HasBoundedCoveringNumber (A : Set T) (c : ℝ≥0∞) (d : ℝ) : Prop where
  ediam_lt_top : Metric.ediam A < ∞
  coveringNumber_le : ∀ ε : ℝ≥0, ε ≤ Metric.ediam A → coveringNumber ε A ≤ c * (ε : ℝ≥0∞)⁻¹ ^ d

lemma HasBoundedCoveringNumber.coveringNumber_lt_top
    (h : HasBoundedCoveringNumber A c d) (hε_ne : ε ≠ 0)
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

lemma HasBoundedCoveringNumber.subset {B : Set T}
    (h : HasBoundedCoveringNumber A c d) (hBA : B ⊆ A) (hd : 0 ≤ d) :
    HasBoundedCoveringNumber B (2 ^ d * c) d := by
  constructor
  · exact lt_of_le_of_lt (Metric.ediam_mono hBA) h.ediam_lt_top
  intro ε hε_le
  by_cases hdA : d = 0 ∧ Metric.ediam A = ∞
  · simp only [hdA.1, ENNReal.rpow_zero, one_mul, mul_one]
    replace h := h.coveringNumber_le 0 (by simp)
    simp only [hdA.1, ENNReal.rpow_zero, mul_one] at h
    calc (coveringNumber ε B : ℝ≥0∞)
    _ ≤ coveringNumber 0 B := mod_cast coveringNumber_anti zero_le'
    _ ≤ coveringNumber (0 / 2) A := mod_cast coveringNumber_subset_le hBA
    _ = coveringNumber 0 A := by simp
    _ ≤ c := h
  push_neg at hdA
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

structure IsCoverWithBoundedCoveringNumber (C : ℕ → Set T) (A : Set T) (c : ℕ → ℝ≥0∞) (d : ℕ → ℝ)
    where
  c_ne_top : ∀ n, c n ≠ ∞
  d_pos : ∀ n, 0 < d n
  isOpen : ∀ n, IsOpen (C n)
  totallyBounded : ∀ n, TotallyBounded (C n)
  hasBoundedCoveringNumber : ∀ n, HasBoundedCoveringNumber (C n) (c n) (d n)
  mono : ∀ n m, n ≤ m → C n ⊆ C m
  subset_iUnion : A ⊆ ⋃ i, C i

open scoped Pointwise in
lemma isCoverWithBoundedCoveringNumber_Ico_nnreal :
    IsCoverWithBoundedCoveringNumber (fun n ↦ Set.Ico (0 : ℝ≥0) (n + 1)) Set.univ
      (fun n ↦ 3 * (n + 1)) (fun _ ↦ 1) where
  c_ne_top n := by finiteness
  d_pos := by simp
  isOpen n := NNReal.isOpen_Ico_zero
  totallyBounded n := totallyBounded_Ico _ _
  hasBoundedCoveringNumber n := by
    have h_iso : Isometry ((↑) : ℝ≥0 → ℝ) := fun x y ↦ rfl
    have h_image : ((↑) : ℝ≥0 → ℝ) '' (Set.Ico (0 : ℝ≥0) (n + 1)) = Set.Ico (0 : ℝ) (n + 1) := by
      ext x
      simp only [Set.mem_image, Set.mem_Ico, zero_le, true_and]
      refine ⟨fun ⟨y, hy, hy_eq⟩ ↦ ?_, fun h ↦ ?_⟩
      · rw [← hy_eq]
        exact ⟨y.2, hy⟩
      · exact ⟨⟨x, h.1⟩, h.2, rfl⟩
    -- todo : extract that have as a lemma
    have h_diam : Metric.ediam (Set.Ico (0 : ℝ≥0) (n + 1)) = n + 1 := by
      rw [← h_iso.ediam_image, h_image]
      simp only [Real.ediam_Ico, sub_zero]
      norm_cast
    constructor
    · simp [h_diam]
    intro ε hε_le
    simp only [ENNReal.rpow_one]
    rw [← h_iso.coveringNumber_image, h_image]
    rw [h_diam] at hε_le
    have : Set.Ico (0 : ℝ) (n + 1) ⊆ Metric.closedEBall (((n : ℝ) + 1) / 2) ((n + 1) / 2) := by
      intro x hx
      simp only [Set.mem_Ico, Metric.mem_closedEBall, edist_dist, dist] at hx ⊢
      refine ENNReal.ofReal_le_of_le_toReal ?_
      simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
      norm_cast
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith
      · simp [hx.2.le]
    calc (coveringNumber ε (Set.Ico (0 : ℝ) (n + 1)) : ℝ≥0∞)
    _ ≤ coveringNumber (ε / 2) (Metric.closedEBall (((n : ℝ) + 1) / 2) ((n + 1) / 2)) := by
      gcongr
      exact coveringNumber_subset_le this
    _ ≤ 3 * ((n + 1) / 2 : ℝ≥0) / (ε / 2 : ℝ≥0) := by
      have h := coveringNumber_closedBall_le_three_mul (r := (n + 1) / 2) (ε := ε / 2)
        (x := ((n : ℝ) + 1) / 2) ?_ ?_
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_add,
          ENNReal.coe_natCast, ENNReal.coe_one, ENNReal.coe_ofNat, Module.finrank_self, pow_one]
          at h
        rwa [ENNReal.coe_div (by simp), ENNReal.coe_div (by simp)]
      · simp
      · gcongr
        exact mod_cast hε_le
    _ = 3 * (n + 1) / ε := by
      conv_lhs => rw [mul_div_assoc]
      conv_rhs => rw [mul_div_assoc]
      congr 1
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_add,
        ENNReal.coe_natCast, ENNReal.coe_one, ENNReal.coe_ofNat]
      simp_rw [div_eq_mul_inv]
      rw [ENNReal.mul_inv (by simp) (by simp), inv_inv, mul_assoc, mul_comm _ (2 : ℝ≥0∞),
        ← mul_assoc _ (2 : ℝ≥0∞), ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
    _ ≤ 3 * (n + 1) * (ε : ℝ≥0∞)⁻¹ := by rw [div_eq_mul_inv]
  mono n m hnm x hx := by
    simp only [Set.mem_Ico, zero_le, true_and] at hx ⊢
    exact hx.trans_le (mod_cast (by gcongr))
  subset_iUnion x hx := by
    simp only [Set.mem_iUnion, Set.mem_Ico, zero_le, true_and]
    obtain ⟨i, hi⟩ := exists_nat_gt x
    exact ⟨i, hi.trans (by simp)⟩
