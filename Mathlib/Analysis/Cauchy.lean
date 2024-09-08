/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weber
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Abs

/-!
# Cauchy's bound on polynomial roots.
-/

variable {K : Type*} [NormedField K]

open Polynomial Finset

/--
Cauchy's bound on the roots of a given polynomial.
-/
noncomputable def cauchyBound (p : K[X]) : ℝ :=
  if h : p.natDegree = 0 then
    0
  else
    sup' (range p.natDegree) (by simpa) (fun x ↦ ‖p.coeff x‖) / ‖p.leadingCoeff‖

lemma cauchyBound_def (p : K[X]) (hp : p.natDegree ≠ 0) :
    cauchyBound p = sup' (range p.natDegree) (by simpa) (fun x ↦ ‖p.coeff x‖) /
      ‖p.leadingCoeff‖ := by
  simp [cauchyBound, hp]

@[simp]
lemma cauchyBound_nonneg (p : K[X]) : 0 ≤ cauchyBound p := by
  unfold cauchyBound
  split
  · rfl
  · apply div_nonneg
    simp only [le_sup'_iff, mem_range, norm_nonneg, and_true]
    use 0, (by omega)
    apply norm_nonneg

theorem norm_lt_cauchyBound_add_one_of_isRoot (p : K[X]) (hp : p ≠ 0) (a : K) (h : p.IsRoot a) :
    ‖a‖ < cauchyBound p + 1 := by
  have : 0 < p.natDegree := coe_lt_degree.mp <| degree_pos_of_root hp h
  rw [IsRoot.def, eval_eq_sum_range, range_add_one] at h
  simp only [mem_range, lt_self_iff_false, not_false_eq_true, sum_insert, coeff_natDegree,
    add_eq_zero_iff_eq_neg] at h
  apply_fun norm at h
  simp only [norm_mul, norm_pow, norm_neg] at h
  suffices ‖a‖ ^ p.natDegree ≤ cauchyBound p * ∑ x ∈ range p.natDegree, ‖a‖ ^ x by
    rcases eq_or_ne ‖a‖ 1 with ha | ha
    · simp only [ha, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, lt_add_iff_pos_left,
        gt_iff_lt] at this ⊢
      apply lt_of_le_of_ne (by simp)
      intro nh
      simp [← nh] at this
      linarith
    rcases lt_or_gt_of_ne ha with ha | ha
    · apply ha.trans_le
      simp
    · rw [geom_sum_eq ‹‖a‖ ≠ 1›] at this
      calc
        ‖a‖ = ‖a‖ - 1 + 1 := by ring
        _ = ‖a‖ ^ p.natDegree * (‖a‖ - 1) / ‖a‖ ^ p.natDegree + 1 := by
          field_simp
        _ ≤ cauchyBound p * ((‖a‖ ^ p.natDegree - 1) / (‖a‖ - 1)) * (‖a‖ - 1)
            / ‖a‖ ^ p.natDegree + 1 := by gcongr; linarith
        _ = cauchyBound p * (‖a‖ ^ p.natDegree - 1)
            / ‖a‖ ^ p.natDegree + 1 := by
          congr 2
          have : ‖a‖ - 1 ≠ 0 := by linarith
          field_simp
        _ < cauchyBound p * ‖a‖ ^ p.natDegree / ‖a‖ ^ p.natDegree + 1 := by
          gcongr
          · apply lt_of_le_of_ne (by simp)
            contrapose! this
            simp only [← this, zero_mul]
            apply pow_pos
            linarith
          simp
        _ = cauchyBound p + 1 := by field_simp
  apply le_of_eq at h
  have pld : ‖p.leadingCoeff‖ ≠ 0 := by simpa
  calc ‖a‖ ^ p.natDegree
    _ = ‖p.leadingCoeff‖ * ‖a‖ ^ p.natDegree / ‖p.leadingCoeff‖ := by
      rw [mul_div_cancel_left₀]
      simpa
    _ ≤ ‖∑ x ∈ range p.natDegree, p.coeff x * a ^ x‖ / ‖p.leadingCoeff‖ := by gcongr
    _ ≤ (∑ x ∈ range p.natDegree, ‖p.coeff x * a ^ x‖) / ‖p.leadingCoeff‖ := by
      gcongr
      apply norm_sum_le
    _ = (∑ x ∈ range p.natDegree, ‖p.coeff x‖ * ‖a‖ ^ x) / ‖p.leadingCoeff‖ := by simp [abs_mul]
    _ ≤ (∑ x ∈ range p.natDegree, ‖p.leadingCoeff‖ * ‖cauchyBound p‖ * ‖a‖ ^ x) /
        ‖p.leadingCoeff‖ := by
      gcongr (∑ x ∈ _, ?_ * _) / _
      rw [cauchyBound_def p this.ne.symm]
      field_simp
      rw [le_abs]
      left
      apply le_sup' (fun x ↦ ‖p.coeff x‖) ‹_›
    _ = ‖cauchyBound p‖ * ∑ x ∈ range p.natDegree, ‖a‖ ^ x := by
      simp only [← mul_sum]
      field_simp
      ring
    _ = cauchyBound p * ∑ x ∈ range p.natDegree, ‖a‖ ^ x := by simp [abs_of_nonneg]
