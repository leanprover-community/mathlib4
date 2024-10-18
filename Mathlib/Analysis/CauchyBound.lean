/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Cauchy's bound on polynomial roots.
-/

variable {K : Type*} [NormedDivisionRing K]

open Polynomial Finset NNReal

/--
Cauchy's bound on the roots of a given polynomial.
-/
noncomputable def cauchyBound (p : K[X]) : ℝ≥0 :=
  sup (range p.natDegree) (‖p.coeff ·‖₊) / ‖p.leadingCoeff‖₊

lemma NNReal.geom_sum {x : ℝ≥0} (h : 1 < x) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i = (x ^ n - 1) / (x - 1) := by
  apply eq_div_of_mul_eq (tsub_pos_of_lt h).ne'
  apply eq_tsub_of_add_eq
  convert geom_sum_mul_add (x - 1) n <;>
  rw [tsub_add_cancel_of_le h.le]

theorem norm_lt_cauchyBound_add_one_of_isRoot (p : K[X]) (hp : p ≠ 0) (a : K) (h : p.IsRoot a) :
    ‖a‖₊ < cauchyBound p + 1 := by
  rw [IsRoot.def, eval_eq_sum_range, range_add_one] at h
  simp only [mem_range, lt_self_iff_false, not_false_eq_true, sum_insert, coeff_natDegree,
    add_eq_zero_iff_eq_neg] at h
  apply_fun nnnorm at h
  simp only [nnnorm_mul, nnnorm_pow, nnnorm_neg] at h
  suffices ‖a‖₊ ^ p.natDegree ≤ cauchyBound p * ∑ x ∈ range p.natDegree, ‖a‖₊ ^ x by
    rcases eq_or_ne ‖a‖₊ 1 with ha | ha
    · simp only [ha, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, lt_add_iff_pos_left,
        gt_iff_lt] at this ⊢
      apply lt_of_le_of_ne (by simp)
      intro nh
      simp [← nh] at this
    rcases lt_or_gt_of_ne ha with ha | ha
    · apply ha.trans_le
      simp
    · rw [NNReal.geom_sum ha] at this
      calc
        ‖a‖₊ = ‖a‖₊ - 1 + 1 := (tsub_add_cancel_of_le ha.le).symm
        _ = ‖a‖₊ ^ p.natDegree * (‖a‖₊ - 1) / ‖a‖₊ ^ p.natDegree + 1 := by
          field_simp
        _ ≤ cauchyBound p * ((‖a‖₊ ^ p.natDegree - 1) / (‖a‖₊ - 1)) * (‖a‖₊ - 1)
            / ‖a‖₊ ^ p.natDegree + 1 := by gcongr
        _ = cauchyBound p * (‖a‖₊ ^ p.natDegree - 1) / ‖a‖₊ ^ p.natDegree + 1 := by
          congr 2
          have : ‖a‖₊ - 1 ≠ 0 := fun nh ↦ (ha.trans_le (tsub_eq_zero_iff_le.mp nh)).false
          field_simp
        _ < cauchyBound p * ‖a‖₊ ^ p.natDegree / ‖a‖₊ ^ p.natDegree + 1 := by
          gcongr
          · apply lt_of_le_of_ne (by simp)
            contrapose! this
            simp only [← this, zero_mul]
            apply pow_pos
            exact zero_lt_one.trans ha
          simp [zero_lt_one.trans ha]
        _ = cauchyBound p + 1 := by field_simp
  apply le_of_eq at h
  have pld : ‖p.leadingCoeff‖₊ ≠ 0 := by simpa
  calc ‖a‖₊ ^ p.natDegree
    _ = ‖p.leadingCoeff‖₊ * ‖a‖₊ ^ p.natDegree / ‖p.leadingCoeff‖₊ := by
      rw [mul_div_cancel_left₀]
      simpa
    _ ≤ ‖∑ x ∈ range p.natDegree, p.coeff x * a ^ x‖₊ / ‖p.leadingCoeff‖₊ := by gcongr
    _ ≤ (∑ x ∈ range p.natDegree, ‖p.coeff x * a ^ x‖₊) / ‖p.leadingCoeff‖₊ := by
      gcongr
      apply nnnorm_sum_le
    _ = (∑ x ∈ range p.natDegree, ‖p.coeff x‖₊ * ‖a‖₊ ^ x) / ‖p.leadingCoeff‖₊ := by simp [abs_mul]
    _ ≤ (∑ x ∈ range p.natDegree, ‖p.leadingCoeff‖₊ * cauchyBound p * ‖a‖₊ ^ x) /
        ‖p.leadingCoeff‖₊ := by
      gcongr (∑ x ∈ _, ?_ * _) / _
      rw [cauchyBound]
      field_simp
      apply le_sup (f := (‖p.coeff ·‖₊)) ‹_›
    _ = cauchyBound p * ∑ x ∈ range p.natDegree, ‖a‖₊ ^ x := by
      simp only [← mul_sum]
      field_simp
      ring
