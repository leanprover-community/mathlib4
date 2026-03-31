/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Cauchy's bound on polynomial roots.

The bound is given by `Polynomial.cauchyBound`, which for `a_n x^n + a_(n-1) x^(n - 1) + ⋯ + a_0` is
`1 + max_(0 ≤ i < n) a_i / a_n`.

The theorem that this gives a bound to polynomial roots is `Polynomial.IsRoot.norm_lt_cauchyBound`.
-/

@[expose] public section

variable {K : Type*} [NormedDivisionRing K]

namespace Polynomial

open Finset NNReal

/--
Cauchy's bound on the roots of a given polynomial.
See `IsRoot.norm_lt_cauchyBound` for the proof that the roots satisfy this bound.
-/
noncomputable def cauchyBound (p : K[X]) : ℝ≥0 :=
  sup (range p.natDegree) (‖p.coeff ·‖₊) / ‖p.leadingCoeff‖₊ + 1

@[simp]
lemma one_le_cauchyBound (p : K[X]) : 1 ≤ cauchyBound p := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_zero : cauchyBound (0 : K[X]) = 1 := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_C (x : K) : cauchyBound (C x) = 1 := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_one : cauchyBound (1 : K[X]) = 1 := cauchyBound_C 1

@[simp]
lemma cauchyBound_X : cauchyBound (X : K[X]) = 1 := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_X_add_C (x : K) : cauchyBound (X + C x) = ‖x‖₊ + 1 := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_X_sub_C (x : K) : cauchyBound (X - C x) = ‖x‖₊ + 1 := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_smul {x : K} (hx : x ≠ 0) (p : K[X]) : cauchyBound (x • p) = cauchyBound p := by
  simp only [cauchyBound, (IsRegular.of_ne_zero hx).left.isSMulRegular,
    natDegree_smul_of_smul_regular, coeff_smul, smul_eq_mul, nnnorm_mul, ← mul_finset_sup,
    leadingCoeff_smul_of_smul_regular, add_left_inj]
  apply mul_div_mul_left
  simpa

/--
`cauchyBound` is a bound on the norm of polynomial roots.
-/
theorem IsRoot.norm_lt_cauchyBound {p : K[X]} (hp : p ≠ 0) {a : K} (h : p.IsRoot a) :
    ‖a‖₊ < cauchyBound p := by
  rw [IsRoot.def, eval_eq_sum_range, range_add_one] at h
  simp only [mem_range, lt_self_iff_false, not_false_eq_true, sum_insert, coeff_natDegree,
    add_eq_zero_iff_eq_neg] at h
  apply_fun nnnorm at h
  simp only [nnnorm_mul, nnnorm_pow, nnnorm_neg] at h
  suffices ‖a‖₊ ^ p.natDegree ≤ (cauchyBound p - 1) * ∑ x ∈ range p.natDegree, ‖a‖₊ ^ x by
    rcases eq_or_ne ‖a‖₊ 1 with ha | ha
    · simp only [ha, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, gt_iff_lt] at this ⊢
      apply lt_of_le_of_ne (by simp)
      intro nh
      simp [← nh, tsub_self] at this
    rcases lt_or_gt_of_ne ha with ha | ha
    · apply ha.trans_le
      simp
    · rw [geom_sum_of_one_lt ha] at this
      calc
        ‖a‖₊ = ‖a‖₊ - 1 + 1 := (tsub_add_cancel_of_le ha.le).symm
        _ = ‖a‖₊ ^ p.natDegree * (‖a‖₊ - 1) / ‖a‖₊ ^ p.natDegree + 1 := by field
        _ ≤ (cauchyBound p - 1) * ((‖a‖₊ ^ p.natDegree - 1) / (‖a‖₊ - 1)) * (‖a‖₊ - 1)
            / ‖a‖₊ ^ p.natDegree + 1 := by gcongr
        _ = (cauchyBound p - 1) * (‖a‖₊ ^ p.natDegree - 1) / ‖a‖₊ ^ p.natDegree + 1 := by
          congr 2
          have : ‖a‖₊ - 1 ≠ 0 := fun nh ↦ (ha.trans_le (tsub_eq_zero_iff_le.mp nh)).false
          field
        _ < (cauchyBound p - 1) * ‖a‖₊ ^ p.natDegree / ‖a‖₊ ^ p.natDegree + 1 := by
          gcongr
          · apply lt_of_le_of_ne (by simp)
            contrapose! this
            simp only [← this, zero_mul]
            apply pow_pos
            exact zero_lt_one.trans ha
          simp [zero_lt_one.trans ha]
        _ = cauchyBound p := by simp [field, tsub_add_cancel_of_le, -eqComm]
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
    _ = (∑ x ∈ range p.natDegree, ‖p.coeff x‖₊ * ‖a‖₊ ^ x) / ‖p.leadingCoeff‖₊ := by simp
    _ ≤ (∑ x ∈ range p.natDegree, ‖p.leadingCoeff‖₊ * (cauchyBound p - 1) * ‖a‖₊ ^ x) /
        ‖p.leadingCoeff‖₊ := by
      gcongr (∑ x ∈ _, ?_ * _) / _
      rw [cauchyBound, add_tsub_cancel_right]
      field_simp
      apply le_sup (f := (‖p.coeff ·‖₊)) ‹_›
    _ = (cauchyBound p - 1) * ∑ x ∈ range p.natDegree, ‖a‖₊ ^ x := by
      simp only [← mul_sum]
      field

end Polynomial
