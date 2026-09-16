/-
Copyright (c) 2026 Joel Cruz Cabrera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joel Cruz Cabrera
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Redheffer

/-!
# The inverse of the zeta matrix is the Möbius matrix

The *Möbius matrix* `Matrix.moebiusMatrix n` is the `n × n` matrix with entry
`μ ((j + 1) / (i + 1))` at `(i, j)` when `i + 1 ∣ j + 1` and `0` otherwise. It is the two-sided
inverse of the zeta (divisibility) matrix `Matrix.zetaMatrix n`: this is Möbius inversion,
`μ * ζ = 1` (`ArithmeticFunction.moebius_mul_coe_zeta`), written for the matrices of the truncated
Dirichlet convolution on `{1, …, n}`.

## Main results

* `Matrix.moebiusMatrix_mul_zetaMatrix`, `Matrix.zetaMatrix_mul_moebiusMatrix`: the two products
  are `1`.
* `Matrix.zetaMatrix_inv`: `(zetaMatrix n)⁻¹ = moebiusMatrix n`.
* `Matrix.det_moebiusMatrix`: the Möbius matrix has determinant `1`.

## Implementation notes

The entry `(i, j)` of `moebiusMatrix n * zetaMatrix n` is
`∑ k, [i + 1 ∣ k + 1] μ ((k + 1) / (i + 1)) [k + 1 ∣ j + 1]`; when `i + 1 ∣ j + 1` the `k` with
`i + 1 ∣ k + 1 ∣ j + 1` are the `(i + 1) d` with `d ∣ (j + 1) / (i + 1)`, and the sum is
`∑ d ∈ ((j + 1) / (i + 1)).divisors, μ d`, which is `ArithmeticFunction.sum_divisors_moebius`.
The other product follows from `Matrix.mul_eq_one_comm`.

## Tags

moebius matrix, zeta matrix, moebius inversion, dirichlet convolution
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.Moebius

namespace Matrix

open ArithmeticFunction

/-- The `n × n` Möbius matrix: the `(i, j)` entry is `μ ((j + 1) / (i + 1))` if `i + 1 ∣ j + 1`
and `0` otherwise. -/
def moebiusMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j ↦ if (i : ℕ) + 1 ∣ (j : ℕ) + 1 then (μ (((j : ℕ) + 1) / ((i : ℕ) + 1)) : ℤ) else 0

@[simp] theorem moebiusMatrix_apply (n : ℕ) (i j : Fin n) :
    moebiusMatrix n i j =
      if (i : ℕ) + 1 ∣ (j : ℕ) + 1 then (μ (((j : ℕ) + 1) / ((i : ℕ) + 1)) : ℤ) else 0 := rfl

theorem moebiusMatrix_isUpperTriangular (n : ℕ) : (moebiusMatrix n).IsUpperTriangular := by
  intro i j hij
  simp only [id] at hij
  have : ¬ ((i : ℕ) + 1 ∣ (j : ℕ) + 1) := fun hd ↦ by
    have := Nat.le_of_dvd (by omega) hd
    omega
  simp [this]

theorem sum_fin_dvd_dvd_eq_sum_divisors {M : Type*} [AddCommMonoid M] (n a b : ℕ) (f : ℕ → M)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ∣ b) (hbn : b ≤ n) :
    (∑ k : Fin n, if a ∣ (k : ℕ) + 1 ∧ (k : ℕ) + 1 ∣ b then f (((k : ℕ) + 1) / a) else 0) =
      ∑ d ∈ (b / a).divisors, f d := by
  obtain ⟨m, rfl⟩ := hab
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hb
    · exact h
  rw [Nat.mul_div_cancel_left m ha,
    Fin.sum_univ_eq_sum_range (fun k ↦ if a ∣ k + 1 ∧ k + 1 ∣ a * m then f ((k + 1) / a) else 0),
    ← sum_filter]
  have hset : (range n).filter (fun k ↦ a ∣ k + 1 ∧ k + 1 ∣ a * m) =
      m.divisors.image (fun d ↦ a * d - 1) := by
    ext k
    simp only [mem_filter, mem_range, mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨hkn, ⟨d, hd⟩, hdvd⟩
      refine ⟨d, ⟨?_, by omega⟩, by omega⟩
      rw [hd] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd
    · rintro ⟨d, ⟨hdm, -⟩, hk⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdm hm
      have hle : d ≤ m := Nat.le_of_dvd hm hdm
      have hak : a * d - 1 + 1 = a * d := by
        have : 1 ≤ a * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
        omega
      refine ⟨?_, ?_, ?_⟩
      · have : a * d ≤ a * m := Nat.mul_le_mul_left a hle
        omega
      · rw [← hk, hak]; exact dvd_mul_right a d
      · rw [← hk, hak]; exact Nat.mul_dvd_mul_left a hdm
  rw [hset, sum_image]
  · refine sum_congr rfl fun d hd ↦ ?_
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hm
    have hak : a * d - 1 + 1 = a * d := by
      have : 1 ≤ a * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    rw [hak, Nat.mul_div_cancel_left d ha]
  · intro x hx y hy hxy
    have hx1 : 1 ≤ x := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hx).1 hm
    have hy1 : 1 ≤ y := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hy).1 hm
    simp only at hxy
    have : a * x = a * y := by
      have h1 : 1 ≤ a * x := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have h2 : 1 ≤ a * y := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) this

theorem moebiusMatrix_mul_zetaMatrix (n : ℕ) : moebiusMatrix n * zetaMatrix n = 1 := by
  ext i j
  simp only [mul_apply, moebiusMatrix_apply, zetaMatrix_apply, one_apply]
  by_cases hij : (i : ℕ) + 1 ∣ (j : ℕ) + 1
  · rw [show (∑ k : Fin n,
          (if (i : ℕ) + 1 ∣ (k : ℕ) + 1 then (μ (((k : ℕ) + 1) / ((i : ℕ) + 1)) : ℤ) else 0) *
            (if (k : ℕ) + 1 ∣ (j : ℕ) + 1 then (1 : ℤ) else 0)) =
        ∑ k : Fin n, if (i : ℕ) + 1 ∣ (k : ℕ) + 1 ∧ (k : ℕ) + 1 ∣ (j : ℕ) + 1
          then (μ (((k : ℕ) + 1) / ((i : ℕ) + 1)) : ℤ) else 0 from
        sum_congr rfl fun k _ ↦ by split_ifs <;> simp_all]
    rw [sum_fin_dvd_dvd_eq_sum_divisors n ((i : ℕ) + 1) ((j : ℕ) + 1) (fun d ↦ (μ d : ℤ)) (by omega)
      (by omega) hij (by omega), sum_divisors_moebius]
    have hq : ((j : ℕ) + 1) / ((i : ℕ) + 1) = 1 ↔ i = j := by
      constructor
      · intro h
        obtain ⟨m, hm⟩ := hij
        rw [hm, Nat.mul_div_cancel_left m (by omega)] at h
        subst h
        exact Fin.ext (by omega)
      · rintro rfl; simp
    by_cases h : i = j
    · subst h; simp
    · have hq1 : ((j : ℕ) + 1) / ((i : ℕ) + 1) ≠ 1 := fun hh ↦ h (hq.mp hh)
      simp [h, hq1]
  · have hne : i ≠ j := fun h ↦ hij (h ▸ dvd_refl _)
    simp only [hne, ↓reduceIte]
    refine sum_eq_zero fun k _ ↦ ?_
    by_cases h1 : (i : ℕ) + 1 ∣ (k : ℕ) + 1
    · by_cases h2 : (k : ℕ) + 1 ∣ (j : ℕ) + 1
      · exact absurd (dvd_trans h1 h2) hij
      · simp [h2]
    · simp [h1]

theorem zetaMatrix_mul_moebiusMatrix (n : ℕ) : zetaMatrix n * moebiusMatrix n = 1 :=
  mul_eq_one_comm.mp (moebiusMatrix_mul_zetaMatrix n)

/-- **Möbius inversion as a matrix identity**: the inverse of the zeta (divisibility) matrix is
the Möbius matrix. -/
theorem zetaMatrix_inv (n : ℕ) : (zetaMatrix n)⁻¹ = moebiusMatrix n :=
  inv_eq_left_inv (moebiusMatrix_mul_zetaMatrix n)

theorem moebiusMatrix_inv (n : ℕ) : (moebiusMatrix n)⁻¹ = zetaMatrix n :=
  inv_eq_left_inv (zetaMatrix_mul_moebiusMatrix n)

@[simp] theorem det_moebiusMatrix (n : ℕ) : (moebiusMatrix n).det = 1 := by
  have h := congrArg det (moebiusMatrix_mul_zetaMatrix n)
  rwa [det_mul, det_zetaMatrix, mul_one, det_one] at h

end Matrix
