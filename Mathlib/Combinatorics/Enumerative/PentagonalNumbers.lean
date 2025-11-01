/-
Copyright (c) 2025 Beibei Xiong.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beibei Xiong
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Pentagonal numbers, parity of strict partitions, and a finite product cut-off

This file introduces:
* the (integer-valued) generalized pentagonal numbers `generalizedPentagonalZ`,
* the parity difference of strict partitions of `n`:
  `strict_partitions_parity_diff n = p_even_distinct n - p_odd_distinct n`,
* a finite product `E n` approximating Euler's generating function, and a simple lemma about its
  coefficient extraction being a restatement with the same cut-off.

These pieces are intended to support proofs around Euler's pentagonal number theorem and
related identities.

## Main definitions

* `p_even_distinct n` : number of partitions of `n` into distinct parts with an even
  number of parts.
* `p_odd_distinct n`  : number of partitions of `n` into distinct parts with an odd
  number of parts.
* `generalizedPentagonalZ j` : the (possibly negative-indexed) generalized pentagonal numbers
  `j*(3*j - 1)/2` as integers.
* `generalizedPentagonalNum j` : the same, coerced to `ℕ` by `Int.toNat`.
* `error_term_e n` : the Euler error-term `eₙ`, which is `(-1)^{|j|}` if `n` equals a generalized
  pentagonal number for some `j : ℤ`, and `0` otherwise.
* `strict_partitions_parity_diff n` : `(p_even_distinct n : ℤ) - (p_odd_distinct n : ℤ)`.
* `E n` : a finite product `∏_{k=1}^{n+1} (1 - X^k)` seen as a `PowerSeries ℤ`.

## Implementation details

* We keep an integer-valued definition `generalizedPentagonalZ : ℤ → ℤ` for convenience in
  arithmetic facts and sign arguments. The natural-number version `generalizedPentagonalNum`
  is just `Int.toNat` of the integer-valued one.
* A bounded search for witnesses `j` such that `n = generalizedPentagonalZ j` is provided by
  `exists_j_iff_exists_j_in_range`.

## TODO

* Connect `error_term_e` and `strict_partitions_parity_diff` via Euler's pentagonal theorem.
* Provide API lemmas for coefficients of the infinite product and its finite truncations.

## Tags

partition, pentagonal number, Euler, generating function

## References

* <https://en.wikipedia.org/wiki/Pentagonal_number_theorem>
-/

open Finset Nat Int Partition PowerSeries Polynomial
open scoped BigOperators

/--
`p_even_distinct n`: number of partitions of `n` into distinct parts with an even number of parts.
-/
def p_even_distinct (n : ℕ) : ℕ :=
  ((Nat.Partition.distincts n).filter (fun p => Even p.parts.card)).card

/--
`p_odd_distinct n`: number of partitions of `n` into distinct parts with an odd number of parts.
-/
def p_odd_distinct (n : ℕ) : ℕ :=
  ((Nat.Partition.distincts n).filter (fun p => Odd p.parts.card)).card

/-!
### Generalized pentagonal numbers and the error term `eₙ`
-/

/--
Generalized pentagonal number (integer-valued): `j ↦ j * (3*j - 1) / 2`.
-/
def generalizedPentagonalZ (j : ℤ) : ℤ := j * (3 * j - 1) / 2

lemma gpn_nonneg (j : ℤ) : 0 ≤ generalizedPentagonalZ j := by
  -- Show `0 ≤ j * (3*j - 1)` and then apply `Int.ediv_nonneg`.
  have : 0 ≤ j * (3 * j - 1) := by
    rcases le_or_gt j 0 with hle | hgt
    · exact mul_nonneg_of_nonpos_of_nonpos hle (by linarith)
    · exact mul_nonneg hgt.le (by linarith)
  exact Int.ediv_nonneg this (by decide)

/--
Natural-number version of generalized pentagonal numbers.
-/
def generalizedPentagonalNum (j : ℤ) : ℕ :=
  Int.toNat (generalizedPentagonalZ j)

lemma gpn_coe (j : ℤ) :
    (generalizedPentagonalNum j : ℤ) = generalizedPentagonalZ j := by
  simp [generalizedPentagonalNum, generalizedPentagonalZ]
  refine (ediv_nonneg_iff_of_pos ?_).mpr ?_
  · norm_num
  · by_cases hj : j > 0
    · refine Int.mul_nonneg ?_ ?_
      · linarith
      · linarith
    · have hle : j ≤ 0 := by linarith
      refine Int.mul_nonneg_of_nonpos_of_nonpos hle ?_
      linarith
/--
`2 ∣ (-j + 3*j^2)`.
-/
theorem even_neg_j_add_three_j_sq (j : ℤ) : 2 ∣ (-j + 3 * j ^ 2) := by
  -- Factorization: `-j + 3*j^2 = j*(3*j - 1)`.
  have h : -j + 3 * j ^ 2 = j * (3 * j - 1) := by ring
  rw [h]
  -- Rewrite as `j*(j-1) + 2*j^2`.
  have h' : j * (3 * j - 1) = j * (j - 1) + 2 * j ^ 2 := by ring
  rw [h']
  -- `2 ∣ j*(j-1)` since product of consecutive integers is even.
  have h_consec : 2 ∣ j * (j - 1) := by
    rcases Int.even_or_odd j with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · use k * (2 * k - 1); ring
    · use k * (2 * k + 1); ring
  -- `2 ∣ 2*j^2` trivially.
  have h_twice : 2 ∣ 2 * j ^ 2 := by use j ^ 2
  -- Sum of two even numbers is even.
  exact dvd_add h_consec h_twice

theorem even_neg_j_add_three_j_sq' (j : ℤ) : Even (-j + 3 * j ^ 2) := by
  have := even_neg_j_add_three_j_sq j
  exact (even_iff_exists_two_nsmul (-j + 3 * j ^ 2)).mpr this

/--
Existence of `j` with `n = generalizedPentagonalZ j` can be restricted to a bounded interval
`j ∈ [-(n+1), n+1]`.
-/
theorem exists_j_iff_exists_j_in_range (n : ℕ) :
    (∃ j : ℤ, n = generalizedPentagonalZ j) ↔
    (∃ j ∈ Finset.Icc (-(n+1 : ℤ)) ((n+1 : ℤ)), n = generalizedPentagonalZ j) := by
  constructor
  · rintro ⟨j, hn⟩
    use j
    constructor
    · refine mem_Icc.mpr ?_
      rw [hn, generalizedPentagonalZ]
      have h_bound1 :  -(j * (3 * j - 1) / 2 + 1) ≤ j := by
        have h_nezero : (2 : ℤ) ≠ 0 := by norm_num
        refine Int.add_nonneg_iff_neg_le.mp ?_
        · by_cases hj : j > 0
          · refine Int.add_nonneg ?_ ?_
            linarith
            refine Int.add_nonneg ?_ ?_
            refine (ediv_nonneg_iff_of_pos ?_).mpr ?_
            linarith
            refine Int.mul_nonneg ?_ ?_
            linarith
            linarith
            linarith
          · have hle : j ≤ 0 := by linarith
            by_cases hj1 : j = 0
            · rw [hj1]
              norm_num
            · have hj2 : j < 0 := by omega
              have h_bound1 : j + j * (3 * j - 1) / 2 = j * (3 * j + 1) / 2 := by
                have h_nezero : (2 : ℤ) ≠ 0 := by norm_num
                refine Int.eq_ediv_of_mul_eq_right h_nezero ?_
                ring_nf
                rw [mul_two ,add_assoc]
                congr 1
                rw [mul_comm _ 3]
                have h_aux :  (-j + 3 * j ^ 2) / 2 * 2 = -j + 3 * j ^ 2 := by
                  apply Int.ediv_two_mul_two_of_even (even_neg_j_add_three_j_sq' j)
                rw [h_aux]
                ring

              rw [← add_assoc, h_bound1]
              refine Int.add_nonneg ?_ ?_
              refine (ediv_nonneg_iff_of_pos ?_).mpr ?_
              omega
              have  h:  0 < j * (3 * j + 1) := by
                refine Int.mul_pos_of_neg_of_neg hj2 ?_
                linarith
              linarith
              omega

      have h_bound2 : j ≤ j * (3 * j - 1) / 2 + 1 := by
        have h_nezero : (2 : ℤ) ≠ 0 := by norm_num
        refine Int.sub_nonneg.mp ?_
        have h_aux : j * (3 * j - 1) / 2 + 1 - j = 3 * j * (j - 1) / 2 + 1 := by

          ring_nf
          rw [sub_add]
          rw [sub_eq_add_neg]
          congr 1
          ring_nf
          refine Int.eq_ediv_of_mul_eq_right h_nezero ?_
          ring_nf
          have h_aux :  (-j + 3 * j ^ 2) / 2 * 2 = -j + 3 * j ^ 2 := by
                  apply Int.ediv_two_mul_two_of_even (even_neg_j_add_three_j_sq' j)
          rw [mul_comm _ 3, h_aux]
          ring

        rw [h_aux]
        refine Int.add_nonneg ?_ ?_
        refine (ediv_nonneg_iff_of_pos ?_).mpr ?_
        omega
        by_cases hj : j < 0
        · have hj1 : j - 1 < 0 := by linarith
          have h_mul_neg : j * (j - 1) > 0 := by
            refine Int.mul_pos_of_neg_of_neg hj hj1
          linarith
        · have hle : j ≥ 0 := by linarith
          by_cases hj1 : j = 0
          · rw [hj1]
            norm_num
          · have hj2 : j > 0 := by omega
            have h_mul_pos : 3 * j * (j - 1) ≥ 0 := by
              refine Int.mul_nonneg ?_ ?_
              linarith
              linarith
            linarith
        linarith
      exact ⟨h_bound1, h_bound2⟩

    · exact hn
  · rintro ⟨j, _, hn⟩
    use j, hn

/--
Decidability of `∃ j : ℤ, n = generalizedPentagonalZ j` via a bounded search window.
-/
instance (n : ℕ) : Decidable (∃ j : ℤ, n = generalizedPentagonalZ j) :=
  decidable_of_iff'
      (∃ j ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ), n = generalizedPentagonalZ j)
      (exists_j_iff_exists_j_in_range n)

/--
Euler's error term `eₙ`. It is `(-1)^{|j|}` if `n` is a generalized pentagonal number
`generalizedPentagonalZ j` for some `j : ℤ`, and `0` otherwise.
-/
noncomputable def error_term_e (n : ℕ) : ℤ :=
  if h : ∃ j : ℤ, n = generalizedPentagonalZ j then
    let j := Classical.choose h
    (-1 : ℤ) ^ j.natAbs
  else
    0

/--
Difference between the numbers of strict partitions with even vs. odd number of parts.
-/
def strict_partitions_parity_diff (n : ℕ) : ℤ :=
  (p_even_distinct n : ℤ) - (p_odd_distinct n : ℤ)

/--
Finite product `E(n) = ∏_{k=1}^{n+1} (1 - X^k)` as a `PowerSeries ℤ`.
-/
noncomputable def E (n : ℕ) : PowerSeries ℤ :=
  ∏ k ∈ Finset.range (n + 1), (1 - (PowerSeries.X : PowerSeries ℤ) ^ (k + 1))

lemma coeff_E_eq_coeff_cutoff (n : ℕ) :
    (PowerSeries.coeff n) (E n) =
      (PowerSeries.coeff n)
        (∏ k ∈ Finset.range (n + 1), (1 - (PowerSeries.X : PowerSeries ℤ) ^ (k + 1))) := by rfl
