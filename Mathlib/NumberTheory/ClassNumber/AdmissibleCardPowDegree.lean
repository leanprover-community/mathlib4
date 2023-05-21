/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module number_theory.class_number.admissible_card_pow_degree
! leanprover-community/mathlib commit 0b9eaaa7686280fad8cce467f5c3c57ee6ce77f8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.NumberTheory.ClassNumber.AdmissibleAbsoluteValue
import Mathbin.Analysis.SpecialFunctions.Pow.Real
import Mathbin.RingTheory.Ideal.LocalRing
import Mathbin.Data.Polynomial.Degree.CardPowDegree

/-!
# Admissible absolute values on polynomials

This file defines an admissible absolute value `polynomial.card_pow_degree_is_admissible` which we
use to show the class number of the ring of integers of a function field is finite.

## Main results

* `polynomial.card_pow_degree_is_admissible` shows `card_pow_degree`,
  mapping `p : polynomial 𝔽_q` to `q ^ degree p`, is admissible
-/


namespace Polynomial

open Polynomial

open AbsoluteValue Real

variable {Fq : Type _} [Fintype Fq]

/-- If `A` is a family of enough low-degree polynomials over a finite semiring, there is a
pair of equal elements in `A`. -/
theorem exists_eq_polynomial [Semiring Fq] {d : ℕ} {m : ℕ} (hm : Fintype.card Fq ^ d ≤ m)
    (b : Fq[X]) (hb : natDegree b ≤ d) (A : Fin m.succ → Fq[X])
    (hA : ∀ i, degree (A i) < degree b) : ∃ i₀ i₁, i₀ ≠ i₁ ∧ A i₁ = A i₀ :=
  by
  -- Since there are > q^d elements of A, and only q^d choices for the highest `d` coefficients,
  -- there must be two elements of A with the same coefficients at
  -- `0`, ... `degree b - 1` ≤ `d - 1`.
  -- In other words, the following map is not injective:
  set f : Fin m.succ → Fin d → Fq := fun i j => (A i).Coeff j
  have : Fintype.card (Fin d → Fq) < Fintype.card (Fin m.succ) := by
    simpa using lt_of_le_of_lt hm (Nat.lt_succ_self m)
  -- Therefore, the differences have all coefficients higher than `deg b - d` equal.
  obtain ⟨i₀, i₁, i_ne, i_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f this
  use i₀, i₁, i_ne
  ext j
  -- The coefficients higher than `deg b` are the same because they are equal to 0.
  by_cases hbj : degree b ≤ j
  ·
    rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hA _) hbj),
      coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hA _) hbj)]
  -- So we only need to look for the coefficients between `0` and `deg b`.
  rw [not_le] at hbj
  apply congr_fun i_eq.symm ⟨j, _⟩
  exact lt_of_lt_of_le (coe_lt_degree.mp hbj) hb
#align polynomial.exists_eq_polynomial Polynomial.exists_eq_polynomial

/-- If `A` is a family of enough low-degree polynomials over a finite ring,
there is a pair of elements in `A` (with different indices but not necessarily
distinct), such that their difference has small degree. -/
theorem exists_approx_polynomial_aux [Ring Fq] {d : ℕ} {m : ℕ} (hm : Fintype.card Fq ^ d ≤ m)
    (b : Fq[X]) (A : Fin m.succ → Fq[X]) (hA : ∀ i, degree (A i) < degree b) :
    ∃ i₀ i₁, i₀ ≠ i₁ ∧ degree (A i₁ - A i₀) < ↑(natDegree b - d) :=
  by
  have hb : b ≠ 0 := by
    rintro rfl
    specialize hA 0
    rw [degree_zero] at hA
    exact not_lt_of_le bot_le hA
  -- Since there are > q^d elements of A, and only q^d choices for the highest `d` coefficients,
  -- there must be two elements of A with the same coefficients at
  -- `degree b - 1`, ... `degree b - d`.
  -- In other words, the following map is not injective:
  set f : Fin m.succ → Fin d → Fq := fun i j => (A i).Coeff (nat_degree b - j.succ)
  have : Fintype.card (Fin d → Fq) < Fintype.card (Fin m.succ) := by
    simpa using lt_of_le_of_lt hm (Nat.lt_succ_self m)
  -- Therefore, the differences have all coefficients higher than `deg b - d` equal.
  obtain ⟨i₀, i₁, i_ne, i_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f this
  use i₀, i₁, i_ne
  refine' (degree_lt_iff_coeff_zero _ _).mpr fun j hj => _
  -- The coefficients higher than `deg b` are the same because they are equal to 0.
  by_cases hbj : degree b ≤ j
  · refine' coeff_eq_zero_of_degree_lt (lt_of_lt_of_le _ hbj)
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt (hA _) (hA _))
  -- So we only need to look for the coefficients between `deg b - d` and `deg b`.
  rw [coeff_sub, sub_eq_zero]
  rw [not_le, degree_eq_nat_degree hb, WithBot.coe_lt_coe] at hbj
  have hj : nat_degree b - j.succ < d :=
    by
    by_cases hd : nat_degree b < d
    · exact lt_of_le_of_lt tsub_le_self hd
    · rw [not_lt] at hd
      have := lt_of_le_of_lt hj (Nat.lt_succ_self j)
      rwa [tsub_lt_iff_tsub_lt hd hbj] at this
  have : j = b.nat_degree - (nat_degree b - j.succ).succ := by
    rw [← Nat.succ_sub hbj, Nat.succ_sub_succ, tsub_tsub_cancel_of_le hbj.le]
  convert congr_fun i_eq.symm ⟨nat_degree b - j.succ, hj⟩
#align polynomial.exists_approx_polynomial_aux Polynomial.exists_approx_polynomial_aux

variable [Field Fq]

/-- If `A` is a family of enough low-degree polynomials over a finite field,
there is a pair of elements in `A` (with different indices but not necessarily
distinct), such that the difference of their remainders is close together. -/
theorem exists_approx_polynomial {b : Fq[X]} (hb : b ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (A : Fin (Fintype.card Fq ^ ⌈-log ε / log (Fintype.card Fq)⌉₊).succ → Fq[X]) :
    ∃ i₀ i₁, i₀ ≠ i₁ ∧ (cardPowDegree (A i₁ % b - A i₀ % b) : ℝ) < cardPowDegree b • ε :=
  by
  have hbε : 0 < card_pow_degree b • ε :=
    by
    rw [Algebra.smul_def, eq_intCast]
    exact mul_pos (int.cast_pos.mpr (AbsoluteValue.pos _ hb)) hε
  have one_lt_q : 1 < Fintype.card Fq := Fintype.one_lt_card
  have one_lt_q' : (1 : ℝ) < Fintype.card Fq := by assumption_mod_cast
  have q_pos : 0 < Fintype.card Fq := by linarith
  have q_pos' : (0 : ℝ) < Fintype.card Fq := by assumption_mod_cast
  -- If `b` is already small enough, then the remainders are equal and we are done.
  by_cases le_b : b.nat_degree ≤ ⌈-log ε / log (Fintype.card Fq)⌉₊
  · obtain ⟨i₀, i₁, i_ne, mod_eq⟩ :=
      exists_eq_polynomial le_rfl b le_b (fun i => A i % b) fun i => EuclideanDomain.mod_lt (A i) hb
    refine' ⟨i₀, i₁, i_ne, _⟩
    simp only at mod_eq
    rwa [mod_eq, sub_self, map_zero, Int.cast_zero]
  -- Otherwise, it suffices to choose two elements whose difference is of small enough degree.
  rw [not_le] at le_b
  obtain ⟨i₀, i₁, i_ne, deg_lt⟩ :=
    exists_approx_polynomial_aux le_rfl b (fun i => A i % b) fun i =>
      EuclideanDomain.mod_lt (A i) hb
  simp only at deg_lt
  use i₀, i₁, i_ne
  -- Again, if the remainders are equal we are done.
  by_cases h : A i₁ % b = A i₀ % b
  · rwa [h, sub_self, map_zero, Int.cast_zero]
  have h' : A i₁ % b - A i₀ % b ≠ 0 := mt sub_eq_zero.mp h
  -- If the remainders are not equal, we'll show their difference is of small degree.
  -- In particular, we'll show the degree is less than the following:
  suffices (nat_degree (A i₁ % b - A i₀ % b) : ℝ) < b.nat_degree + log ε / log (Fintype.card Fq) by
    rwa [← Real.log_lt_log_iff (int.cast_pos.mpr (card_pow_degree.pos h')) hbε,
      card_pow_degree_nonzero _ h', card_pow_degree_nonzero _ hb, Algebra.smul_def, eq_intCast,
      Int.cast_pow, Int.cast_ofNat, Int.cast_pow, Int.cast_ofNat,
      log_mul (pow_ne_zero _ q_pos'.ne') hε.ne', ← rpow_nat_cast, ← rpow_nat_cast, log_rpow q_pos',
      log_rpow q_pos', ← lt_div_iff (log_pos one_lt_q'), add_div,
      mul_div_cancel _ (log_pos one_lt_q').ne']
  -- And that result follows from manipulating the result from `exists_approx_polynomial_aux`
  -- to turn the `-⌈-stuff⌉₊` into `+ stuff`.
  refine' lt_of_lt_of_le (nat.cast_lt.mpr (with_bot.coe_lt_coe.mp _)) _
  swap
  · convert deg_lt
    rw [degree_eq_nat_degree h']
  rw [← sub_neg_eq_add, neg_div]
  refine' le_trans _ (sub_le_sub_left (Nat.le_ceil _) (b.nat_degree : ℝ))
  rw [← neg_div]
  exact le_of_eq (Nat.cast_sub le_b.le)
#align polynomial.exists_approx_polynomial Polynomial.exists_approx_polynomial

/-- If `x` is close to `y` and `y` is close to `z`, then `x` and `z` are at least as close. -/
theorem cardPowDegree_anti_archimedean {x y z : Fq[X]} {a : ℤ} (hxy : cardPowDegree (x - y) < a)
    (hyz : cardPowDegree (y - z) < a) : cardPowDegree (x - z) < a :=
  by
  have ha : 0 < a := lt_of_le_of_lt (AbsoluteValue.nonneg _ _) hxy
  by_cases hxy' : x = y
  · rwa [hxy']
  by_cases hyz' : y = z
  · rwa [← hyz']
  by_cases hxz' : x = z
  · rwa [hxz', sub_self, map_zero]
  rw [← Ne.def, ← sub_ne_zero] at hxy' hyz' hxz'
  refine' lt_of_le_of_lt _ (max_lt hxy hyz)
  rw [card_pow_degree_nonzero _ hxz', card_pow_degree_nonzero _ hxy',
    card_pow_degree_nonzero _ hyz']
  have : (1 : ℤ) ≤ Fintype.card Fq := by exact_mod_cast (@Fintype.one_lt_card Fq _ _).le
  simp only [Int.cast_pow, Int.cast_ofNat, le_max_iff]
  refine' Or.imp (pow_le_pow this) (pow_le_pow this) _
  rw [nat_degree_le_iff_degree_le, nat_degree_le_iff_degree_le, ← le_max_iff, ←
    degree_eq_nat_degree hxy', ← degree_eq_nat_degree hyz']
  convert degree_add_le (x - y) (y - z) using 2
  exact (sub_add_sub_cancel _ _ _).symm
#align polynomial.card_pow_degree_anti_archimedean Polynomial.cardPowDegree_anti_archimedean

/-- A slightly stronger version of `exists_partition` on which we perform induction on `n`:
for all `ε > 0`, we can partition the remainders of any family of polynomials `A`
into equivalence classes, where the equivalence(!) relation is "closer than `ε`". -/
theorem exists_partition_polynomial_aux (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : Fq[X]} (hb : b ≠ 0)
    (A : Fin n → Fq[X]) :
    ∃ t : Fin n → Fin (Fintype.card Fq ^ ⌈-log ε / log (Fintype.card Fq)⌉₊),
      ∀ i₀ i₁ : Fin n,
        t i₀ = t i₁ ↔ (cardPowDegree (A i₁ % b - A i₀ % b) : ℝ) < cardPowDegree b • ε :=
  by
  have hbε : 0 < card_pow_degree b • ε :=
    by
    rw [Algebra.smul_def, eq_intCast]
    exact mul_pos (int.cast_pos.mpr (AbsoluteValue.pos _ hb)) hε
  -- We go by induction on the size `A`.
  induction' n with n ih
  · refine' ⟨finZeroElim, finZeroElim⟩
  -- Show `anti_archimedean` also holds for real distances.
  have anti_archim' :
    ∀ {i j k} {ε : ℝ},
      (card_pow_degree (A i % b - A j % b) : ℝ) < ε →
        (card_pow_degree (A j % b - A k % b) : ℝ) < ε →
          (card_pow_degree (A i % b - A k % b) : ℝ) < ε :=
    by
    intro i j k ε
    simp_rw [← Int.lt_ceil]
    exact card_pow_degree_anti_archimedean
  obtain ⟨t', ht'⟩ := ih (Fin.tail A)
  -- We got rid of `A 0`, so determine the index `j` of the partition we'll re-add it to.
  rsuffices ⟨j, hj⟩ :
    ∃ j, ∀ i, t' i = j ↔ (card_pow_degree (A 0 % b - A i.succ % b) : ℝ) < card_pow_degree b • ε
  · refine' ⟨Fin.cons j t', fun i₀ i₁ => _⟩
    refine' Fin.cases _ (fun i₀ => _) i₀ <;> refine' Fin.cases _ (fun i₁ => _) i₁
    · simpa using hbε
    · rw [Fin.cons_succ, Fin.cons_zero, eq_comm, AbsoluteValue.map_sub]
      exact hj i₁
    · rw [Fin.cons_succ, Fin.cons_zero]
      exact hj i₀
    · rw [Fin.cons_succ, Fin.cons_succ]
      exact ht' i₀ i₁
  -- `exists_approx_polynomial` guarantees that we can insert `A 0` into some partition `j`,
  -- but not that `j` is uniquely defined (which is needed to keep the induction going).
  obtain ⟨j, hj⟩ :
    ∃ j,
      ∀ i : Fin n,
        t' i = j → (card_pow_degree (A 0 % b - A i.succ % b) : ℝ) < card_pow_degree b • ε :=
    by
    by_contra this
    push_neg  at this
    obtain ⟨j₀, j₁, j_ne, approx⟩ :=
      exists_approx_polynomial hb hε
        (Fin.cons (A 0) fun j => A (Fin.succ (Classical.choose (this j))))
    revert j_ne approx
    refine' Fin.cases _ (fun j₀ => _) j₀ <;>
      refine' Fin.cases (fun j_ne approx => _) (fun j₁ j_ne approx => _) j₁
    · exact absurd rfl j_ne
    · rw [Fin.cons_succ, Fin.cons_zero, ← not_le, AbsoluteValue.map_sub] at approx
      have := (Classical.choose_spec (this j₁)).2
      contradiction
    · rw [Fin.cons_succ, Fin.cons_zero, ← not_le] at approx
      have := (Classical.choose_spec (this j₀)).2
      contradiction
    · rw [Fin.cons_succ, Fin.cons_succ] at approx
      rw [Ne.def, Fin.succ_inj] at j_ne
      have : j₀ = j₁ :=
        (Classical.choose_spec (this j₀)).1.symm.trans
          (((ht' (Classical.choose (this j₀)) (Classical.choose (this j₁))).mpr approx).trans
            (Classical.choose_spec (this j₁)).1)
      contradiction
  -- However, if one of those partitions `j` is inhabited by some `i`, then this `j` works.
  by_cases exists_nonempty_j :
    ∃ j,
      (∃ i, t' i = j) ∧
        ∀ i, t' i = j → (card_pow_degree (A 0 % b - A i.succ % b) : ℝ) < card_pow_degree b • ε
  · obtain ⟨j, ⟨i, hi⟩, hj⟩ := exists_nonempty_j
    refine' ⟨j, fun i' => ⟨hj i', fun hi' => trans ((ht' _ _).mpr _) hi⟩⟩
    apply anti_archim' _ hi'
    rw [AbsoluteValue.map_sub]
    exact hj _ hi
  -- And otherwise, we can just take any `j`, since those are empty.
  refine' ⟨j, fun i => ⟨hj i, fun hi => _⟩⟩
  have := exists_nonempty_j ⟨t' i, ⟨i, rfl⟩, fun i' hi' => anti_archim' hi ((ht' _ _).mp hi')⟩
  contradiction
#align polynomial.exists_partition_polynomial_aux Polynomial.exists_partition_polynomial_aux

/-- For all `ε > 0`, we can partition the remainders of any family of polynomials `A`
into classes, where all remainders in a class are close together. -/
theorem exists_partition_polynomial (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : Fq[X]} (hb : b ≠ 0)
    (A : Fin n → Fq[X]) :
    ∃ t : Fin n → Fin (Fintype.card Fq ^ ⌈-log ε / log (Fintype.card Fq)⌉₊),
      ∀ i₀ i₁ : Fin n,
        t i₀ = t i₁ → (cardPowDegree (A i₁ % b - A i₀ % b) : ℝ) < cardPowDegree b • ε :=
  by
  obtain ⟨t, ht⟩ := exists_partition_polynomial_aux n hε hb A
  exact ⟨t, fun i₀ i₁ hi => (ht i₀ i₁).mp hi⟩
#align polynomial.exists_partition_polynomial Polynomial.exists_partition_polynomial

/-- `λ p, fintype.card Fq ^ degree p` is an admissible absolute value.
We set `q ^ degree 0 = 0`. -/
noncomputable def cardPowDegreeIsAdmissible :
    IsAdmissible (cardPowDegree : AbsoluteValue Fq[X] ℤ) :=
  {
    @cardPowDegree_isEuclidean Fq _
      _ with
    card := fun ε => Fintype.card Fq ^ ⌈-log ε / log (Fintype.card Fq)⌉₊
    exists_partition' := fun n ε hε b hb => exists_partition_polynomial n hε hb }
#align polynomial.card_pow_degree_is_admissible Polynomial.cardPowDegreeIsAdmissible

end Polynomial

