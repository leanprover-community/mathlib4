/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.Data.Polynomial.Degree.CardPowDegree

#align_import number_theory.class_number.admissible_card_pow_degree from "leanprover-community/mathlib"@"0b9eaaa7686280fad8cce467f5c3c57ee6ce77f8"

/-!
# Admissible absolute values on polynomials

This file defines an admissible absolute value `Polynomial.cardPowDegreeIsAdmissible` which we
use to show the class number of the ring of integers of a function field is finite.

## Main results

* `Polynomial.cardPowDegreeIsAdmissible` shows `cardPowDegree`,
  mapping `p : Polynomial 𝔽_q` to `q ^ degree p`, is admissible
-/


namespace Polynomial

open Polynomial

open AbsoluteValue Real

variable {Fq : Type*} [Fintype Fq]

/-- If `A` is a family of enough low-degree polynomials over a finite semiring, there is a
pair of equal elements in `A`. -/
theorem exists_eq_polynomial [Semiring Fq] {d : ℕ} {m : ℕ} (hm : Fintype.card Fq ^ d ≤ m)
    (b : Fq[X]) (hb : natDegree b ≤ d) (A : Fin m.succ → Fq[X])
    (hA : ∀ i, degree (A i) < degree b) : ∃ i₀ i₁, i₀ ≠ i₁ ∧ A i₁ = A i₀ := by
  -- Since there are > q^d elements of A, and only q^d choices for the highest `d` coefficients,
  -- there must be two elements of A with the same coefficients at
  -- `0`, ... `degree b - 1` ≤ `d - 1`.
  -- In other words, the following map is not injective:
  set f : Fin m.succ → Fin d → Fq := fun i j => (A i).coeff j
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ A i₁ = A i₀
  have : Fintype.card (Fin d → Fq) < Fintype.card (Fin m.succ) := by
    simpa using lt_of_le_of_lt hm (Nat.lt_succ_self m)
  -- Therefore, the differences have all coefficients higher than `deg b - d` equal.
  obtain ⟨i₀, i₁, i_ne, i_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f this
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ A i₁ = A i₀
  use i₀, i₁, i_ne
  -- ⊢ A i₁ = A i₀
  ext j
  -- ⊢ coeff (A i₁) j = coeff (A i₀) j
  -- The coefficients higher than `deg b` are the same because they are equal to 0.
  by_cases hbj : degree b ≤ j
  -- ⊢ coeff (A i₁) j = coeff (A i₀) j
  · rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hA _) hbj),
      coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hA _) hbj)]
  -- So we only need to look for the coefficients between `0` and `deg b`.
  rw [not_le] at hbj
  -- ⊢ coeff (A i₁) j = coeff (A i₀) j
  apply congr_fun i_eq.symm ⟨j, _⟩
  -- ⊢ j < d
  exact lt_of_lt_of_le (coe_lt_degree.mp hbj) hb
  -- 🎉 no goals
#align polynomial.exists_eq_polynomial Polynomial.exists_eq_polynomial

/-- If `A` is a family of enough low-degree polynomials over a finite ring,
there is a pair of elements in `A` (with different indices but not necessarily
distinct), such that their difference has small degree. -/
theorem exists_approx_polynomial_aux [Ring Fq] {d : ℕ} {m : ℕ} (hm : Fintype.card Fq ^ d ≤ m)
    (b : Fq[X]) (A : Fin m.succ → Fq[X]) (hA : ∀ i, degree (A i) < degree b) :
    ∃ i₀ i₁, i₀ ≠ i₁ ∧ degree (A i₁ - A i₀) < ↑(natDegree b - d) := by
  have hb : b ≠ 0 := by
    rintro rfl
    specialize hA 0
    rw [degree_zero] at hA
    exact not_lt_of_le bot_le hA
  -- Since there are > q^d elements of A, and only q^d choices for the highest `d` coefficients,
  -- there must be two elements of A with the same coefficients at
  -- `degree b - 1`, ... `degree b - d`.
  -- In other words, the following map is not injective:
  set f : Fin m.succ → Fin d → Fq := fun i j => (A i).coeff (natDegree b - j.succ)
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ degree (A i₁ - A i₀) < ↑(natDegree b - d)
  have : Fintype.card (Fin d → Fq) < Fintype.card (Fin m.succ) := by
    simpa using lt_of_le_of_lt hm (Nat.lt_succ_self m)
  -- Therefore, the differences have all coefficients higher than `deg b - d` equal.
  obtain ⟨i₀, i₁, i_ne, i_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f this
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ degree (A i₁ - A i₀) < ↑(natDegree b - d)
  use i₀, i₁, i_ne
  -- ⊢ degree (A i₁ - A i₀) < ↑(natDegree b - d)
  refine' (degree_lt_iff_coeff_zero _ _).mpr fun j hj => _
  -- ⊢ coeff (A i₁ - A i₀) j = 0
  -- The coefficients higher than `deg b` are the same because they are equal to 0.
  by_cases hbj : degree b ≤ j
  -- ⊢ coeff (A i₁ - A i₀) j = 0
  · refine' coeff_eq_zero_of_degree_lt (lt_of_lt_of_le _ hbj)
    -- ⊢ degree (A i₁ - A i₀) < degree b
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt (hA _) (hA _))
    -- 🎉 no goals
  -- So we only need to look for the coefficients between `deg b - d` and `deg b`.
  rw [coeff_sub, sub_eq_zero]
  -- ⊢ coeff (A i₁) j = coeff (A i₀) j
  rw [not_le, degree_eq_natDegree hb] at hbj
  -- ⊢ coeff (A i₁) j = coeff (A i₀) j
  have hbj : j < natDegree b := (@WithBot.coe_lt_coe _ _ _).mp hbj
  -- ⊢ coeff (A i₁) j = coeff (A i₀) j
  have hj : natDegree b - j.succ < d := by
    by_cases hd : natDegree b < d
    · exact lt_of_le_of_lt tsub_le_self hd
    · rw [not_lt] at hd
      have := lt_of_le_of_lt hj (Nat.lt_succ_self j)
      rwa [tsub_lt_iff_tsub_lt hd hbj] at this
  have : j = b.natDegree - (natDegree b - j.succ).succ := by
    rw [← Nat.succ_sub hbj, Nat.succ_sub_succ, tsub_tsub_cancel_of_le hbj.le]
  convert congr_fun i_eq.symm ⟨natDegree b - j.succ, hj⟩
  -- 🎉 no goals
#align polynomial.exists_approx_polynomial_aux Polynomial.exists_approx_polynomial_aux

variable [Field Fq]

/-- If `A` is a family of enough low-degree polynomials over a finite field,
there is a pair of elements in `A` (with different indices but not necessarily
distinct), such that the difference of their remainders is close together. -/
theorem exists_approx_polynomial {b : Fq[X]} (hb : b ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (A : Fin (Fintype.card Fq ^ ⌈-log ε / log (Fintype.card Fq)⌉₊).succ → Fq[X]) :
    ∃ i₀ i₁, i₀ ≠ i₁ ∧ (cardPowDegree (A i₁ % b - A i₀ % b) : ℝ) < cardPowDegree b • ε := by
  have hbε : 0 < cardPowDegree b • ε := by
    rw [Algebra.smul_def, eq_intCast]
    exact mul_pos (Int.cast_pos.mpr (AbsoluteValue.pos _ hb)) hε
  have one_lt_q : 1 < Fintype.card Fq := Fintype.one_lt_card
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ ↑(↑cardPowDegree (A i₁ % b - A i₀ % b)) < ↑cardPowDegree  …
  have one_lt_q' : (1 : ℝ) < Fintype.card Fq := by assumption_mod_cast
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ ↑(↑cardPowDegree (A i₁ % b - A i₀ % b)) < ↑cardPowDegree  …
  have q_pos : 0 < Fintype.card Fq := by linarith
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ ↑(↑cardPowDegree (A i₁ % b - A i₀ % b)) < ↑cardPowDegree  …
  have q_pos' : (0 : ℝ) < Fintype.card Fq := by assumption_mod_cast
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ ↑(↑cardPowDegree (A i₁ % b - A i₀ % b)) < ↑cardPowDegree  …
  -- If `b` is already small enough, then the remainders are equal and we are done.
  by_cases le_b : b.natDegree ≤ ⌈-log ε / log (Fintype.card Fq)⌉₊
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ ↑(↑cardPowDegree (A i₁ % b - A i₀ % b)) < ↑cardPowDegree  …
  · obtain ⟨i₀, i₁, i_ne, mod_eq⟩ :=
      exists_eq_polynomial le_rfl b le_b (fun i => A i % b) fun i => EuclideanDomain.mod_lt (A i) hb
    refine' ⟨i₀, i₁, i_ne, _⟩
    -- ⊢ ↑(↑cardPowDegree (A i₁ % b - A i₀ % b)) < ↑cardPowDegree b • ε
    rwa [mod_eq, sub_self, map_zero, Int.cast_zero]
    -- 🎉 no goals
  -- Otherwise, it suffices to choose two elements whose difference is of small enough degree.
  rw [not_le] at le_b
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ ↑(↑cardPowDegree (A i₁ % b - A i₀ % b)) < ↑cardPowDegree  …
  obtain ⟨i₀, i₁, i_ne, deg_lt⟩ := exists_approx_polynomial_aux le_rfl b (fun i => A i % b) fun i =>
    EuclideanDomain.mod_lt (A i) hb
  use i₀, i₁, i_ne
  -- ⊢ ↑(↑cardPowDegree (A i₁ % b - A i₀ % b)) < ↑cardPowDegree b • ε
  -- Again, if the remainders are equal we are done.
  by_cases h : A i₁ % b = A i₀ % b
  -- ⊢ ↑(↑cardPowDegree (A i₁ % b - A i₀ % b)) < ↑cardPowDegree b • ε
  · rwa [h, sub_self, map_zero, Int.cast_zero]
    -- 🎉 no goals
  have h' : A i₁ % b - A i₀ % b ≠ 0 := mt sub_eq_zero.mp h
  -- ⊢ ↑(↑cardPowDegree (A i₁ % b - A i₀ % b)) < ↑cardPowDegree b • ε
  -- If the remainders are not equal, we'll show their difference is of small degree.
  -- In particular, we'll show the degree is less than the following:
  suffices (natDegree (A i₁ % b - A i₀ % b) : ℝ) < b.natDegree + log ε / log (Fintype.card Fq) by
    rwa [← Real.log_lt_log_iff (Int.cast_pos.mpr (cardPowDegree.pos h')) hbε,
      cardPowDegree_nonzero _ h', cardPowDegree_nonzero _ hb, Algebra.smul_def, eq_intCast,
      Int.cast_pow, Int.cast_ofNat, Int.cast_pow, Int.cast_ofNat,
      log_mul (pow_ne_zero _ q_pos'.ne') hε.ne', ← rpow_nat_cast, ← rpow_nat_cast, log_rpow q_pos',
      log_rpow q_pos', ← lt_div_iff (log_pos one_lt_q'), add_div,
      mul_div_cancel _ (log_pos one_lt_q').ne']
  -- And that result follows from manipulating the result from `exists_approx_polynomial_aux`
  -- to turn the `-⌈-stuff⌉₊` into `+ stuff`.
  refine' lt_of_lt_of_le (Nat.cast_lt.mpr (WithBot.coe_lt_coe.mp _)) _
  swap
  · convert deg_lt
    -- ⊢ ↑(natDegree (A i₁ % b - A i₀ % b)) = degree (A i₁ % b - A i₀ % b)
    rw [degree_eq_natDegree h']; rfl
    -- ⊢ ↑(natDegree (A i₁ % b - A i₀ % b)) = ↑(natDegree (A i₁ % b - A i₀ % b))
                                 -- 🎉 no goals
  rw [← sub_neg_eq_add, neg_div]
  -- ⊢ ↑(natDegree b - ⌈-(log ε / log ↑(Fintype.card Fq))⌉₊) ≤ ↑(natDegree b) - -(l …
  refine' le_trans _ (sub_le_sub_left (Nat.le_ceil _) (b.natDegree : ℝ))
  -- ⊢ ↑(natDegree b - ⌈-(log ε / log ↑(Fintype.card Fq))⌉₊) ≤ ↑(natDegree b) - ↑⌈- …
  rw [← neg_div]
  -- ⊢ ↑(natDegree b - ⌈-log ε / log ↑(Fintype.card Fq)⌉₊) ≤ ↑(natDegree b) - ↑⌈-lo …
  exact le_of_eq (Nat.cast_sub le_b.le)
  -- 🎉 no goals
#align polynomial.exists_approx_polynomial Polynomial.exists_approx_polynomial

/-- If `x` is close to `y` and `y` is close to `z`, then `x` and `z` are at least as close. -/
theorem cardPowDegree_anti_archimedean {x y z : Fq[X]} {a : ℤ} (hxy : cardPowDegree (x - y) < a)
    (hyz : cardPowDegree (y - z) < a) : cardPowDegree (x - z) < a := by
  have ha : 0 < a := lt_of_le_of_lt (AbsoluteValue.nonneg _ _) hxy
  -- ⊢ ↑cardPowDegree (x - z) < a
  by_cases hxy' : x = y
  -- ⊢ ↑cardPowDegree (x - z) < a
  · rwa [hxy']
    -- 🎉 no goals
  by_cases hyz' : y = z
  -- ⊢ ↑cardPowDegree (x - z) < a
  · rwa [← hyz']
    -- 🎉 no goals
  by_cases hxz' : x = z
  -- ⊢ ↑cardPowDegree (x - z) < a
  · rwa [hxz', sub_self, map_zero]
    -- 🎉 no goals
  rw [← Ne.def, ← sub_ne_zero] at hxy' hyz' hxz'
  -- ⊢ ↑cardPowDegree (x - z) < a
  refine' lt_of_le_of_lt _ (max_lt hxy hyz)
  -- ⊢ ↑cardPowDegree (x - z) ≤ max (↑cardPowDegree (x - y)) (↑cardPowDegree (y - z))
  rw [cardPowDegree_nonzero _ hxz', cardPowDegree_nonzero _ hxy',
    cardPowDegree_nonzero _ hyz']
  have : (1 : ℤ) ≤ Fintype.card Fq := by exact_mod_cast (@Fintype.one_lt_card Fq _ _).le
  -- ⊢ ↑(Fintype.card Fq) ^ natDegree (x - z) ≤ max (↑(Fintype.card Fq) ^ natDegree …
  simp only [Int.cast_pow, Int.cast_ofNat, le_max_iff]
  -- ⊢ ↑(Fintype.card Fq) ^ natDegree (x - z) ≤ ↑(Fintype.card Fq) ^ natDegree (x - …
  refine' Or.imp (pow_le_pow this) (pow_le_pow this) _
  -- ⊢ natDegree (x - z) ≤ natDegree (x - y) ∨ natDegree (x - z) ≤ natDegree (y - z)
  rw [natDegree_le_iff_degree_le, natDegree_le_iff_degree_le, ← le_max_iff, ←
    degree_eq_natDegree hxy', ← degree_eq_natDegree hyz']
  convert degree_add_le (x - y) (y - z) using 2
  -- ⊢ x - z = x - y + (y - z)
  exact (sub_add_sub_cancel _ _ _).symm
  -- 🎉 no goals
#align polynomial.card_pow_degree_anti_archimedean Polynomial.cardPowDegree_anti_archimedean

/-- A slightly stronger version of `exists_partition` on which we perform induction on `n`:
for all `ε > 0`, we can partition the remainders of any family of polynomials `A`
into equivalence classes, where the equivalence(!) relation is "closer than `ε`". -/
theorem exists_partition_polynomial_aux (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : Fq[X]} (hb : b ≠ 0)
    (A : Fin n → Fq[X]) : ∃ t : Fin n → Fin (Fintype.card Fq ^ ⌈-log ε / log (Fintype.card Fq)⌉₊),
      ∀ i₀ i₁ : Fin n, t i₀ = t i₁ ↔
        (cardPowDegree (A i₁ % b - A i₀ % b) : ℝ) < cardPowDegree b • ε := by
  have hbε : 0 < cardPowDegree b • ε := by
    rw [Algebra.smul_def, eq_intCast]
    exact mul_pos (Int.cast_pos.mpr (AbsoluteValue.pos _ hb)) hε
  -- We go by induction on the size `A`.
  induction' n with n ih
  -- ⊢ ∃ t, ∀ (i₀ i₁ : Fin Nat.zero), t i₀ = t i₁ ↔ ↑(↑cardPowDegree (A i₁ % b - A  …
  · refine' ⟨finZeroElim, finZeroElim⟩
    -- 🎉 no goals
  -- Show `anti_archimedean` also holds for real distances.
  have anti_archim' : ∀ {i j k} {ε : ℝ},
    (cardPowDegree (A i % b - A j % b) : ℝ) < ε →
      (cardPowDegree (A j % b - A k % b) : ℝ) < ε →
        (cardPowDegree (A i % b - A k % b) : ℝ) < ε := by
    intro i j k ε
    simp_rw [← Int.lt_ceil]
    exact cardPowDegree_anti_archimedean
  obtain ⟨t', ht'⟩ := ih (Fin.tail A)
  -- ⊢ ∃ t, ∀ (i₀ i₁ : Fin (Nat.succ n)), t i₀ = t i₁ ↔ ↑(↑cardPowDegree (A i₁ % b  …
  -- We got rid of `A 0`, so determine the index `j` of the partition we'll re-add it to.
  rsuffices ⟨j, hj⟩ :
    ∃ j, ∀ i, t' i = j ↔ (cardPowDegree (A 0 % b - A i.succ % b) : ℝ) < cardPowDegree b • ε
  · refine' ⟨Fin.cons j t', fun i₀ i₁ => _⟩
    -- ⊢ Fin.cons j t' i₀ = Fin.cons j t' i₁ ↔ ↑(↑cardPowDegree (A i₁ % b - A i₀ % b) …
    refine' Fin.cases _ (fun i₀ => _) i₀ <;> refine' Fin.cases _ (fun i₁ => _) i₁
    -- ⊢ Fin.cons j t' 0 = Fin.cons j t' i₁ ↔ ↑(↑cardPowDegree (A i₁ % b - A 0 % b))  …
                                             -- ⊢ Fin.cons j t' 0 = Fin.cons j t' 0 ↔ ↑(↑cardPowDegree (A 0 % b - A 0 % b)) <  …
                                             -- ⊢ Fin.cons j t' (Fin.succ i₀) = Fin.cons j t' 0 ↔ ↑(↑cardPowDegree (A 0 % b -  …
    · simpa using hbε
      -- 🎉 no goals
    · rw [Fin.cons_succ, Fin.cons_zero, eq_comm, AbsoluteValue.map_sub]
      -- ⊢ t' i₁ = j ↔ ↑(↑cardPowDegree (A 0 % b - A (Fin.succ i₁) % b)) < ↑cardPowDegr …
      exact hj i₁
      -- 🎉 no goals
    · rw [Fin.cons_succ, Fin.cons_zero]
      -- ⊢ t' i₀ = j ↔ ↑(↑cardPowDegree (A 0 % b - A (Fin.succ i₀) % b)) < ↑cardPowDegr …
      exact hj i₀
      -- 🎉 no goals
    · rw [Fin.cons_succ, Fin.cons_succ]
      -- ⊢ t' i₀ = t' i₁ ↔ ↑(↑cardPowDegree (A (Fin.succ i₁) % b - A (Fin.succ i₀) % b) …
      exact ht' i₀ i₁
      -- 🎉 no goals
  -- `exists_approx_polynomial` guarantees that we can insert `A 0` into some partition `j`,
  -- but not that `j` is uniquely defined (which is needed to keep the induction going).
  obtain ⟨j, hj⟩ : ∃ j, ∀ i : Fin n,
      t' i = j → (cardPowDegree (A 0 % b - A i.succ % b) : ℝ) < cardPowDegree b • ε := by
    by_contra hg
    push_neg at hg
    obtain ⟨j₀, j₁, j_ne, approx⟩ := exists_approx_polynomial hb hε
      (Fin.cons (A 0) fun j => A (Fin.succ (Classical.choose (hg j))))
    revert j_ne approx
    refine' Fin.cases _ (fun j₀ => _) j₀ <;>
      refine' Fin.cases (fun j_ne approx => _) (fun j₁ j_ne approx => _) j₁
    · exact absurd rfl j_ne
    · rw [Fin.cons_succ, Fin.cons_zero, ← not_le, AbsoluteValue.map_sub] at approx
      have := (Classical.choose_spec (hg j₁)).2
      contradiction
    · rw [Fin.cons_succ, Fin.cons_zero, ← not_le] at approx
      have := (Classical.choose_spec (hg j₀)).2
      contradiction
    · rw [Fin.cons_succ, Fin.cons_succ] at approx
      rw [Ne.def, Fin.succ_inj] at j_ne
      have : j₀ = j₁ := (Classical.choose_spec (hg j₀)).1.symm.trans
        (((ht' (Classical.choose (hg j₀)) (Classical.choose (hg j₁))).mpr approx).trans
          (Classical.choose_spec (hg j₁)).1)
      contradiction
  -- However, if one of those partitions `j` is inhabited by some `i`, then this `j` works.
  by_cases exists_nonempty_j : ∃ j, (∃ i, t' i = j) ∧
      ∀ i, t' i = j → (cardPowDegree (A 0 % b - A i.succ % b) : ℝ) < cardPowDegree b • ε
  · obtain ⟨j, ⟨i, hi⟩, hj⟩ := exists_nonempty_j
    -- ⊢ ∃ j, ∀ (i : Fin n), t' i = j ↔ ↑(↑cardPowDegree (A 0 % b - A (Fin.succ i) %  …
    refine' ⟨j, fun i' => ⟨hj i', fun hi' => _root_.trans ((ht' _ _).mpr _) hi⟩⟩
    -- ⊢ ↑(↑cardPowDegree (Fin.tail A i % b - Fin.tail A i' % b)) < ↑cardPowDegree b  …
    apply anti_archim' _ hi'
    -- ⊢ ↑(↑cardPowDegree (A (Fin.succ i) % b - A 0 % b)) < ↑cardPowDegree b • ε
    rw [AbsoluteValue.map_sub]
    -- ⊢ ↑(↑cardPowDegree (A 0 % b - A (Fin.succ i) % b)) < ↑cardPowDegree b • ε
    exact hj _ hi
    -- 🎉 no goals
  -- And otherwise, we can just take any `j`, since those are empty.
  refine' ⟨j, fun i => ⟨hj i, fun hi => _⟩⟩
  -- ⊢ t' i = j
  have := exists_nonempty_j ⟨t' i, ⟨i, rfl⟩, fun i' hi' => anti_archim' hi ((ht' _ _).mp hi')⟩
  -- ⊢ t' i = j
  contradiction
  -- 🎉 no goals
#align polynomial.exists_partition_polynomial_aux Polynomial.exists_partition_polynomial_aux

/-- For all `ε > 0`, we can partition the remainders of any family of polynomials `A`
into classes, where all remainders in a class are close together. -/
theorem exists_partition_polynomial (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : Fq[X]} (hb : b ≠ 0)
    (A : Fin n → Fq[X]) : ∃ t : Fin n → Fin (Fintype.card Fq ^ ⌈-log ε / log (Fintype.card Fq)⌉₊),
      ∀ i₀ i₁ : Fin n, t i₀ = t i₁ →
        (cardPowDegree (A i₁ % b - A i₀ % b) : ℝ) < cardPowDegree b • ε := by
  obtain ⟨t, ht⟩ := exists_partition_polynomial_aux n hε hb A
  -- ⊢ ∃ t, ∀ (i₀ i₁ : Fin n), t i₀ = t i₁ → ↑(↑cardPowDegree (A i₁ % b - A i₀ % b) …
  exact ⟨t, fun i₀ i₁ hi => (ht i₀ i₁).mp hi⟩
  -- 🎉 no goals
#align polynomial.exists_partition_polynomial Polynomial.exists_partition_polynomial

/-- `fun p => Fintype.card Fq ^ degree p` is an admissible absolute value.
We set `q ^ degree 0 = 0`. -/
noncomputable def cardPowDegreeIsAdmissible :
    IsAdmissible (cardPowDegree : AbsoluteValue Fq[X] ℤ) :=
  { @cardPowDegree_isEuclidean Fq _
      _ with
    card := fun ε => Fintype.card Fq ^ ⌈-log ε / log (Fintype.card Fq)⌉₊
    exists_partition' := fun n _ hε _ hb => exists_partition_polynomial n hε hb }
#align polynomial.card_pow_degree_is_admissible Polynomial.cardPowDegreeIsAdmissible

end Polynomial
