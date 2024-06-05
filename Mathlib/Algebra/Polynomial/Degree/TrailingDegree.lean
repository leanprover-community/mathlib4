/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.ENat.Basic

#align_import data.polynomial.degree.trailing_degree from "leanprover-community/mathlib"@"302eab4f46abb63de520828de78c04cb0f9b5836"

/-!
# Trailing degree of univariate polynomials

## Main definitions

* `trailingDegree p`: the multiplicity of `X` in the polynomial `p`
* `natTrailingDegree`: a variant of `trailingDegree` that takes values in the natural numbers
* `trailingCoeff`: the coefficient at index `natTrailingDegree p`

Converts most results about `degree`, `natDegree` and `leadingCoeff` to results about the bottom
end of a polynomial
-/


noncomputable section

open Function Polynomial Finsupp Finset

open scoped Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

/-- `trailingDegree p` is the multiplicity of `x` in the polynomial `p`, i.e. the smallest
`X`-exponent in `p`.
`trailingDegree p = some n` when `p ≠ 0` and `n` is the smallest power of `X` that appears
in `p`, otherwise
`trailingDegree 0 = ⊤`. -/
def trailingDegree (p : R[X]) : ℕ∞ :=
  p.support.min
#align polynomial.trailing_degree Polynomial.trailingDegree

theorem trailingDegree_lt_wf : WellFounded fun p q : R[X] => trailingDegree p < trailingDegree q :=
  InvImage.wf trailingDegree wellFounded_lt
#align polynomial.trailing_degree_lt_wf Polynomial.trailingDegree_lt_wf

/-- `natTrailingDegree p` forces `trailingDegree p` to `ℕ`, by defining
`natTrailingDegree ⊤ = 0`. -/
def natTrailingDegree (p : R[X]) : ℕ :=
  (trailingDegree p).getD 0
#align polynomial.nat_trailing_degree Polynomial.natTrailingDegree

/-- `trailingCoeff p` gives the coefficient of the smallest power of `X` in `p`-/
def trailingCoeff (p : R[X]) : R :=
  coeff p (natTrailingDegree p)
#align polynomial.trailing_coeff Polynomial.trailingCoeff

/-- a polynomial is `monic_at` if its trailing coefficient is 1 -/
def TrailingMonic (p : R[X]) :=
  trailingCoeff p = (1 : R)
#align polynomial.trailing_monic Polynomial.TrailingMonic

theorem TrailingMonic.def : TrailingMonic p ↔ trailingCoeff p = 1 :=
  Iff.rfl
#align polynomial.trailing_monic.def Polynomial.TrailingMonic.def

instance TrailingMonic.decidable [DecidableEq R] : Decidable (TrailingMonic p) :=
  inferInstanceAs <| Decidable (trailingCoeff p = (1 : R))
#align polynomial.trailing_monic.decidable Polynomial.TrailingMonic.decidable

@[simp]
theorem TrailingMonic.trailingCoeff {p : R[X]} (hp : p.TrailingMonic) : trailingCoeff p = 1 :=
  hp
#align polynomial.trailing_monic.trailing_coeff Polynomial.TrailingMonic.trailingCoeff

@[simp]
theorem trailingDegree_zero : trailingDegree (0 : R[X]) = ⊤ :=
  rfl
#align polynomial.trailing_degree_zero Polynomial.trailingDegree_zero

@[simp]
theorem trailingCoeff_zero : trailingCoeff (0 : R[X]) = 0 :=
  rfl
#align polynomial.trailing_coeff_zero Polynomial.trailingCoeff_zero

@[simp]
theorem natTrailingDegree_zero : natTrailingDegree (0 : R[X]) = 0 :=
  rfl
#align polynomial.nat_trailing_degree_zero Polynomial.natTrailingDegree_zero

theorem trailingDegree_eq_top : trailingDegree p = ⊤ ↔ p = 0 :=
  ⟨fun h => support_eq_empty.1 (Finset.min_eq_top.1 h), fun h => by simp [h]⟩
#align polynomial.trailing_degree_eq_top Polynomial.trailingDegree_eq_top

theorem trailingDegree_eq_natTrailingDegree (hp : p ≠ 0) :
    trailingDegree p = (natTrailingDegree p : ℕ∞) := by
  let ⟨n, hn⟩ :=
    not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt trailingDegree_eq_top.1 hp))
  have hn : trailingDegree p = n := Classical.not_not.1 hn
  rw [natTrailingDegree, hn]
  rfl
#align polynomial.trailing_degree_eq_nat_trailing_degree Polynomial.trailingDegree_eq_natTrailingDegree

theorem trailingDegree_eq_iff_natTrailingDegree_eq {p : R[X]} {n : ℕ} (hp : p ≠ 0) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n := by
  rw [trailingDegree_eq_natTrailingDegree hp]
  exact WithTop.coe_eq_coe
#align polynomial.trailing_degree_eq_iff_nat_trailing_degree_eq Polynomial.trailingDegree_eq_iff_natTrailingDegree_eq

theorem trailingDegree_eq_iff_natTrailingDegree_eq_of_pos {p : R[X]} {n : ℕ} (hn : 0 < n) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n := by
  constructor
  · intro H
    rwa [← trailingDegree_eq_iff_natTrailingDegree_eq]
    rintro rfl
    rw [trailingDegree_zero] at H
    exact Option.noConfusion H
  · intro H
    rwa [trailingDegree_eq_iff_natTrailingDegree_eq]
    rintro rfl
    rw [natTrailingDegree_zero] at H
    rw [H] at hn
    exact lt_irrefl _ hn
#align polynomial.trailing_degree_eq_iff_nat_trailing_degree_eq_of_pos Polynomial.trailingDegree_eq_iff_natTrailingDegree_eq_of_pos

theorem natTrailingDegree_eq_of_trailingDegree_eq_some {p : R[X]} {n : ℕ}
    (h : trailingDegree p = n) : natTrailingDegree p = n :=
  have hp0 : p ≠ 0 := fun hp0 => by rw [hp0] at h; exact Option.noConfusion h
  Option.some_inj.1 <|
    show (natTrailingDegree p : ℕ∞) = n by rwa [← trailingDegree_eq_natTrailingDegree hp0]
#align polynomial.nat_trailing_degree_eq_of_trailing_degree_eq_some Polynomial.natTrailingDegree_eq_of_trailingDegree_eq_some

@[simp]
theorem natTrailingDegree_le_trailingDegree : ↑(natTrailingDegree p) ≤ trailingDegree p := by
  by_cases hp : p = 0;
  · rw [hp, trailingDegree_zero]
    exact le_top
  rw [trailingDegree_eq_natTrailingDegree hp]
#align polynomial.nat_trailing_degree_le_trailing_degree Polynomial.natTrailingDegree_le_trailingDegree

theorem natTrailingDegree_eq_of_trailingDegree_eq [Semiring S] {q : S[X]}
    (h : trailingDegree p = trailingDegree q) : natTrailingDegree p = natTrailingDegree q := by
  unfold natTrailingDegree
  rw [h]
#align polynomial.nat_trailing_degree_eq_of_trailing_degree_eq Polynomial.natTrailingDegree_eq_of_trailingDegree_eq

theorem trailingDegree_le_of_ne_zero (h : coeff p n ≠ 0) : trailingDegree p ≤ n :=
  show @LE.le ℕ∞ _ p.support.min n from min_le (mem_support_iff.2 h)
#align polynomial.le_trailing_degree_of_ne_zero Polynomial.trailingDegree_le_of_ne_zero

theorem natTrailingDegree_le_of_ne_zero (h : coeff p n ≠ 0) : natTrailingDegree p ≤ n := by
  have : WithTop.some (natTrailingDegree p) = Nat.cast (natTrailingDegree p) := rfl
  rw [← WithTop.coe_le_coe, this, ← trailingDegree_eq_natTrailingDegree]
  · exact trailingDegree_le_of_ne_zero h
  · intro h
    subst h
    exact h rfl
#align polynomial.nat_trailing_degree_le_of_ne_zero Polynomial.natTrailingDegree_le_of_ne_zero

@[simp] lemma coeff_natTrailingDegree_eq_zero : coeff p p.natTrailingDegree = 0 ↔ p = 0 := by
  constructor
  · rintro h
    by_contra hp
    obtain ⟨n, hpn, hn⟩ := by simpa using min_mem_image_coe $ support_nonempty.2 hp
    obtain rfl := (trailingDegree_eq_iff_natTrailingDegree_eq hp).1 hn.symm
    exact hpn h
  · rintro rfl
    simp

lemma coeff_natTrailingDegree_ne_zero : coeff p p.natTrailingDegree ≠ 0 ↔ p ≠ 0 :=
  coeff_natTrailingDegree_eq_zero.not

@[simp] lemma natTrailingDegree_eq_zero : natTrailingDegree p = 0 ↔ p = 0 ∨ coeff p 0 ≠ 0 := by
  constructor
  · rw [or_iff_not_imp_left]
    rintro h hp
    rwa [← h, coeff_natTrailingDegree_ne_zero]
  · rintro (rfl | h)
    · simp
    · exact nonpos_iff_eq_zero.1 $ natTrailingDegree_le_of_ne_zero h

lemma trailingDegree_eq_zero : trailingDegree p = 0 ↔ coeff p 0 ≠ 0 := by
  obtain rfl | hp := eq_or_ne p 0
  · simp [WithTop.top_ne_zero (α := ℕ)]
  · exact (trailingDegree_eq_iff_natTrailingDegree_eq hp).trans $
      natTrailingDegree_eq_zero.trans $ or_iff_right hp

lemma natTrailingDegree_ne_zero : natTrailingDegree p ≠ 0 ↔ p ≠ 0 ∧ coeff p 0 = 0 :=
  natTrailingDegree_eq_zero.not.trans $ by rw [not_or, not_ne_iff]

lemma trailingDegree_ne_zero : trailingDegree p ≠ 0 ↔ coeff p 0 = 0 :=
  trailingDegree_eq_zero.not_left

@[simp] theorem trailingDegree_le_trailingDegree (h : coeff q (natTrailingDegree p) ≠ 0) :
    trailingDegree q ≤ trailingDegree p := by
  by_cases hp : p = 0
  · rw [hp]
    exact le_top
  · rw [trailingDegree_eq_natTrailingDegree hp]
    exact trailingDegree_le_of_ne_zero h
#align polynomial.trailing_degree_le_trailing_degree Polynomial.trailingDegree_le_trailingDegree

theorem trailingDegree_ne_of_natTrailingDegree_ne {n : ℕ} :
    p.natTrailingDegree ≠ n → trailingDegree p ≠ n := by
  -- Porting note: Needed to account for different coercion behaviour & add the lemma below
  have : Nat.cast n = WithTop.some n := rfl
  exact mt fun h => by rw [natTrailingDegree, h, this, ← WithTop.some_eq_coe, Option.getD_some]
#align polynomial.trailing_degree_ne_of_nat_trailing_degree_ne Polynomial.trailingDegree_ne_of_natTrailingDegree_ne

theorem natTrailingDegree_le_of_trailingDegree_le {n : ℕ} {hp : p ≠ 0}
    (H : (n : ℕ∞) ≤ trailingDegree p) : n ≤ natTrailingDegree p := by
  rw [trailingDegree_eq_natTrailingDegree hp] at H
  exact WithTop.coe_le_coe.mp H
#align polynomial.nat_trailing_degree_le_of_trailing_degree_le Polynomial.natTrailingDegree_le_of_trailingDegree_le

theorem natTrailingDegree_le_natTrailingDegree {hq : q ≠ 0}
    (hpq : p.trailingDegree ≤ q.trailingDegree) : p.natTrailingDegree ≤ q.natTrailingDegree := by
  by_cases hp : p = 0;
  · rw [hp, natTrailingDegree_zero]
    exact zero_le _
  rw [trailingDegree_eq_natTrailingDegree hp, trailingDegree_eq_natTrailingDegree hq] at hpq
  exact WithTop.coe_le_coe.1 hpq
#align polynomial.nat_trailing_degree_le_nat_trailing_degree Polynomial.natTrailingDegree_le_natTrailingDegree

@[simp]
theorem trailingDegree_monomial (ha : a ≠ 0) : trailingDegree (monomial n a) = n := by
  rw [trailingDegree, support_monomial n ha, min_singleton]
  rfl
#align polynomial.trailing_degree_monomial Polynomial.trailingDegree_monomial

theorem natTrailingDegree_monomial (ha : a ≠ 0) : natTrailingDegree (monomial n a) = n := by
  rw [natTrailingDegree, trailingDegree_monomial ha]
  rfl
#align polynomial.nat_trailing_degree_monomial Polynomial.natTrailingDegree_monomial

theorem natTrailingDegree_monomial_le : natTrailingDegree (monomial n a) ≤ n :=
  letI := Classical.decEq R
  if ha : a = 0 then by simp [ha] else (natTrailingDegree_monomial ha).le
#align polynomial.nat_trailing_degree_monomial_le Polynomial.natTrailingDegree_monomial_le

theorem le_trailingDegree_monomial : ↑n ≤ trailingDegree (monomial n a) :=
  letI := Classical.decEq R
  if ha : a = 0 then by simp [ha] else (trailingDegree_monomial ha).ge
#align polynomial.le_trailing_degree_monomial Polynomial.le_trailingDegree_monomial

@[simp]
theorem trailingDegree_C (ha : a ≠ 0) : trailingDegree (C a) = (0 : ℕ∞) :=
  trailingDegree_monomial ha
set_option linter.uppercaseLean3 false in
#align polynomial.trailing_degree_C Polynomial.trailingDegree_C

theorem le_trailingDegree_C : (0 : ℕ∞) ≤ trailingDegree (C a) :=
  le_trailingDegree_monomial
set_option linter.uppercaseLean3 false in
#align polynomial.le_trailing_degree_C Polynomial.le_trailingDegree_C

theorem trailingDegree_one_le : (0 : ℕ∞) ≤ trailingDegree (1 : R[X]) := by
  rw [← C_1]
  exact le_trailingDegree_C
#align polynomial.trailing_degree_one_le Polynomial.trailingDegree_one_le

@[simp]
theorem natTrailingDegree_C (a : R) : natTrailingDegree (C a) = 0 :=
  nonpos_iff_eq_zero.1 natTrailingDegree_monomial_le
set_option linter.uppercaseLean3 false in
#align polynomial.nat_trailing_degree_C Polynomial.natTrailingDegree_C

@[simp]
theorem natTrailingDegree_one : natTrailingDegree (1 : R[X]) = 0 :=
  natTrailingDegree_C 1
#align polynomial.nat_trailing_degree_one Polynomial.natTrailingDegree_one

@[simp]
theorem natTrailingDegree_natCast (n : ℕ) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_natCast, natTrailingDegree_C]
#align polynomial.nat_trailing_degree_nat_cast Polynomial.natTrailingDegree_natCast

@[deprecated (since := "2024-04-17")]
alias natTrailingDegree_nat_cast := natTrailingDegree_natCast

@[simp]
theorem trailingDegree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : trailingDegree (C a * X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial, trailingDegree_monomial ha]
set_option linter.uppercaseLean3 false in
#align polynomial.trailing_degree_C_mul_X_pow Polynomial.trailingDegree_C_mul_X_pow

theorem le_trailingDegree_C_mul_X_pow (n : ℕ) (a : R) :
    (n : ℕ∞) ≤ trailingDegree (C a * X ^ n) := by
  rw [C_mul_X_pow_eq_monomial]
  exact le_trailingDegree_monomial
set_option linter.uppercaseLean3 false in
#align polynomial.le_trailing_degree_C_mul_X_pow Polynomial.le_trailingDegree_C_mul_X_pow

theorem coeff_eq_zero_of_lt_trailingDegree (h : (n : ℕ∞) < trailingDegree p) : coeff p n = 0 :=
  Classical.not_not.1 (mt trailingDegree_le_of_ne_zero (not_le_of_gt h))
#align polynomial.coeff_eq_zero_of_trailing_degree_lt Polynomial.coeff_eq_zero_of_lt_trailingDegree

theorem coeff_eq_zero_of_lt_natTrailingDegree {p : R[X]} {n : ℕ} (h : n < p.natTrailingDegree) :
    p.coeff n = 0 := by
  apply coeff_eq_zero_of_lt_trailingDegree
  by_cases hp : p = 0
  · rw [hp, trailingDegree_zero]
    exact WithTop.coe_lt_top n
  · rw [trailingDegree_eq_natTrailingDegree hp]
    exact WithTop.coe_lt_coe.2 h
#align polynomial.coeff_eq_zero_of_lt_nat_trailing_degree Polynomial.coeff_eq_zero_of_lt_natTrailingDegree

@[simp]
theorem coeff_natTrailingDegree_pred_eq_zero {p : R[X]} {hp : (0 : ℕ∞) < natTrailingDegree p} :
    p.coeff (p.natTrailingDegree - 1) = 0 :=
  coeff_eq_zero_of_lt_natTrailingDegree <|
    Nat.sub_lt ((WithTop.zero_lt_coe (natTrailingDegree p)).mp hp) Nat.one_pos
#align polynomial.coeff_nat_trailing_degree_pred_eq_zero Polynomial.coeff_natTrailingDegree_pred_eq_zero

theorem le_trailingDegree_X_pow (n : ℕ) : (n : ℕ∞) ≤ trailingDegree (X ^ n : R[X]) := by
  simpa only [C_1, one_mul] using le_trailingDegree_C_mul_X_pow n (1 : R)
set_option linter.uppercaseLean3 false in
#align polynomial.le_trailing_degree_X_pow Polynomial.le_trailingDegree_X_pow

theorem le_trailingDegree_X : (1 : ℕ∞) ≤ trailingDegree (X : R[X]) :=
  le_trailingDegree_monomial
set_option linter.uppercaseLean3 false in
#align polynomial.le_trailing_degree_X Polynomial.le_trailingDegree_X

theorem natTrailingDegree_X_le : (X : R[X]).natTrailingDegree ≤ 1 :=
  natTrailingDegree_monomial_le
set_option linter.uppercaseLean3 false in
#align polynomial.nat_trailing_degree_X_le Polynomial.natTrailingDegree_X_le

@[simp]
theorem trailingCoeff_eq_zero : trailingCoeff p = 0 ↔ p = 0 :=
  ⟨fun h =>
    _root_.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h)
        (mem_of_min (trailingDegree_eq_natTrailingDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩
#align polynomial.trailing_coeff_eq_zero Polynomial.trailingCoeff_eq_zero

theorem trailingCoeff_nonzero_iff_nonzero : trailingCoeff p ≠ 0 ↔ p ≠ 0 :=
  not_congr trailingCoeff_eq_zero
#align polynomial.trailing_coeff_nonzero_iff_nonzero Polynomial.trailingCoeff_nonzero_iff_nonzero

theorem natTrailingDegree_mem_support_of_nonzero : p ≠ 0 → natTrailingDegree p ∈ p.support :=
  mem_support_iff.mpr ∘ trailingCoeff_nonzero_iff_nonzero.mpr
#align polynomial.nat_trailing_degree_mem_support_of_nonzero Polynomial.natTrailingDegree_mem_support_of_nonzero

theorem natTrailingDegree_le_of_mem_supp (a : ℕ) : a ∈ p.support → natTrailingDegree p ≤ a :=
  natTrailingDegree_le_of_ne_zero ∘ mem_support_iff.mp
#align polynomial.nat_trailing_degree_le_of_mem_supp Polynomial.natTrailingDegree_le_of_mem_supp

theorem natTrailingDegree_eq_support_min' (h : p ≠ 0) :
    natTrailingDegree p = p.support.min' (nonempty_support_iff.mpr h) := by
  apply le_antisymm
  · apply le_min'
    intro y hy
    exact natTrailingDegree_le_of_mem_supp y hy
  · apply Finset.min'_le
    exact mem_support_iff.mpr (trailingCoeff_nonzero_iff_nonzero.mpr h)
#align polynomial.nat_trailing_degree_eq_support_min' Polynomial.natTrailingDegree_eq_support_min'

theorem le_natTrailingDegree (hp : p ≠ 0) (hn : ∀ m < n, p.coeff m = 0) :
    n ≤ p.natTrailingDegree := by
  rw [natTrailingDegree_eq_support_min' hp]
  exact Finset.le_min' _ _ _ fun m hm => not_lt.1 fun hmn => mem_support_iff.1 hm <| hn _ hmn
#align polynomial.le_nat_trailing_degree Polynomial.le_natTrailingDegree

theorem natTrailingDegree_le_natDegree (p : R[X]) : p.natTrailingDegree ≤ p.natDegree := by
  by_cases hp : p = 0
  · rw [hp, natDegree_zero, natTrailingDegree_zero]
  · exact le_natDegree_of_ne_zero (mt trailingCoeff_eq_zero.mp hp)
#align polynomial.nat_trailing_degree_le_nat_degree Polynomial.natTrailingDegree_le_natDegree

theorem natTrailingDegree_mul_X_pow {p : R[X]} (hp : p ≠ 0) (n : ℕ) :
    (p * X ^ n).natTrailingDegree = p.natTrailingDegree + n := by
  apply le_antisymm
  · refine natTrailingDegree_le_of_ne_zero fun h => mt trailingCoeff_eq_zero.mp hp ?_
    rwa [trailingCoeff, ← coeff_mul_X_pow]
  · rw [natTrailingDegree_eq_support_min' fun h => hp (mul_X_pow_eq_zero h), Finset.le_min'_iff]
    intro y hy
    have key : n ≤ y := by
      rw [mem_support_iff, coeff_mul_X_pow'] at hy
      exact by_contra fun h => hy (if_neg h)
    rw [mem_support_iff, coeff_mul_X_pow', if_pos key] at hy
    exact (le_tsub_iff_right key).mp (natTrailingDegree_le_of_ne_zero hy)
set_option linter.uppercaseLean3 false in
#align polynomial.nat_trailing_degree_mul_X_pow Polynomial.natTrailingDegree_mul_X_pow

theorem le_trailingDegree_mul : p.trailingDegree + q.trailingDegree ≤ (p * q).trailingDegree := by
  refine Finset.le_min fun n hn => ?_
  rw [mem_support_iff, coeff_mul] at hn
  obtain ⟨⟨i, j⟩, hij, hpq⟩ := exists_ne_zero_of_sum_ne_zero hn
  refine
    (add_le_add (min_le (mem_support_iff.mpr (left_ne_zero_of_mul hpq)))
          (min_le (mem_support_iff.mpr (right_ne_zero_of_mul hpq)))).trans
      (le_of_eq ?_)
  rwa [← WithTop.coe_add, WithTop.coe_eq_coe, ← mem_antidiagonal]
#align polynomial.le_trailing_degree_mul Polynomial.le_trailingDegree_mul

theorem le_natTrailingDegree_mul (h : p * q ≠ 0) :
    p.natTrailingDegree + q.natTrailingDegree ≤ (p * q).natTrailingDegree := by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, mul_zero])
  -- Porting note: Needed to account for different coercion behaviour & add the lemma below
  have : ∀ (p : R[X]), WithTop.some (natTrailingDegree p) = Nat.cast (natTrailingDegree p) :=
    fun p ↦ rfl
  rw [← WithTop.coe_le_coe, WithTop.coe_add, this p, this q, this (p * q),
    ← trailingDegree_eq_natTrailingDegree hp, ← trailingDegree_eq_natTrailingDegree hq,
    ← trailingDegree_eq_natTrailingDegree h]
  exact le_trailingDegree_mul
#align polynomial.le_nat_trailing_degree_mul Polynomial.le_natTrailingDegree_mul

theorem coeff_mul_natTrailingDegree_add_natTrailingDegree : (p * q).coeff
    (p.natTrailingDegree + q.natTrailingDegree) = p.trailingCoeff * q.trailingCoeff := by
  rw [coeff_mul]
  refine
    Finset.sum_eq_single (p.natTrailingDegree, q.natTrailingDegree) ?_ fun h =>
      (h (mem_antidiagonal.mpr rfl)).elim
  rintro ⟨i, j⟩ h₁ h₂
  rw [mem_antidiagonal] at h₁
  by_cases hi : i < p.natTrailingDegree
  · rw [coeff_eq_zero_of_lt_natTrailingDegree hi, zero_mul]
  by_cases hj : j < q.natTrailingDegree
  · rw [coeff_eq_zero_of_lt_natTrailingDegree hj, mul_zero]
  rw [not_lt] at hi hj
  refine (h₂ (Prod.ext_iff.mpr ?_).symm).elim
  exact (add_eq_add_iff_eq_and_eq hi hj).mp h₁.symm
#align polynomial.coeff_mul_nat_trailing_degree_add_nat_trailing_degree Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree

theorem trailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff ≠ 0) :
    (p * q).trailingDegree = p.trailingDegree + q.trailingDegree := by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, trailingCoeff_zero, zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, trailingCoeff_zero, mul_zero])
  refine le_antisymm ?_ le_trailingDegree_mul
  rw [trailingDegree_eq_natTrailingDegree hp, trailingDegree_eq_natTrailingDegree hq, ←
    ENat.coe_add]
  apply trailingDegree_le_of_ne_zero
  rwa [coeff_mul_natTrailingDegree_add_natTrailingDegree]
#align polynomial.trailing_degree_mul' Polynomial.trailingDegree_mul'

theorem natTrailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff ≠ 0) :
    (p * q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree := by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, trailingCoeff_zero, zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, trailingCoeff_zero, mul_zero])
  -- Porting note: Needed to account for different coercion behaviour & add the lemmas below
  have aux1 : ∀ n, Nat.cast n = WithTop.some (n) := fun n ↦ rfl
  have aux2 : ∀ (p : R[X]), WithTop.some (natTrailingDegree p) = Nat.cast (natTrailingDegree p) :=
    fun p ↦ rfl
  apply natTrailingDegree_eq_of_trailingDegree_eq_some
  rw [trailingDegree_mul' h, aux1 (natTrailingDegree p + natTrailingDegree q),
    WithTop.coe_add, aux2 p, aux2 q, ← trailingDegree_eq_natTrailingDegree hp, ←
    trailingDegree_eq_natTrailingDegree hq]
#align polynomial.nat_trailing_degree_mul' Polynomial.natTrailingDegree_mul'

theorem natTrailingDegree_mul [NoZeroDivisors R] (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree :=
  natTrailingDegree_mul'
    (mul_ne_zero (mt trailingCoeff_eq_zero.mp hp) (mt trailingCoeff_eq_zero.mp hq))
#align polynomial.nat_trailing_degree_mul Polynomial.natTrailingDegree_mul

end Semiring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

@[simp]
theorem trailingDegree_one : trailingDegree (1 : R[X]) = (0 : ℕ∞) :=
  trailingDegree_C one_ne_zero
#align polynomial.trailing_degree_one Polynomial.trailingDegree_one

@[simp]
theorem trailingDegree_X : trailingDegree (X : R[X]) = 1 :=
  trailingDegree_monomial one_ne_zero
set_option linter.uppercaseLean3 false in
#align polynomial.trailing_degree_X Polynomial.trailingDegree_X

@[simp]
theorem natTrailingDegree_X : (X : R[X]).natTrailingDegree = 1 :=
  natTrailingDegree_monomial one_ne_zero
set_option linter.uppercaseLean3 false in
#align polynomial.nat_trailing_degree_X Polynomial.natTrailingDegree_X

@[simp]
lemma trailingDegree_X_pow (n : ℕ) :
    (X ^ n : R[X]).trailingDegree = n := by
  rw [X_pow_eq_monomial, trailingDegree_monomial one_ne_zero]

@[simp]
lemma natTrailingDegree_X_pow (n : ℕ) :
    (X ^ n : R[X]).natTrailingDegree = n := by
  rw [X_pow_eq_monomial, natTrailingDegree_monomial one_ne_zero]

end NonzeroSemiring

section Ring

variable [Ring R]

@[simp]
theorem trailingDegree_neg (p : R[X]) : trailingDegree (-p) = trailingDegree p := by
  unfold trailingDegree
  rw [support_neg]
#align polynomial.trailing_degree_neg Polynomial.trailingDegree_neg

@[simp]
theorem natTrailingDegree_neg (p : R[X]) : natTrailingDegree (-p) = natTrailingDegree p := by
  simp [natTrailingDegree]
#align polynomial.nat_trailing_degree_neg Polynomial.natTrailingDegree_neg

@[simp]
theorem natTrailingDegree_intCast (n : ℤ) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_intCast, natTrailingDegree_C]
#align polynomial.nat_trailing_degree_int_cast Polynomial.natTrailingDegree_intCast

@[deprecated (since := "2024-04-17")]
alias natTrailingDegree_int_cast := natTrailingDegree_intCast

end Ring

section Semiring

variable [Semiring R]

/-- The second-lowest coefficient, or 0 for constants -/
def nextCoeffUp (p : R[X]) : R :=
  if p.natTrailingDegree = 0 then 0 else p.coeff (p.natTrailingDegree + 1)
#align polynomial.next_coeff_up Polynomial.nextCoeffUp

@[simp] lemma nextCoeffUp_zero : nextCoeffUp (0 : R[X]) = 0 := by simp [nextCoeffUp]

@[simp]
theorem nextCoeffUp_C_eq_zero (c : R) : nextCoeffUp (C c) = 0 := by
  rw [nextCoeffUp]
  simp
set_option linter.uppercaseLean3 false in
#align polynomial.next_coeff_up_C_eq_zero Polynomial.nextCoeffUp_C_eq_zero

theorem nextCoeffUp_of_constantCoeff_eq_zero (p : R[X]) (hp : coeff p 0 = 0) :
    nextCoeffUp p = p.coeff (p.natTrailingDegree + 1) := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  · rw [nextCoeffUp, if_neg (natTrailingDegree_ne_zero.2 ⟨hp₀, hp⟩)]
#align polynomial.next_coeff_up_of_pos_nat_trailing_degree Polynomial.nextCoeffUp_of_constantCoeff_eq_zero

end Semiring

section Semiring

variable [Semiring R] {p q : R[X]}

theorem coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt
    (h : trailingDegree p < trailingDegree q) : coeff q (natTrailingDegree p) = 0 :=
  coeff_eq_zero_of_lt_trailingDegree <| natTrailingDegree_le_trailingDegree.trans_lt h
#align polynomial.coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt Polynomial.coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt

theorem ne_zero_of_trailingDegree_lt {n : ℕ∞} (h : trailingDegree p < n) : p ≠ 0 := fun h₀ =>
  h.not_le (by simp [h₀])
#align polynomial.ne_zero_of_trailing_degree_lt Polynomial.ne_zero_of_trailingDegree_lt

lemma natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (h : constantCoeff p ≠ 0) :
    p.natTrailingDegree = 0 :=
  le_antisymm (natTrailingDegree_le_of_ne_zero h) zero_le'

namespace Monic

lemma eq_X_pow_iff_natDegree_le_natTrailingDegree (h₁ : p.Monic) :
    p = X ^ p.natDegree ↔ p.natDegree ≤ p.natTrailingDegree := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · nontriviality R
    rw [h, natTrailingDegree_X_pow, ← h]
  · ext n
    rw [coeff_X_pow]
    obtain hn | rfl | hn := lt_trichotomy n p.natDegree
    · rw [if_neg hn.ne, coeff_eq_zero_of_lt_natTrailingDegree (hn.trans_le h)]
    · simpa only [if_pos rfl] using h₁.leadingCoeff
    · rw [if_neg hn.ne', coeff_eq_zero_of_natDegree_lt hn]

lemma eq_X_pow_iff_natTrailingDegree_eq_natDegree (h₁ : p.Monic) :
    p = X ^ p.natDegree ↔ p.natTrailingDegree = p.natDegree :=
  h₁.eq_X_pow_iff_natDegree_le_natTrailingDegree.trans (natTrailingDegree_le_natDegree p).ge_iff_eq

@[deprecated] -- 2024-04-26
alias ⟨_, eq_X_pow_of_natTrailingDegree_eq_natDegree⟩ := eq_X_pow_iff_natTrailingDegree_eq_natDegree

end Monic

end Semiring

end Polynomial
