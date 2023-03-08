/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module data.polynomial.degree.trailing_degree
! leanprover-community/mathlib commit 302eab4f46abb63de520828de78c04cb0f9b5836
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Enat.Basic
import Mathbin.Data.Polynomial.Degree.Definitions

/-!
# Trailing degree of univariate polynomials

## Main definitions

* `trailing_degree p`: the multiplicity of `X` in the polynomial `p`
* `nat_trailing_degree`: a variant of `trailing_degree` that takes values in the natural numbers
* `trailing_coeff`: the coefficient at index `nat_trailing_degree p`

Converts most results about `degree`, `nat_degree` and `leading_coeff` to results about the bottom
end of a polynomial
-/


noncomputable section

open Function Polynomial Finsupp Finset

open BigOperators Classical Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

/-- `trailing_degree p` is the multiplicity of `x` in the polynomial `p`, i.e. the smallest
`X`-exponent in `p`.
`trailing_degree p = some n` when `p ≠ 0` and `n` is the smallest power of `X` that appears
in `p`, otherwise
`trailing_degree 0 = ⊤`. -/
def trailingDegree (p : R[X]) : ℕ∞ :=
  p.support.min
#align polynomial.trailing_degree Polynomial.trailingDegree

theorem trailingDegree_lt_wf : WellFounded fun p q : R[X] => trailingDegree p < trailingDegree q :=
  InvImage.wf trailingDegree (WithTop.wellFounded_lt Nat.lt_wfRel)
#align polynomial.trailing_degree_lt_wf Polynomial.trailingDegree_lt_wf

/-- `nat_trailing_degree p` forces `trailing_degree p` to `ℕ`, by defining
`nat_trailing_degree ⊤ = 0`. -/
def natTrailingDegree (p : R[X]) : ℕ :=
  (trailingDegree p).getD 0
#align polynomial.nat_trailing_degree Polynomial.natTrailingDegree

/-- `trailing_coeff p` gives the coefficient of the smallest power of `X` in `p`-/
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

instance TrailingMonic.decidable [DecidableEq R] : Decidable (TrailingMonic p) := by
  unfold trailing_monic <;> infer_instance
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
    trailingDegree p = (natTrailingDegree p : ℕ∞) :=
  by
  let ⟨n, hn⟩ :=
    not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt trailingDegree_eq_top.1 hp))
  have hn : trailingDegree p = n := Classical.not_not.1 hn
  rw [nat_trailing_degree, hn] <;> rfl
#align polynomial.trailing_degree_eq_nat_trailing_degree Polynomial.trailingDegree_eq_natTrailingDegree

theorem trailingDegree_eq_iff_natTrailingDegree_eq {p : R[X]} {n : ℕ} (hp : p ≠ 0) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n := by
  rw [trailing_degree_eq_nat_trailing_degree hp, WithTop.coe_eq_coe]
#align polynomial.trailing_degree_eq_iff_nat_trailing_degree_eq Polynomial.trailingDegree_eq_iff_natTrailingDegree_eq

theorem trailingDegree_eq_iff_natTrailingDegree_eq_of_pos {p : R[X]} {n : ℕ} (hn : 0 < n) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n :=
  by
  constructor
  · intro H
    rwa [← trailing_degree_eq_iff_nat_trailing_degree_eq]
    rintro rfl
    rw [trailing_degree_zero] at H
    exact Option.noConfusion H
  · intro H
    rwa [trailing_degree_eq_iff_nat_trailing_degree_eq]
    rintro rfl
    rw [nat_trailing_degree_zero] at H
    rw [H] at hn
    exact lt_irrefl _ hn
#align polynomial.trailing_degree_eq_iff_nat_trailing_degree_eq_of_pos Polynomial.trailingDegree_eq_iff_natTrailingDegree_eq_of_pos

theorem natTrailingDegree_eq_of_trailingDegree_eq_some {p : R[X]} {n : ℕ}
    (h : trailingDegree p = n) : natTrailingDegree p = n :=
  have hp0 : p ≠ 0 := fun hp0 => by rw [hp0] at h <;> exact Option.noConfusion h
  Option.some_inj.1 <|
    show (natTrailingDegree p : ℕ∞) = n by rwa [← trailing_degree_eq_nat_trailing_degree hp0]
#align polynomial.nat_trailing_degree_eq_of_trailing_degree_eq_some Polynomial.natTrailingDegree_eq_of_trailingDegree_eq_some

@[simp]
theorem natTrailingDegree_le_trailingDegree : ↑(natTrailingDegree p) ≤ trailingDegree p :=
  by
  by_cases hp : p = 0;
  · rw [hp, trailing_degree_zero]
    exact le_top
  rw [trailing_degree_eq_nat_trailing_degree hp]
  exact le_rfl
#align polynomial.nat_trailing_degree_le_trailing_degree Polynomial.natTrailingDegree_le_trailingDegree

theorem natTrailingDegree_eq_of_trailingDegree_eq [Semiring S] {q : S[X]}
    (h : trailingDegree p = trailingDegree q) : natTrailingDegree p = natTrailingDegree q := by
  unfold nat_trailing_degree <;> rw [h]
#align polynomial.nat_trailing_degree_eq_of_trailing_degree_eq Polynomial.natTrailingDegree_eq_of_trailingDegree_eq

theorem le_trailingDegree_of_ne_zero (h : coeff p n ≠ 0) : trailingDegree p ≤ n :=
  show @LE.le ℕ∞ _ p.support.min n from min_le (mem_support_iff.2 h)
#align polynomial.le_trailing_degree_of_ne_zero Polynomial.le_trailingDegree_of_ne_zero

theorem natTrailingDegree_le_of_ne_zero (h : coeff p n ≠ 0) : natTrailingDegree p ≤ n :=
  by
  rw [← WithTop.coe_le_coe, ← trailing_degree_eq_nat_trailing_degree]
  · exact le_trailing_degree_of_ne_zero h
  · intro h
    subst h
    exact h rfl
#align polynomial.nat_trailing_degree_le_of_ne_zero Polynomial.natTrailingDegree_le_of_ne_zero

theorem trailingDegree_le_trailingDegree (h : coeff q (natTrailingDegree p) ≠ 0) :
    trailingDegree q ≤ trailingDegree p :=
  by
  by_cases hp : p = 0
  · rw [hp]
    exact le_top
  · rw [trailing_degree_eq_nat_trailing_degree hp]
    exact le_trailing_degree_of_ne_zero h
#align polynomial.trailing_degree_le_trailing_degree Polynomial.trailingDegree_le_trailingDegree

theorem trailingDegree_ne_of_natTrailingDegree_ne {n : ℕ} :
    p.natTrailingDegree ≠ n → trailingDegree p ≠ n :=
  mt fun h => by rw [nat_trailing_degree, h, Option.getD_coe]
#align polynomial.trailing_degree_ne_of_nat_trailing_degree_ne Polynomial.trailingDegree_ne_of_natTrailingDegree_ne

theorem natTrailingDegree_le_of_trailingDegree_le {n : ℕ} {hp : p ≠ 0}
    (H : (n : ℕ∞) ≤ trailingDegree p) : n ≤ natTrailingDegree p :=
  by
  rw [trailing_degree_eq_nat_trailing_degree hp] at H
  exact with_top.coe_le_coe.mp H
#align polynomial.nat_trailing_degree_le_of_trailing_degree_le Polynomial.natTrailingDegree_le_of_trailingDegree_le

theorem natTrailingDegree_le_natTrailingDegree {hq : q ≠ 0}
    (hpq : p.trailingDegree ≤ q.trailingDegree) : p.natTrailingDegree ≤ q.natTrailingDegree :=
  by
  by_cases hp : p = 0;
  · rw [hp, nat_trailing_degree_zero]
    exact zero_le _
  rwa [trailing_degree_eq_nat_trailing_degree hp, trailing_degree_eq_nat_trailing_degree hq,
    WithTop.coe_le_coe] at hpq
#align polynomial.nat_trailing_degree_le_nat_trailing_degree Polynomial.natTrailingDegree_le_natTrailingDegree

@[simp]
theorem trailingDegree_monomial (ha : a ≠ 0) : trailingDegree (monomial n a) = n := by
  rw [trailing_degree, support_monomial n ha, min_singleton]
#align polynomial.trailing_degree_monomial Polynomial.trailingDegree_monomial

theorem natTrailingDegree_monomial (ha : a ≠ 0) : natTrailingDegree (monomial n a) = n := by
  rw [nat_trailing_degree, trailing_degree_monomial ha] <;> rfl
#align polynomial.nat_trailing_degree_monomial Polynomial.natTrailingDegree_monomial

theorem natTrailingDegree_monomial_le : natTrailingDegree (monomial n a) ≤ n :=
  if ha : a = 0 then by simp [ha] else (natTrailingDegree_monomial ha).le
#align polynomial.nat_trailing_degree_monomial_le Polynomial.natTrailingDegree_monomial_le

theorem le_trailingDegree_monomial : ↑n ≤ trailingDegree (monomial n a) :=
  if ha : a = 0 then by simp [ha] else (trailingDegree_monomial ha).ge
#align polynomial.le_trailing_degree_monomial Polynomial.le_trailingDegree_monomial

@[simp]
theorem trailingDegree_c (ha : a ≠ 0) : trailingDegree (C a) = (0 : ℕ∞) :=
  trailingDegree_monomial ha
#align polynomial.trailing_degree_C Polynomial.trailingDegree_c

theorem le_trailingDegree_c : (0 : ℕ∞) ≤ trailingDegree (C a) :=
  le_trailingDegree_monomial
#align polynomial.le_trailing_degree_C Polynomial.le_trailingDegree_c

theorem trailingDegree_one_le : (0 : ℕ∞) ≤ trailingDegree (1 : R[X]) := by
  rw [← C_1] <;> exact le_trailing_degree_C
#align polynomial.trailing_degree_one_le Polynomial.trailingDegree_one_le

@[simp]
theorem natTrailingDegree_c (a : R) : natTrailingDegree (C a) = 0 :=
  nonpos_iff_eq_zero.1 natTrailingDegree_monomial_le
#align polynomial.nat_trailing_degree_C Polynomial.natTrailingDegree_c

@[simp]
theorem natTrailingDegree_one : natTrailingDegree (1 : R[X]) = 0 :=
  natTrailingDegree_c 1
#align polynomial.nat_trailing_degree_one Polynomial.natTrailingDegree_one

@[simp]
theorem natTrailingDegree_nat_cast (n : ℕ) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_nat_cast, nat_trailing_degree_C]
#align polynomial.nat_trailing_degree_nat_cast Polynomial.natTrailingDegree_nat_cast

@[simp]
theorem trailingDegree_c_mul_x_pow (n : ℕ) (ha : a ≠ 0) : trailingDegree (C a * X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial, trailing_degree_monomial ha]
#align polynomial.trailing_degree_C_mul_X_pow Polynomial.trailingDegree_c_mul_x_pow

theorem le_trailingDegree_c_mul_x_pow (n : ℕ) (a : R) : (n : ℕ∞) ≤ trailingDegree (C a * X ^ n) :=
  by
  rw [C_mul_X_pow_eq_monomial]
  exact le_trailing_degree_monomial
#align polynomial.le_trailing_degree_C_mul_X_pow Polynomial.le_trailingDegree_c_mul_x_pow

theorem coeff_eq_zero_of_trailingDegree_lt (h : (n : ℕ∞) < trailingDegree p) : coeff p n = 0 :=
  Classical.not_not.1 (mt le_trailingDegree_of_ne_zero (not_le_of_gt h))
#align polynomial.coeff_eq_zero_of_trailing_degree_lt Polynomial.coeff_eq_zero_of_trailingDegree_lt

theorem coeff_eq_zero_of_lt_natTrailingDegree {p : R[X]} {n : ℕ} (h : n < p.natTrailingDegree) :
    p.coeff n = 0 := by
  apply coeff_eq_zero_of_trailing_degree_lt
  by_cases hp : p = 0
  · rw [hp, trailing_degree_zero]
    exact WithTop.coe_lt_top n
  · rwa [trailing_degree_eq_nat_trailing_degree hp, WithTop.coe_lt_coe]
#align polynomial.coeff_eq_zero_of_lt_nat_trailing_degree Polynomial.coeff_eq_zero_of_lt_natTrailingDegree

@[simp]
theorem coeff_natTrailingDegree_pred_eq_zero {p : R[X]} {hp : (0 : ℕ∞) < natTrailingDegree p} :
    p.coeff (p.natTrailingDegree - 1) = 0 :=
  coeff_eq_zero_of_lt_natTrailingDegree <|
    Nat.sub_lt ((WithTop.zero_lt_coe (natTrailingDegree p)).mp hp) Nat.one_pos
#align polynomial.coeff_nat_trailing_degree_pred_eq_zero Polynomial.coeff_natTrailingDegree_pred_eq_zero

theorem le_trailingDegree_x_pow (n : ℕ) : (n : ℕ∞) ≤ trailingDegree (X ^ n : R[X]) := by
  simpa only [C_1, one_mul] using le_trailing_degree_C_mul_X_pow n (1 : R)
#align polynomial.le_trailing_degree_X_pow Polynomial.le_trailingDegree_x_pow

theorem le_trailingDegree_x : (1 : ℕ∞) ≤ trailingDegree (X : R[X]) :=
  le_trailingDegree_monomial
#align polynomial.le_trailing_degree_X Polynomial.le_trailingDegree_x

theorem natTrailingDegree_x_le : (X : R[X]).natTrailingDegree ≤ 1 :=
  natTrailingDegree_monomial_le
#align polynomial.nat_trailing_degree_X_le Polynomial.natTrailingDegree_x_le

@[simp]
theorem trailingCoeff_eq_zero : trailingCoeff p = 0 ↔ p = 0 :=
  ⟨fun h =>
    by_contradiction fun hp =>
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
    natTrailingDegree p = p.support.min' (nonempty_support_iff.mpr h) :=
  by
  apply le_antisymm
  · apply le_min'
    intro y hy
    exact nat_trailing_degree_le_of_mem_supp y hy
  · apply Finset.min'_le
    exact mem_support_iff.mpr (trailing_coeff_nonzero_iff_nonzero.mpr h)
#align polynomial.nat_trailing_degree_eq_support_min' Polynomial.natTrailingDegree_eq_support_min'

theorem le_natTrailingDegree (hp : p ≠ 0) (hn : ∀ m < n, p.coeff m = 0) : n ≤ p.natTrailingDegree :=
  by
  rw [nat_trailing_degree_eq_support_min' hp]
  exact Finset.le_min' _ _ _ fun m hm => not_lt.1 fun hmn => mem_support_iff.1 hm <| hn _ hmn
#align polynomial.le_nat_trailing_degree Polynomial.le_natTrailingDegree

theorem natTrailingDegree_le_natDegree (p : R[X]) : p.natTrailingDegree ≤ p.natDegree :=
  by
  by_cases hp : p = 0
  · rw [hp, nat_degree_zero, nat_trailing_degree_zero]
  · exact le_nat_degree_of_ne_zero (mt trailing_coeff_eq_zero.mp hp)
#align polynomial.nat_trailing_degree_le_nat_degree Polynomial.natTrailingDegree_le_natDegree

theorem natTrailingDegree_mul_x_pow {p : R[X]} (hp : p ≠ 0) (n : ℕ) :
    (p * X ^ n).natTrailingDegree = p.natTrailingDegree + n :=
  by
  apply le_antisymm
  · refine' nat_trailing_degree_le_of_ne_zero fun h => mt trailing_coeff_eq_zero.mp hp _
    rwa [trailing_coeff, ← coeff_mul_X_pow]
  · rw [nat_trailing_degree_eq_support_min' fun h => hp (mul_X_pow_eq_zero h), Finset.le_min'_iff]
    intro y hy
    have key : n ≤ y := by
      rw [mem_support_iff, coeff_mul_X_pow'] at hy
      exact by_contra fun h => hy (if_neg h)
    rw [mem_support_iff, coeff_mul_X_pow', if_pos key] at hy
    exact (le_tsub_iff_right key).mp (nat_trailing_degree_le_of_ne_zero hy)
#align polynomial.nat_trailing_degree_mul_X_pow Polynomial.natTrailingDegree_mul_x_pow

theorem le_trailingDegree_mul : p.trailingDegree + q.trailingDegree ≤ (p * q).trailingDegree :=
  by
  refine' Finset.le_min fun n hn => _
  rw [mem_support_iff, coeff_mul] at hn
  obtain ⟨⟨i, j⟩, hij, hpq⟩ := exists_ne_zero_of_sum_ne_zero hn
  refine'
    (add_le_add (min_le (mem_support_iff.mpr (left_ne_zero_of_mul hpq)))
          (min_le (mem_support_iff.mpr (right_ne_zero_of_mul hpq)))).trans
      (le_of_eq _)
  rwa [← WithTop.coe_add, WithTop.coe_eq_coe, ← nat.mem_antidiagonal]
#align polynomial.le_trailing_degree_mul Polynomial.le_trailingDegree_mul

theorem le_natTrailingDegree_mul (h : p * q ≠ 0) :
    p.natTrailingDegree + q.natTrailingDegree ≤ (p * q).natTrailingDegree :=
  by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, mul_zero])
  rw [← WithTop.coe_le_coe, WithTop.coe_add, ← trailing_degree_eq_nat_trailing_degree hp, ←
    trailing_degree_eq_nat_trailing_degree hq, ← trailing_degree_eq_nat_trailing_degree h]
  exact le_trailing_degree_mul
#align polynomial.le_nat_trailing_degree_mul Polynomial.le_natTrailingDegree_mul

theorem coeff_mul_natTrailingDegree_add_natTrailingDegree :
    (p * q).coeff (p.natTrailingDegree + q.natTrailingDegree) = p.trailingCoeff * q.trailingCoeff :=
  by
  rw [coeff_mul]
  refine'
    Finset.sum_eq_single (p.nat_trailing_degree, q.nat_trailing_degree) _ fun h =>
      (h (nat.mem_antidiagonal.mpr rfl)).elim
  rintro ⟨i, j⟩ h₁ h₂
  rw [nat.mem_antidiagonal] at h₁
  by_cases hi : i < p.nat_trailing_degree
  · rw [coeff_eq_zero_of_lt_nat_trailing_degree hi, zero_mul]
  by_cases hj : j < q.nat_trailing_degree
  · rw [coeff_eq_zero_of_lt_nat_trailing_degree hj, mul_zero]
  rw [not_lt] at hi hj
  refine' (h₂ (prod.ext_iff.mpr _).symm).elim
  exact (add_eq_add_iff_eq_and_eq hi hj).mp h₁.symm
#align polynomial.coeff_mul_nat_trailing_degree_add_nat_trailing_degree Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree

theorem trailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff ≠ 0) :
    (p * q).trailingDegree = p.trailingDegree + q.trailingDegree :=
  by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, trailing_coeff_zero, zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, trailing_coeff_zero, mul_zero])
  refine' le_antisymm _ le_trailing_degree_mul
  rw [trailing_degree_eq_nat_trailing_degree hp, trailing_degree_eq_nat_trailing_degree hq, ←
    ENat.coe_add]
  apply le_trailing_degree_of_ne_zero
  rwa [coeff_mul_nat_trailing_degree_add_nat_trailing_degree]
#align polynomial.trailing_degree_mul' Polynomial.trailingDegree_mul'

theorem natTrailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff ≠ 0) :
    (p * q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree :=
  by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, trailing_coeff_zero, zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, trailing_coeff_zero, mul_zero])
  apply nat_trailing_degree_eq_of_trailing_degree_eq_some
  rw [trailing_degree_mul' h, WithTop.coe_add, ← trailing_degree_eq_nat_trailing_degree hp, ←
    trailing_degree_eq_nat_trailing_degree hq]
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
  trailingDegree_c one_ne_zero
#align polynomial.trailing_degree_one Polynomial.trailingDegree_one

@[simp]
theorem trailingDegree_x : trailingDegree (X : R[X]) = 1 :=
  trailingDegree_monomial one_ne_zero
#align polynomial.trailing_degree_X Polynomial.trailingDegree_x

@[simp]
theorem natTrailingDegree_x : (X : R[X]).natTrailingDegree = 1 :=
  natTrailingDegree_monomial one_ne_zero
#align polynomial.nat_trailing_degree_X Polynomial.natTrailingDegree_x

end NonzeroSemiring

section Ring

variable [Ring R]

@[simp]
theorem trailingDegree_neg (p : R[X]) : trailingDegree (-p) = trailingDegree p := by
  unfold trailing_degree <;> rw [support_neg]
#align polynomial.trailing_degree_neg Polynomial.trailingDegree_neg

@[simp]
theorem natTrailingDegree_neg (p : R[X]) : natTrailingDegree (-p) = natTrailingDegree p := by
  simp [nat_trailing_degree]
#align polynomial.nat_trailing_degree_neg Polynomial.natTrailingDegree_neg

@[simp]
theorem natTrailingDegree_int_cast (n : ℤ) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_int_cast, nat_trailing_degree_C]
#align polynomial.nat_trailing_degree_int_cast Polynomial.natTrailingDegree_int_cast

end Ring

section Semiring

variable [Semiring R]

/-- The second-lowest coefficient, or 0 for constants -/
def nextCoeffUp (p : R[X]) : R :=
  if p.natTrailingDegree = 0 then 0 else p.coeff (p.natTrailingDegree + 1)
#align polynomial.next_coeff_up Polynomial.nextCoeffUp

@[simp]
theorem nextCoeffUp_c_eq_zero (c : R) : nextCoeffUp (C c) = 0 :=
  by
  rw [next_coeff_up]
  simp
#align polynomial.next_coeff_up_C_eq_zero Polynomial.nextCoeffUp_c_eq_zero

theorem nextCoeffUp_of_pos_natTrailingDegree (p : R[X]) (hp : 0 < p.natTrailingDegree) :
    nextCoeffUp p = p.coeff (p.natTrailingDegree + 1) :=
  by
  rw [next_coeff_up, if_neg]
  contrapose! hp
  simpa
#align polynomial.next_coeff_up_of_pos_nat_trailing_degree Polynomial.nextCoeffUp_of_pos_natTrailingDegree

end Semiring

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type _}

theorem coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt
    (h : trailingDegree p < trailingDegree q) : coeff q (natTrailingDegree p) = 0 :=
  coeff_eq_zero_of_trailingDegree_lt <| natTrailingDegree_le_trailingDegree.trans_lt h
#align polynomial.coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt Polynomial.coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt

theorem ne_zero_of_trailingDegree_lt {n : ℕ∞} (h : trailingDegree p < n) : p ≠ 0 := fun h₀ =>
  h.not_le (by simp [h₀])
#align polynomial.ne_zero_of_trailing_degree_lt Polynomial.ne_zero_of_trailingDegree_lt

end Semiring

end Polynomial

