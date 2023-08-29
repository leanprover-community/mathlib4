/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Polynomial.Degree.Definitions

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

open BigOperators Classical Polynomial

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
  InvImage.wf trailingDegree (WithTop.wellFounded_lt Nat.lt_wfRel.2)
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

-- Porting note: Removed unused argument `[DecidableEq R]`?
instance TrailingMonic.decidable: Decidable (TrailingMonic p) := inferInstance
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
                                                                    -- 🎉 no goals
#align polynomial.trailing_degree_eq_top Polynomial.trailingDegree_eq_top

theorem trailingDegree_eq_natTrailingDegree (hp : p ≠ 0) :
    trailingDegree p = (natTrailingDegree p : ℕ∞) := by
  let ⟨n, hn⟩ :=
    not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt trailingDegree_eq_top.1 hp))
  have hn : trailingDegree p = n := Classical.not_not.1 hn
  -- ⊢ trailingDegree p = ↑(natTrailingDegree p)
  rw [natTrailingDegree, hn]
  -- ⊢ ↑n = ↑(Option.getD (↑n) 0)
  rfl
  -- 🎉 no goals
#align polynomial.trailing_degree_eq_nat_trailing_degree Polynomial.trailingDegree_eq_natTrailingDegree

theorem trailingDegree_eq_iff_natTrailingDegree_eq {p : R[X]} {n : ℕ} (hp : p ≠ 0) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n := by
  rw [trailingDegree_eq_natTrailingDegree hp]
  -- ⊢ ↑(natTrailingDegree p) = ↑n ↔ natTrailingDegree p = n
  exact WithTop.coe_eq_coe
  -- 🎉 no goals
#align polynomial.trailing_degree_eq_iff_nat_trailing_degree_eq Polynomial.trailingDegree_eq_iff_natTrailingDegree_eq

theorem trailingDegree_eq_iff_natTrailingDegree_eq_of_pos {p : R[X]} {n : ℕ} (hn : 0 < n) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n := by
  constructor
  -- ⊢ trailingDegree p = ↑n → natTrailingDegree p = n
  · intro H
    -- ⊢ natTrailingDegree p = n
    rwa [← trailingDegree_eq_iff_natTrailingDegree_eq]
    -- ⊢ p ≠ 0
    rintro rfl
    -- ⊢ False
    rw [trailingDegree_zero] at H
    -- ⊢ False
    exact Option.noConfusion H
    -- 🎉 no goals
  · intro H
    -- ⊢ trailingDegree p = ↑n
    rwa [trailingDegree_eq_iff_natTrailingDegree_eq]
    -- ⊢ p ≠ 0
    rintro rfl
    -- ⊢ False
    rw [natTrailingDegree_zero] at H
    -- ⊢ False
    rw [H] at hn
    -- ⊢ False
    exact lt_irrefl _ hn
    -- 🎉 no goals
#align polynomial.trailing_degree_eq_iff_nat_trailing_degree_eq_of_pos Polynomial.trailingDegree_eq_iff_natTrailingDegree_eq_of_pos

theorem natTrailingDegree_eq_of_trailingDegree_eq_some {p : R[X]} {n : ℕ}
    (h : trailingDegree p = n) : natTrailingDegree p = n :=
  have hp0 : p ≠ 0 := fun hp0 => by rw [hp0] at h; exact Option.noConfusion h
                                    -- ⊢ False
                                                   -- 🎉 no goals
  Option.some_inj.1 <|
    show (natTrailingDegree p : ℕ∞) = n by rwa [← trailingDegree_eq_natTrailingDegree hp0]
                                           -- 🎉 no goals
#align polynomial.nat_trailing_degree_eq_of_trailing_degree_eq_some Polynomial.natTrailingDegree_eq_of_trailingDegree_eq_some

@[simp]
theorem natTrailingDegree_le_trailingDegree : ↑(natTrailingDegree p) ≤ trailingDegree p := by
  by_cases hp : p = 0;
  -- ⊢ ↑(natTrailingDegree p) ≤ trailingDegree p
  · rw [hp, trailingDegree_zero]
    -- ⊢ ↑(natTrailingDegree 0) ≤ ⊤
    exact le_top
    -- 🎉 no goals
  rw [trailingDegree_eq_natTrailingDegree hp]
  -- 🎉 no goals
#align polynomial.nat_trailing_degree_le_trailing_degree Polynomial.natTrailingDegree_le_trailingDegree

theorem natTrailingDegree_eq_of_trailingDegree_eq [Semiring S] {q : S[X]}
    (h : trailingDegree p = trailingDegree q) : natTrailingDegree p = natTrailingDegree q := by
  unfold natTrailingDegree
  -- ⊢ Option.getD (trailingDegree p) 0 = Option.getD (trailingDegree q) 0
  rw [h]
  -- 🎉 no goals
#align polynomial.nat_trailing_degree_eq_of_trailing_degree_eq Polynomial.natTrailingDegree_eq_of_trailingDegree_eq

theorem le_trailingDegree_of_ne_zero (h : coeff p n ≠ 0) : trailingDegree p ≤ n :=
  show @LE.le ℕ∞ _ p.support.min n from min_le (mem_support_iff.2 h)
#align polynomial.le_trailing_degree_of_ne_zero Polynomial.le_trailingDegree_of_ne_zero

theorem natTrailingDegree_le_of_ne_zero (h : coeff p n ≠ 0) : natTrailingDegree p ≤ n := by
  have : WithTop.some (natTrailingDegree p) = Nat.cast (natTrailingDegree p) := rfl
  -- ⊢ natTrailingDegree p ≤ n
  rw [← WithTop.coe_le_coe, this, ← trailingDegree_eq_natTrailingDegree]
  -- ⊢ trailingDegree p ≤ ↑n
  · exact le_trailingDegree_of_ne_zero h
    -- 🎉 no goals
  · intro h
    -- ⊢ False
    subst h
    -- ⊢ False
    exact h rfl
    -- 🎉 no goals
#align polynomial.nat_trailing_degree_le_of_ne_zero Polynomial.natTrailingDegree_le_of_ne_zero

theorem trailingDegree_le_trailingDegree (h : coeff q (natTrailingDegree p) ≠ 0) :
    trailingDegree q ≤ trailingDegree p := by
  by_cases hp : p = 0
  -- ⊢ trailingDegree q ≤ trailingDegree p
  · rw [hp]
    -- ⊢ trailingDegree q ≤ trailingDegree 0
    exact le_top
    -- 🎉 no goals
  · rw [trailingDegree_eq_natTrailingDegree hp]
    -- ⊢ trailingDegree q ≤ ↑(natTrailingDegree p)
    exact le_trailingDegree_of_ne_zero h
    -- 🎉 no goals
#align polynomial.trailing_degree_le_trailing_degree Polynomial.trailingDegree_le_trailingDegree

theorem trailingDegree_ne_of_natTrailingDegree_ne {n : ℕ} :
    p.natTrailingDegree ≠ n → trailingDegree p ≠ n := by
  -- Porting note: Needed to account for different coercion behaviour & add the lemma below
  have : Nat.cast n = WithTop.some n := rfl
  -- ⊢ natTrailingDegree p ≠ n → trailingDegree p ≠ ↑n
  exact mt fun h => by rw [natTrailingDegree, h, this, ←WithTop.some_eq_coe, Option.getD_some]
  -- 🎉 no goals
#align polynomial.trailing_degree_ne_of_nat_trailing_degree_ne Polynomial.trailingDegree_ne_of_natTrailingDegree_ne

theorem natTrailingDegree_le_of_trailingDegree_le {n : ℕ} {hp : p ≠ 0}
    (H : (n : ℕ∞) ≤ trailingDegree p) : n ≤ natTrailingDegree p := by
  rw [trailingDegree_eq_natTrailingDegree hp] at H
  -- ⊢ n ≤ natTrailingDegree p
  exact WithTop.coe_le_coe.mp H
  -- 🎉 no goals
#align polynomial.nat_trailing_degree_le_of_trailing_degree_le Polynomial.natTrailingDegree_le_of_trailingDegree_le

theorem natTrailingDegree_le_natTrailingDegree {hq : q ≠ 0}
    (hpq : p.trailingDegree ≤ q.trailingDegree) : p.natTrailingDegree ≤ q.natTrailingDegree := by
  by_cases hp : p = 0;
  -- ⊢ natTrailingDegree p ≤ natTrailingDegree q
  · rw [hp, natTrailingDegree_zero]
    -- ⊢ 0 ≤ natTrailingDegree q
    exact zero_le _
    -- 🎉 no goals
  rw [trailingDegree_eq_natTrailingDegree hp, trailingDegree_eq_natTrailingDegree hq] at hpq
  -- ⊢ natTrailingDegree p ≤ natTrailingDegree q
  exact WithTop.coe_le_coe.1 hpq
  -- 🎉 no goals
#align polynomial.nat_trailing_degree_le_nat_trailing_degree Polynomial.natTrailingDegree_le_natTrailingDegree

@[simp]
theorem trailingDegree_monomial (ha : a ≠ 0) : trailingDegree (monomial n a) = n := by
  rw [trailingDegree, support_monomial n ha, min_singleton]
  -- ⊢ ↑n = ↑n
  rfl
  -- 🎉 no goals
#align polynomial.trailing_degree_monomial Polynomial.trailingDegree_monomial

theorem natTrailingDegree_monomial (ha : a ≠ 0) : natTrailingDegree (monomial n a) = n := by
  rw [natTrailingDegree, trailingDegree_monomial ha]
  -- ⊢ Option.getD (↑n) 0 = n
  rfl
  -- 🎉 no goals
#align polynomial.nat_trailing_degree_monomial Polynomial.natTrailingDegree_monomial

theorem natTrailingDegree_monomial_le : natTrailingDegree (monomial n a) ≤ n :=
  if ha : a = 0 then by simp [ha] else (natTrailingDegree_monomial ha).le
                        -- 🎉 no goals
#align polynomial.nat_trailing_degree_monomial_le Polynomial.natTrailingDegree_monomial_le

theorem le_trailingDegree_monomial : ↑n ≤ trailingDegree (monomial n a) :=
  if ha : a = 0 then by simp [ha] else (trailingDegree_monomial ha).ge
                        -- 🎉 no goals
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
  -- ⊢ 0 ≤ trailingDegree (↑C 1)
  exact le_trailingDegree_C
  -- 🎉 no goals
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
theorem natTrailingDegree_nat_cast (n : ℕ) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_nat_cast, natTrailingDegree_C]
  -- 🎉 no goals
#align polynomial.nat_trailing_degree_nat_cast Polynomial.natTrailingDegree_nat_cast

@[simp]
theorem trailingDegree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : trailingDegree (C a * X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial, trailingDegree_monomial ha]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.trailing_degree_C_mul_X_pow Polynomial.trailingDegree_C_mul_X_pow

theorem le_trailingDegree_C_mul_X_pow (n : ℕ) (a : R) :
    (n : ℕ∞) ≤ trailingDegree (C a * X ^ n) := by
  rw [C_mul_X_pow_eq_monomial]
  -- ⊢ ↑n ≤ trailingDegree (↑(monomial n) a)
  exact le_trailingDegree_monomial
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.le_trailing_degree_C_mul_X_pow Polynomial.le_trailingDegree_C_mul_X_pow

theorem coeff_eq_zero_of_trailingDegree_lt (h : (n : ℕ∞) < trailingDegree p) : coeff p n = 0 :=
  Classical.not_not.1 (mt le_trailingDegree_of_ne_zero (not_le_of_gt h))
#align polynomial.coeff_eq_zero_of_trailing_degree_lt Polynomial.coeff_eq_zero_of_trailingDegree_lt

theorem coeff_eq_zero_of_lt_natTrailingDegree {p : R[X]} {n : ℕ} (h : n < p.natTrailingDegree) :
    p.coeff n = 0 := by
  apply coeff_eq_zero_of_trailingDegree_lt
  -- ⊢ ↑n < trailingDegree p
  by_cases hp : p = 0
  -- ⊢ ↑n < trailingDegree p
  · rw [hp, trailingDegree_zero]
    -- ⊢ ↑n < ⊤
    exact WithTop.coe_lt_top n
    -- 🎉 no goals
  · rw [trailingDegree_eq_natTrailingDegree hp]
    -- ⊢ ↑n < ↑(natTrailingDegree p)
    exact WithTop.coe_lt_coe.2 h
    -- 🎉 no goals
#align polynomial.coeff_eq_zero_of_lt_nat_trailing_degree Polynomial.coeff_eq_zero_of_lt_natTrailingDegree

@[simp]
theorem coeff_natTrailingDegree_pred_eq_zero {p : R[X]} {hp : (0 : ℕ∞) < natTrailingDegree p} :
    p.coeff (p.natTrailingDegree - 1) = 0 :=
  coeff_eq_zero_of_lt_natTrailingDegree <|
    Nat.sub_lt ((WithTop.zero_lt_coe (natTrailingDegree p)).mp hp) Nat.one_pos
#align polynomial.coeff_nat_trailing_degree_pred_eq_zero Polynomial.coeff_natTrailingDegree_pred_eq_zero

theorem le_trailingDegree_X_pow (n : ℕ) : (n : ℕ∞) ≤ trailingDegree (X ^ n : R[X]) := by
  simpa only [C_1, one_mul] using le_trailingDegree_C_mul_X_pow n (1 : R)
  -- 🎉 no goals
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
  -- ⊢ natTrailingDegree p ≤ min' (support p) (_ : Finset.Nonempty (support p))
  · apply le_min'
    -- ⊢ ∀ (y : ℕ), y ∈ support p → natTrailingDegree p ≤ y
    intro y hy
    -- ⊢ natTrailingDegree p ≤ y
    exact natTrailingDegree_le_of_mem_supp y hy
    -- 🎉 no goals
  · apply Finset.min'_le
    -- ⊢ natTrailingDegree p ∈ support p
    exact mem_support_iff.mpr (trailingCoeff_nonzero_iff_nonzero.mpr h)
    -- 🎉 no goals
#align polynomial.nat_trailing_degree_eq_support_min' Polynomial.natTrailingDegree_eq_support_min'

theorem le_natTrailingDegree (hp : p ≠ 0) (hn : ∀ m < n, p.coeff m = 0) :
    n ≤ p.natTrailingDegree := by
  rw [natTrailingDegree_eq_support_min' hp]
  -- ⊢ n ≤ min' (support p) (_ : Finset.Nonempty (support p))
  exact Finset.le_min' _ _ _ fun m hm => not_lt.1 fun hmn => mem_support_iff.1 hm <| hn _ hmn
  -- 🎉 no goals
#align polynomial.le_nat_trailing_degree Polynomial.le_natTrailingDegree

theorem natTrailingDegree_le_natDegree (p : R[X]) : p.natTrailingDegree ≤ p.natDegree := by
  by_cases hp : p = 0
  -- ⊢ natTrailingDegree p ≤ natDegree p
  · rw [hp, natDegree_zero, natTrailingDegree_zero]
    -- 🎉 no goals
  · exact le_natDegree_of_ne_zero (mt trailingCoeff_eq_zero.mp hp)
    -- 🎉 no goals
#align polynomial.nat_trailing_degree_le_nat_degree Polynomial.natTrailingDegree_le_natDegree

theorem natTrailingDegree_mul_X_pow {p : R[X]} (hp : p ≠ 0) (n : ℕ) :
    (p * X ^ n).natTrailingDegree = p.natTrailingDegree + n := by
  apply le_antisymm
  -- ⊢ natTrailingDegree (p * X ^ n) ≤ natTrailingDegree p + n
  · refine' natTrailingDegree_le_of_ne_zero fun h => mt trailingCoeff_eq_zero.mp hp _
    -- ⊢ trailingCoeff p = 0
    rwa [trailingCoeff, ← coeff_mul_X_pow]
    -- 🎉 no goals
  · rw [natTrailingDegree_eq_support_min' fun h => hp (mul_X_pow_eq_zero h), Finset.le_min'_iff]
    -- ⊢ ∀ (y : ℕ), y ∈ support (p * X ^ n) → natTrailingDegree p + n ≤ y
    intro y hy
    -- ⊢ natTrailingDegree p + n ≤ y
    have key : n ≤ y := by
      rw [mem_support_iff, coeff_mul_X_pow'] at hy
      exact by_contra fun h => hy (if_neg h)
    rw [mem_support_iff, coeff_mul_X_pow', if_pos key] at hy
    -- ⊢ natTrailingDegree p + n ≤ y
    exact (le_tsub_iff_right key).mp (natTrailingDegree_le_of_ne_zero hy)
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.nat_trailing_degree_mul_X_pow Polynomial.natTrailingDegree_mul_X_pow

theorem le_trailingDegree_mul : p.trailingDegree + q.trailingDegree ≤ (p * q).trailingDegree := by
  refine' Finset.le_min fun n hn => _
  -- ⊢ trailingDegree p + trailingDegree q ≤ ↑n
  rw [mem_support_iff, coeff_mul] at hn
  -- ⊢ trailingDegree p + trailingDegree q ≤ ↑n
  obtain ⟨⟨i, j⟩, hij, hpq⟩ := exists_ne_zero_of_sum_ne_zero hn
  -- ⊢ trailingDegree p + trailingDegree q ≤ ↑n
  refine'
    (add_le_add (min_le (mem_support_iff.mpr (left_ne_zero_of_mul hpq)))
          (min_le (mem_support_iff.mpr (right_ne_zero_of_mul hpq)))).trans
      (le_of_eq _)
  rwa [← WithTop.coe_add, WithTop.coe_eq_coe, ← Nat.mem_antidiagonal]
  -- 🎉 no goals
#align polynomial.le_trailing_degree_mul Polynomial.le_trailingDegree_mul

theorem le_natTrailingDegree_mul (h : p * q ≠ 0) :
    p.natTrailingDegree + q.natTrailingDegree ≤ (p * q).natTrailingDegree := by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, zero_mul])
  -- ⊢ natTrailingDegree p + natTrailingDegree q ≤ natTrailingDegree (p * q)
  have hq : q ≠ 0 := fun hq => h (by rw [hq, mul_zero])
  -- ⊢ natTrailingDegree p + natTrailingDegree q ≤ natTrailingDegree (p * q)
  -- Porting note: Needed to account for different coercion behaviour & add the lemma below
  have : ∀ (p : R[X]), WithTop.some (natTrailingDegree p) = Nat.cast (natTrailingDegree p) :=
    fun p ↦ rfl
  rw [← WithTop.coe_le_coe, WithTop.coe_add, this p, this q, this (p * q),
    ← trailingDegree_eq_natTrailingDegree hp, ← trailingDegree_eq_natTrailingDegree hq,
    ← trailingDegree_eq_natTrailingDegree h]
  exact le_trailingDegree_mul
  -- 🎉 no goals
#align polynomial.le_nat_trailing_degree_mul Polynomial.le_natTrailingDegree_mul

theorem coeff_mul_natTrailingDegree_add_natTrailingDegree : (p * q).coeff
    (p.natTrailingDegree + q.natTrailingDegree) = p.trailingCoeff * q.trailingCoeff := by
  rw [coeff_mul]
  -- ⊢ ∑ x in Nat.antidiagonal (natTrailingDegree p + natTrailingDegree q), coeff p …
  refine'
    Finset.sum_eq_single (p.natTrailingDegree, q.natTrailingDegree) _ fun h =>
      (h (Nat.mem_antidiagonal.mpr rfl)).elim
  rintro ⟨i, j⟩ h₁ h₂
  -- ⊢ coeff p (i, j).fst * coeff q (i, j).snd = 0
  rw [Nat.mem_antidiagonal] at h₁
  -- ⊢ coeff p (i, j).fst * coeff q (i, j).snd = 0
  by_cases hi : i < p.natTrailingDegree
  -- ⊢ coeff p (i, j).fst * coeff q (i, j).snd = 0
  · rw [coeff_eq_zero_of_lt_natTrailingDegree hi, zero_mul]
    -- 🎉 no goals
  by_cases hj : j < q.natTrailingDegree
  -- ⊢ coeff p (i, j).fst * coeff q (i, j).snd = 0
  · rw [coeff_eq_zero_of_lt_natTrailingDegree hj, mul_zero]
    -- 🎉 no goals
  rw [not_lt] at hi hj
  -- ⊢ coeff p (i, j).fst * coeff q (i, j).snd = 0
  refine' (h₂ (Prod.ext_iff.mpr _).symm).elim
  -- ⊢ (natTrailingDegree p, natTrailingDegree q).fst = (i, j).fst ∧ (natTrailingDe …
  exact (add_eq_add_iff_eq_and_eq hi hj).mp h₁.symm
  -- 🎉 no goals
#align polynomial.coeff_mul_nat_trailing_degree_add_nat_trailing_degree Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree

theorem trailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff ≠ 0) :
    (p * q).trailingDegree = p.trailingDegree + q.trailingDegree := by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, trailingCoeff_zero, zero_mul])
  -- ⊢ trailingDegree (p * q) = trailingDegree p + trailingDegree q
  have hq : q ≠ 0 := fun hq => h (by rw [hq, trailingCoeff_zero, mul_zero])
  -- ⊢ trailingDegree (p * q) = trailingDegree p + trailingDegree q
  refine' le_antisymm _ le_trailingDegree_mul
  -- ⊢ trailingDegree (p * q) ≤ trailingDegree p + trailingDegree q
  rw [trailingDegree_eq_natTrailingDegree hp, trailingDegree_eq_natTrailingDegree hq, ←
    ENat.coe_add]
  apply le_trailingDegree_of_ne_zero
  -- ⊢ coeff (p * q) (natTrailingDegree p + natTrailingDegree q) ≠ 0
  rwa [coeff_mul_natTrailingDegree_add_natTrailingDegree]
  -- 🎉 no goals
#align polynomial.trailing_degree_mul' Polynomial.trailingDegree_mul'

theorem natTrailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff ≠ 0) :
    (p * q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree := by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, trailingCoeff_zero, zero_mul])
  -- ⊢ natTrailingDegree (p * q) = natTrailingDegree p + natTrailingDegree q
  have hq : q ≠ 0 := fun hq => h (by rw [hq, trailingCoeff_zero, mul_zero])
  -- ⊢ natTrailingDegree (p * q) = natTrailingDegree p + natTrailingDegree q
  -- Porting note: Needed to account for different coercion behaviour & add the lemmas below
  have aux1 : ∀ n, Nat.cast n = WithTop.some (n) := fun n ↦ rfl
  -- ⊢ natTrailingDegree (p * q) = natTrailingDegree p + natTrailingDegree q
  have aux2 : ∀ (p : R[X]), WithTop.some (natTrailingDegree p) = Nat.cast (natTrailingDegree p) :=
    fun p ↦ rfl
  apply natTrailingDegree_eq_of_trailingDegree_eq_some
  -- ⊢ trailingDegree (p * q) = ↑(natTrailingDegree p + natTrailingDegree q)
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

end NonzeroSemiring

section Ring

variable [Ring R]

@[simp]
theorem trailingDegree_neg (p : R[X]) : trailingDegree (-p) = trailingDegree p := by
  unfold trailingDegree
  -- ⊢ Finset.min (support (-p)) = Finset.min (support p)
  rw [support_neg]
  -- 🎉 no goals
#align polynomial.trailing_degree_neg Polynomial.trailingDegree_neg

@[simp]
theorem natTrailingDegree_neg (p : R[X]) : natTrailingDegree (-p) = natTrailingDegree p := by
  simp [natTrailingDegree]
  -- 🎉 no goals
#align polynomial.nat_trailing_degree_neg Polynomial.natTrailingDegree_neg

@[simp]
theorem natTrailingDegree_int_cast (n : ℤ) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_int_cast, natTrailingDegree_C]
  -- 🎉 no goals
#align polynomial.nat_trailing_degree_int_cast Polynomial.natTrailingDegree_int_cast

end Ring

section Semiring

variable [Semiring R]

/-- The second-lowest coefficient, or 0 for constants -/
def nextCoeffUp (p : R[X]) : R :=
  if p.natTrailingDegree = 0 then 0 else p.coeff (p.natTrailingDegree + 1)
#align polynomial.next_coeff_up Polynomial.nextCoeffUp

@[simp]
theorem nextCoeffUp_C_eq_zero (c : R) : nextCoeffUp (C c) = 0 := by
  rw [nextCoeffUp]
  -- ⊢ (if natTrailingDegree (↑C c) = 0 then 0 else coeff (↑C c) (natTrailingDegree …
  simp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.next_coeff_up_C_eq_zero Polynomial.nextCoeffUp_C_eq_zero

theorem nextCoeffUp_of_pos_natTrailingDegree (p : R[X]) (hp : 0 < p.natTrailingDegree) :
    nextCoeffUp p = p.coeff (p.natTrailingDegree + 1) := by
  rw [nextCoeffUp, if_neg]
  -- ⊢ ¬natTrailingDegree p = 0
  contrapose! hp
  -- ⊢ natTrailingDegree p ≤ 0
  simpa
  -- 🎉 no goals
#align polynomial.next_coeff_up_of_pos_nat_trailing_degree Polynomial.nextCoeffUp_of_pos_natTrailingDegree

end Semiring

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt
    (h : trailingDegree p < trailingDegree q) : coeff q (natTrailingDegree p) = 0 :=
  coeff_eq_zero_of_trailingDegree_lt <| natTrailingDegree_le_trailingDegree.trans_lt h
#align polynomial.coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt Polynomial.coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt

theorem ne_zero_of_trailingDegree_lt {n : ℕ∞} (h : trailingDegree p < n) : p ≠ 0 := fun h₀ =>
  h.not_le (by simp [h₀])
               -- 🎉 no goals
#align polynomial.ne_zero_of_trailing_degree_lt Polynomial.ne_zero_of_trailingDegree_lt

end Semiring

end Polynomial
