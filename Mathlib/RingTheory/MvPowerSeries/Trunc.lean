/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!

# Formal (multivariate) power series - Truncation

* `MvPowerSeries.trunc n φ` truncates a formal multivariate power series
  to the multivariate polynomial that has the same coefficients as `φ`,
  for all `m < n`, and `0` otherwise.

  Note that here, `m` and `n` have types `σ →₀ ℕ`,
  so that `m < n` means that `m ≠ n` and `m s ≤ n s` for all `s : σ`.

* `MvPowerSeries.trunc_one` : truncation of the unit power series

* `MvPowerSeries.trunc_C` : truncation of a constant

* `MvPowerSeries.trunc_C_mul` : truncation of constant multiple.

* `MvPowerSeries.trunc' n φ` truncates a formal multivariate power series
  to the multivariate polynomial that has the same coefficients as `φ`,
  for all `m ≤ n`, and `0` otherwise.

  Here, `m` and `n`  have types `σ →₀ ℕ` so that `m ≤ n` means that `m s ≤ n s` for all `s : σ`.


* `MvPowerSeries.coeff_mul_eq_coeff_trunc'_mul_trunc'` : compares the coefficients
  of a product with those of the product of truncations.

* `MvPowerSeries.trunc'_one` : truncation of the unit power series.

* `MvPowerSeries.trunc'_C` : truncation of a constant.

* `MvPowerSeries.trunc'_C_mul` : truncation of a constant multiple.

* `MvPowerSeries.trunc'_map` : image of a truncation under a change of rings

## TODO

* Unify both versions using a general purpose API

-/

@[expose] public section


noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp

variable {σ R S : Type*}

section TruncLT

variable [DecidableEq σ] [CommSemiring R] (n : σ →₀ ℕ)

/-- Auxiliary definition for the truncation function. -/
def truncFun (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m ∈ Finset.Iio n, MvPolynomial.monomial m (coeff m φ)

theorem coeff_truncFun (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncFun n φ).coeff m = if m < n then coeff m φ else 0 := by
  classical
  simp [truncFun, MvPolynomial.coeff_sum]

variable (R) in
/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function from `σ`
to the naturals, then `trunc' R n f` is the multivariable power series obtained from `f`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `a i ≤ n i` for all `i`
and `a i < n i` for some `i`. -/
def trunc : MvPowerSeries σ R →+ MvPolynomial σ R where
  toFun := truncFun n
  map_zero' := by
    classical
    ext
    simp [coeff_truncFun]
  map_add' := by
    classical
    intro x y
    ext m
    simp only [coeff_truncFun, MvPolynomial.coeff_add, ite_add_ite, ← map_add, add_zero]

theorem coeff_trunc (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc R n φ).coeff m = if m < n then coeff m φ else 0 := by
  classical simp [trunc, coeff_truncFun]

@[simp]
theorem trunc_one (n : σ →₀ ℕ) (hnn : n ≠ 0) : trunc R n 1 = 1 :=
  MvPolynomial.ext _ _ fun m ↦ by
    classical
    rw [coeff_trunc, coeff_one]
    split_ifs with H H'
    · subst m
      simp
    · symm
      rw [MvPolynomial.coeff_one]
      exact if_neg (Ne.symm H')
    · symm
      rw [MvPolynomial.coeff_one]
      refine if_neg ?_
      rintro rfl
      apply H
      exact Ne.bot_lt hnn

@[simp]
theorem trunc_C (n : σ →₀ ℕ) (hnn : n ≠ 0) (a : R) : trunc R n (C a) = MvPolynomial.C a :=
  MvPolynomial.ext _ _ fun m ↦ by
    classical
    rw [coeff_trunc, coeff_C, MvPolynomial.coeff_C]
    split_ifs with H <;> first | rfl | try simp_all only [ne_eq, not_true_eq_false]
    exfalso; apply H; subst m; exact Ne.bot_lt hnn

@[simp]
theorem trunc_C_mul (n : σ →₀ ℕ) (a : R) (p : MvPowerSeries σ R) :
    trunc R n (C a * p) = MvPolynomial.C a * trunc R n p := by
  ext m; simp [coeff_trunc]

@[simp]
theorem trunc_map [CommSemiring S] (n : σ →₀ ℕ) (f : R →+* S) (p : MvPowerSeries σ R) :
    trunc S n (map f p) = MvPolynomial.map f (trunc R n p) := by
  ext m; simp [coeff_trunc, MvPolynomial.coeff_map, apply_ite f]

end TruncLT

section TruncLE

variable [DecidableEq σ] [CommSemiring R] (n : σ →₀ ℕ)

/-- Auxiliary definition for the truncation function. -/
def truncFun' (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m ∈ Finset.Iic n, MvPolynomial.monomial m (coeff m φ)

/-- Coefficients of the truncated function. -/
theorem coeff_truncFun' (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncFun' n φ).coeff m = if m ≤ n then coeff m φ else 0 := by
  classical
  simp [truncFun', MvPolynomial.coeff_sum]

variable (R) in
/--
The `n`th truncation of a multivariate formal power series to a multivariate polynomial.

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function from `σ`
to the naturals, then `trunc' R n f` is the multivariable power series obtained from `f`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `a i ≤ n i` for all `i`. -/
def trunc' : MvPowerSeries σ R →+ MvPolynomial σ R where
  toFun := truncFun' n
  map_zero' := by
    ext
    simp only [coeff_truncFun', map_zero, ite_self, MvPolynomial.coeff_zero]
  map_add' x y := by
    ext m
    simp only [coeff_truncFun', MvPolynomial.coeff_add]
    rw [ite_add_ite, ← map_add, zero_add]

/-- Coefficients of the truncation of a multivariate power series. -/
theorem coeff_trunc' (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc' R n φ).coeff m = if m ≤ n then coeff m φ else 0 :=
  coeff_truncFun' n m φ

theorem trunc'_trunc' {n m : σ →₀ ℕ} (h : n ≤ m) (φ : MvPowerSeries σ R) :
    trunc' R n (trunc' R m φ) = trunc' R n φ := by
  ext d
  by_cases hd : d ≤ n
  · symm
    simp only [coeff_trunc', if_pos hd, MvPolynomial.coeff_coe, left_eq_ite_iff]
    intro h'
    have : d ≤ m := .trans hd h
    contradiction
  · simp [coeff_trunc', if_neg hd]

/-- Truncation of the multivariate power series `1` -/
@[simp]
theorem trunc'_one (n : σ →₀ ℕ) : trunc' R n 1 = 1 :=
  MvPolynomial.ext _ _ fun m ↦ by
    classical
    rw [coeff_trunc', coeff_one]
    split_ifs with H H'
    · subst m; simp only [MvPolynomial.coeff_zero_one]
    · rw [MvPolynomial.coeff_one, if_neg (Ne.symm H')]
    · rw [MvPolynomial.coeff_one, if_neg ?_]
      rintro rfl
      exact H (zero_le n)

@[simp]
theorem trunc'_C (n : σ →₀ ℕ) (a : R) :
    trunc' R n (C a) = MvPolynomial.C a :=
  MvPolynomial.ext _ _ fun m ↦ by
    classical
    rw [coeff_trunc', coeff_C, MvPolynomial.coeff_C]
    split_ifs with H <;> first | rfl | try simp_all
    exfalso; apply H; subst m; exact zero_le n

/-- Coefficients of the truncation of a product of two multivariate power series -/
theorem coeff_mul_eq_coeff_trunc'_mul_trunc' (n : σ →₀ ℕ)
    (f g : MvPowerSeries σ R) {m : σ →₀ ℕ} (h : m ≤ n) :
    coeff m (f * g) = (trunc' R n f * trunc' R n g).coeff m := by
  classical
  simp only [MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  simp only [mem_antidiagonal] at hij
  rw [← hij] at h
  simp only
  apply congr_arg₂
  · rw [coeff_trunc', if_pos (le_trans le_self_add h)]
  · rw [coeff_trunc', if_pos (le_trans le_add_self h)]

theorem trunc'_trunc'_pow {n : σ →₀ ℕ} {k : ℕ} (hk : 1 ≤ k) (φ : MvPowerSeries σ R) :
    trunc' R n ((trunc' R n φ) ^ k) = trunc' R n (φ ^ k) := by
  induction k, hk using Nat.le_induction with
  | base => simp [trunc'_trunc']
  | succ m h_le ih =>
    ext d
    by_cases hd : d ≤ n
    · rw [coeff_trunc', if_pos hd, pow_succ, pow_succ, coeff_mul_eq_coeff_trunc'_mul_trunc' n _ _
        hd, ih, coeff_trunc', if_pos hd, MvPolynomial.coeff_mul, coeff_mul, Finset.sum_congr rfl]
      intro x hx
      have le_aux₁ : x.1 ≤ n := .trans (Finset.mem_antidiagonal.mp hx ▸ self_le_add_right _ _) hd
      have le_aux₂ : x.2 ≤ n := .trans (Finset.mem_antidiagonal.mp hx ▸ self_le_add_left _ _) hd
      simp [coeff_trunc', if_pos le_aux₁, coeff_trunc', if_pos le_aux₂]
    simp [coeff_trunc', if_neg hd]

@[simp]
theorem trunc'_C_mul (n : σ →₀ ℕ) (a : R) (p : MvPowerSeries σ R) :
    trunc' R n (C a * p) = MvPolynomial.C a * trunc' R n p := by
  ext m; simp [coeff_trunc']

@[simp]
theorem trunc'_map [CommSemiring S] (n : σ →₀ ℕ) (f : R →+* S) (p : MvPowerSeries σ R) :
    trunc' S n (map f p) = MvPolynomial.map f (trunc' R n p) := by
  ext m; simp [coeff_trunc', MvPolynomial.coeff_map, apply_ite f]

section

theorem totalDegree_trunc' {n : σ →₀ ℕ} (φ : MvPowerSeries σ R) :
    (trunc' R n φ).totalDegree ≤ n.degree := by
  have supp_aux : (trunc' R n φ).support ⊆ (Set.Icc 0 n).toFinset := fun d hd => by
    simp only [Set.toFinset_Icc, Finset.mem_Icc, zero_le, true_and]
    by_contra hc
    simp [coeff_trunc', if_neg hc] at hd
  have : Finsupp.degree n = (Set.Icc 0 n).toFinset.sup fun s ↦ s.sum fun x e ↦ e := by
    refine eq_of_le_of_ge (Finset.le_sup (by simp)) ?_
    · simp only [Set.toFinset_Icc, Finset.sup_le_iff, Finset.mem_Icc, zero_le, true_and]
      intro b hb
      simp only [Finsupp.degree, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.sum]
      exact .trans (Finset.sum_le_sum_of_subset (b.support_mono hb))
        (Finset.sum_le_sum fun i _ => hb i)
  rw [MvPolynomial.totalDegree, this]
  exact Finset.sup_mono supp_aux

theorem ext_trunc' {f g : MvPowerSeries σ R} : f = g ↔ ∀ n, trunc' R n f = trunc' R n g := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  ext n
  specialize h n
  have {f' : MvPowerSeries σ R} : f'.coeff n = (trunc' R n f').coeff n := by
    rw [coeff_trunc', if_pos le_rfl]
  simp_rw [this, h]

open Filter in
theorem eq_iff_frequently_trunc'_eq {f g : MvPowerSeries σ R} :
    f = g ↔ ∃ᶠ m in atTop, trunc' R m f = trunc' R m g := by
  refine ⟨fun h => by simp [h, atTop_neBot], fun h => ?_⟩
  ext n
  obtain ⟨m, hm₁, hm₂⟩ := h.forall_exists_of_atTop n
  have {f' : MvPowerSeries σ R} : f'.coeff n = (trunc' R m f').coeff n := by
    rw [coeff_trunc', if_pos hm₁]
  simp [this, hm₂]

end

end TruncLE

end MvPowerSeries

end
