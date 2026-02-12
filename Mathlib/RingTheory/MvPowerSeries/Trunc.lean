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

* `MvPowerSeries.truncFinset s p` restricts the support of a multivariate power series `p`
  to a finite set of monomials and obtains a multivariate polynomial.

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

-/

@[expose] public section


noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp

variable {σ R S : Type*}

section TruncFinset

variable [CommSemiring R] (s : Finset (σ →₀ ℕ))

variable (R) in
/-- Restrict the support of a multivariate power series to a finite set of monomials and
obtain a multivariate polynomial. -/
def truncFinset : MvPowerSeries σ R →ₗ[R] MvPolynomial σ R where
  toFun p := ∑ x ∈ s, MvPolynomial.monomial x (p.coeff x)
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by
    classical
    ext; simp [MvPolynomial.coeff_sum]

theorem truncFinset_apply (p : MvPowerSeries σ R) :
    truncFinset R s p = ∑ x ∈ s, MvPolynomial.monomial x (p.coeff x) := by rfl

theorem coeff_truncFinset {x : σ →₀ ℕ} (p : MvPowerSeries σ R) (h : x ∈ s) :
    (truncFinset R s p).coeff x = p.coeff x := by
  classical
  simp [truncFinset_apply, MvPolynomial.coeff_sum]
  aesop

theorem coeff_truncFinset_eq_zero {x : σ →₀ ℕ} (p : MvPowerSeries σ R) (h : x ∉ s) :
    (truncFinset R s p).coeff x = 0 := by
  classical
  simp [truncFinset_apply, MvPolynomial.coeff_sum]
  aesop

theorem truncFinset_monomial {x : σ →₀ ℕ} (r : R) (h : x ∈ s) :
    truncFinset R s (monomial x r) = MvPolynomial.monomial x r := by
  classical
  ext y; by_cases hy : y ∈ s
  · rw [coeff_truncFinset _ _ hy, coeff_monomial, MvPolynomial.coeff_monomial]
    simp [eq_comm]
  rw [coeff_truncFinset_eq_zero _ _ hy, MvPolynomial.coeff_monomial, if_neg (by aesop)]

theorem truncFinset_monomial_eq_zero {x : σ →₀ ℕ} (r : R) (h : x ∉ s) :
    truncFinset R s (monomial x r) = 0 := by
  classical
  ext; simp [truncFinset, MvPolynomial.coeff_sum, coeff_monomial]
  aesop

theorem truncFinset_C (h : 0 ∈ s) (r : R) : truncFinset R s (C r) = MvPolynomial.C r :=
  truncFinset_monomial s r h

theorem truncFinset_one (h : 0 ∈ s) : truncFinset R s (1 : MvPowerSeries σ R) = 1 :=
  truncFinset_C s h 1

variable {s} in
theorem truncFinset_truncFinset {t : Finset (σ →₀ ℕ)} (h : s ⊆ t) (p : MvPowerSeries σ R) :
    truncFinset R s (truncFinset R t p) = truncFinset R s p := by
  ext x; by_cases hx : x ∈ s
  · rw [coeff_truncFinset _ _ hx, coeff_truncFinset _ _ hx, MvPolynomial.coeff_coe,
      coeff_truncFinset _ _ (h hx)]
  rw [coeff_truncFinset_eq_zero _ _ hx, coeff_truncFinset_eq_zero _ _ hx]

theorem truncFinset_map [CommSemiring S] (f : R →+* S) (p : MvPowerSeries σ R) :
    truncFinset S s (map f p) = MvPolynomial.map f (truncFinset R s p) := by
  ext x; by_cases hx : x ∈ s
  · simp [coeff_map, MvPolynomial.coeff_map, coeff_truncFinset _ _ hx]
  simp [MvPolynomial.coeff_map, coeff_truncFinset_eq_zero _ _ hx]

variable {s} in
theorem coeff_mul_eq_coeff_truncFinset_mul_truncFinset (hs : IsLowerSet (SetLike.coe s))
    {x : σ →₀ ℕ} (f g : MvPowerSeries σ R) (hx : x ∈ s) : coeff x (f * g) =
      (truncFinset R s f * truncFinset R s g).coeff x := by
  classical
  simp only [MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  simp only [mem_antidiagonal] at hij
  rw [coeff_truncFinset _ _ (hs (show i ≤ x by simp [← hij]) hx),
    coeff_truncFinset _ _ (hs (show j ≤ x by simp [← hij]) hx)]

theorem truncFinset_truncFinset_pow (hs : IsLowerSet (SetLike.coe s)) {k : ℕ} (hk : 1 ≤ k)
    (p : MvPowerSeries σ R) : truncFinset R s ((truncFinset R s p) ^ k) =
      truncFinset R s (p ^ k) := by
  induction k, hk using Nat.le_induction with
  | base => simp [truncFinset_truncFinset]
  | succ n hmn ih =>
    ext x; by_cases hx : x ∈ s
    · rw [coeff_truncFinset _ _ hx, coeff_truncFinset _ _ hx, pow_succ,
        coeff_mul_eq_coeff_truncFinset_mul_truncFinset hs _ _ hx, ih,
        truncFinset_truncFinset (by rfl), pow_succ,
        coeff_mul_eq_coeff_truncFinset_mul_truncFinset hs _ _ hx]
    simp [coeff_truncFinset_eq_zero _ _ hx]

theorem support_truncFinset_subset (p : MvPowerSeries σ R) : (truncFinset R s p).support ⊆ s := by
  intro; contrapose!
  simpa using coeff_truncFinset_eq_zero s p

end TruncFinset

section TruncLT

variable [DecidableEq σ] [CommSemiring R] (n : σ →₀ ℕ)

variable (R) in
/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function from `σ`
to the naturals, then `trunc' R n f` is the multivariable polynomial obtained from `f`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `a i ≤ n i` for all `i`
and `a i < n i` for some `i`. -/
def trunc : MvPowerSeries σ R →ₗ[R] MvPolynomial σ R := truncFinset R (Finset.Iio n)

theorem coeff_trunc (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc R n φ).coeff m = if m < n then coeff m φ else 0 := by
  classical split
  · exact coeff_truncFinset (Finset.Iio n) φ (by aesop)
  exact coeff_truncFinset_eq_zero (Finset.Iio n) φ (by aesop)

@[simp]
theorem trunc_one (n : σ →₀ ℕ) (hnn : n ≠ 0) : trunc R n 1 = 1 :=
  truncFinset_one (Finset.Iio n) (by simpa using pos_of_ne_zero hnn)

@[simp]
theorem trunc_C (n : σ →₀ ℕ) (hnn : n ≠ 0) (a : R) : trunc R n (C a) = MvPolynomial.C a :=
  truncFinset_C (Finset.Iio n) (by simpa using pos_of_ne_zero hnn) a

@[simp]
theorem trunc_C_mul (n : σ →₀ ℕ) (a : R) (p : MvPowerSeries σ R) :
    trunc R n (C a * p) = MvPolynomial.C a * trunc R n p := by
  ext m; simp [coeff_trunc]

@[simp]
theorem trunc_map [CommSemiring S] (n : σ →₀ ℕ) (f : R →+* S) (p : MvPowerSeries σ R) :
    trunc S n (map f p) = MvPolynomial.map f (trunc R n p) := truncFinset_map (Finset.Iio n) f p

end TruncLT

section TruncLE

variable [DecidableEq σ] [CommSemiring R] (n : σ →₀ ℕ)

variable (R) in
/--
The `n`th truncation of a multivariate formal power series to a multivariate polynomial.

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function from `σ`
to the naturals, then `trunc' R n f` is the multivariable polynomial obtained from `f`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `a i ≤ n i` for all `i`. -/
def trunc' : MvPowerSeries σ R →ₗ[R] MvPolynomial σ R := truncFinset R (Finset.Iic n)

/-- Coefficients of the truncation of a multivariate power series. -/
theorem coeff_trunc' (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc' R n φ).coeff m = if m ≤ n then coeff m φ else 0 := by
  classical split
  · exact coeff_truncFinset (Finset.Iic n) φ (by aesop)
  exact coeff_truncFinset_eq_zero (Finset.Iic n) φ (by aesop)

theorem trunc'_trunc' {n m : σ →₀ ℕ} (h : n ≤ m) (φ : MvPowerSeries σ R) :
    trunc' R n (trunc' R m φ) = trunc' R n φ :=
  truncFinset_truncFinset (Finset.Iic_subset_Iic.mpr h) φ

/-- Truncation of the multivariate power series `1` -/
@[simp]
theorem trunc'_one (n : σ →₀ ℕ) : trunc' R n 1 = 1 := truncFinset_one (Finset.Iic n) (by simp)

@[simp]
theorem trunc'_C (n : σ →₀ ℕ) (a : R) : trunc' R n (C a) = MvPolynomial.C a :=
  truncFinset_C (Finset.Iic n) (by simp) a

/-- Coefficients of the truncation of a product of two multivariate power series -/
theorem coeff_mul_eq_coeff_trunc'_mul_trunc' (n : σ →₀ ℕ)
    (f g : MvPowerSeries σ R) {m : σ →₀ ℕ} (h : m ≤ n) :
    coeff m (f * g) = (trunc' R n f * trunc' R n g).coeff m :=
  coeff_mul_eq_coeff_truncFinset_mul_truncFinset (by intro; grind) f g (by simpa)

theorem trunc'_trunc'_pow {n : σ →₀ ℕ} {k : ℕ} (hk : 1 ≤ k) (φ : MvPowerSeries σ R) :
    trunc' R n ((trunc' R n φ) ^ k) = trunc' R n (φ ^ k) :=
  truncFinset_truncFinset_pow (Finset.Iic n) (by intro; grind) hk φ

@[simp]
theorem trunc'_C_mul (n : σ →₀ ℕ) (a : R) (p : MvPowerSeries σ R) :
    trunc' R n (C a * p) = MvPolynomial.C a * trunc' R n p := by
  ext m; simp [coeff_trunc']

@[simp]
theorem trunc'_map [CommSemiring S] (n : σ →₀ ℕ) (f : R →+* S) (p : MvPowerSeries σ R) :
    trunc' S n (map f p) = MvPolynomial.map f (trunc' R n p) := truncFinset_map (Finset.Iic n) f p

section

theorem totalDegree_trunc' {n : σ →₀ ℕ} (φ : MvPowerSeries σ R) :
    (trunc' R n φ).totalDegree ≤ n.degree := by
  have supp_aux : (trunc' R n φ).support ⊆ Finset.Iic n := support_truncFinset_subset ..
  have : n.degree = (Finset.Iic n).sup fun s ↦ s.sum fun x e ↦ e := by
    refine le_antisymm (Finset.le_sup (by simp)) (Finset.sup_le_iff.mpr fun b hb ↦ ?_)
    · rw [Finset.mem_Iic] at hb
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
