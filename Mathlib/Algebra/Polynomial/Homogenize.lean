/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Finsupp.Notation
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogenize a univariate polynomial

In this file we define a function `Polynomial.homogenize p n`
that takes a polynomial `p` and a natural number `n`
and returns a homogeneous bivariate polynomial of degree `n`.

If `n` is at least the degree of `p`, then `(homogenize p n).eval ![x, 1] = p.eval x`.

We use `MvPolynomial (Fin 2) R` to represent bivariate polynomials
instead of `R[X][Y]` (i.e., `Polynomial (Polynomial R)`),
because Mathlib has a theory about homogeneous multivariate polynomials,
but not about homogeneous bivariate polynomials encoded as `R[X][Y]`.
-/

open Finset

namespace Polynomial

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- Given a polynomial `p` and a number `n ≥ natDegree p`,
returns a homogeneous bivariate polynomial `q` of degree `n` such that `q(x, 1) = p(x)`.

It is defined as `∑ k + l = n, a_k X_0^k X_1^l`, where `a_k` is the `k`th coefficient of `p`. -/
noncomputable def homogenize (p : R[X]) (n : ℕ) : MvPolynomial (Fin 2) R :=
  ∑ kl ∈ antidiagonal n, .monomial (fun₀ | 0 => kl.1 | 1 => kl.2) (p.coeff kl.1)

@[simp]
lemma homogenize_zero (n : ℕ) : homogenize (0 : R[X]) n = 0 := by
  simp [homogenize]

@[simp]
lemma homogenize_add (p q : R[X]) (n : ℕ) :
    homogenize (p + q) n = homogenize p n + homogenize q n := by
  simp [homogenize, Finset.sum_add_distrib]

@[simp]
lemma homogenize_smul {S : Type*} [Semiring S] [Module S R] (c : S) (p : R[X]) (n : ℕ) :
    homogenize (c • p) n = c • homogenize p n := by
  simp [homogenize, Finset.smul_sum, MvPolynomial.smul_monomial]

/-- `homogenize` as a bundled linear map. -/
@[simps]
noncomputable def homogenizeLM (n : ℕ) : R[X] →ₗ[R] MvPolynomial (Fin 2) R where
  toFun p := homogenize p n
  map_add' := (homogenize_add · · n)
  map_smul' := (homogenize_smul · · n)

@[simp]
lemma homogenize_finsetSum {ι : Type*} (s : Finset ι) (p : ι → R[X]) (n : ℕ) :
    homogenize (∑ i ∈ s, p i) n = ∑ i ∈ s, homogenize (p i) n :=
  _root_.map_sum (homogenizeLM n) p s

lemma homogenize_map {S : Type*} [CommSemiring S] (f : R →+* S) (p : R[X]) (n : ℕ) :
    homogenize (p.map f) n = MvPolynomial.map f (homogenize p n) := by
  simp [homogenize]

@[simp]
lemma homogenize_C_mul (c : R) (p : R[X]) (n : ℕ) :
    homogenize (C c * p) n = .C c * homogenize p n := by
  simp only [C_mul', homogenize_smul, MvPolynomial.C_mul']

@[simp]
lemma homogenize_monomial {m n : ℕ} (h : m ≤ n) (r : R) :
    homogenize (monomial m r) n = .monomial (fun₀ | 0 => m | 1 => n - m) r := by
  rw [homogenize, Finset.sum_eq_single (a := (m, n - m))]
  · simp
  · aesop (add simp coeff_monomial)
  · simp [h]

lemma homogenize_monomial_of_lt {m n : ℕ} (h : n < m) (r : R) :
    homogenize (monomial m r) n = 0 := by
  rw [homogenize]
  apply Finset.sum_eq_zero
  aesop (add simp coeff_monomial)

@[simp]
lemma homogenize_X_pow {m n : ℕ} (h : m ≤ n) :
    homogenize (X ^ m : R[X]) n = .X 0 ^ m * .X 1 ^ (n - m) := by
  rw [X_pow_eq_monomial, homogenize_monomial h, Finsupp.update_eq_add_single (by simp),
    MvPolynomial.monomial_single_add, ← MvPolynomial.X_pow_eq_monomial]

@[simp]
lemma homogenize_X {n : ℕ} (hn : n ≠ 0) : homogenize (X : R[X]) n = .X 0 * .X 1 ^ (n - 1) := by
  rw [← pow_one X, homogenize_X_pow, pow_one]
  rwa [Nat.one_le_iff_ne_zero]

@[simp]
lemma homogenize_C (c : R) (n : ℕ) : homogenize (.C c) n = .C c * .X 1 ^ n := by
  simpa [MvPolynomial.C_mul_X_pow_eq_monomial] using homogenize_monomial (Nat.zero_le n) c

@[simp]
lemma homogenize_one (n : ℕ) : homogenize (1 : R[X]) n = .X 1 ^ n := by
  simpa using homogenize_C (1 : R) n

lemma coeff_homogenize (p : R[X]) (n : ℕ) (m : Fin 2 →₀ ℕ) :
    (homogenize p n).coeff m = if m 0 + m 1 = n then coeff p (m 0) else 0 := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp [*, ite_add_ite]
  | monomial k c =>
    rcases le_or_gt k n with hkn | hnk
    · rw [homogenize_monomial hkn, coeff_monomial, MvPolynomial.coeff_monomial]
      have : (fun₀ | 0 => m 0 | 1 => m 1) = m := by ext i; fin_cases i <;> simp
      aesop
    · aesop (add simp homogenize_monomial_of_lt) (add simp coeff_monomial)

lemma eval₂_homogenize_of_eq_one {S : Type*} [CommSemiring S] {p : R[X]} {n : ℕ}
    (hn : natDegree p ≤ n) (f : R →+* S) (g : Fin 2 → S) (hg : g 1 = 1) :
    MvPolynomial.eval₂ f g (p.homogenize n) = p.eval₂ f (g 0) := by
  apply Polynomial.induction_with_natDegree_le
    (fun p ↦ MvPolynomial.eval₂ f g (p.homogenize n) = p.eval₂ f (g 0)) (N := n)
  · simp
  · simp +contextual [hg]
  · simp +contextual
  · assumption

lemma aeval_homogenize_of_eq_one {A : Type*} [CommSemiring A] [Algebra R A] {p : R[X]} {n : ℕ}
    (hn : natDegree p ≤ n) (g : Fin 2 → A) (hg : g 1 = 1) :
    MvPolynomial.aeval g (p.homogenize n) = aeval (g 0) p := by
  apply eval₂_homogenize_of_eq_one <;> assumption

/-- If `deg p ≤ n`, then `homogenize p n (x, 1) = p x`. -/
@[simp]
lemma aeval_homogenize_X_one (p : R[X]) {n : ℕ} (hn : natDegree p ≤ n) :
    MvPolynomial.aeval ![X, 1] (p.homogenize n) = p := by
  rw [aeval_homogenize_of_eq_one] <;> simp [*]

@[simp]
lemma isHomogeneous_homogenize {n : ℕ} (p : R[X]) : (p.homogenize n).IsHomogeneous n := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ ?_
  simp only [Prod.forall, mem_antidiagonal]
  rintro a b rfl
  apply MvPolynomial.isHomogeneous_monomial
  simp [Finsupp.update_eq_add_single]

lemma homogenize_eq_of_isHomogeneous {p : R[X]} {n : ℕ} {q : MvPolynomial (Fin 2) R}
    (hq : q.IsHomogeneous n) (hpq : MvPolynomial.aeval ![X, 1] q = p) :
    p.homogenize n = q := by
  subst p
  rw [q.as_sum]
  simp only [MvPolynomial.aeval_sum, MvPolynomial.aeval_monomial, ← C_eq_algebraMap,
    homogenize_finsetSum, homogenize_C_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [MvPolynomial.monomial_eq]
  congr 1
  obtain rfl : m.weight 1 = n := hq <| by simpa using hm
  simp [Finsupp.prod_fintype, Finsupp.weight_apply, Finsupp.sum_fintype, Fin.prod_univ_two,
    Fin.sum_univ_two]

lemma homogenize_mul (p q : R[X]) {m n : ℕ} (hm : natDegree p ≤ m) (hn : natDegree q ≤ n) :
    homogenize (p * q) (m + n) = homogenize p m * homogenize q n := by
  apply homogenize_eq_of_isHomogeneous
  · apply_rules [MvPolynomial.IsHomogeneous.mul, isHomogeneous_homogenize]
  · simp [*]

lemma homogenize_finsetProd {ι : Type*} {s : Finset ι} {p : ι → R[X]} {n : ι → ℕ}
    (h : ∀ i ∈ s, (p i).natDegree ≤ n i) :
    homogenize (∏ i ∈ s, p i) (∑ i ∈ s, n i) = ∏ i ∈ s, homogenize (p i) (n i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ihs =>
    simp only [prod_cons, sum_cons, forall_mem_cons] at *
    rw [homogenize_mul _ _ h.1, ihs h.2]
    exact (natDegree_prod_le _ _).trans (sum_le_sum h.2)

lemma homogenize_dvd [NoZeroDivisors R] {p q : R[X]} (h : p ∣ q) :
    homogenize p p.natDegree ∣ homogenize q q.natDegree := by
  rcases h with ⟨r, rfl⟩
  obtain rfl | rfl | ⟨hp₀, hr₀⟩ : p = 0 ∨ r = 0 ∨ p ≠ 0 ∧ r ≠ 0 := by tauto
  · simp
  · simp
  · rw [natDegree_mul hp₀ hr₀, homogenize_mul _ _ le_rfl le_rfl]
    apply dvd_mul_right

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

@[simp]
lemma homogenize_neg (p : R[X]) (n : ℕ) : (-p).homogenize n = -p.homogenize n :=
  map_neg (homogenizeLM n) p

@[simp]
lemma homogenize_sub (p q : R[X]) (n : ℕ) :
    (p - q).homogenize n = p.homogenize n - q.homogenize n :=
  map_sub (homogenizeLM n) p q

end CommRing

variable {K : Type*} [Semifield K]

lemma eval_homogenize {p : K[X]} {n : ℕ} (hn : p.natDegree ≤ n) (x : Fin 2 → K) (hx : x 1 ≠ 0) :
    MvPolynomial.eval x (p.homogenize n) = p.eval (x 0 / x 1) * x 1 ^ n := by
  simp only [homogenize, Polynomial.eval_eq_sum_range' (Nat.lt_succ.mpr hn),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [MvPolynomial.eval_monomial, Finsupp.update_eq_add_single, Finsupp.prod_add_index',
    Finsupp.prod_single_index, Finsupp.prod_single_index, pow_sub₀]
  · ring
  all_goals simp_all [pow_add, Nat.lt_add_one_iff]

end Polynomial
