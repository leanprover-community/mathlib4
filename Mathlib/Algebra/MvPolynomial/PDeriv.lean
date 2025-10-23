/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Yury Kudryashov
-/
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Partial derivatives of polynomials

This file defines the notion of the formal *partial derivative* of a polynomial,
the derivative with respect to a single variable.
This derivative is not connected to the notion of derivative from analysis.
It is based purely on the polynomial exponents and coefficients.

## Main declarations

* `MvPolynomial.pderiv i p` : the partial derivative of `p` with respect to `i`, as a bundled
  derivation of `MvPolynomial σ R`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommRing R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

-/


noncomputable section

universe u v

namespace MvPolynomial

open Set Function Finsupp

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

section PDeriv

variable [CommSemiring R]

/-- `pderiv i p` is the partial derivative of `p` with respect to `i` -/
def pderiv (i : σ) : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  letI := Classical.decEq σ
  mkDerivation R <| Pi.single i 1

theorem pderiv_def [DecidableEq σ] (i : σ) : pderiv i = mkDerivation R (Pi.single i 1) := by
  unfold pderiv; congr!

@[simp]
theorem pderiv_monomial {i : σ} :
    pderiv i (monomial s a) = monomial (s - single i 1) (a * s i) := by
  classical
  simp only [pderiv_def, mkDerivation_monomial, Finsupp.smul_sum, smul_eq_mul, ← smul_mul_assoc,
    ← (monomial _).map_smul]
  refine (Finset.sum_eq_single i (fun j _ hne => ?_) fun hi => ?_).trans ?_
  · simp [Pi.single_eq_of_ne hne]
  · rw [Finsupp.notMem_support_iff] at hi; simp [hi]
  · simp

lemma X_mul_pderiv_monomial {i : σ} {m : σ →₀ ℕ} {r : R} :
    X i * pderiv i (monomial m r) = m i • monomial m r := by
  rw [pderiv_monomial, X, monomial_mul, smul_monomial]
  by_cases h : m i = 0
  · simp_rw [h, Nat.cast_zero, mul_zero, zero_smul, monomial_zero]
  rw [one_mul, mul_comm, nsmul_eq_mul, add_comm, sub_add_single_one_cancel h]

theorem pderiv_C {i : σ} : pderiv i (C a) = 0 :=
  derivation_C _ _

theorem pderiv_one {i : σ} : pderiv i (1 : MvPolynomial σ R) = 0 := pderiv_C

@[simp]
theorem pderiv_X [DecidableEq σ] (i j : σ) :
    pderiv i (X j : MvPolynomial σ R) = Pi.single (M := fun _ => _) i 1 j := by
  rw [pderiv_def, mkDerivation_X]

@[simp]
theorem pderiv_X_self (i : σ) : pderiv i (X i : MvPolynomial σ R) = 1 := by classical simp

@[simp]
theorem pderiv_X_of_ne {i j : σ} (h : j ≠ i) : pderiv i (X j : MvPolynomial σ R) = 0 := by
  classical simp [h]

theorem pderiv_eq_zero_of_notMem_vars {i : σ} {f : MvPolynomial σ R} (h : i ∉ f.vars) :
    pderiv i f = 0 :=
  derivation_eq_zero_of_forall_mem_vars fun _ hj => pderiv_X_of_ne <| ne_of_mem_of_not_mem hj h

@[deprecated (since := "2025-05-23")]
alias pderiv_eq_zero_of_not_mem_vars := pderiv_eq_zero_of_notMem_vars

theorem pderiv_monomial_single {i : σ} {n : ℕ} : pderiv i (monomial (single i n) a) =
    monomial (single i (n - 1)) (a * n) := by simp

theorem pderiv_mul {i : σ} {f g : MvPolynomial σ R} :
    pderiv i (f * g) = pderiv i f * g + f * pderiv i g := by
  simp only [(pderiv i).leibniz f g, smul_eq_mul, mul_comm, add_comm]

theorem pderiv_pow {i : σ} {f : MvPolynomial σ R} {n : ℕ} :
    pderiv i (f ^ n) = n * f ^ (n - 1) * pderiv i f := by
  rw [(pderiv i).leibniz_pow f n, nsmul_eq_mul, smul_eq_mul, mul_assoc]

theorem pderiv_C_mul {f : MvPolynomial σ R} {i : σ} : pderiv i (C a * f) = C a * pderiv i f := by
  rw [C_mul', Derivation.map_smul, C_mul']

theorem pderiv_map {S} [CommSemiring S] {φ : R →+* S} {f : MvPolynomial σ R} {i : σ} :
    pderiv i (map φ f) = map φ (pderiv i f) := by
  apply induction_on f (fun r ↦ by simp) (fun p q hp hq ↦ by simp [hp, hq]) fun p j eq ↦ ?_
  obtain rfl | h := eq_or_ne j i
  · simp [eq]
  · simp [eq, h]

lemma pderiv_rename {τ : Type*} {f : σ → τ} (hf : Function.Injective f)
    (x : σ) (p : MvPolynomial σ R) :
    pderiv (f x) (rename f p) = rename f (pderiv x p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p a h =>
    simp only [map_mul, MvPolynomial.rename_X, Derivation.leibniz, MvPolynomial.pderiv_X,
      Pi.single_apply, hf.eq_iff, smul_eq_mul, mul_ite, mul_one, mul_zero, h, map_add]
    split_ifs <;> simp

lemma aeval_sumElim_pderiv_inl {S τ : Type*} [CommRing S] [Algebra R S]
    (p : MvPolynomial (σ ⊕ τ) R) (f : τ → S) (j : σ) :
    aeval (Sum.elim X (C ∘ f)) ((pderiv (Sum.inl j)) p) =
      (pderiv j) ((aeval (Sum.elim X (C ∘ f))) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q h =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X, h]
    cases q <;> simp [Pi.single_apply]

end PDeriv

end MvPolynomial
