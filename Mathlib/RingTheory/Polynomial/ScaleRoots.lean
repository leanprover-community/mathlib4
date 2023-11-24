/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Devon Tuma
-/
import Mathlib.RingTheory.NonZeroDivisors
import Mathlib.Data.Polynomial.AlgebraMap

#align_import ring_theory.polynomial.scale_roots from "leanprover-community/mathlib"@"40ac1b258344e0c2b4568dc37bfad937ec35a727"

/-!
# Scaling the roots of a polynomial

This file defines `scaleRoots p s` for a polynomial `p` in one variable and a ring element `s` to
be the polynomial with root `r * s` for each root `r` of `p` and proves some basic results about it.
-/


variable {R S A K : Type*}

namespace Polynomial

open BigOperators Polynomial

section Semiring

variable [Semiring R] [Semiring S]

/-- `scaleRoots p s` is a polynomial with root `r * s` for each root `r` of `p`. -/
noncomputable def scaleRoots (p : R[X]) (s : R) : R[X] :=
  ∑ i in p.support, monomial i (p.coeff i * s ^ (p.natDegree - i))
#align polynomial.scale_roots Polynomial.scaleRoots

@[simp]
theorem coeff_scaleRoots (p : R[X]) (s : R) (i : ℕ) :
    (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i) := by
  simp (config := { contextual := true }) [scaleRoots, coeff_monomial]
#align polynomial.coeff_scale_roots Polynomial.coeff_scaleRoots

theorem coeff_scaleRoots_natDegree (p : R[X]) (s : R) :
    (scaleRoots p s).coeff p.natDegree = p.leadingCoeff := by
  rw [leadingCoeff, coeff_scaleRoots, tsub_self, pow_zero, mul_one]
#align polynomial.coeff_scale_roots_nat_degree Polynomial.coeff_scaleRoots_natDegree

@[simp]
theorem zero_scaleRoots (s : R) : scaleRoots 0 s = 0 := by
  ext
  simp
#align polynomial.zero_scale_roots Polynomial.zero_scaleRoots

theorem scaleRoots_ne_zero {p : R[X]} (hp : p ≠ 0) (s : R) : scaleRoots p s ≠ 0 := by
  intro h
  have : p.coeff p.natDegree ≠ 0 := mt leadingCoeff_eq_zero.mp hp
  have : (scaleRoots p s).coeff p.natDegree = 0 :=
    congr_fun (congr_arg (coeff : R[X] → ℕ → R) h) p.natDegree
  rw [coeff_scaleRoots_natDegree] at this
  contradiction
#align polynomial.scale_roots_ne_zero Polynomial.scaleRoots_ne_zero

theorem support_scaleRoots_le (p : R[X]) (s : R) : (scaleRoots p s).support ≤ p.support := by
  intro
  simpa using left_ne_zero_of_mul
#align polynomial.support_scale_roots_le Polynomial.support_scaleRoots_le

theorem support_scaleRoots_eq (p : R[X]) {s : R} (hs : s ∈ nonZeroDivisors R) :
    (scaleRoots p s).support = p.support :=
  le_antisymm (support_scaleRoots_le p s)
    (by intro i
        simp only [coeff_scaleRoots, Polynomial.mem_support_iff]
        intro p_ne_zero ps_zero
        have := pow_mem hs (p.natDegree - i) _ ps_zero
        contradiction)
#align polynomial.support_scale_roots_eq Polynomial.support_scaleRoots_eq

@[simp]
theorem degree_scaleRoots (p : R[X]) {s : R} : degree (scaleRoots p s) = degree p := by
  haveI := Classical.propDecidable
  by_cases hp : p = 0
  · rw [hp, zero_scaleRoots]
  refine' le_antisymm (Finset.sup_mono (support_scaleRoots_le p s)) (degree_le_degree _)
  rw [coeff_scaleRoots_natDegree]
  intro h
  have := leadingCoeff_eq_zero.mp h
  contradiction
#align polynomial.degree_scale_roots Polynomial.degree_scaleRoots

@[simp]
theorem natDegree_scaleRoots (p : R[X]) (s : R) : natDegree (scaleRoots p s) = natDegree p := by
  simp only [natDegree, degree_scaleRoots]
#align polynomial.nat_degree_scale_roots Polynomial.natDegree_scaleRoots

theorem monic_scaleRoots_iff {p : R[X]} (s : R) : Monic (scaleRoots p s) ↔ Monic p := by
  simp only [Monic, leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots_natDegree]
#align polynomial.monic_scale_roots_iff Polynomial.monic_scaleRoots_iff

theorem map_scaleRoots (p : R[X]) (x : R) (f : R →+* S) (h : f p.leadingCoeff ≠ 0) :
    (p.scaleRoots x).map f = (p.map f).scaleRoots (f x) := by
  ext
  simp [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ h]
#align polynomial.map_scale_roots Polynomial.map_scaleRoots

end Semiring

section CommSemiring

variable [Semiring S] [CommSemiring R] [Semiring A] [Field K]

theorem scaleRoots_eval₂_mul_of_commute {p : S[X]} (f : S →+* A) (a : A) (s : S)
    (hsa : Commute (f s) a) (hf : ∀ s₁ s₂, Commute (f s₁) (f s₂)) :
    eval₂ f (f s * a) (scaleRoots p s) = f s ^ p.natDegree * eval₂ f a p := by
   calc
    _ = (scaleRoots p s).support.sum fun i =>
          f (coeff p i * s ^ (p.natDegree - i)) * (f s * a) ^ i :=
      by simp [eval₂_eq_sum, sum_def]
    _ = p.support.sum fun i => f (coeff p i * s ^ (p.natDegree - i)) * (f s * a) ^ i :=
      (Finset.sum_subset (support_scaleRoots_le p s) fun i _hi hi' => by
        let this : coeff p i * s ^ (p.natDegree - i) = 0 := by simpa using hi'
        simp [this])
    _ = p.support.sum fun i : ℕ => f (p.coeff i) * f s ^ (p.natDegree - i + i) * a ^ i :=
      (Finset.sum_congr rfl fun i _hi => by
        simp_rw [f.map_mul, f.map_pow, pow_add, hsa.mul_pow, mul_assoc])
    _ = p.support.sum fun i : ℕ => f s ^ p.natDegree * (f (p.coeff i) * a ^ i) :=
      (Finset.sum_congr rfl fun i hi => by
        rw [mul_assoc, ← map_pow, (hf _ _).left_comm, map_pow, tsub_add_cancel_of_le]
        exact le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi))
    _ = f s ^ p.natDegree * p.support.sum fun i : ℕ => f (p.coeff i) * a ^ i := Finset.mul_sum.symm
    _ = f s ^ p.natDegree * eval₂ f a p := by simp [eval₂_eq_sum, sum_def]

theorem scaleRoots_eval₂_mul {p : S[X]} (f : S →+* R) (r : R) (s : S) :
    eval₂ f (f s * r) (scaleRoots p s) = f s ^ p.natDegree * eval₂ f r p :=
  scaleRoots_eval₂_mul_of_commute f r s (mul_comm _ _) fun _ _ ↦ mul_comm _ _
#align polynomial.scale_roots_eval₂_mul Polynomial.scaleRoots_eval₂_mul

theorem scaleRoots_eval₂_eq_zero {p : S[X]} (f : S →+* R) {r : R} {s : S} (hr : eval₂ f r p = 0) :
    eval₂ f (f s * r) (scaleRoots p s) = 0 := by rw [scaleRoots_eval₂_mul, hr, mul_zero]
#align polynomial.scale_roots_eval₂_eq_zero Polynomial.scaleRoots_eval₂_eq_zero

theorem scaleRoots_aeval_eq_zero [Algebra R A] {p : R[X]} {a : A} {r : R} (ha : aeval a p = 0) :
    aeval (algebraMap R A r * a) (scaleRoots p r) = 0 := by
  rw [aeval_def, scaleRoots_eval₂_mul_of_commute, ← aeval_def, ha, mul_zero]
  · apply Algebra.commutes
  · intros; rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
#align polynomial.scale_roots_aeval_eq_zero Polynomial.scaleRoots_aeval_eq_zero

theorem scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero {p : S[X]} {f : S →+* K}
    (hf : Function.Injective f) {r s : S} (hr : eval₂ f (f r / f s) p = 0)
    (hs : s ∈ nonZeroDivisors S) : eval₂ f (f r) (scaleRoots p s) = 0 := by
  nontriviality S using Subsingleton.eq_zero
  convert @scaleRoots_eval₂_eq_zero _ _ _ _ p f _ s hr
  rw [← mul_div_assoc, mul_comm, mul_div_cancel]
  exact map_ne_zero_of_mem_nonZeroDivisors _ hf hs
#align polynomial.scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero Polynomial.scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero

theorem scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero [Algebra R K]
    (inj : Function.Injective (algebraMap R K)) {p : R[X]} {r s : R}
    (hr : aeval (algebraMap R K r / algebraMap R K s) p = 0) (hs : s ∈ nonZeroDivisors R) :
    aeval (algebraMap R K r) (scaleRoots p s) = 0 :=
  scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero inj hr hs
#align polynomial.scale_roots_aeval_eq_zero_of_aeval_div_eq_zero Polynomial.scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero

end CommSemiring

end Polynomial
