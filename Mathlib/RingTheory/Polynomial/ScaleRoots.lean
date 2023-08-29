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
  -- 🎉 no goals
#align polynomial.coeff_scale_roots Polynomial.coeff_scaleRoots

theorem coeff_scaleRoots_natDegree (p : R[X]) (s : R) :
    (scaleRoots p s).coeff p.natDegree = p.leadingCoeff := by
  rw [leadingCoeff, coeff_scaleRoots, tsub_self, pow_zero, mul_one]
  -- 🎉 no goals
#align polynomial.coeff_scale_roots_nat_degree Polynomial.coeff_scaleRoots_natDegree

@[simp]
theorem zero_scaleRoots (s : R) : scaleRoots 0 s = 0 := by
  ext
  -- ⊢ coeff (scaleRoots 0 s) n✝ = coeff 0 n✝
  simp
  -- 🎉 no goals
#align polynomial.zero_scale_roots Polynomial.zero_scaleRoots

theorem scaleRoots_ne_zero {p : R[X]} (hp : p ≠ 0) (s : R) : scaleRoots p s ≠ 0 := by
  intro h
  -- ⊢ False
  have : p.coeff p.natDegree ≠ 0 := mt leadingCoeff_eq_zero.mp hp
  -- ⊢ False
  have : (scaleRoots p s).coeff p.natDegree = 0 :=
    congr_fun (congr_arg (coeff : R[X] → ℕ → R) h) p.natDegree
  rw [coeff_scaleRoots_natDegree] at this
  -- ⊢ False
  contradiction
  -- 🎉 no goals
#align polynomial.scale_roots_ne_zero Polynomial.scaleRoots_ne_zero

theorem support_scaleRoots_le (p : R[X]) (s : R) : (scaleRoots p s).support ≤ p.support := by
  intro
  -- ⊢ a✝ ∈ support (scaleRoots p s) → a✝ ∈ support p
  simpa using left_ne_zero_of_mul
  -- 🎉 no goals
#align polynomial.support_scale_roots_le Polynomial.support_scaleRoots_le

theorem support_scaleRoots_eq (p : R[X]) {s : R} (hs : s ∈ nonZeroDivisors R) :
    (scaleRoots p s).support = p.support :=
  le_antisymm (support_scaleRoots_le p s)
    (by intro i
        -- ⊢ i ∈ support p → i ∈ support (scaleRoots p s)
        simp only [coeff_scaleRoots, Polynomial.mem_support_iff]
        -- ⊢ coeff p i ≠ 0 → coeff p i * s ^ (natDegree p - i) ≠ 0
        intro p_ne_zero ps_zero
        -- ⊢ False
        have := pow_mem hs (p.natDegree - i) _ ps_zero
        -- ⊢ False
        contradiction)
        -- 🎉 no goals
#align polynomial.support_scale_roots_eq Polynomial.support_scaleRoots_eq

@[simp]
theorem degree_scaleRoots (p : R[X]) {s : R} : degree (scaleRoots p s) = degree p := by
  haveI := Classical.propDecidable
  -- ⊢ degree (scaleRoots p s) = degree p
  by_cases hp : p = 0
  -- ⊢ degree (scaleRoots p s) = degree p
  · rw [hp, zero_scaleRoots]
    -- 🎉 no goals
  refine' le_antisymm (Finset.sup_mono (support_scaleRoots_le p s)) (degree_le_degree _)
  -- ⊢ coeff (scaleRoots p s) (natDegree p) ≠ 0
  rw [coeff_scaleRoots_natDegree]
  -- ⊢ leadingCoeff p ≠ 0
  intro h
  -- ⊢ False
  have := leadingCoeff_eq_zero.mp h
  -- ⊢ False
  contradiction
  -- 🎉 no goals
#align polynomial.degree_scale_roots Polynomial.degree_scaleRoots

@[simp]
theorem natDegree_scaleRoots (p : R[X]) (s : R) : natDegree (scaleRoots p s) = natDegree p := by
  simp only [natDegree, degree_scaleRoots]
  -- 🎉 no goals
#align polynomial.nat_degree_scale_roots Polynomial.natDegree_scaleRoots

theorem monic_scaleRoots_iff {p : R[X]} (s : R) : Monic (scaleRoots p s) ↔ Monic p := by
  simp only [Monic, leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots_natDegree]
  -- 🎉 no goals
#align polynomial.monic_scale_roots_iff Polynomial.monic_scaleRoots_iff

theorem map_scaleRoots (p : R[X]) (x : R) (f : R →+* S) (h : f p.leadingCoeff ≠ 0) :
    (p.scaleRoots x).map f = (p.map f).scaleRoots (f x) := by
  ext
  -- ⊢ coeff (map f (scaleRoots p x)) n✝ = coeff (scaleRoots (map f p) (↑f x)) n✝
  simp [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ h]
  -- 🎉 no goals
#align polynomial.map_scale_roots Polynomial.map_scaleRoots

end Semiring

section CommSemiring

variable [Semiring S] [CommSemiring R] [CommSemiring A] [Field K]

theorem scaleRoots_eval₂_mul {p : S[X]} (f : S →+* R) (r : R) (s : S) :
    eval₂ f (f s * r) (scaleRoots p s) = f s ^ p.natDegree * eval₂ f r p :=
  calc
    _ = (scaleRoots p s).support.sum fun i =>
          f (coeff p i * s ^ (p.natDegree - i)) * (f s * r) ^ i :=
      by simp [eval₂_eq_sum, sum_def]
         -- 🎉 no goals
    _ = p.support.sum fun i => f (coeff p i * s ^ (p.natDegree - i)) * (f s * r) ^ i :=
      (Finset.sum_subset (support_scaleRoots_le p s) fun i _hi hi' => by
        let this : coeff p i * s ^ (p.natDegree - i) = 0 := by simpa using hi'
        -- ⊢ ↑f (coeff p i * s ^ (natDegree p - i)) * (↑f s * r) ^ i = 0
        simp [this])
        -- 🎉 no goals
    _ = p.support.sum fun i : ℕ => f (p.coeff i) * f s ^ (p.natDegree - i + i) * r ^ i :=
      (Finset.sum_congr rfl fun i _hi => by
        simp_rw [f.map_mul, f.map_pow, pow_add, mul_pow, mul_assoc])
        -- 🎉 no goals
    _ = p.support.sum fun i : ℕ => f s ^ p.natDegree * (f (p.coeff i) * r ^ i) :=
      (Finset.sum_congr rfl fun i hi => by
        rw [mul_assoc, mul_left_comm, tsub_add_cancel_of_le]
        -- ⊢ i ≤ natDegree p
        exact le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi))
        -- 🎉 no goals
    _ = f s ^ p.natDegree * p.support.sum fun i : ℕ => f (p.coeff i) * r ^ i := Finset.mul_sum.symm
    _ = f s ^ p.natDegree * eval₂ f r p := by simp [eval₂_eq_sum, sum_def]
                                              -- 🎉 no goals

#align polynomial.scale_roots_eval₂_mul Polynomial.scaleRoots_eval₂_mul

theorem scaleRoots_eval₂_eq_zero {p : S[X]} (f : S →+* R) {r : R} {s : S} (hr : eval₂ f r p = 0) :
    eval₂ f (f s * r) (scaleRoots p s) = 0 := by rw [scaleRoots_eval₂_mul, hr, mul_zero]
                                                 -- 🎉 no goals
#align polynomial.scale_roots_eval₂_eq_zero Polynomial.scaleRoots_eval₂_eq_zero

theorem scaleRoots_aeval_eq_zero [Algebra R A] {p : R[X]} {a : A} {r : R} (ha : aeval a p = 0) :
    aeval (algebraMap R A r * a) (scaleRoots p r) = 0 :=
  scaleRoots_eval₂_eq_zero (algebraMap R A) ha
#align polynomial.scale_roots_aeval_eq_zero Polynomial.scaleRoots_aeval_eq_zero

theorem scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero {p : S[X]} {f : S →+* K}
    (hf : Function.Injective f) {r s : S} (hr : eval₂ f (f r / f s) p = 0)
    (hs : s ∈ nonZeroDivisors S) : eval₂ f (f r) (scaleRoots p s) = 0 := by
  nontriviality S using Subsingleton.eq_zero
  -- ⊢ eval₂ f (↑f r) (scaleRoots p s) = 0
  convert @scaleRoots_eval₂_eq_zero _ _ _ _ p f _ s hr
  -- ⊢ ↑f r = ↑f s * (↑f r / ↑f s)
  rw [← mul_div_assoc, mul_comm, mul_div_cancel]
  -- ⊢ ↑f s ≠ 0
  exact map_ne_zero_of_mem_nonZeroDivisors _ hf hs
  -- 🎉 no goals
#align polynomial.scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero Polynomial.scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero

theorem scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero [Algebra R K]
    (inj : Function.Injective (algebraMap R K)) {p : R[X]} {r s : R}
    (hr : aeval (algebraMap R K r / algebraMap R K s) p = 0) (hs : s ∈ nonZeroDivisors R) :
    aeval (algebraMap R K r) (scaleRoots p s) = 0 :=
  scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero inj hr hs
#align polynomial.scale_roots_aeval_eq_zero_of_aeval_div_eq_zero Polynomial.scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero

end CommSemiring

end Polynomial
