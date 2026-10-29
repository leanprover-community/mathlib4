/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Lince
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Hermite interpolation using Hasse derivatives

Prescribed Hasse derivatives at finitely many distinct points determine a unique
polynomial of degree less than the total number of prescribed values. The orders
may differ between points, and the field may have any characteristic.
-/

@[expose] public section

set_option autoImplicit false

open scoped Polynomial
open Finset Module

namespace Polynomial

theorem pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero
    {R : Type*} [CommRing R] (p : R[X]) (x : R) (n : ℕ) :
    (X - C x) ^ n ∣ p ↔ ∀ k < n, (hasseDeriv k p).eval x = 0 := by
  have hcoe : ∀ q : R[X], taylorEquiv x q = taylor x q := fun _ ↦ rfl
  have ht : taylor x ((X - C x) ^ n) = X ^ n := by
    rw [taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right]
  rw [← map_dvd_iff (taylorEquiv x), hcoe, hcoe, ht, X_pow_dvd_iff]
  exact forall₂_congr fun k _ ↦ by rw [taylor_coeff]

theorem sum_rootMultiplicity_le_natDegree
    {R : Type*} [CommRing R] [IsDomain R] (p : R[X]) (s : Finset R) :
    ∑ x ∈ s, p.rootMultiplicity x ≤ p.natDegree := by
  classical
  have hsum : ∑ x ∈ s, p.roots.count x ≤ Multiset.card p.roots := by
    rw [← Multiset.toFinset_sum_count_eq p.roots,
      ← Finset.sum_subset (Finset.inter_subset_left (s₁ := s) (s₂ := p.roots.toFinset))
        (fun x hx hx' => Multiset.count_eq_zero.mpr fun hm =>
          hx' (Finset.mem_inter.2 ⟨hx, Multiset.mem_toFinset.2 hm⟩))]
    exact Finset.sum_le_sum_of_subset Finset.inter_subset_right
  simpa only [count_roots] using hsum.trans p.card_roots'

theorem eq_zero_of_degree_lt_of_hasseDeriv_eval_eq_zero
    {R : Type*} [CommRing R] [IsDomain R] (p : R[X]) (s : Finset R) (m : R → ℕ)
    (hdeg : p.degree < (∑ x ∈ s, m x : ℕ))
    (h : ∀ x ∈ s, ∀ k < m x, (hasseDeriv k p).eval x = 0) : p = 0 := by
  by_contra hp
  have hbound : ∑ x ∈ s, m x ≤ p.natDegree := by
    refine (Finset.sum_le_sum fun x hx ↦ ?_).trans (sum_rootMultiplicity_le_natDegree p s)
    exact (le_rootMultiplicity_iff hp).2
      ((pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero p x (m x)).2 (h x hx))
  exact (not_lt_of_ge hbound) ((natDegree_lt_iff_degree_lt hp).2 hdeg)

theorem eq_of_degree_lt_of_hasseDeriv_eval_eq
    {R : Type*} [CommRing R] [IsDomain R] (p q : R[X]) (s : Finset R) (m : R → ℕ)
    (hp : p.degree < (∑ x ∈ s, m x : ℕ))
    (hq : q.degree < (∑ x ∈ s, m x : ℕ))
    (h : ∀ x ∈ s, ∀ k < m x, (hasseDeriv k p).eval x = (hasseDeriv k q).eval x) :
    p = q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_degree_lt_of_hasseDeriv_eval_eq_zero (p - q) s m
  · exact (degree_sub_le p q).trans_lt (max_lt hp hq)
  · intro x hx k hk
    simp only [map_sub, eval_sub, sub_eq_zero]
    exact h x hx k hk

/-- Evaluation of the Hasse derivatives at the prescribed points, as a linear map
from polynomials of degree less than the total multiplicity to the product of the
jets.  It is bijective by the two theorems below. -/
noncomputable def hermiteEvaluation {K : Type*} [Field K] (s : Finset K) (m : K → ℕ) :
    K[X]_(∑ x ∈ s, m x) →ₗ[K] (x : s) → Fin (m x) → K where
  toFun p x k := (hasseDeriv k (p : K[X])).eval x
  map_add' p q := by ext x k; simp
  map_smul' a p := by
    ext x k
    show (hasseDeriv k (a • (p : K[X]))).eval (x : K) =
      a * (hasseDeriv k (p : K[X])).eval (x : K)
    rw [(hasseDeriv k).map_smul, smul_eq_C_mul, eval_mul, eval_C]

theorem hermiteEvaluation_injective {K : Type*} [Field K] (s : Finset K) (m : K → ℕ) :
    Function.Injective (hermiteEvaluation s m) := by
  intro p q h
  apply Subtype.ext
  apply eq_of_degree_lt_of_hasseDeriv_eval_eq (p : K[X]) (q : K[X]) s m
    (mem_degreeLT.1 p.property) (mem_degreeLT.1 q.property)
  intro x hx k hk
  exact congrFun (congrFun h ⟨x, hx⟩) ⟨k, hk⟩

theorem hermiteEvaluation_surjective {K : Type*} [Field K] (s : Finset K) (m : K → ℕ) :
    Function.Surjective (hermiteEvaluation s m) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1
    (hermiteEvaluation_injective s m)
  rw [Module.finrank_eq_card_basis (degreeLT.basis K _)]
  simp [Module.finrank_pi_fintype, Finset.sum_attach]

theorem existsUnique_hermiteInterpolation {K : Type*} [Field K]
    (s : Finset K) (m : K → ℕ) (values : (x : s) → Fin (m x) → K) :
    ∃! p : K[X], p.degree < (∑ x ∈ s, m x : ℕ) ∧
      ∀ (x : s) (k : Fin (m x)), (hasseDeriv k p).eval (x : K) = values x k := by
  obtain ⟨p, hp⟩ := hermiteEvaluation_surjective s m values
  refine ⟨p, ⟨mem_degreeLT.1 p.property, ?_⟩, ?_⟩
  · exact fun x k ↦ congrFun (congrFun hp x) k
  · intro q hq
    apply eq_of_degree_lt_of_hasseDeriv_eval_eq q (p : K[X]) s m hq.1
      (mem_degreeLT.1 p.property)
    intro x hx k hk
    exact (hq.2 ⟨x, hx⟩ ⟨k, hk⟩).trans (congrFun (congrFun hp ⟨x, hx⟩) ⟨k, hk⟩).symm

end Polynomial
