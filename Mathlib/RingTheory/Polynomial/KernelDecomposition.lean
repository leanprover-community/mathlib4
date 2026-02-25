/-
Copyright (c) 2025 Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Polynomial.Smeval
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Kernel decomposition for products of pairwise coprime polynomials

This file proves the kernels lemma: if `P i` for `i ∈ s` are pairwise coprime polynomials, then the
kernel of the product `∏ i ∈ s, P i` evaluated via `smeval` at an endomorphism `f` equals the
sum of the individual kernels.

## Main results

* `ker_smeval_le_ker_smeval_prod`: each individual kernel is contained in the product
  kernel.
* `ker_smeval_prod_le_iSup_ker_smeval`: the product kernel is contained in the
  sum of individual kernels, given pairwise coprimality.
* `ker_smeval_prod_eq_iSup_ker_smeval`: the kernel of the product equals the sum
  of the individual kernels for pairwise coprime polynomials.

## Tags

kernel, coprime, polynomial, endomorphism, smeval
-/

@[expose] public section

open Polynomial
open scoped Function

namespace LinearMap

variable {ι K E : Type*} [CommRing K] [AddCommGroup E] [Module K E]


/-- If `i ∈ s`, then `ker(P i |>.smeval f) ≤ ker(s.prod P |>.smeval f)`. -/
theorem ker_smeval_le_ker_smeval_prod (f : Module.End K E)
    (s : Finset ι) (P : ι → K[X]) (i : ι) (hi : i ∈ s) :
    (P i |>.smeval f).ker ≤ (s.prod P |>.smeval f).ker := by
  classical
  intro x hxi
  rw [mem_ker] at hxi ⊢
  have prod_eq : s.prod P = (s.erase i).prod P * P i := by
    rw [mul_comm, Finset.mul_prod_erase s P hi]
  rw [prod_eq, Polynomial.smeval_mul, Module.End.mul_apply, hxi, map_zero]


/-- If the polynomials `P i` for `i ∈ s` are pairwise coprime, then
`ker(s.prod P |>.smeval f) ≤ ⨆ i ∈ s, ker(P i |>.smeval f)`. -/
theorem ker_smeval_prod_le_iSup_ker_smeval (f : Module.End K E)
    (s : Finset ι) (P : ι → K[X]) (hs : s.Nonempty)
    (h : (s : Set ι).Pairwise <| IsCoprime.onFun P) :
    (s.prod P |>.smeval f).ker ≤ ⨆ i ∈ s, (P i |>.smeval f).ker := by
  classical
  -- Lift the pairwise coprimality to the subtype
  have h' : Pairwise (IsCoprime on fun i : s ↦ P i) := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [Function.onFun]
    exact h hi hj (fun h_eq => hij (Subtype.ext h_eq))
  -- Bézout identity
  obtain ⟨Q, hQ⟩ := (exists_sum_eq_one_iff_pairwise_coprime hs).mpr h'
  intro x hx
  rw [mem_ker] at hx
  -- Deduce that smeval of the Bézout sum is the identity
  have hQ_smeval : (∑ i ∈ s, Q i * ∏ j ∈ s \ {i}, P j).smeval f = 1 := by
    simp [hQ]
  -- Decompose x using the Bézout identity
  have hx_eq : x = ∑ i ∈ s, ((Q i * ∏ j ∈ s \ {i}, P j).smeval f) x := by
    rw [← sum_apply, ← Polynomial.smeval_finset_sum_apply, hQ_smeval,
      Module.End.one_eq_id, id_apply]
  rw [hx_eq]
  -- Each summand belongs to the corresponding kernel
  refine Submodule.sum_mem_biSup fun i hi => ?_
  rw [mem_ker, ← Module.End.mul_apply, ← Polynomial.smeval_mul]
  have prod_identity : P i * (Q i * ∏ j ∈ s \ {i}, P j) = Q i * s.prod P := by
    rw [Finset.sdiff_singleton_eq_erase]
    calc P i * (Q i * ∏ j ∈ s.erase i, P j)
        = Q i * (P i * ∏ j ∈ s.erase i, P j) := by ring
      _ = Q i * s.prod P := by rw [Finset.mul_prod_erase s P hi]
  rw [prod_identity, Polynomial.smeval_mul, Module.End.mul_apply, hx, map_zero]

/-! ### Main theorem: kernel of product equals sum of kernels -/

/-- If the polynomials `P i` for `i ∈ s` are pairwise coprime, then the kernel of the
product `∏ i ∈ s, P i` evaluated via `smeval` at an endomorphism `f` equals the sum
of the individual kernels. -/
theorem ker_smeval_prod_eq_iSup_ker_smeval (f : Module.End K E)
    (s : Finset ι) (P : ι → K[X])
    (h : (s : Set ι).Pairwise <| IsCoprime.onFun P) :
    (s.prod P |>.smeval f).ker = ⨆ i ∈ s, (P i |>.smeval f).ker := by
  classical
  by_cases hs : s.Nonempty
  · exact le_antisymm
      (ker_smeval_prod_le_iSup_ker_smeval f s P hs h)
      (iSup₂_le fun i hi => ker_smeval_le_ker_smeval_prod f s P i hi)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp [Module.End.one_eq_id, ker_id]

end LinearMap