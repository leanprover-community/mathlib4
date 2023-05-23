/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module ring_theory.adjoin.power_basis
! leanprover-community/mathlib commit 825edd3cd735e87495b0c2a2114fc3929eefce41
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Adjoin.Basic
import Mathbin.RingTheory.PowerBasis
import Mathbin.LinearAlgebra.Matrix.Basis

/-!
# Power basis for `algebra.adjoin R {x}`

This file defines the canonical power basis on `algebra.adjoin R {x}`,
where `x` is an integral element over `R`.
-/


variable {K S : Type _} [Field K] [CommRing S] [Algebra K S]

namespace Algebra

open Polynomial

open PowerBasis

open BigOperators

/-- The elements `1, x, ..., x ^ (d - 1)` for a basis for the `K`-module `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def adjoin.powerBasisAux {x : S} (hx : IsIntegral K x) :
    Basis (Fin (minpoly K x).natDegree) K (adjoin K ({x} : Set S)) :=
  by
  have hST : Function.Injective (algebraMap (adjoin K ({x} : Set S)) S) := Subtype.coe_injective
  have hx' :
    IsIntegral K (show adjoin K ({x} : Set S) from ⟨x, subset_adjoin (Set.mem_singleton x)⟩) :=
    by
    apply (isIntegral_algebraMap_iff hST).mp
    convert hx
    infer_instance
  have minpoly_eq := minpoly.eq_of_algebraMap_eq hST hx' rfl
  apply
    @Basis.mk (Fin (minpoly K x).natDegree) _ (adjoin K {x}) fun i =>
      ⟨x, subset_adjoin (Set.mem_singleton x)⟩ ^ (i : ℕ)
  · have := linearIndependent_pow _
    rwa [minpoly_eq] at this
  · rintro ⟨y, hy⟩ _
    have := hx'.mem_span_pow
    rw [minpoly_eq] at this
    apply this
    · rw [adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨f, rfl⟩ := (aeval x).mem_range.mp hy
      use f
      ext
      exact aeval_algebra_map_apply S (⟨x, _⟩ : adjoin K {x}) _
#align algebra.adjoin.power_basis_aux Algebra.adjoin.powerBasisAux

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. See `algebra.adjoin.power_basis'` for
a version over a more general base ring. -/
@[simps gen dim]
noncomputable def adjoin.powerBasis {x : S} (hx : IsIntegral K x) :
    PowerBasis K (adjoin K ({x} : Set S))
    where
  gen := ⟨x, subset_adjoin (Set.mem_singleton x)⟩
  dim := (minpoly K x).natDegree
  Basis := adjoin.powerBasisAux hx
  basis_eq_pow := Basis.mk_apply _ _
#align algebra.adjoin.power_basis Algebra.adjoin.powerBasis

end Algebra

open Algebra

/-- The power basis given by `x` if `B.gen ∈ adjoin K {x}`. See `power_basis.of_gen_mem_adjoin'`
for a version over a more general base ring. -/
@[simps]
noncomputable def PowerBasis.ofGenMemAdjoin {x : S} (B : PowerBasis K S) (hint : IsIntegral K x)
    (hx : B.gen ∈ adjoin K ({x} : Set S)) : PowerBasis K S :=
  (Algebra.adjoin.powerBasis hint).map <|
    (Subalgebra.equivOfEq _ _ <| PowerBasis.adjoin_eq_top_of_gen_mem_adjoin hx).trans
      Subalgebra.topEquiv
#align power_basis.of_gen_mem_adjoin PowerBasis.ofGenMemAdjoin

section IsIntegral

namespace PowerBasis

open Polynomial

open Polynomial

variable {R : Type _} [CommRing R] [Algebra R S] [Algebra R K] [IsScalarTower R K S]

variable {A : Type _} [CommRing A] [Algebra R A] [Algebra S A]

variable [IsScalarTower R S A] {B : PowerBasis S A} (hB : IsIntegral R B.gen)

include hB

/-- If `B : power_basis S A` is such that `is_integral R B.gen`, then
`is_integral R (B.basis.repr (B.gen ^ n) i)` for all `i` if
`minpoly S B.gen = (minpoly R B.gen).map (algebra_map R S)`. This is the case if `R` is a GCD domain
and `S` is its fraction ring. -/
theorem repr_gen_pow_isIntegral [IsDomain S]
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) (n : ℕ) :
    ∀ i, IsIntegral R (B.Basis.repr (B.gen ^ n) i) :=
  by
  intro i
  let Q := X ^ n %ₘ minpoly R B.gen
  have : B.gen ^ n = aeval B.gen Q :=
    by
    rw [← @aeval_X_pow R _ _ _ _ B.gen, ← mod_by_monic_add_div (X ^ n) (minpoly.monic hB)]
    simp
  by_cases hQ : Q = 0
  · simp [this, hQ, isIntegral_zero]
  have hlt : Q.nat_degree < B.dim :=
    by
    rw [← B.nat_degree_minpoly, hmin, (minpoly.monic hB).natDegree_map,
      nat_degree_lt_nat_degree_iff hQ]
    letI : Nontrivial R := nontrivial.of_polynomial_ne hQ
    exact degree_mod_by_monic_lt _ (minpoly.monic hB)
    infer_instance
  rw [this, aeval_eq_sum_range' hlt]
  simp only [LinearEquiv.map_sum, LinearEquiv.map_smulₛₗ, RingHom.id_apply, Finset.sum_apply']
  refine' IsIntegral.sum _ fun j hj => _
  replace hj := Finset.mem_range.1 hj
  rw [← Fin.val_mk hj, ← B.basis_eq_pow, Algebra.smul_def, IsScalarTower.algebraMap_apply R S A, ←
    Algebra.smul_def, LinearEquiv.map_smul]
  simp only [algebraMap_smul, Finsupp.coe_smul, Pi.smul_apply, B.basis.repr_self_apply]
  by_cases hij : (⟨j, hj⟩ : Fin _) = i
  · simp only [hij, eq_self_iff_true, if_true]
    rw [Algebra.smul_def, mul_one]
    exact isIntegral_algebraMap
  · simp [hij, isIntegral_zero]
#align power_basis.repr_gen_pow_is_integral PowerBasis.repr_gen_pow_isIntegral

variable {B}

/-- Let `B : power_basis S A` be such that `is_integral R B.gen`, and let `x y : A` be elements with
integral coordinates in the base `B.basis`. Then `is_integral R ((B.basis.repr (x * y) i)` for all
`i` if `minpoly S B.gen = (minpoly R B.gen).map (algebra_map R S)`. This is the case if `R` is a GCD
domain and `S` is its fraction ring. -/
theorem repr_mul_isIntegral [IsDomain S] {x y : A} (hx : ∀ i, IsIntegral R (B.Basis.repr x i))
    (hy : ∀ i, IsIntegral R (B.Basis.repr y i))
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) :
    ∀ i, IsIntegral R (B.Basis.repr (x * y) i) :=
  by
  intro i
  rw [← B.basis.sum_repr x, ← B.basis.sum_repr y, Finset.sum_mul_sum, LinearEquiv.map_sum,
    Finset.sum_apply']
  refine' IsIntegral.sum _ fun I hI => _
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, LinearEquiv.map_smulₛₗ,
    RingHom.id_apply, Finsupp.coe_smul, Pi.smul_apply, id.smul_eq_mul]
  refine' isIntegral_mul (hy _) (isIntegral_mul (hx _) _)
  simp only [coe_basis, ← pow_add]
  refine' repr_gen_pow_is_integral hB hmin _ _
#align power_basis.repr_mul_is_integral PowerBasis.repr_mul_isIntegral

/-- Let `B : power_basis S A` be such that `is_integral R B.gen`, and let `x : A` be and element
with integral coordinates in the base `B.basis`. Then `is_integral R ((B.basis.repr (x ^ n) i)` for
all `i` and all `n` if `minpoly S B.gen = (minpoly R B.gen).map (algebra_map R S)`. This is the case
if `R` is a GCD domain and `S` is its fraction ring. -/
theorem repr_pow_isIntegral [IsDomain S] {x : A} (hx : ∀ i, IsIntegral R (B.Basis.repr x i))
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) (n : ℕ) :
    ∀ i, IsIntegral R (B.Basis.repr (x ^ n) i) :=
  by
  nontriviality A using Subsingleton.elim (x ^ n) 0, isIntegral_zero
  revert hx
  refine' Nat.case_strong_induction_on n _ fun n hn => _
  · intro hx i
    rw [pow_zero, ← pow_zero B.gen, ← Fin.val_mk B.dim_pos, ← B.basis_eq_pow,
      B.basis.repr_self_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · intro hx
    rw [pow_succ]
    exact repr_mul_is_integral hB hx (fun _ => hn _ le_rfl (fun _ => hx _) _) hmin
#align power_basis.repr_pow_is_integral PowerBasis.repr_pow_isIntegral

/-- Let `B B' : power_basis K S` be such that `is_integral R B.gen`, and let `P : R[X]` be such that
`aeval B.gen P = B'.gen`. Then `is_integral R (B.basis.to_matrix B'.basis i j)` for all `i` and `j`
if `minpoly K B.gen = (minpoly R B.gen).map (algebra_map R L)`. This is the case
if `R` is a GCD domain and `K` is its fraction ring. -/
theorem toMatrix_isIntegral {B B' : PowerBasis K S} {P : R[X]} (h : aeval B.gen P = B'.gen)
    (hB : IsIntegral R B.gen) (hmin : minpoly K B.gen = (minpoly R B.gen).map (algebraMap R K)) :
    ∀ i j, IsIntegral R (B.Basis.toMatrix B'.Basis i j) :=
  by
  intro i j
  rw [B.basis.to_matrix_apply, B'.coe_basis]
  refine' repr_pow_is_integral hB (fun i => _) hmin _ _
  rw [← h, aeval_eq_sum_range, LinearEquiv.map_sum, Finset.sum_apply']
  refine' IsIntegral.sum _ fun n hn => _
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R K S, ← Algebra.smul_def,
    LinearEquiv.map_smul, algebraMap_smul]
  exact isIntegral_smul _ (repr_gen_pow_is_integral hB hmin _ _)
#align power_basis.to_matrix_is_integral PowerBasis.toMatrix_isIntegral

end PowerBasis

end IsIntegral

