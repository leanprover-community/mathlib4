/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu

! This file was ported from Lean 3 source module linear_algebra.free_module.norm
! leanprover-community/mathlib commit 90b0d53ee6ffa910e5c2a977ce7e2fc704647974
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.FreeModule.IdealQuotient
import Mathbin.RingTheory.Norm

/-!
# Norms on free modules over principal ideal domains
-/


open Ideal Polynomial

open scoped BigOperators Polynomial

variable {R S ι : Type _} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing S]
  [IsDomain S] [Algebra R S]

section CommRing

variable (F : Type _) [CommRing F] [Algebra F R] [Algebra F S] [IsScalarTower F R S]

/-- For a nonzero element `f` in an algebra `S` over a principal ideal domain `R` that is finite and
free as an `R`-module, the norm of `f` relative to `R` is associated to the product of the Smith
coefficients of the ideal generated by `f`. -/
theorem associated_norm_prod_smith [Fintype ι] (b : Basis ι R S) {f : S} (hf : f ≠ 0) :
    Associated (Algebra.norm R f) (∏ i, smithCoeffs b _ (span_singleton_eq_bot.Not.2 hf) i) :=
  by
  have hI := span_singleton_eq_bot.not.2 hf
  let b' := ring_basis b (span {f}) hI
  classical
  rw [← Matrix.det_diagonal, ← LinearMap.det_toLin b']
  let e :=
    (b'.equiv ((span {f}).selfBasis b hI) <| Equiv.refl _).trans
      ((LinearEquiv.coord S S f hf).restrictScalars R)
  refine' (LinearMap.associated_det_of_eq_comp e _ _ _).symm
  dsimp only [e, LinearEquiv.trans_apply]
  simp_rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply, ← LinearMap.ext_iff]
  refine' b'.ext fun i => _
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Matrix.toLin_apply, Basis.repr_self,
    Finsupp.single_eq_pi_single, Matrix.diagonal_mulVec_single, Pi.single_apply, ite_smul,
    zero_smul, Finset.sum_ite_eq', mul_one, if_pos (Finset.mem_univ _), b'.equiv_apply]
  change _ = f * _
  rw [mul_comm, ← smul_eq_mul, LinearEquiv.restrictScalars_apply, LinearEquiv.coord_apply_smul,
    Ideal.selfBasis_def]
  rfl
#align associated_norm_prod_smith associated_norm_prod_smith

end CommRing

section Field

variable {F : Type _} [Field F] [Algebra F[X] S] [Finite ι]

instance (b : Basis ι F[X] S) {I : Ideal S} (hI : I ≠ ⊥) (i : ι) :
    FiniteDimensional F (F[X] ⧸ span ({I.smithCoeffs b hI i} : Set F[X])) :=
  (AdjoinRoot.powerBasis <| I.smithCoeffs_ne_zero b hI i).FiniteDimensional

/-- For a nonzero element `f` in a `F[X]`-module `S`, the dimension of $S/\langle f \rangle$ as an
`F`-vector space is the degree of the norm of `f` relative to `F[X]`. -/
theorem finrank_quotient_span_eq_natDegree_norm [Algebra F S] [IsScalarTower F F[X] S]
    (b : Basis ι F[X] S) {f : S} (hf : f ≠ 0) :
    FiniteDimensional.finrank F (S ⧸ span ({f} : Set S)) = (Algebra.norm F[X] f).natDegree :=
  by
  haveI := Fintype.ofFinite ι
  have h := span_singleton_eq_bot.not.2 hf
  rw [nat_degree_eq_of_degree_eq
      (degree_eq_degree_of_associated <| associated_norm_prod_smith b hf),
    nat_degree_prod _ _ fun i _ => smith_coeffs_ne_zero b _ h i, finrank_quotient_eq_sum F h b]
  -- finrank_quotient_eq_sum slow
  congr with i
  exact (AdjoinRoot.powerBasis <| smith_coeffs_ne_zero b _ h i).finrank
#align finrank_quotient_span_eq_nat_degree_norm finrank_quotient_span_eq_natDegree_norm

end Field

