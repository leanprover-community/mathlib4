/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp

! This file was ported from Lean 3 source module linear_algebra.eigenspace.minpoly
! leanprover-community/mathlib commit 6b0169218d01f2837d79ea2784882009a0da1aa1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Eigenspace.Basic
import Mathbin.FieldTheory.Minpoly.Field

/-!
# Eigenvalues are the roots of the minimal polynomial.

## Tags

eigenvalue, minimal polynomial
-/


universe u v w

namespace Module

namespace End

open Polynomial FiniteDimensional

open scoped Polynomial

variable {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]

theorem eigenspace_aeval_polynomial_degree_1 (f : End K V) (q : K[X]) (hq : degree q = 1) :
    eigenspace f (-q.coeff 0 / q.leadingCoeff) = (aeval f q).ker :=
  calc
    eigenspace f (-q.coeff 0 / q.leadingCoeff) =
        (q.leadingCoeff • f - algebraMap K (End K V) (-q.coeff 0)).ker :=
      by rw [eigenspace_div]; intro h; rw [leading_coeff_eq_zero_iff_deg_eq_bot.1 h] at hq ;
      cases hq
    _ = (aeval f (C q.leadingCoeff * X + C (q.coeff 0))).ker := by rw [C_mul', aeval_def];
      simp [algebraMap, Algebra.toRingHom]
    _ = (aeval f q).ker := by rwa [← eq_X_add_C_of_degree_eq_one]
#align module.End.eigenspace_aeval_polynomial_degree_1 Module.End.eigenspace_aeval_polynomial_degree_1

theorem ker_aeval_ring_hom'_unit_polynomial (f : End K V) (c : K[X]ˣ) :
    (aeval f (c : K[X])).ker = ⊥ :=
  by
  rw [Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]
  simp only [aeval_def, eval₂_C]
  apply ker_algebra_map_End
  apply coeff_coe_units_zero_ne_zero c
#align module.End.ker_aeval_ring_hom'_unit_polynomial Module.End.ker_aeval_ring_hom'_unit_polynomial

theorem aeval_apply_of_hasEigenvector {f : End K V} {p : K[X]} {μ : K} {x : V}
    (h : f.HasEigenvector μ x) : aeval f p x = p.eval μ • x :=
  by
  apply p.induction_on
  · intro a; simp [Module.algebraMap_end_apply]
  · intro p q hp hq; simp [hp, hq, add_smul]
  · intro n a hna
    rw [mul_comm, pow_succ, mul_assoc, AlgHom.map_mul, LinearMap.mul_apply, mul_comm, hna]
    simp only [mem_eigenspace_iff.1 h.1, smul_smul, aeval_X, eval_mul, eval_C, eval_pow, eval_X,
      LinearMap.map_smulₛₗ, RingHom.id_apply, mul_comm]
#align module.End.aeval_apply_of_has_eigenvector Module.End.aeval_apply_of_hasEigenvector

theorem isRoot_of_hasEigenvalue {f : End K V} {μ : K} (h : f.HasEigenvalue μ) :
    (minpoly K f).IsRoot μ :=
  by
  rcases(Submodule.ne_bot_iff _).1 h with ⟨w, ⟨H, ne0⟩⟩
  refine' Or.resolve_right (smul_eq_zero.1 _) ne0
  simp [← aeval_apply_of_has_eigenvector ⟨H, ne0⟩, minpoly.aeval K f]
#align module.End.is_root_of_has_eigenvalue Module.End.isRoot_of_hasEigenvalue

variable [FiniteDimensional K V] (f : End K V)

variable {f} {μ : K}

theorem hasEigenvalue_of_isRoot (h : (minpoly K f).IsRoot μ) : f.HasEigenvalue μ :=
  by
  cases' dvd_iff_is_root.2 h with p hp
  rw [has_eigenvalue, eigenspace]
  intro con
  cases' (LinearMap.isUnit_iff_ker_eq_bot _).2 Con with u hu
  have p_ne_0 : p ≠ 0 := by
    intro con
    apply minpoly.ne_zero f.is_integral
    rw [hp, Con, MulZeroClass.mul_zero]
  have h_deg := minpoly.degree_le_of_ne_zero K f p_ne_0 _
  · rw [hp, degree_mul, degree_X_sub_C, Polynomial.degree_eq_natDegree p_ne_0] at h_deg 
    norm_cast at h_deg 
    linarith
  · have h_aeval := minpoly.aeval K f
    revert h_aeval
    simp [hp, ← hu]
#align module.End.has_eigenvalue_of_is_root Module.End.hasEigenvalue_of_isRoot

theorem hasEigenvalue_iff_isRoot : f.HasEigenvalue μ ↔ (minpoly K f).IsRoot μ :=
  ⟨isRoot_of_hasEigenvalue, hasEigenvalue_of_isRoot⟩
#align module.End.has_eigenvalue_iff_is_root Module.End.hasEigenvalue_iff_isRoot

/-- An endomorphism of a finite-dimensional vector space has finitely many eigenvalues. -/
noncomputable instance (f : End K V) : Fintype f.Eigenvalues :=
  Set.Finite.fintype
    (by
      have h : minpoly K f ≠ 0 := minpoly.ne_zero f.is_integral
      convert (minpoly K f).rootSet_finite K
      ext μ
      have : μ ∈ {μ : K | f.eigenspace μ = ⊥ → False} ↔ ¬f.eigenspace μ = ⊥ := by tauto
      convert rfl.mpr this
      simp [Polynomial.rootSet_def, Polynomial.mem_roots h, ← has_eigenvalue_iff_is_root,
        has_eigenvalue])

end End

end Module

