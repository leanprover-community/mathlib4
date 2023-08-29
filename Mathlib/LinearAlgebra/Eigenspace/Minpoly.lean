/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.Minpoly.Field

#align_import linear_algebra.eigenspace.minpoly from "leanprover-community/mathlib"@"c3216069e5f9369e6be586ccbfcde2592b3cec92"

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
    eigenspace f (-q.coeff 0 / q.leadingCoeff) = LinearMap.ker (aeval f q) :=
  calc
    eigenspace f (-q.coeff 0 / q.leadingCoeff)
    _ = LinearMap.ker (q.leadingCoeff • f - algebraMap K (End K V) (-q.coeff 0)) := by
          rw [eigenspace_div]
          -- ⊢ leadingCoeff q ≠ 0
          intro h
          -- ⊢ False
          rw [leadingCoeff_eq_zero_iff_deg_eq_bot.1 h] at hq
          -- ⊢ False
          cases hq
          -- 🎉 no goals
    _ = LinearMap.ker (aeval f (C q.leadingCoeff * X + C (q.coeff 0))) := by
          rw [C_mul', aeval_def]; simp [algebraMap, Algebra.toRingHom]
          -- ⊢ LinearMap.ker (leadingCoeff q • f - ↑(algebraMap K (End K V)) (-coeff q 0))  …
                                  -- 🎉 no goals
    _ = LinearMap.ker (aeval f q) := by rwa [← eq_X_add_C_of_degree_eq_one]
                                        -- 🎉 no goals
#align module.End.eigenspace_aeval_polynomial_degree_1 Module.End.eigenspace_aeval_polynomial_degree_1

theorem ker_aeval_ring_hom'_unit_polynomial (f : End K V) (c : K[X]ˣ) :
    LinearMap.ker (aeval f (c : K[X])) = ⊥ := by
  rw [Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]
  -- ⊢ LinearMap.ker (↑(aeval f) (↑C (coeff (↑c) 0))) = ⊥
  simp only [aeval_def, eval₂_C]
  -- ⊢ LinearMap.ker (↑(algebraMap K (End K V)) (coeff (↑c) 0)) = ⊥
  apply ker_algebraMap_end
  -- ⊢ coeff (↑c) 0 ≠ 0
  apply coeff_coe_units_zero_ne_zero c
  -- 🎉 no goals
#align module.End.ker_aeval_ring_hom'_unit_polynomial Module.End.ker_aeval_ring_hom'_unit_polynomial

theorem aeval_apply_of_hasEigenvector {f : End K V} {p : K[X]} {μ : K} {x : V}
    (h : f.HasEigenvector μ x) : aeval f p x = p.eval μ • x := by
  refine' p.induction_on _ _ _
  · intro a; simp [Module.algebraMap_end_apply]
    -- ⊢ ↑(↑(aeval f) (↑C a)) x = eval μ (↑C a) • x
             -- 🎉 no goals
  · intro p q hp hq; simp [hp, hq, add_smul]
    -- ⊢ ↑(↑(aeval f) (p + q)) x = eval μ (p + q) • x
                     -- 🎉 no goals
  · intro n a hna
    -- ⊢ ↑(↑(aeval f) (↑C a * X ^ (n + 1))) x = eval μ (↑C a * X ^ (n + 1)) • x
    rw [mul_comm, pow_succ, mul_assoc, AlgHom.map_mul, LinearMap.mul_apply, mul_comm, hna]
    -- ⊢ ↑(↑(aeval f) X) (eval μ (↑C a * X ^ n) • x) = eval μ (X * (↑C a * X ^ n)) • x
    simp only [mem_eigenspace_iff.1 h.1, smul_smul, aeval_X, eval_mul, eval_C, eval_pow, eval_X,
      LinearMap.map_smulₛₗ, RingHom.id_apply, mul_comm]
#align module.End.aeval_apply_of_has_eigenvector Module.End.aeval_apply_of_hasEigenvector

theorem isRoot_of_hasEigenvalue {f : End K V} {μ : K} (h : f.HasEigenvalue μ) :
    (minpoly K f).IsRoot μ := by
  rcases(Submodule.ne_bot_iff _).1 h with ⟨w, ⟨H, ne0⟩⟩
  -- ⊢ IsRoot (minpoly K f) μ
  refine' Or.resolve_right (smul_eq_zero.1 _) ne0
  -- ⊢ eval μ (minpoly K f) • w = 0
  simp [← aeval_apply_of_hasEigenvector ⟨H, ne0⟩, minpoly.aeval K f]
  -- 🎉 no goals
#align module.End.is_root_of_has_eigenvalue Module.End.isRoot_of_hasEigenvalue

variable [FiniteDimensional K V] (f : End K V)

variable {f} {μ : K}

theorem hasEigenvalue_of_isRoot (h : (minpoly K f).IsRoot μ) : f.HasEigenvalue μ := by
  cases' dvd_iff_isRoot.2 h with p hp
  -- ⊢ HasEigenvalue f μ
  rw [HasEigenvalue, eigenspace]
  -- ⊢ LinearMap.ker (f - ↑(algebraMap K (End K V)) μ) ≠ ⊥
  intro con
  -- ⊢ False
  cases' (LinearMap.isUnit_iff_ker_eq_bot _).2 con with u hu
  -- ⊢ False
  have p_ne_0 : p ≠ 0 := by
    intro con
    apply minpoly.ne_zero f.isIntegral
    rw [hp, con, mul_zero]
  have : (aeval f) p = 0 := by
    have h_aeval := minpoly.aeval K f
    revert h_aeval
    simp [hp, ← hu]
  have h_deg := minpoly.degree_le_of_ne_zero K f p_ne_0 this
  -- ⊢ False
  rw [hp, degree_mul, degree_X_sub_C, Polynomial.degree_eq_natDegree p_ne_0] at h_deg
  -- ⊢ False
  norm_cast at h_deg
  -- ⊢ False
  linarith
  -- 🎉 no goals
#align module.End.has_eigenvalue_of_is_root Module.End.hasEigenvalue_of_isRoot

theorem hasEigenvalue_iff_isRoot : f.HasEigenvalue μ ↔ (minpoly K f).IsRoot μ :=
  ⟨isRoot_of_hasEigenvalue, hasEigenvalue_of_isRoot⟩
#align module.End.has_eigenvalue_iff_is_root Module.End.hasEigenvalue_iff_isRoot

/-- An endomorphism of a finite-dimensional vector space has finitely many eigenvalues. -/
noncomputable instance (f : End K V) : Fintype f.Eigenvalues :=
  Set.Finite.fintype <| show {μ | eigenspace f μ ≠ ⊥}.Finite by
    have h : minpoly K f ≠ 0 := minpoly.ne_zero f.isIntegral
    -- ⊢ Set.Finite {μ | eigenspace f μ ≠ ⊥}
    convert (minpoly K f).rootSet_finite K
    -- ⊢ {μ | eigenspace f μ ≠ ⊥} = rootSet (minpoly K f) K
    ext μ
    -- ⊢ μ ∈ {μ | eigenspace f μ ≠ ⊥} ↔ μ ∈ rootSet (minpoly K f) K
    -- Porting note: was the below, but this applied unwanted simp lemmas
    -- ```
    -- classical simp [Polynomial.rootSet_def, Polynomial.mem_roots h, ← hasEigenvalue_iff_isRoot,
    --   HasEigenvalue]
    -- ```
    rw [Set.mem_setOf_eq, ← HasEigenvalue, hasEigenvalue_iff_isRoot, mem_rootSet_of_ne h, IsRoot,
      coe_aeval_eq_eval]

end End

end Module
