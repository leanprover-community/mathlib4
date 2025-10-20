/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Eigenvalues are the roots of the minimal polynomial.

## Tags

eigenvalue, minimal polynomial
-/


universe u v w

namespace Module

namespace End

open Polynomial Module

open scoped Polynomial

section CommSemiring

variable {R : Type v} {M : Type w} [CommSemiring R] [AddCommMonoid M] [Module R M]

theorem ker_aeval_ring_hom'_unit_polynomial (f : End R M) (c : R[X]ˣ) :
    LinearMap.ker (aeval f (c : R[X])) = ⊥ :=
  LinearMap.ker_eq_bot'.mpr fun m hm ↦ by
    simpa [← mul_apply, ← aeval_mul] using congr(c⁻¹.1.aeval f $hm)

end CommSemiring

section CommRing

variable {R : Type v} {M : Type w} [CommRing R] [AddCommGroup M] [Module R M] {f : End R M} {μ : R}

theorem aeval_apply_of_hasEigenvector {f : End R M} {p : R[X]} {μ : R} {x : M}
    (h : f.HasEigenvector μ x) : aeval f p x = p.eval μ • x := by
  refine p.induction_on ?_ ?_ ?_
  · intro a; simp [Module.algebraMap_end_apply]
  · intro p q hp hq; simp [hp, hq, add_smul]
  · intro n a hna
    rw [mul_comm, pow_succ', mul_assoc, map_mul, Module.End.mul_apply, mul_comm, hna]
    simp only [mem_eigenspace_iff.1 h.1, smul_smul, aeval_X, eval_mul, eval_C, eval_pow, eval_X,
      LinearMap.map_smulₛₗ, RingHom.id_apply, mul_comm]

theorem isRoot_of_hasEigenvalue [NoZeroSMulDivisors R M] {f : End R M} {μ : R}
    (h : f.HasEigenvalue μ) : (minpoly R f).IsRoot μ := by
  rcases (Submodule.ne_bot_iff _).1 h with ⟨w, ⟨H, ne0⟩⟩
  refine Or.resolve_right (smul_eq_zero.1 ?_) ne0
  rw [← aeval_apply_of_hasEigenvector ⟨H, ne0⟩]
  simp

section IsDomain

variable [IsDomain R] [Module.Finite R M]

theorem hasEigenvalue_of_isRoot (h : (minpoly R f).IsRoot μ) : f.HasEigenvalue μ := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr h
  obtain ⟨v, hv⟩ : ∃ v : M, q.aeval f v ≠ 0 := by
    by_contra! h_contra
    have := minpoly.min R f
      ((monic_X_sub_C μ).of_mul_monic_left (hq ▸ minpoly.monic (Algebra.IsIntegral.isIntegral f)))
      (LinearMap.ext h_contra)
    rw [hq, degree_mul, degree_X_sub_C, degree_eq_natDegree] at this
    · norm_cast at this; grind
    · rintro rfl
      exact minpoly.ne_zero (Algebra.IsIntegral.isIntegral f) (mul_zero (X - C μ) ▸ hq)
  refine Module.End.hasEigenvalue_of_hasEigenvector (hasEigenvector_iff.mpr ⟨?_, hv⟩)
  simpa [sub_eq_zero, hq] using congr($(minpoly.aeval R f) v)

variable [NoZeroSMulDivisors R M]

theorem hasEigenvalue_iff_isRoot : f.HasEigenvalue μ ↔ (minpoly R f).IsRoot μ :=
  ⟨isRoot_of_hasEigenvalue, hasEigenvalue_of_isRoot⟩

variable (f)

lemma finite_hasEigenvalue : Set.Finite f.HasEigenvalue := by
  have h : minpoly R f ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R := R) f)
  convert (minpoly R f).rootSet_finite R
  ext μ
  change f.HasEigenvalue μ ↔ _
  rw [hasEigenvalue_iff_isRoot, mem_rootSet_of_ne h, IsRoot, coe_aeval_eq_eval]

/-- An endomorphism of a finite-dimensional vector space has finitely many eigenvalues. -/
noncomputable instance : Fintype f.Eigenvalues :=
  Set.Finite.fintype f.finite_hasEigenvalue

end IsDomain

end CommRing

section Field

variable {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]

theorem eigenspace_aeval_polynomial_degree_1 (f : End K V) (q : K[X]) (hq : degree q = 1) :
    eigenspace f (-q.coeff 0 / q.leadingCoeff) = LinearMap.ker (aeval f q) :=
  calc
    eigenspace f (-q.coeff 0 / q.leadingCoeff)
    _ = LinearMap.ker (q.leadingCoeff • f - algebraMap K (End K V) (-q.coeff 0)) := by
          apply eigenspace_div
          rw [Ne, leadingCoeff_eq_zero_iff_deg_eq_bot, hq]
          exact WithBot.one_ne_bot
    _ = LinearMap.ker (aeval f (C q.leadingCoeff * X + C (q.coeff 0))) := by
          rw [C_mul', aeval_def]; simp [algebraMap, Algebra.algebraMap]
    _ = LinearMap.ker (aeval f q) := by rwa [← eq_X_add_C_of_degree_eq_one]

end Field

end End

end Module

section FiniteSpectrum

/-- An endomorphism of a finite-dimensional vector space has a finite spectrum. -/
theorem Module.End.finite_spectrum {K : Type v} {V : Type w} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : Module.End K V) :
    Set.Finite (spectrum K f) := by
  convert f.finite_hasEigenvalue
  ext f x
  exact Module.End.hasEigenvalue_iff_mem_spectrum.symm

variable {n R : Type*} [Field R] [Fintype n] [DecidableEq n]

/-- An n x n matrix over a field has a finite spectrum. -/
theorem Matrix.finite_spectrum (A : Matrix n n R) : Set.Finite (spectrum R A) := by
  rw [← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv <| Pi.basisFun R n) A]
  exact Module.End.finite_spectrum _

instance Matrix.instFiniteSpectrum (A : Matrix n n R) : Finite (spectrum R A) :=
  Set.finite_coe_iff.mpr (Matrix.finite_spectrum A)

end FiniteSpectrum
