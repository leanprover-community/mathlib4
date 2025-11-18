/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Polynomials supported by a set of variables

This file contains the definition and lemmas about `MvPolynomial.supported`.

## Main definitions

* `MvPolynomial.supported` : Given a set `s : Set σ`, `supported R s` is the subalgebra of
  `MvPolynomial σ R` consisting of polynomials whose set of variables is contained in `s`.
  This subalgebra is isomorphic to `MvPolynomial s R`.

## Tags
variables, polynomial, vars
-/


universe u v w

namespace MvPolynomial

variable {σ : Type*} {R : Type u}

section CommSemiring

variable [CommSemiring R] {p : MvPolynomial σ R}

variable (R) in
/-- The set of polynomials whose variables are contained in `s` as a `Subalgebra` over `R`. -/
noncomputable def supported (s : Set σ) : Subalgebra R (MvPolynomial σ R) :=
  Algebra.adjoin R (X '' s)

open Algebra

theorem supported_eq_range_rename (s : Set σ) : supported R s = (rename ((↑) : s → σ)).range := by
  rw [supported, Set.image_eq_range, adjoin_range_eq_range_aeval, rename]
  congr

/-- The isomorphism between the subalgebra of polynomials supported by `s` and
`MvPolynomial s R`. -/
noncomputable def supportedEquivMvPolynomial (s : Set σ) : supported R s ≃ₐ[R] MvPolynomial s R :=
  (Subalgebra.equivOfEq _ _ (supported_eq_range_rename s)).trans
    (AlgEquiv.ofInjective (rename ((↑) : s → σ)) (rename_injective _ Subtype.val_injective)).symm

@[simp]
theorem supportedEquivMvPolynomial_symm_C (s : Set σ) (x : R) :
    (supportedEquivMvPolynomial s).symm (C x) = algebraMap R (supported R s) x := by
  ext1
  simp [supportedEquivMvPolynomial, MvPolynomial.algebraMap_eq]

@[simp]
theorem supportedEquivMvPolynomial_symm_X (s : Set σ) (i : s) :
    (↑((supportedEquivMvPolynomial s).symm (X i : MvPolynomial s R)) : MvPolynomial σ R) = X ↑i :=
  by simp [supportedEquivMvPolynomial]

variable {s t : Set σ}

theorem mem_supported : p ∈ supported R s ↔ ↑p.vars ⊆ s := by
  classical
  rw [supported_eq_range_rename, AlgHom.mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    refine _root_.trans (Finset.coe_subset.2 (vars_rename _ _)) ?_
    simp
  · intro hs
    exact exists_rename_eq_of_vars_subset_range p ((↑) : s → σ) Subtype.val_injective (by simpa)

theorem supported_eq_vars_subset : (supported R s : Set (MvPolynomial σ R)) = { p | ↑p.vars ⊆ s } :=
  Set.ext fun _ ↦ mem_supported

@[simp]
theorem mem_supported_vars (p : MvPolynomial σ R) : p ∈ supported R (↑p.vars : Set σ) := by
  rw [mem_supported]

variable (s)

theorem supported_eq_adjoin_X : supported R s = Algebra.adjoin R (X '' s) := rfl

@[simp]
theorem supported_univ : supported R (Set.univ : Set σ) = ⊤ := by
  simp [Algebra.eq_top_iff, mem_supported]

@[simp]
theorem supported_empty : supported R (∅ : Set σ) = ⊥ := by simp [supported_eq_adjoin_X]

variable {s}

theorem supported_mono (st : s ⊆ t) : supported R s ≤ supported R t :=
  Algebra.adjoin_mono (Set.image_mono st)

@[simp]
theorem X_mem_supported [Nontrivial R] {i : σ} : X i ∈ supported R s ↔ i ∈ s := by
  simp [mem_supported]

@[simp]
theorem supported_le_supported_iff [Nontrivial R] : supported R s ≤ supported R t ↔ s ⊆ t := by
  constructor
  · intro h i
    simpa using @h (X i)
  · exact supported_mono

theorem supported_strictMono [Nontrivial R] :
    StrictMono (supported R : Set σ → Subalgebra R (MvPolynomial σ R)) :=
  strictMono_of_le_iff_le fun _ _ ↦ supported_le_supported_iff.symm

theorem exists_restrict_to_vars (R : Type*) [CommRing R] {F : MvPolynomial σ ℤ}
    (hF : ↑F.vars ⊆ s) : ∃ f : (s → R) → R, ∀ x : σ → R, f (x ∘ (↑) : s → R) = aeval x F := by
  rw [← mem_supported, supported_eq_range_rename, AlgHom.mem_range] at hF
  obtain ⟨F', hF'⟩ := hF
  use fun z ↦ aeval z F'
  intro x
  simp only [← hF', aeval_rename]

end CommSemiring

end MvPolynomial
