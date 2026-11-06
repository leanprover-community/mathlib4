/-
Copyright (c) 2026 Antoine Chambert-Loir, María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Homogeneous algebra morphisms between graded algebras

* `AlgHom.isHomogeneous`: property, for an algebra morphism,
to be homogeneous with respect to graded structures on the source and the target.

* `AlgHom.isHomogeneous_aeval`: `MvPolynomial.aeval` is homogeneous
when the indeterminates are mapped to homogeneous elements
of adequae grades.

-/

@[expose] public section

namespace AlgHom

open MvPolynomial

variable {R S : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] [Algebra R S]
  {ι κ : Type*} {A : Type*} [CommSemiring A] [Algebra R A]
  (𝒜 : ι → Submodule R A)

/-- An `R`-algebra map `f` between graded algebras `A` and `B` is homogeneous
with respect to a map `φ : ι → κ` if, for every degree `i`, `f(𝒜 i) ⊆ ℬ (φ i)`. -/
def isHomogeneous {B : Type*} [CommSemiring B] [Algebra R B] [Algebra S B]
    (ℬ : κ → Submodule S B) (φ : ι → κ) (f : A →ₐ[R] B) : Prop :=
  ∀ i a, a ∈ 𝒜 i → f a ∈ ℬ (φ i)

/-- The evaluation of a weighted homogeneous polynomial at
  elements of adequate grades is homogeneous -/
theorem isHomogeneous_aeval [DecidableEq ι] [AddCommMonoid ι] [AddCommMonoid κ] [GradedAlgebra 𝒜]
    {σ : Type*} {w : σ → κ} {φ : κ →+ ι} {f : σ → A} (h : ∀ s : σ, f s ∈ 𝒜 (φ (w s))) :
    isHomogeneous (weightedHomogeneousSubmodule R w) 𝒜 φ (aeval f) := by
  intro i p hp
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro c hc
  rw [aeval_monomial, ← smul_eq_mul, algebraMap_smul]
  apply Submodule.smul_mem
  rw [Finsupp.prod]
  convert SetLike.finset_prod_npow_mem_graded c.support (fun j ↦ φ (w j)) f ⇑c (fun s _ ↦ h s)
  rw [mem_support_iff] at hc
  simp_rw [← map_nsmul, ← map_sum]
  rw [← hp hc, Finsupp.weight_apply, Finsupp.sum]

end AlgHom
