/-
Copyright (c) 2025 Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mrugała
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Monoid algebras commute with base change

In this file we show that monoid algebras are stable under pushout.

## TODO

Additivise
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace MonoidAlgebra
variable {R M S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [CommMonoid M]
variable [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]

variable (R A B) in
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/
noncomputable def tensorEquiv : A ⊗[R] B[M] ≃ₐ[A] (A ⊗[R] B)[M] := by
  refine .ofAlgHom
    (Algebra.TensorProduct.lift
      ((IsScalarTower.toAlgHom A (A ⊗[R] B) _).comp Algebra.TensorProduct.includeLeft)
      (mapRangeAlgHom _ Algebra.TensorProduct.includeRight) fun p n ↦ .all ..)
    (MonoidAlgebra.liftNCAlgHom (Algebra.TensorProduct.map (.id _ _) singleOneAlgHom)
      (Algebra.TensorProduct.includeRight.toMonoidHom.comp (of B M)) fun _ _ ↦ .all ..) ?_ ?_
  · apply AlgHom.toLinearMap_injective
    ext
    simp
  · ext : 1
    · ext
    apply AlgHom.toLinearMap_injective
    ext
    simp

@[simp]
lemma tensorEquiv_tmul (a : A) (p : B[M]) :
    tensorEquiv R A B (a ⊗ₜ p) = a • mapRangeAlgHom M Algebra.TensorProduct.includeRight p := by
  simp [tensorEquiv, Algebra.smul_def]

@[simp]
lemma tensorEquiv_symm_single (m : M) (a : A) (b : B) :
    (tensorEquiv R A B).symm (single m (a ⊗ₜ b)) = a ⊗ₜ single m b := by simp [tensorEquiv]

variable (R A) in
/-- The base change of `R[M]` to an `R`-algebra `A` is isomorphic to `A[M]` as an `A`-algebra. -/
noncomputable def scalarTensorEquiv : A ⊗[R] R[M] ≃ₐ[A] A[M] :=
  (tensorEquiv ..).trans <| mapRangeAlgEquiv A M <| Algebra.TensorProduct.rid R A A

@[simp]
lemma scalarTensorEquiv_tmul (a : A) (p : R[M]) :
    scalarTensorEquiv R A (a ⊗ₜ p) = a • mapRangeAlgHom M (Algebra.ofId ..) p := by
  ext; simp [scalarTensorEquiv]; simp [Algebra.smul_def, Algebra.commutes]

@[simp]
lemma scalarTensorEquiv_symm_single (m : M) (a : A) :
    (scalarTensorEquiv R A).symm (single m a) = a ⊗ₜ single m 1 := by simp [scalarTensorEquiv]

open scoped AlgebraMonoidAlgebra

instance [Algebra S B] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B]
    [Algebra.IsPushout R S A B] : Algebra.IsPushout R S A[M] B[M] where
  out := .of_equiv ((tensorEquiv (M := M) R S A).trans <|
      mapRangeAlgEquiv S M <| Algebra.IsPushout.equiv R S A B).toLinearEquiv fun x ↦ by
    induction x using Finsupp.induction_linear <;> simp_all [Algebra.IsPushout.equiv_tmul]

instance [Algebra S B] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B]
    [Algebra.IsPushout R A S B] : Algebra.IsPushout R A[M] S B[M] :=
  have : Algebra.IsPushout R S A B := .symm ‹_›
  .symm inferInstance

end MonoidAlgebra

end
