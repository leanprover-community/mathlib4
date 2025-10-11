/-
Copyright (c) 2025 Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mrugała
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.IsTensorProduct

/-!
# Monoid algebras are invariant under base change

In this file we show that monoid algebras are stable under pushout.

## TODO

Additivise
-/

noncomputable section

open TensorProduct

namespace MonoidAlgebra
variable {R M S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [CommMonoid M]
variable [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]

variable (R A B) in
/-- Tensoring `MonoidAlgebra R M` on the left by an `R`-algebra `A` is algebraically
equivalent to `MonoidAlgebra A M`. -/
noncomputable def tensorEquiv : A ⊗[R] MonoidAlgebra B M ≃ₐ[A] MonoidAlgebra (A ⊗[R] B) M := by
  refine .ofAlgHom
    (Algebra.TensorProduct.lift
      ((IsScalarTower.toAlgHom A (A ⊗[R] B) _).comp Algebra.TensorProduct.includeLeft)
      (mapRangeAlgHom _ Algebra.TensorProduct.includeRight)
      (fun p n => .all _ _))
    (MonoidAlgebra.liftNCAlgHom (Algebra.TensorProduct.map (.id _ _) singleOneAlgHom)
        ((Algebra.TensorProduct.includeRight.toMonoidHom.comp (of B M))) (fun _ _ ↦ .all _ _)) ?_ ?_
  · classical
    apply AlgHom.toLinearMap_injective
    ext
    simp [liftNCAlgHom, liftNCRingHom, single_apply]
  · ext : 1
    · ext
    apply AlgHom.toLinearMap_injective
    ext
    simp [liftNCAlgHom, liftNCRingHom, mapRangeAlgHom]

@[simp]
lemma tensorEquiv_tmul (a : A) (p : MonoidAlgebra B M) :
    tensorEquiv R A B (a ⊗ₜ p) = a • mapRangeAlgHom M Algebra.TensorProduct.includeRight p := by
  simp [tensorEquiv, Algebra.smul_def]

@[simp]
lemma algebraTensorAlgEquiv_symm_single (m : M) (a : A) (b : B) :
    (tensorEquiv R A B).symm (single m (a ⊗ₜ b)) = a ⊗ₜ single m b := by
  simp [tensorEquiv]

/-- The tensor product of the monoid algebra by an algebra `N`
is algebraically equivalent to a monoid algebra with coefficients in `N`. -/
noncomputable def scalarTensorEquiv : A ⊗[R] MonoidAlgebra R M ≃ₐ[A] MonoidAlgebra A M :=
  (tensorEquiv ..).trans (mapRangeAlgEquiv M (Algebra.TensorProduct.rid R A A))

attribute [local instance] algebraMonoidAlgebra in
instance [Algebra S B] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B]
    [Algebra.IsPushout R S A B] :
    Algebra.IsPushout R S (MonoidAlgebra A M) (MonoidAlgebra B M) where
  out := .of_equiv ((tensorEquiv (M := M) R S A).trans
      (mapRangeAlgEquiv M (Algebra.IsPushout.equiv R S A B))).toLinearEquiv fun x ↦ by
    induction x using Finsupp.induction_linear
    · simp
    · simp_all
    · simp [mapRangeAlgHom, mapRangeRingHom, liftNCRingHom, Algebra.IsPushout.equiv_tmul]

attribute [local instance] algebraMonoidAlgebra in
instance [Algebra S B] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B]
    [Algebra.IsPushout R A S B] : Algebra.IsPushout R (MonoidAlgebra A M) S (MonoidAlgebra B M) :=
  have : Algebra.IsPushout R S A B := .symm ‹_›
  .symm inferInstance

end MonoidAlgebra

end
