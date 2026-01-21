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

@[expose] public noncomputable section

open Algebra TensorProduct

namespace MonoidAlgebra
variable {R M S A B : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring A] [CommSemiring B]
variable [Algebra R S] [Algebra R A] [Algebra R B] [CommMonoid M]

-- Note: Cannot be additivised automatically because of the use of `Multiplicative`
-- in `AddMonoidAlgebra.liftNCAlgHom` and `of`
/-- Implementation detail. -/
noncomputable def _root_.AddMonoidAlgebra.tensorEquiv.invFun [AddCommMonoid M] :
    AddMonoidAlgebra (A ⊗[R] B) M →ₐ[A] A ⊗[R] AddMonoidAlgebra B M :=
  AddMonoidAlgebra.liftNCAlgHom
    (Algebra.TensorProduct.map (.id _ _) AddMonoidAlgebra.singleZeroAlgHom)
    (Algebra.TensorProduct.includeRight.toMonoidHom.comp <| AddMonoidAlgebra.of B M)
      fun _ _ ↦ .all ..

/-- Implementation detail. -/
@[to_additive existing (dont_translate := R A B)]
def tensorEquiv.invFun : (A ⊗[R] B)[M] →ₐ[A] A ⊗[R] B[M] :=
  MonoidAlgebra.liftNCAlgHom (Algebra.TensorProduct.map (.id _ _) singleOneAlgHom)
    (Algebra.TensorProduct.includeRight.toMonoidHom.comp (of B M)) fun _ _ ↦ .all ..

omit [CommMonoid M] in
variable (R A B) [AddCommMonoid M] in
lemma _root_.AddMonoidAlgebra.tensorEquiv.invFun_tmul (a : A) (m : M) (b : B) :
    AddMonoidAlgebra.tensorEquiv.invFun (single m (a ⊗ₜ[R] b)) = a ⊗ₜ single m b := by
  simp [AddMonoidAlgebra.tensorEquiv.invFun]

@[to_additive existing (dont_translate := R A B) (attr := simp)]
lemma tensorEquiv.invFun_tmul (a : A) (m : M) (b : B) :
    tensorEquiv.invFun (single m (a ⊗ₜ[R] b)) = a ⊗ₜ single m b := by
  simp [tensorEquiv.invFun]

variable (R A B) in
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/
@[to_additive (dont_translate := R A B)
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/]
noncomputable def tensorEquiv : A ⊗[R] B[M] ≃ₐ[A] (A ⊗[R] B)[M] := by
  refine .ofAlgHom
    (Algebra.TensorProduct.lift
      ((IsScalarTower.toAlgHom A (A ⊗[R] B) _).comp Algebra.TensorProduct.includeLeft)
      (mapRangeAlgHom _ Algebra.TensorProduct.includeRight) fun p n ↦ .all ..)
      tensorEquiv.invFun ?_ ?_
  · apply AlgHom.toLinearMap_injective
    ext
    simp
  · ext : 1
    · ext
    apply AlgHom.toLinearMap_injective
    ext
    simp

@[to_additive (dont_translate := A B) (attr := simp)]
lemma tensorEquiv_tmul (a : A) (p : B[M]) :
    tensorEquiv R A B (a ⊗ₜ p) = a • mapRangeAlgHom M Algebra.TensorProduct.includeRight p := by
  simp [tensorEquiv, Algebra.smul_def]

@[to_additive (dont_translate := R A B) (attr := simp)]
lemma tensorEquiv_symm_single (m : M) (a : A) (b : B) :
    (tensorEquiv R A B).symm (single m (a ⊗ₜ b)) = a ⊗ₜ single m b := tensorEquiv.invFun_tmul ..

variable (R A) in
/-- The base change of `R[M]` to an `R`-algebra `A` is isomorphic to `A[M]` as an `A`-algebra. -/
@[to_additive (dont_translate := R A) (relevant_arg := M)
/-- The base change of `R[M]` to an `R`-algebra `A` is isomorphic to `A[M]` as an `A`-algebra. -/]
noncomputable def scalarTensorEquiv : A ⊗[R] R[M] ≃ₐ[A] A[M] :=
  (tensorEquiv ..).trans <| mapRangeAlgEquiv A M <| Algebra.TensorProduct.rid R A A

@[to_additive (dont_translate := R A) (relevant_arg := M) (attr := simp)]
lemma scalarTensorEquiv_tmul (a : A) (p : R[M]) :
    scalarTensorEquiv R A (a ⊗ₜ p) = a • mapRangeAlgHom M (Algebra.ofId ..) p := by
  ext; simp [scalarTensorEquiv]; simp [Algebra.smul_def, Algebra.commutes]

@[to_additive (dont_translate := R A) (relevant_arg := M) (attr := simp)]
lemma scalarTensorEquiv_symm_single (m : M) (a : A) :
    (scalarTensorEquiv R A).symm (single m a) = a ⊗ₜ single m 1 := by simp [scalarTensorEquiv]

open scoped AlgebraMonoidAlgebra

variable [Algebra S B] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B]

@[to_additive (dont_translate := R S B)]
instance instIsPushout [IsPushout R S A B] : IsPushout R S A[M] B[M] where
  out := .of_equiv ((tensorEquiv (M := M) R S A).trans <|
      mapRangeAlgEquiv S M <| IsPushout.equiv R S A B).toLinearEquiv fun x ↦ by
    induction x using induction_linear <;> simp_all [IsPushout.equiv_tmul]

@[to_additive (dont_translate := R)]
instance instIsPushout' [IsPushout R A S B] : IsPushout R A[M] S B[M] :=
  have : IsPushout R S A B := .symm ‹_›; .symm inferInstance

end MonoidAlgebra

end
