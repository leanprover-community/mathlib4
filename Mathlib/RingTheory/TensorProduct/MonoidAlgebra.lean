/-
Copyright (c) 2025 Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mrugała
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Monoid algebras commute with base change

In this file we show that monoid algebras are stable under pushout.
-/

@[expose] public noncomputable section

open Algebra TensorProduct

namespace MonoidAlgebra
variable {R M N S A B : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring A] [CommSemiring B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A] [IsScalarTower R S A]
  [CommMonoid M] [CommMonoid N]

-- Note: Cannot be additivised automatically because of the use of `Multiplicative`
-- in `AddMonoidAlgebra.liftNCAlgHom` and `of`
/-- Implementation detail. -/
noncomputable def _root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun [AddCommMonoid M] :
    AddMonoidAlgebra (A ⊗[R] B) M →ₐ[S] A ⊗[R] AddMonoidAlgebra B M :=
  AddMonoidAlgebra.liftNCAlgHom
    (Algebra.TensorProduct.map (.id _ _) AddMonoidAlgebra.singleZeroAlgHom)
    (Algebra.TensorProduct.includeRight.toMonoidHom.comp <| AddMonoidAlgebra.of B M)
      fun _ _ ↦ .all ..

/-- Implementation detail. -/
@[to_additive existing (dont_translate := R)]
def rTensorEquivAlgEquiv.invFun : (A ⊗[R] B)[M] →ₐ[S] A ⊗[R] B[M] :=
  MonoidAlgebra.liftNCAlgHom (Algebra.TensorProduct.map (.id _ _) singleOneAlgHom)
    (Algebra.TensorProduct.includeRight.toMonoidHom.comp (of B M)) fun _ _ ↦ .all ..

omit [CommMonoid M] in
variable (R A B) [AddCommMonoid M] in
lemma _root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun_tmul (a : A) (m : M) (b : B) :
    AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun (S := S) (.single m (a ⊗ₜ[R] b)) =
       a ⊗ₜ .single m b := by
  simp [AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun]

@[to_additive existing (dont_translate := R) (attr := simp)]
lemma rTensorEquivAlgEquiv.invFun_tmul (a : A) (m : M) (b : B) :
    rTensorEquivAlgEquiv.invFun (S := S) (single m (a ⊗ₜ[R] b)) = a ⊗ₜ single m b := by
  simp [rTensorEquivAlgEquiv.invFun]

variable (R S A B) in
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/
@[to_additive (dont_translate := R S A B)
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/]
noncomputable def rTensorEquivAlgEquiv : A ⊗[R] B[M] ≃ₐ[S] (A ⊗[R] B)[M] := by
  refine .restrictScalars S <| .ofAlgHom
    (Algebra.TensorProduct.lift
      ((IsScalarTower.toAlgHom A (A ⊗[R] B) _).comp Algebra.TensorProduct.includeLeft)
      (mapAlgHom _ Algebra.TensorProduct.includeRight) fun p n ↦ .all ..)
      rTensorEquivAlgEquiv.invFun ?_ ?_
  · apply AlgHom.toLinearMap_injective
    ext
    simp
  · ext : 1
    apply AlgHom.toLinearMap_injective
    ext
    simp

@[to_additive (dont_translate := R A B) (attr := simp)]
lemma rTensorEquiv_tmulAlgEquiv (a : A) (p : B[M]) :
    rTensorEquivAlgEquiv R S A B (a ⊗ₜ p) =
      a • mapAlgHom M Algebra.TensorProduct.includeRight p := by
  simp [rTensorEquivAlgEquiv, Algebra.smul_def]

@[to_additive (dont_translate := R A B) (attr := simp)]
lemma rTensorEquiv_symm_singleAlgEquiv (m : M) (a : A) (b : B) :
    (rTensorEquivAlgEquiv R S A B).symm (single m (a ⊗ₜ b)) = a ⊗ₜ single m b :=
  rTensorEquivAlgEquiv.invFun_tmul ..

variable (R A B) in
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/
@[to_additive (dont_translate := R A B)
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/]
noncomputable def lTensorAlgEquiv : A[M] ⊗[R] B ≃ₐ[R] (A ⊗[R] B)[M] :=
  (Algebra.TensorProduct.comm ..).trans <| (rTensorEquivAlgEquiv _ _ _ _).trans <|
    mapAlgEquiv _ _ <| Algebra.TensorProduct.comm ..

@[to_additive (dont_translate := R A B) (attr := simp)]
lemma lTensorAlgEquiv_symm_single (m : M) (a : A) (b : B) :
    (lTensorAlgEquiv R A B).symm (single m (a ⊗ₜ b)) = single m a ⊗ₜ b := by
  simp [lTensorAlgEquiv]

variable (R A) in
/-- The base change of `R[M]` to an `R`-algebra `A` is isomorphic to `A[M]` as an `A`-algebra. -/
@[to_additive (dont_translate := R A)
/-- The base change of `R[M]` to an `R`-algebra `A` is isomorphic to `A[M]` as an `A`-algebra. -/]
noncomputable def scalarTensorEquiv : A ⊗[R] R[M] ≃ₐ[A] A[M] :=
  (rTensorEquivAlgEquiv ..).trans <| mapAlgEquiv A M <| Algebra.TensorProduct.rid R A A

@[to_additive (dont_translate := R A) (attr := simp)]
lemma scalarTensorEquiv_tmul (a : A) (p : R[M]) :
    scalarTensorEquiv R A (a ⊗ₜ p) = a • mapAlgHom M (Algebra.ofId ..) p := by
  ext; simp [scalarTensorEquiv]; simp [Algebra.smul_def, Algebra.commutes]

@[to_additive (dont_translate := R A) (attr := simp)]
lemma scalarTensorEquiv_symm_single (m : M) (a : A) :
    (scalarTensorEquiv R A).symm (single m a) = a ⊗ₜ single m 1 := by simp [scalarTensorEquiv]

open scoped AlgebraMonoidAlgebra

variable [Algebra S B] [Algebra A B] [IsScalarTower R A B] [IsScalarTower R S B]

@[to_additive (dont_translate := R S B)]
instance instIsPushout [IsPushout R S A B] : IsPushout R S A[M] B[M] where
  out := .of_equiv ((rTensorEquivAlgEquiv R S S A (M := M)).trans <|
      mapAlgEquiv S M <| IsPushout.equiv R S A B).toLinearEquiv fun x ↦ by
    induction x using induction_linear <;> simp_all [IsPushout.equiv_tmul]

@[to_additive (dont_translate := R)]
instance instIsPushout' [IsPushout R A S B] : IsPushout R A[M] S B[M] :=
  have : IsPushout R S A B := .symm ‹_›; .symm inferInstance

omit [CommMonoid M] [CommMonoid N]

-- TODO: Generalise to different base rings, strengthen to an `AlgEquiv`
variable (R) in
/-- The tensor product of two monoid algebras is the monoid algebra of their product. -/
@[to_additive (dont_translate := R) (attr := simps! apply_coeff)
/-- The tensor product of two monoid algebras is the monoid algebra of their product. -/]
noncomputable def tensorEquiv : R[M] ⊗[R] R[N] ≃ₗ[R] R[M × N] :=
  TensorProduct.congr (coeffLinearEquiv _) (coeffLinearEquiv _) ≪≫ₗ
    finsuppTensorFinsupp' .. ≪≫ₗ (coeffLinearEquiv _).symm

@[to_additive (dont_translate := R) (attr := simp)]
lemma tensorEquiv_single_tmul_single (m : M) (r₁ : R) (n : N) (r₂ : R) :
    tensorEquiv R (single m r₁ ⊗ₜ single n r₂) = single (m, n) (r₁ * r₂) := by ext; simp

@[to_additive (dont_translate := R)]
lemma tensorEquiv_symm_single_eq_single_one_tmul (mn : M × N) (r : R) :
    (tensorEquiv R).symm (single mn r) = single mn.1 1 ⊗ₜ single mn.2 r := by
  simp [tensorEquiv, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

@[to_additive (dont_translate := R)]
lemma tensorEquiv_symm_single_eq_tmul_single_one (mn : M × N) (r : R) :
    (tensorEquiv R).symm (single mn r) = single mn.1 r ⊗ₜ single mn.2 1 := by
  simp [tensorEquiv, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one]

end MonoidAlgebra

end
