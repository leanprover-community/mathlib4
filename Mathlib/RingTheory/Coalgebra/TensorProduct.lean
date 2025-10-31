/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Andrew Yang
-/
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Coalgebra.Equiv

/-!
# Tensor products of coalgebras

Suppose `S` is an `R`-algebra. Given an `S`-coalgebra `A` and `R`-coalgebra `B`, we can define
a natural comultiplication map `Δ : A ⊗[R] B → (A ⊗[R] B) ⊗[S] (A ⊗[R] B)`
and counit map `ε : A ⊗[R] B → S` induced by the comultiplication and counit maps of `A` and `B`.

In this file we show that `Δ, ε` satisfy the axioms of a coalgebra, and also define other data
in the monoidal structure on `R`-coalgebras, like the tensor product of two coalgebra morphisms
as a coalgebra morphism.

In particular, when `R = S` we get tensor products of coalgebras, and when `A = S` we get
the base change `S ⊗[R] B` as an `S`-coalgebra.

-/

open TensorProduct

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [AddCommMonoid A] [AddCommMonoid B]
    [Algebra R S] [Module R A] [Module S A] [Module R B] [IsScalarTower R S A]

namespace TensorProduct

open Coalgebra

section CoalgebraStruct
variable [CoalgebraStruct R B] [CoalgebraStruct S A]

noncomputable
instance instCoalgebraStruct : CoalgebraStruct S (A ⊗[R] B) where
  comul :=
    AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B ∘ₗ
      AlgebraTensorModule.map comul comul
  counit := AlgebraTensorModule.rid R S S ∘ₗ AlgebraTensorModule.map counit counit

lemma comul_def :
    Coalgebra.comul (R := S) (A := A ⊗[R] B) =
      AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B ∘ₗ
        AlgebraTensorModule.map Coalgebra.comul Coalgebra.comul :=
  rfl

lemma counit_def :
    Coalgebra.counit (R := S) (A := A ⊗[R] B) =
      AlgebraTensorModule.rid R S S ∘ₗ AlgebraTensorModule.map counit counit :=
  rfl

@[simp]
lemma comul_tmul (x : A) (y : B) :
    comul (x ⊗ₜ y) =
      AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B (comul x ⊗ₜ comul y) := rfl

@[simp]
lemma counit_tmul (x : A) (y : B) :
    counit (R := S) (x ⊗ₜ[R] y) = counit (R := R) y • counit (R := S) x := rfl

end CoalgebraStruct

variable [Coalgebra R B] [Coalgebra S A]

open Lean.Parser.Tactic in
/-- `hopf_tensor_induction x with x₁ x₂` attempts to replace `x` by
`x₁ ⊗ₜ x₂` via linearity. This is an implementation detail that is used to set up tensor products
of coalgebras, bialgebras, and hopf algebras, and shouldn't be relied on downstream. -/
scoped macro "hopf_tensor_induction " var:elimTarget "with " var₁:ident var₂:ident : tactic =>
  `(tactic|
    (induction $var with
      | zero => simp only [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero,
          zero_tmul, zero_mul, mul_zero]
      | add _ _ h₁ h₂ =>
        -- avoid the more general `map_add` for performance reasons
        simp only [LinearEquiv.map_add, LinearMap.map_add,
          tmul_add, add_tmul, add_mul, mul_add, h₁, h₂]
      | tmul $var₁ $var₂ => ?_))

private lemma coassoc :
    TensorProduct.assoc S (A ⊗[R] B) (A ⊗[R] B) (A ⊗[R] B) ∘ₗ
      (comul (R := S) (A := (A ⊗[R] B))).rTensor (A ⊗[R] B) ∘ₗ
        (comul (R := S) (A := (A ⊗[R] B))) =
    (comul (R := S) (A := (A ⊗[R] B))).lTensor (A ⊗[R] B) ∘ₗ
      (comul (R := S) (A := (A ⊗[R] B))) := by
  ext x y
  let F : A ⊗[S] (A ⊗[S] A) ⊗[R] (B ⊗[R] (B ⊗[R] B)) ≃ₗ[S]
    A ⊗[R] B ⊗[S] (A ⊗[R] B ⊗[S] (A ⊗[R] B)) :=
    AlgebraTensorModule.tensorTensorTensorComm _ _ _ _ _ _ _ _ ≪≫ₗ
      AlgebraTensorModule.congr (.refl _ _)
        (AlgebraTensorModule.tensorTensorTensorComm _ _ _ _ _ _ _ _)
  let F' : A ⊗[S] (A ⊗[S] A) ⊗[R] (B ⊗[R] (B ⊗[R] B)) →ₗ[S]
      A ⊗[R] B ⊗[S] (A ⊗[R] B ⊗[S] (A ⊗[R] B)) :=
    TensorProduct.mapOfCompatibleSMul _ _ _ _ ∘ₗ
        TensorProduct.map .id (TensorProduct.mapOfCompatibleSMul _ _ _ _) ∘ₗ F.toLinearMap
  convert congr(F ($(Coalgebra.coassoc_apply x) ⊗ₜ[R] $(Coalgebra.coassoc_apply y))) using 1
  · dsimp
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    dsimp
    hopf_tensor_induction comul (R := S) x₁ with x₁₁ x₁₂
    hopf_tensor_induction comul (R := R) y₁ with y₁₁ y₁₂
    rfl
  · dsimp
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    dsimp
    hopf_tensor_induction comul (R := S) x₂ with x₂₁ x₂₂
    hopf_tensor_induction comul (R := R) y₂ with y₂₁ y₂₂
    rfl

noncomputable
instance instCoalgebra : Coalgebra S (A ⊗[R] B) where
  coassoc := coassoc (R := R)
  rTensor_counit_comp_comul := by
    ext x y
    convert congr((TensorProduct.lid S _).symm
      (TensorProduct.lid _ _ $(rTensor_counit_comul (R := S) x) ⊗ₜ[R]
        TensorProduct.lid _ _ $(rTensor_counit_comul (R := R) y)))
    · dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      apply (TensorProduct.lid S _).injective
      dsimp
      rw [tmul_smul, smul_assoc, one_smul, smul_tmul']
    · dsimp
      simp only [one_smul]
  lTensor_counit_comp_comul := by
    ext x y
    convert congr((TensorProduct.rid S _).symm
      (TensorProduct.rid _ _ $(lTensor_counit_comul (R := S) x) ⊗ₜ[R]
        TensorProduct.rid _ _ $(lTensor_counit_comul (R := R) y)))
    · dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      apply (TensorProduct.rid S _).injective
      dsimp
      rw [tmul_smul, smul_assoc, one_smul, smul_tmul']
    · dsimp
      simp only [one_smul]

instance [IsCocomm S A] [IsCocomm R B] : IsCocomm S (A ⊗[R] B) where
  comm_comp_comul := by
    ext x y
    dsimp
    conv_rhs => rw [← comm_comul _ x, ← comm_comul _ y]
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    simp

end TensorProduct

namespace Coalgebra
namespace TensorProduct

variable {R S M N P Q : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N]
  [Module R P] [Module R Q] [Module S M] [IsScalarTower R S M] [Coalgebra S M] [Module S N]
  [IsScalarTower R S N] [Coalgebra S N] [Coalgebra R P] [Coalgebra R Q]

section

/-- The tensor product of two coalgebra morphisms as a coalgebra morphism. -/
noncomputable def map (f : M →ₗc[S] N) (g : P →ₗc[R] Q) :
    M ⊗[R] P →ₗc[S] N ⊗[R] Q where
  toLinearMap := AlgebraTensorModule.map f.toLinearMap g.toLinearMap
  counit_comp := by ext; simp
  map_comp_comul := by
    ext x y
    dsimp
    simp only [← CoalgHomClass.map_comp_comul_apply]
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    simp

@[simp]
theorem map_tmul (f : M →ₗc[S] N) (g : P →ₗc[R] Q) (x : M) (y : P) :
    map f g (x ⊗ₜ y) = f x ⊗ₜ g y :=
  rfl

@[simp]
theorem map_toLinearMap (f : M →ₗc[S] N) (g : P →ₗc[R] Q) :
    map f g = AlgebraTensorModule.map (f : M →ₗ[S] N) (g : P →ₗ[R] Q) := rfl

variable (R S M N P)

/-- The associator for tensor products of R-coalgebras, as a coalgebra equivalence. -/
protected noncomputable def assoc :
    (M ⊗[S] N) ⊗[R] P ≃ₗc[S] M ⊗[S] (N ⊗[R] P) :=
  { AlgebraTensorModule.assoc R S S M N P with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x y z
      dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := S) y with y₁ y₂
      hopf_tensor_induction comul (R := R) z with z₁ z₂
      simp }

variable {R S M N P}

@[simp]
theorem assoc_tmul (x : M) (y : N) (z : P) :
    Coalgebra.TensorProduct.assoc R S M N P ((x ⊗ₜ y) ⊗ₜ z) = x ⊗ₜ (y ⊗ₜ z) :=
  rfl

@[simp]
theorem assoc_symm_tmul (x : M) (y : N) (z : P) :
    (Coalgebra.TensorProduct.assoc R S M N P).symm (x ⊗ₜ (y ⊗ₜ z)) = (x ⊗ₜ y) ⊗ₜ z :=
  rfl

@[simp]
theorem assoc_toLinearEquiv :
    Coalgebra.TensorProduct.assoc R S M N P = AlgebraTensorModule.assoc R S S M N P := rfl

variable (R P)

/-- The base ring is a left identity for the tensor product of coalgebras, up to
coalgebra equivalence. -/
protected noncomputable def lid : R ⊗[R] P ≃ₗc[R] P :=
  { _root_.TensorProduct.lid R P with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x
      dsimp
      simp only [one_smul]
      hopf_tensor_induction comul (R := R) x with x₁ x₂
      simp }

variable {R P}

@[simp]
theorem lid_toLinearEquiv :
    (Coalgebra.TensorProduct.lid R P) = _root_.TensorProduct.lid R P := rfl

@[simp]
theorem lid_tmul (r : R) (a : P) : Coalgebra.TensorProduct.lid R P (r ⊗ₜ a) = r • a := rfl

@[simp]
theorem lid_symm_apply (a : P) : (Coalgebra.TensorProduct.lid R P).symm a = 1 ⊗ₜ a := rfl

variable (R S M) in
/-- The base ring is a right identity for the tensor product of coalgebras, up to
coalgebra equivalence. -/
protected noncomputable def rid : M ⊗[R] R ≃ₗc[S] M :=
  { AlgebraTensorModule.rid R S M with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x
      dsimp
      simp only [one_smul]
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      simp }

@[simp]
theorem rid_toLinearEquiv :
    (Coalgebra.TensorProduct.rid R S M) = AlgebraTensorModule.rid R S M := rfl

@[simp]
theorem rid_tmul (r : R) (a : M) : Coalgebra.TensorProduct.rid R S M (a ⊗ₜ r) = r • a := rfl

@[simp]
theorem rid_symm_apply (a : M) : (Coalgebra.TensorProduct.rid R S M).symm a = a ⊗ₜ 1 := rfl

end

end TensorProduct
end Coalgebra
namespace CoalgHom

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N]
  [Module R P] [Coalgebra R M] [Coalgebra R N] [Coalgebra R P]

variable (M)

/-- `lTensor M f : M ⊗ N →ₗc M ⊗ P` is the natural coalgebra morphism induced by `f : N →ₗc P`. -/
noncomputable abbrev lTensor (f : N →ₗc[R] P) : M ⊗[R] N →ₗc[R] M ⊗[R] P :=
  Coalgebra.TensorProduct.map (CoalgHom.id R M) f

/-- `rTensor M f : N ⊗ M →ₗc P ⊗ M` is the natural coalgebra morphism induced by `f : N →ₗc P`. -/
noncomputable abbrev rTensor (f : N →ₗc[R] P) : N ⊗[R] M →ₗc[R] P ⊗[R] M :=
  Coalgebra.TensorProduct.map f (CoalgHom.id R M)

end CoalgHom
