/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Andrew Yang
-/
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Coalgebra.Equiv

/-!
# Tensor products of coalgebras

Given two `R`-coalgebras `M, N`, we can define a natural comultiplication map
`Δ : M ⊗[R] N → (M ⊗[R] N) ⊗[R] (M ⊗[R] N)` and counit map `ε : M ⊗[R] N → R` induced by
the comultiplication and counit maps of `M` and `N`.

In this file we show that `Δ, ε` satisfy the axioms of a coalgebra, and also define other data
in the monoidal structure on `R`-coalgebras, like the tensor product of two coalgebra morphisms
as a coalgebra morphism.

-/

open TensorProduct

variable {R A B : Type*} [CommSemiring R] [AddCommMonoid B] [AddCommMonoid A]
    [Module R A] [Module R B] [Coalgebra R A] [Coalgebra R B]

namespace TensorProduct

open Coalgebra

noncomputable
instance instCoalgebraStruct : CoalgebraStruct R (A ⊗[R] B) where
  comul :=
    AlgebraTensorModule.tensorTensorTensorComm R R R R A A B B ∘ₗ
      AlgebraTensorModule.map comul comul
  counit := AlgebraTensorModule.rid R R R ∘ₗ AlgebraTensorModule.map counit counit

lemma comul_def :
    Coalgebra.comul (R := R) (A := A ⊗[R] B) =
      AlgebraTensorModule.tensorTensorTensorComm R R R R A A B B ∘ₗ
        AlgebraTensorModule.map Coalgebra.comul Coalgebra.comul :=
  rfl

@[deprecated (since := "2025-04-09")] alias instCoalgebraStruct_comul := comul_def

lemma counit_def :
    Coalgebra.counit (R := R) (A := A ⊗[R] B) =
      AlgebraTensorModule.rid R R R ∘ₗ AlgebraTensorModule.map counit counit :=
  rfl

@[deprecated (since := "2025-04-09")] alias instCoalgebraStruct_counit := counit_def

@[simp]
lemma comul_tmul (x : A) (y : B) :
    comul (x ⊗ₜ y) =
      AlgebraTensorModule.tensorTensorTensorComm R R R R A A B B (comul x ⊗ₜ comul y) := rfl

@[simp]
lemma counit_tmul (x : A) (y : B) :
    counit (R := R) (x ⊗ₜ[R] y) = counit (R := R) y • counit (R := R) x := rfl

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
    TensorProduct.assoc R (A ⊗[R] B) (A ⊗[R] B) (A ⊗[R] B) ∘ₗ
      (comul (R := R) (A := (A ⊗[R] B))).rTensor (A ⊗[R] B) ∘ₗ
        (comul (R := R) (A := (A ⊗[R] B))) =
    (comul (R := R) (A := (A ⊗[R] B))).lTensor (A ⊗[R] B) ∘ₗ
      (comul (R := R) (A := (A ⊗[R] B))) := by
  ext x y
  let F : (A ⊗[R] A ⊗[R] A) ⊗[R] (B ⊗[R] B ⊗[R] B) ≃ₗ[R]
    (A ⊗[R] B) ⊗[R] (A ⊗[R] B) ⊗[R] A ⊗[R] B :=
    AlgebraTensorModule.tensorTensorTensorComm _ _ _ _ _ _ _ _ ≪≫ₗ
      AlgebraTensorModule.congr (.refl _ _)
        (AlgebraTensorModule.tensorTensorTensorComm _ _ _ _ _ _ _ _)
  let F' : (A ⊗[R] A ⊗[R] A) ⊗[R] (B ⊗[R] B ⊗[R] B) →ₗ[R]
      (A ⊗[R] B) ⊗[R] (A ⊗[R] B) ⊗[R] A ⊗[R] B :=
    TensorProduct.mapOfCompatibleSMul _ _ _ _ ∘ₗ
        TensorProduct.map .id (TensorProduct.mapOfCompatibleSMul _ _ _ _) ∘ₗ F.toLinearMap
  convert congr(F ($(Coalgebra.coassoc_apply x) ⊗ₜ[R] $(Coalgebra.coassoc_apply y))) using 1
  · dsimp
    hopf_tensor_induction comul (R := R) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    dsimp
    hopf_tensor_induction comul (R := R) x₁ with x₁₁ x₁₂
    hopf_tensor_induction comul (R := R) y₁ with y₁₁ y₁₂
    rfl
  · dsimp
    hopf_tensor_induction comul (R := R) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    dsimp
    hopf_tensor_induction comul (R := R) x₂ with x₂₁ x₂₂
    hopf_tensor_induction comul (R := R) y₂ with y₂₁ y₂₂
    rfl

noncomputable
instance instCoalgebra : Coalgebra R (A ⊗[R] B) where
  coassoc := coassoc (R := R)
  rTensor_counit_comp_comul := by
    ext x y
    convert congr((TensorProduct.lid R _).symm
      (TensorProduct.lid _ _ $(rTensor_counit_comul (R := R) x) ⊗ₜ[R]
        TensorProduct.lid _ _ $(rTensor_counit_comul (R := R) y)))
    · dsimp
      hopf_tensor_induction comul (R := R) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      apply (TensorProduct.lid R _).injective
      dsimp
      rw [tmul_smul, mul_smul, one_smul, smul_tmul']
    · dsimp
      simp only [one_smul]
  lTensor_counit_comp_comul := by
    ext x y
    convert congr((TensorProduct.rid R _).symm
      (TensorProduct.rid _ _ $(lTensor_counit_comul (R := R) x) ⊗ₜ[R]
        TensorProduct.rid _ _ $(lTensor_counit_comul (R := R) y)))
    · dsimp
      hopf_tensor_induction comul (R := R) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      apply (TensorProduct.rid R _).injective
      dsimp
      rw [tmul_smul, mul_smul, one_smul, smul_tmul']
    · dsimp
      simp only [one_smul]

end TensorProduct

namespace Coalgebra
namespace TensorProduct

variable {R M N P Q : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N]
  [Module R P] [Module R Q] [Coalgebra R M]
  [Coalgebra R N] [Coalgebra R P] [Coalgebra R Q]

section

/-- The tensor product of two coalgebra morphisms as a coalgebra morphism. -/
noncomputable def map (f : M →ₗc[R] N) (g : P →ₗc[R] Q) :
    M ⊗[R] P →ₗc[R] N ⊗[R] Q where
  toLinearMap := AlgebraTensorModule.map f.toLinearMap g.toLinearMap
  counit_comp := by ext; simp
  map_comp_comul := by
    ext x y
    dsimp
    simp only [← CoalgHomClass.map_comp_comul_apply]
    hopf_tensor_induction comul (R := R) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    simp

@[simp]
theorem map_tmul (f : M →ₗc[R] N) (g : P →ₗc[R] Q) (x : M) (y : P) :
    map f g (x ⊗ₜ y) = f x ⊗ₜ g y :=
  rfl

@[simp]
theorem map_toLinearMap (f : M →ₗc[R] N) (g : P →ₗc[R] Q) :
    map f g = AlgebraTensorModule.map (f : M →ₗ[R] N) (g : P →ₗ[R] Q) := rfl

variable (R M N P)

/-- The associator for tensor products of R-coalgebras, as a coalgebra equivalence. -/
protected noncomputable def assoc :
    (M ⊗[R] N) ⊗[R] P ≃ₗc[R] M ⊗[R] (N ⊗[R] P) :=
  { AlgebraTensorModule.assoc R R R M N P with
    counit_comp := by ext; simp [mul_assoc]
    map_comp_comul := by
      ext x y z
      dsimp
      hopf_tensor_induction comul (R := R) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      hopf_tensor_induction comul (R := R) z with z₁ z₂
      simp }

variable {R M N P}

@[simp]
theorem assoc_tmul (x : M) (y : N) (z : P) :
    Coalgebra.TensorProduct.assoc R M N P ((x ⊗ₜ y) ⊗ₜ z) = x ⊗ₜ (y ⊗ₜ z) :=
  rfl

@[simp]
theorem assoc_symm_tmul (x : M) (y : N) (z : P) :
    (Coalgebra.TensorProduct.assoc R M N P).symm (x ⊗ₜ (y ⊗ₜ z)) = (x ⊗ₜ y) ⊗ₜ z :=
  rfl

@[simp]
theorem assoc_toLinearEquiv :
    Coalgebra.TensorProduct.assoc R M N P = AlgebraTensorModule.assoc R R R M N P := rfl

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

variable (R M)

/-- The base ring is a right identity for the tensor product of coalgebras, up to
coalgebra equivalence. -/
protected noncomputable def rid : M ⊗[R] R ≃ₗc[R] M :=
  { AlgebraTensorModule.rid R R M with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x
      dsimp
      simp only [one_smul]
      hopf_tensor_induction comul (R := R) x with x₁ x₂
      simp }

variable {R M}

@[simp]
theorem rid_toLinearEquiv :
    (Coalgebra.TensorProduct.rid R M) = AlgebraTensorModule.rid R R M := rfl

@[simp]
theorem rid_tmul (r : R) (a : M) : Coalgebra.TensorProduct.rid R M (a ⊗ₜ r) = r • a := rfl

@[simp]
theorem rid_symm_apply (a : M) : (Coalgebra.TensorProduct.rid R M).symm a = a ⊗ₜ 1 := rfl

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
