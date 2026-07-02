/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Convolution product on Hopf algebra maps

This file constructs the ring structure on bialgebra homs `C → A` where `C` and `A` are Hopf
algebras and multiplication is given by
```
         |
         μ
|   |   / \
f * g = f g
|   |   \ /
         δ
         |
```
diagrammatically, where `μ` stands for multiplication and `δ` for comultiplication.
-/

public section

suppress_compilation

open Algebra Coalgebra Bialgebra HopfAlgebra TensorProduct WithConv
open scoped RingTheory.LinearMap

variable {R A C : Type*} [CommSemiring R]

namespace HopfAlgebra
section Semiring
variable [Semiring A] [HopfAlgebra R A]

lemma antipode_comp_mul_comp_comm :
    antipode R ∘ₗ .mul' R A ∘ₗ (TensorProduct.comm R A A).toLinearMap =
      .mul' R A ∘ₗ map (antipode R) (antipode R) := by
  apply WithConv.toConv_injective
  apply left_inv_eq_right_inv (a := toConv <| LinearMap.mul' R A ∘ₗ TensorProduct.comm R A A) <;>
    ext a b
  · simp [((ℛ R a).tmul (ℛ R b)).convMul_apply, ← Bialgebra.counit_mul,
      ← sum_antipode_mul_eq_algebraMap_counit ((ℛ R b).mul (ℛ R a)),
      ← Finset.map_swap_product (ℛ R b).index (ℛ R a).index]
  · simp [((ℛ R a).tmul (ℛ R b)).convMul_apply,
      ← Finset.map_swap_product (ℛ R a).index (ℛ R b).index,
      Finset.sum_product (ℛ R b).index, ← Finset.mul_sum, mul_assoc ((ℛ R b).left _),
      ← mul_assoc ((ℛ R a).left _), ← Finset.sum_mul, sum_mul_antipode_eq_algebraMap_counit,
      ← (Algebra.commute_algebraMap_left (ε a) (_ : A)).left_comm,
      ← (Algebra.commute_algebraMap_left (ε a) (_ : A)).eq]

lemma antipode_mul_antidistrib (a b : A) : antipode R (a * b) = antipode R b * antipode R a := by
  exact congr($antipode_comp_mul_comp_comm (b ⊗ₜ a))

@[deprecated (since := "2026-06-05")] alias antipode_mul := antipode_mul_antidistrib

variable (R A) in
/-- The antipode of a commutative Hopf algebra as an anti-algebra hom. -/
@[expose, simps!]
def antipodeAlgHomOp : A →ₐ[R] Aᵐᵒᵖ := .ofLinearMap
    ((MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ antipode R)
    (MulOpposite.op_injective (by simp))
    (fun x y ↦ MulOpposite.op_injective (by simp [antipode_mul_antidistrib]))

end Semiring

variable [CommSemiring A] [HopfAlgebra R A]

lemma antipode_mul_distrib (a b : A) : antipode R (a * b) = antipode R a * antipode R b := by
  rw [antipode_mul_antidistrib, mul_comm]

variable (R A) in
/-- The antipode of a commutative Hopf algebra as an algebra hom. -/
@[expose, simps!]
def antipodeAlgHom : A →ₐ[R] A := .ofLinearMap (antipode R) antipode_one antipode_mul_distrib

@[simp] lemma toLinearMap_antipodeAlgHom : (antipodeAlgHom R A).toLinearMap = antipode R := rfl

end HopfAlgebra

namespace LinearMap

variable [Semiring C] [HopfAlgebra R C]

@[simp] lemma antipode_mul_id : toConv (antipode R (A := C)) * toConv id = 1 := by
  ext c; rw [(ℛ R c).convMul_apply]; simp [sum_antipode_mul_eq_algebraMap_counit (ℛ R c)]

@[simp] lemma id_mul_antipode : toConv id * toConv (antipode R (A := C)) = 1 := by
  ext c; rw [(ℛ R c).convMul_apply]; simp [sum_mul_antipode_eq_algebraMap_counit (ℛ R c)]

end LinearMap

namespace LinearMap
variable [Semiring C] [HopfAlgebra R C]

local notation "𝑺" => antipode R (A := C)
local notation "𝑭" => δ ∘ₗ 𝑺
local notation "𝑮" => (𝑺 ⊗ₘ 𝑺) ∘ₗ TensorProduct.comm R C C ∘ₗ δ

lemma comul_right_inv : toConv δ * toConv 𝑭 = 1 := by
  apply WithConv.ext
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, ofConv_toConv]
  calc μ ∘ₗ map δ (δ ∘ₗ 𝑺) ∘ₗ δ
      = μ ∘ₗ ((δ ∘ₗ id) ⊗ₘ (δ ∘ₗ 𝑺)) ∘ₗ δ := rfl
    _ = μ ∘ₗ (δ ⊗ₘ δ) ∘ₗ (id ⊗ₘ 𝑺) ∘ₗ δ := by
        simp only [_root_.TensorProduct.map_comp, comp_assoc]
    _ = δ ∘ₗ μ ∘ₗ (id ⊗ₘ 𝑺) ∘ₗ δ := by
        have : (μ ∘ₗ (δ ⊗ₘ δ) : C ⊗[R] C →ₗ[R] C ⊗[R] C) = δ ∘ₗ μ := by ext; simp
        simp [this, ← comp_assoc]
    _ = δ ∘ₗ (toConv id * toConv 𝑺).ofConv := by simp [LinearMap.convMul_def]
    _ = δ ∘ₗ (1 : WithConv (C →ₗ[R] C)).ofConv := by rw [id_mul_antipode]
    _ = η ∘ₗ ε := by
        simp [LinearMap.convOne_def, show (δ ∘ₗ η : R →ₗ[R] C ⊗[R] C) = η from by ext; simp; rfl,
          ← comp_assoc]

end LinearMap

namespace AlgHom
variable [CommSemiring A] [CommSemiring C] [Bialgebra R C] [HopfAlgebra R A]

instance convInv : Inv (WithConv <| A →ₐ[R] C) where
  inv f := toConv <| f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)

instance convGroup : Group (WithConv <| A →ₐ[R] C) where
  inv_mul_cancel f := by
    have H : (lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv) =
      f.ofConv.comp (lmul' R) := by ext <;> simp
    trans toConv <| ((lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
      ((Algebra.TensorProduct.map
      (HopfAlgebra.antipodeAlgHom R A) (.id _ _)).comp (comulAlgHom R A))
    · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
        ← Algebra.TensorProduct.map_comp]; rfl
    rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
    change f.ofConv.toLinearMap.comp (toConv (antipode R (A := A)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv <| A →ₗ[R] C)
    rw [LinearMap.antipode_mul_id]
    ext
    simp

instance [IsCocomm R A] : CommGroup (WithConv <| A →ₐ[R] C) where

lemma antipode_id_cancel :
    toConv (HopfAlgebra.antipodeAlgHom R A) * toConv (AlgHom.id R A) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne]
  simp [LinearMap.antipode_mul_id]

lemma counitAlgHom_comp_antipodeAlgHom :
    (counitAlgHom R A).comp (HopfAlgebra.antipodeAlgHom R A) = counitAlgHom R A :=
  AlgHom.toLinearMap_injective <| by simp

end AlgHom
