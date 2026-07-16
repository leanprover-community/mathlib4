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

We also provide `HopfAlgebra.ofAntipodeOfAdjoin`, which upgrades a bialgebra `A` to a Hopf algebra
given an algebra hom `S : A →ₐ[R] Aᵐᵒᵖ` satisfying the antipode identities on a generating set.
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
  ext _; exact congr($HopfAlgebra.mul_antipode_rTensor_comul _)

@[simp] lemma id_mul_antipode : toConv id * toConv (antipode R (A := C)) = 1 := by
  ext _; exact congr($HopfAlgebra.mul_antipode_lTensor_comul _)

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
        have : (δ ∘ₗ η : R →ₗ[R] C ⊗[R] C) = η := by
          ext; simp only [coe_comp, Function.comp_apply, linearMap_apply, map_one, comul_one]
        simp [LinearMap.convOne_def, this, ← comp_assoc]

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
  ext _; exact congr($HopfAlgebra.mul_antipode_rTensor_comul _)

lemma id_antipode_cancel :
    toConv (AlgHom.id R A) * toConv (HopfAlgebra.antipodeAlgHom R A) = 1 := by
  ext _; exact congr($HopfAlgebra.mul_antipode_lTensor_comul _)

lemma counitAlgHom_comp_antipodeAlgHom :
    (counitAlgHom R A).comp (HopfAlgebra.antipodeAlgHom R A) = counitAlgHom R A :=
  AlgHom.toLinearMap_injective <| by simp

end AlgHom

namespace HopfAlgebra

section OfAntipodeOfAdjoin

open LinearMap

variable [Semiring A] [Bialgebra R A] {X : Set A} (S : A →ₐ[R] Aᵐᵒᵖ)

/-- `𝑺` denotes the candidate antipode `A →ₗ[R] A` induced by the algebra hom
`S : A →ₐ[R] Aᵐᵒᵖ`. -/
local notation "𝑺" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (MulOpposite.opLinearEquiv R (M := A))) ∘ₗ
    AlgHom.toLinearMap S

theorem convMul_id_eq_one_of_adjoin_eq_top (hX : adjoin R X = ⊤)
    (h : ∀ x ∈ X, μ (rTensor A 𝑺 (δ x)) = η[R] (ε x)) :
    toConv 𝑺 * toConv .id = 1 := by
  ext t
  have ht : t ∈ adjoin R X := hX.ge trivial
  induction ht using adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r => simp [comul_algebraMap, Algebra.TensorProduct.algebraMap_apply]
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | mul x y _ _ hx hy =>
    rw [(ℛ R x).convMul_apply] at hx
    rw [(ℛ R y).convMul_apply] at hy
    simp only [id_coe, id_eq, convOne_apply] at hx hy
    calc
      _ = ∑ j ∈ (ℛ R y).index, 𝑺 ((ℛ R y).left j) *
          (∑ i ∈ (ℛ R x).index, 𝑺 ((ℛ R x).left i) * (ℛ R x).right i) * (ℛ R y).right j := by
        rw [((ℛ R x).mul (ℛ R y)).convMul_apply]
        simp only [id_coe, id_eq, Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left,
          Coalgebra.Repr.mul_right, Finset.sum_product]
        rw [Finset.sum_comm]
        simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = algebraMap R A (ε x) *
          ∑ j ∈ (ℛ R y).index, 𝑺 ((ℛ R y).left j) * (ℛ R y).right j := by
        rw [hx, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [← mul_assoc, Algebra.commutes, mul_assoc]
      _ = algebraMap R A (ε (x * y)) := by rw [hy, counit_mul, map_mul]

theorem id_convMul_eq_one_of_adjoin_eq_top (hX : adjoin R X = ⊤)
    (h : ∀ x ∈ X, μ (lTensor A 𝑺 (δ x)) = η[R] (ε x)) :
    toConv .id * toConv 𝑺 = 1 := by
  ext t
  have ht : t ∈ adjoin R X := hX.ge trivial
  induction ht using adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r => simp [comul_algebraMap, Algebra.TensorProduct.algebraMap_apply]
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | mul x y _ _ hx hy =>
    rw [(ℛ R x).convMul_apply] at hx
    rw [(ℛ R y).convMul_apply] at hy
    simp only [id_coe, id_eq, convOne_apply] at hx hy
    calc
      _ = ∑ i ∈ (ℛ R x).index, (ℛ R x).left i *
          (∑ j ∈ (ℛ R y).index, (ℛ R y).left j * 𝑺 ((ℛ R y).right j)) * 𝑺 ((ℛ R x).right i) := by
        rw [((ℛ R x).mul (ℛ R y)).convMul_apply]
        simp only [id_coe, id_eq, Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left,
          Coalgebra.Repr.mul_right, Finset.sum_product]
        simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = (∑ i ∈ (ℛ R x).index, (ℛ R x).left i * 𝑺 ((ℛ R x).right i)) *
          algebraMap R A (ε y) := by
        rw [hy, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_assoc, Algebra.commutes, mul_assoc]
      _ = algebraMap R A (ε (x * y)) := by rw [hx, counit_mul, map_mul]

/--
If `A` is generated as an `R`-algebra by `X`, and `S : A →ₐ[R] Aᵐᵒᵖ` satisfies the two
antipode identities on `X`, then the underlying linear map gives a Hopf algebra structure on `A`.
-/
noncomputable abbrev ofAntipodeOfAdjoin (hX : adjoin R X = ⊤)
    (hxr : ∀ x ∈ X, μ (rTensor A 𝑺 (δ x)) = η[R] (ε x))
    (hxl : ∀ x ∈ X, μ (lTensor A 𝑺 (δ x)) = η[R] (ε x)) : HopfAlgebra R A :=
  ofConvInverse 𝑺 (convMul_id_eq_one_of_adjoin_eq_top S hX hxr)
    (id_convMul_eq_one_of_adjoin_eq_top S hX hxl)

end OfAntipodeOfAdjoin

end HopfAlgebra
