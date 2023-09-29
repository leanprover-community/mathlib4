/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.RingTheory.TensorProduct
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.Data.ZMod.Basic

/-!
# Graded tensor products over super- (`ZMod 2`-graded)

The graded product  $A \otimes B$ is defined on homogeneous tensors by

$$ (a \otimes b) \cdot (a' \otimes b') = (-1)^{\deg a' \deg b} (a \cdot a') \otimes (b \cdot b') $$

See also https://math.stackexchange.com/a/2024228/1896
-/

local notation "ℤ₂" => ZMod 2
open scoped TensorProduct

variable {R A B : Type*}

section zmod2_pow

/-- There is a canonical power operation by `ℤˣ` on `ZMod 2`. -/
instance : Pow ℤˣ (ZMod 2) where
  pow s z₂ := s ^ z₂.val

lemma z₂pow_def (s : ℤˣ) (x : ZMod 2) : s ^ x = s ^ x.val := rfl

@[simp] lemma z₂pow_zero (s : ℤˣ) : (s ^ (0 : ZMod 2) : ℤˣ) = (1 : ℤˣ) := pow_zero _
@[simp] lemma z₂pow_one (s : ℤˣ) : (s ^ (1 : ZMod 2) : ℤˣ) = s := pow_one _
lemma z₂pow_add (s : ℤˣ) (x y : ZMod 2) : s ^ (x + y) = s ^ x * s ^ y := by
  simp only [z₂pow_def]
  rw [ZMod.val_add, ←pow_eq_pow_mod, pow_add]
  fin_cases s <;> simp

end zmod2_pow


namespace TensorProduct

section external
variable (𝒜 : ZMod 2 → Type*) (ℬ : ZMod 2 → Type*)
variable [CommRing R]
variable [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (ℬ i)]
variable [∀ i, Module R (𝒜 i)] [∀ i, Module R (ℬ i)]
variable [DirectSum.GRing 𝒜] [DirectSum.GRing ℬ]
variable [DirectSum.GAlgebra R 𝒜] [DirectSum.GAlgebra R ℬ]

local notation "𝒜ℬ" => (fun i : ℤ₂ × ℤ₂ => 𝒜 (Prod.fst i) ⊗[R] ℬ (Prod.snd i))

-- this helps with performance
instance (i : ℤ₂ × ℤ₂) : Module R (𝒜 (Prod.fst i) ⊗[R] ℬ (Prod.snd i)) :=
  TensorProduct.leftModule

variable (R) in
/-- Auxliary construction used to build `gradedMul`. This operates on direct sums of tensors
instead of tensors of direct sums. -/
noncomputable irreducible_def gradedMulAux :
    (DirectSum _ 𝒜ℬ) →ₗ[R] (DirectSum _ 𝒜ℬ) →ₗ[R] (DirectSum _ 𝒜ℬ) := by
  refine TensorProduct.curry ?_
  refine ?_ ∘ₗ (TensorProduct.directSum R 𝒜ℬ 𝒜ℬ).toLinearMap
  refine DirectSum.toModule R _ _ fun i => ?_
  have o := DirectSum.lof R _ 𝒜ℬ (i.1.1 + i.2.1, i.1.2 + i.2.2)
  have s : ℤˣ := ((-1 : ℤˣ)^(i.1.2 * i.2.1 : ℤ₂) : ℤˣ)
  refine (s • o) ∘ₗ ?_
  refine ?_ ∘ₗ (TensorProduct.tensorTensorTensorComm R _ _ _ _).toLinearMap
  refine TensorProduct.map (TensorProduct.lift ?_) (TensorProduct.lift ?_)
  · exact DirectSum.gMulLHom R _
  · exact DirectSum.gMulLHom R _

open DirectSum (lof)
open GradedMonoid (GMul)

set_option maxHeartbeats 400000 in
@[simp]
theorem gradedMulAux_lof_tmul_lof_tmul (i₁ j₁ i₂ j₂ : ℤ₂)
    (a₁ : 𝒜 i₁) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : ℬ j₂) :
    gradedMulAux R 𝒜 ℬ (lof R _ 𝒜ℬ (i₁, j₁) (a₁ ⊗ₜ b₁)) (lof R _ 𝒜ℬ (i₂, j₂) (a₂ ⊗ₜ b₂)) =
      (-1 : ℤˣ)^(j₁ * i₂)
        • lof R _ 𝒜ℬ (_, _) (GMul.mul a₁ a₂ ⊗ₜ GMul.mul b₁ b₂) := by
  rw [gradedMulAux]
  dsimp
  simp

set_option maxHeartbeats 4000000
variable (R) in
/-- The multiplication operation for tensor products of externally `ZMod 2`-graded algebras. -/
noncomputable irreducible_def gradedMul :
    letI AB := (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)
    letI : Module R AB := TensorProduct.leftModule
    AB →ₗ[R] AB →ₗ[R] AB := by
  refine TensorProduct.curry ?_
  let e := TensorProduct.directSum R 𝒜 ℬ
  let e' := e.symm.toLinearMap
  refine e' ∘ₗ ?_
  refine ?_ ∘ₗ TensorProduct.map e.toLinearMap e.toLinearMap
  refine TensorProduct.lift ?_
  exact gradedMulAux R 𝒜 ℬ

theorem gradedMul_of_tmul_of (i₁ j₁ i₂ j₂ : ℤ₂)
    (a₁ : 𝒜 i₁) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : ℬ j₂) :
    gradedMul R 𝒜 ℬ (lof R _ 𝒜 i₁ a₁ ⊗ₜ lof R _ ℬ j₁ b₁) (lof R _ 𝒜 i₂ a₂ ⊗ₜ lof R _ ℬ j₂ b₂) =
      (-1 : ℤˣ)^(j₁ * i₂)
        • (lof R _ 𝒜 _ (GMul.mul a₁ a₂) ⊗ₜ lof R _ ℬ _ (GMul.mul b₁ b₂)) := by
  rw [gradedMul]
  dsimp only [TensorProduct.curry_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    TensorProduct.map_tmul, TensorProduct.lift.tmul]
  rw [TensorProduct.directSum_lof_tmul_lof, TensorProduct.directSum_lof_tmul_lof,
    gradedMulAux_lof_tmul_lof_tmul, Units.smul_def, zsmul_eq_smul_cast R, map_smul,
    TensorProduct.directSum_symm_lof_tmul, ←zsmul_eq_smul_cast, ←Units.smul_def]

theorem one_gradedMul (x : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ 1 x = x := by
  suffices gradedMul R 𝒜 ℬ 1 = LinearMap.id by
    exact FunLike.congr_fun this x
  ext ia a ib b
  dsimp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.id_coe, id_eq]
  rw [Algebra.TensorProduct.one_def]
  erw [gradedMul_of_tmul_of]
  rw [zero_mul, z₂pow_zero, one_smul]
  simp_rw [DirectSum.lof_eq_of]
  rw [←DirectSum.of_mul_of, ←DirectSum.of_mul_of]
  erw [one_mul, one_mul]

theorem gradedMul_one (x : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ x 1 = x := by
  suffices (gradedMul R 𝒜 ℬ).flip 1 = LinearMap.id by
    exact FunLike.congr_fun this x
  ext
  dsimp
  rw [Algebra.TensorProduct.one_def]
  erw [gradedMul_of_tmul_of]
  rw [mul_zero, z₂pow_zero, one_smul]
  simp_rw [DirectSum.lof_eq_of]
  rw [←DirectSum.of_mul_of, ←DirectSum.of_mul_of]
  erw [mul_one, mul_one]

theorem gradedMul_assoc (x y z : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ (gradedMul R 𝒜 ℬ x y) z = gradedMul R 𝒜 ℬ x (gradedMul R 𝒜 ℬ y z) := by
  let mA := gradedMul R 𝒜 ℬ
    -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mA ∘ₗ mA =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip <| LinearMap.llcomp R _ _ _ mA.flip ∘ₗ mA).flip by
    exact FunLike.congr_fun (FunLike.congr_fun (FunLike.congr_fun this x) y) z
  ext ixa xa ixb xb iya ya iyb yb iza za izb zb
  dsimp
  save
  simp_rw [gradedMul_of_tmul_of, Units.smul_def, zsmul_eq_smul_cast R,
    LinearMap.map_smul₂, LinearMap.map_smul, gradedMul_of_tmul_of, DirectSum.lof_eq_of,
    ←DirectSum.of_mul_of, mul_assoc]
  save
  simp_rw [←zsmul_eq_smul_cast R, ←Units.smul_def, smul_smul, ←z₂pow_add, add_mul, mul_add]
  congr 2
  abel

end external

section internal
variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable (𝒜 : ZMod 2 → Submodule R A) (ℬ : ZMod 2 → Submodule R B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

open DirectSum


variable (R) in
/-- A Type synonym for `A ⊗[R] B`, but with multiplication as `TensorProduct.gradedMul`. -/
def SuperTensorProduct
    (𝒜 : ZMod 2 → Submodule R A) (ℬ : ZMod 2 → Submodule R B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] :
    Type _ :=
  A ⊗[R] B

scoped[TensorProduct] notation:100 𝒜 " ⊗'[" R "] " ℬ:100 => SuperTensorProduct R 𝒜 ℬ

instance instAddCommGroupWithOne : AddCommGroupWithOne (𝒜 ⊗'[R] ℬ) :=
  Algebra.TensorProduct.instAddCommGroupWithOne
instance : Module R (𝒜 ⊗'[R] ℬ) := TensorProduct.leftModule

namespace SuperTensorProduct

variable (R) in
def of : A ⊗[R] B ≃ₗ[R] 𝒜 ⊗'[R] ℬ := LinearEquiv.refl _ _

@[simp]
theorem of_one : of R 𝒜 ℬ 1 = 1 := rfl

@[simp]
theorem of_symm_one : (of R 𝒜 ℬ).symm 1 = 1 := rfl

@[simp] theorem of_symm_of (x : A ⊗[R] B) : (of R 𝒜 ℬ).symm (of R 𝒜 ℬ x) = x := rfl
@[simp] theorem symm_of_of (x : 𝒜 ⊗'[R] ℬ) : of R 𝒜 ℬ ((of R 𝒜 ℬ).symm x) = x := rfl

variable (R) {𝒜 ℬ} in
abbrev tmul (a : A) (b : B) := of R 𝒜 ℬ (a ⊗ₜ b)

notation:100 x " ⊗ₜ'" y:100 => tmul _ x y
notation:100 x " ⊗ₜ'[" R "] " y:100 => tmul R x y

local notation "↥" P => { x // x ∈ P}

variable (R) in
noncomputable def auxEquiv : (𝒜 ⊗'[R] ℬ) ≃ₗ[R] (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i) :=
  let fA := (decomposeAlgEquiv 𝒜).toLinearEquiv
  let fB := (decomposeAlgEquiv ℬ).toLinearEquiv
  (of R 𝒜 ℬ).symm.trans (TensorProduct.congr fA fB)

@[simp] theorem auxEquiv_one : auxEquiv R 𝒜 ℬ 1 = 1 := by
  dsimp [auxEquiv]
  simp_rw [Algebra.TensorProduct.one_def, congr_tmul]
  dsimp
  rw [AlgEquiv.map_one, AlgEquiv.map_one]

/-- Auxiliary construction used to build the `Mul` instance and get distributivity of `+` and
`\smul`. -/
noncomputable def mulHom : (𝒜 ⊗'[R] ℬ) →ₗ[R] (𝒜 ⊗'[R] ℬ) →ₗ[R] (𝒜 ⊗'[R] ℬ) := by
  letI fAB1 := auxEquiv R 𝒜 ℬ
  have := ((gradedMul R (𝒜 ·) (ℬ ·)).compl₁₂ fAB1.toLinearMap fAB1.toLinearMap).compr₂ fAB1.symm.toLinearMap
  exact this

attribute [pp_dot] AlgEquiv.toLinearEquiv LinearEquiv.symm LinearEquiv.trans


theorem mulHom_apply (x y : 𝒜 ⊗'[R] ℬ) :
    mulHom 𝒜 ℬ x y
      = (auxEquiv R 𝒜 ℬ).symm (gradedMul R (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x) (auxEquiv R 𝒜 ℬ y)) :=
  rfl

noncomputable instance : Mul (𝒜 ⊗'[R] ℬ) where mul x y := mulHom 𝒜 ℬ x y

theorem mul_def (x y : 𝒜 ⊗'[R] ℬ) : x * y = mulHom 𝒜 ℬ x y := rfl

noncomputable instance : Monoid (𝒜 ⊗'[R] ℬ) where
  mul_one x := by
    rw [mul_def, mulHom_apply, auxEquiv_one, gradedMul_one, LinearEquiv.symm_apply_apply]
  one_mul x := by
    rw [mul_def, mulHom_apply, auxEquiv_one, one_gradedMul, LinearEquiv.symm_apply_apply]
  mul_assoc x y z := by
    simp_rw [mul_def, mulHom_apply, LinearEquiv.apply_symm_apply]
    rw [gradedMul_assoc]

noncomputable instance : Ring (𝒜 ⊗'[R] ℬ) where
  __ := instAddCommGroupWithOne
  right_distrib x y z := by rw [mul_def, map_add]
  left_distrib x y z := by rw [mul_def, map_add]

theorem coe_mul_coe {i₁ j₁ i₂ j₂ : ℤ₂} (a₁ : 𝒜 i₁) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : ℬ j₂) :
  ((a₁ : A) ⊗ₜ'[R] (b₁ : B) * (a₂ : A) ⊗ₜ'[R] (b₂ : B) : 𝒜 ⊗'[R] ℬ) =
      (-1 : ℤˣ)^(j₁ * i₂) • ((a₁ * a₂ : A) ⊗ₜ' (b₁ * b₂ : B)) := by
  dsimp only [mul_def, mulHom_apply, of_symm_of]
  save
  dsimp [auxEquiv, tmul]
  rw [congr_symm_tmul]
  rw [gradedMul_of_tmul_of]
  sorry

end SuperTensorProduct

end TensorProduct
