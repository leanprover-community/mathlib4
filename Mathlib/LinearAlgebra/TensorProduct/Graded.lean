/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.ZMod.IntUnitsPower
import Mathlib.RingTheory.TensorProduct
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Graded tensor products over super- (`ZMod 2`-graded)

The graded tensor product $A \hat\otimes_R B$ is imbued with a multiplication defined on homogeneous
tensors by:

$$(a \otimes b) \cdot (a' \otimes b') = (-1)^{\deg a' \deg b} (a \cdot a') \otimes (b \cdot b')$$

where $A$ and $B$ are algebras graded by `ZMod 2`, also known as superalgebras.

## Main results

* `TensorProduct.gradedMul`: this multiplication on externally-graded rings, as a bilinear map
* `SuperTensorProduct R 𝒜 ℬ`: for families of submodules of `A` and `B` that form a graded algebra,
  this is a type alias for `A ⊗'[R] B` with the appropriate multiplication.
* `SuperTensorProduct.instAlgebra`: the ring structure induced by this multiplication.
* `SuperTensorProduct.liftEquiv`: a universal property for graded tensor products


## Notation

`𝒜 ⊗'[R] ℬ` is notation for `SuperTensorProduct R 𝒜 ℬ`

## References

* https://math.stackexchange.com/q/202718/1896
* TODO: find appropriate part of Bourbaki

## TODO

Show that the tensor product of graded algebras is itself a graded algebra.
-/

suppress_compilation

local notation "ℤ₂" => ZMod 2
open scoped TensorProduct

variable {R A B : Type*}

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
/-- Auxliary construction used to build `TensorProduct.gradedMul`.

This operates on direct sums of tensors instead of tensors of direct sums. -/
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
  dsimp only [TensorProduct.curry_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul]
  rw [TensorProduct.directSum_lof_tmul_lof, TensorProduct.directSum_lof_tmul_lof,
    gradedMulAux_lof_tmul_lof_tmul, Units.smul_def, zsmul_eq_smul_cast R, map_smul,
    TensorProduct.directSum_symm_lof_tmul, ←zsmul_eq_smul_cast, ←Units.smul_def]

theorem algebraMap_gradedMul (r : R) (x : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ (algebraMap R _ r ⊗ₜ 1) x = r • x := by
  suffices gradedMul R 𝒜 ℬ (algebraMap R _ r ⊗ₜ 1) = DistribMulAction.toLinearMap R _ r by
    exact FunLike.congr_fun this x
  ext ia a ib b
  dsimp
  erw [gradedMul_of_tmul_of]
  rw [zero_mul, z₂pow_zero, one_smul]
  simp_rw [DirectSum.lof_eq_of]
  rw [←DirectSum.of_mul_of, ←DirectSum.of_mul_of, smul_tmul']
  erw [one_mul, _root_.Algebra.smul_def]
  rfl

theorem one_gradedMul (x : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ 1 x = x := by
  simpa only [_root_.map_one, one_smul] using algebraMap_gradedMul 𝒜 ℬ 1 x

theorem gradedMul_algebraMap (x : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) (r : R) :
    gradedMul R 𝒜 ℬ x (algebraMap R _ r ⊗ₜ 1) = r • x := by
  suffices (gradedMul R 𝒜 ℬ).flip (algebraMap R _ r ⊗ₜ 1) = DistribMulAction.toLinearMap R _ r by
    exact FunLike.congr_fun this x
  ext
  dsimp
  erw [gradedMul_of_tmul_of]
  rw [mul_zero, z₂pow_zero, one_smul]
  simp_rw [DirectSum.lof_eq_of]
  rw [←DirectSum.of_mul_of, ←DirectSum.of_mul_of, smul_tmul']
  erw [mul_one, _root_.Algebra.smul_def, Algebra.commutes]
  rfl

theorem gradedMul_one (x : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ x 1 = x := by
  simpa only [_root_.map_one, one_smul] using gradedMul_algebraMap 𝒜 ℬ x 1

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

end TensorProduct

section internal
variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable (𝒜 : ZMod 2 → Submodule R A) (ℬ : ZMod 2 → Submodule R B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

open DirectSum


variable (R) in
/-- A Type synonym for `A ⊗[R] B`, but with multiplication as `TensorProduct.gradedMul`.

This has notation `𝒜 ⊗'[R] ℬ`. -/
@[nolint unusedArguments]
def SuperTensorProduct
    (𝒜 : ZMod 2 → Submodule R A) (ℬ : ZMod 2 → Submodule R B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] :
    Type _ :=
  A ⊗[R] B

namespace SuperTensorProduct

open TensorProduct

@[inherit_doc SuperTensorProduct]
scoped[TensorProduct] notation:100 𝒜 " ⊗'[" R "] " ℬ:100 => SuperTensorProduct R 𝒜 ℬ

instance instAddCommGroupWithOne : AddCommGroupWithOne (𝒜 ⊗'[R] ℬ) :=
  Algebra.TensorProduct.instAddCommGroupWithOne
instance : Module R (𝒜 ⊗'[R] ℬ) := TensorProduct.leftModule

variable (R) in
/-- The casting equivalence to move between regular and graded tensor products. -/
def of : A ⊗[R] B ≃ₗ[R] 𝒜 ⊗'[R] ℬ := LinearEquiv.refl _ _

@[simp]
theorem of_one : of R 𝒜 ℬ 1 = 1 := rfl

@[simp]
theorem of_symm_one : (of R 𝒜 ℬ).symm 1 = 1 := rfl

-- for dsimp
@[simp, nolint simpNF]
theorem of_symm_of (x : A ⊗[R] B) : (of R 𝒜 ℬ).symm (of R 𝒜 ℬ x) = x := rfl

-- for dsimp
@[simp, nolint simpNF]
theorem symm_of_of (x : 𝒜 ⊗'[R] ℬ) : of R 𝒜 ℬ ((of R 𝒜 ℬ).symm x) = x := rfl

/-- Two linear maps from the graded tensor product agree if they agree on the underlying tensor
product. -/
@[ext]
theorem hom_ext {M} [AddCommMonoid M] [Module R M] ⦃f g : 𝒜 ⊗'[R] ℬ →ₗ[R] M⦄
    (h : f ∘ₗ of R 𝒜 ℬ = (g ∘ₗ of R 𝒜 ℬ : A ⊗[R] B →ₗ[R] M)) :
    f = g :=
  h

variable (R) {𝒜 ℬ} in
/-- The graded tensor product of two elements of graded rings. -/
abbrev tmul (a : A) (b : B) := of R 𝒜 ℬ (a ⊗ₜ b)

@[inherit_doc]
notation:100 x " ⊗ₜ'" y:100 => tmul _ x y

@[inherit_doc]
notation:100 x " ⊗ₜ'[" R "] " y:100 => tmul R x y

variable (R) in
/-- An auxiliary construction to move between the graded tensor product of internally-graded objects
and the product of direct sums.-/
noncomputable def auxEquiv : (𝒜 ⊗'[R] ℬ) ≃ₗ[R] (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i) :=
  let fA := (decomposeAlgEquiv 𝒜).toLinearEquiv
  let fB := (decomposeAlgEquiv ℬ).toLinearEquiv
  (of R 𝒜 ℬ).symm.trans (TensorProduct.congr fA fB)

@[simp] theorem auxEquiv_tmul (a : A) (b : B) :
    auxEquiv R 𝒜 ℬ (a ⊗ₜ' b : 𝒜 ⊗'[R] ℬ) = decompose 𝒜 a ⊗ₜ decompose ℬ b := rfl

@[simp] theorem auxEquiv_one : auxEquiv R 𝒜 ℬ 1 = 1 := by
  rw [←of_one, Algebra.TensorProduct.one_def, auxEquiv_tmul 𝒜 ℬ, DirectSum.decompose_one,
    DirectSum.decompose_one, Algebra.TensorProduct.one_def]

/-- Auxiliary construction used to build the `Mul` instance and get distributivity of `+` and
`\smul`. -/
noncomputable def mulHom : (𝒜 ⊗'[R] ℬ) →ₗ[R] (𝒜 ⊗'[R] ℬ) →ₗ[R] (𝒜 ⊗'[R] ℬ) := by
  letI fAB1 := auxEquiv R 𝒜 ℬ
  have := ((gradedMul R (𝒜 ·) (ℬ ·)).compl₁₂ fAB1.toLinearMap fAB1.toLinearMap).compr₂
    fAB1.symm.toLinearMap
  exact this

theorem mulHom_apply (x y : 𝒜 ⊗'[R] ℬ) :
    mulHom 𝒜 ℬ x y
      = (auxEquiv R 𝒜 ℬ).symm (gradedMul R (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x) (auxEquiv R 𝒜 ℬ y)) :=
  rfl

/-- The multipication on the super tensor product.

See `SuperTensorProduct.coe_mul_coe` for a characterization on pure tensors. -/
noncomputable instance : Mul (𝒜 ⊗'[R] ℬ) where mul x y := mulHom 𝒜 ℬ x y

theorem mul_def (x y : 𝒜 ⊗'[R] ℬ) : x * y = mulHom 𝒜 ℬ x y := rfl

noncomputable instance instMonoid : Monoid (𝒜 ⊗'[R] ℬ) where
  mul_one x := by
    rw [mul_def, mulHom_apply, auxEquiv_one, gradedMul_one, LinearEquiv.symm_apply_apply]
  one_mul x := by
    rw [mul_def, mulHom_apply, auxEquiv_one, one_gradedMul, LinearEquiv.symm_apply_apply]
  mul_assoc x y z := by
    simp_rw [mul_def, mulHom_apply, LinearEquiv.apply_symm_apply]
    rw [gradedMul_assoc]

noncomputable instance instRing : Ring (𝒜 ⊗'[R] ℬ) where
  __ := instAddCommGroupWithOne 𝒜 ℬ
  __ := instMonoid 𝒜 ℬ
  right_distrib x y z := by simp_rw [mul_def, LinearMap.map_add₂]
  left_distrib x y z := by simp_rw [mul_def, map_add]
  mul_zero x := by simp_rw [mul_def, map_zero]
  zero_mul x := by simp_rw [mul_def, LinearMap.map_zero₂]

set_option maxHeartbeats 800000 in
/-- Note that a more general `tmul_coe_mul_coe_tmul` is available. -/
theorem coe_tmul_coe_mul_coe_tmul_coe {i₁ j₁ i₂ j₂ : ℤ₂}
    (a₁ : 𝒜 i₁) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : ℬ j₂) :
    ((a₁ : A) ⊗ₜ'[R] (b₁ : B) * (a₂ : A) ⊗ₜ'[R] (b₂ : B) : 𝒜 ⊗'[R] ℬ) =
      (-1 : ℤˣ)^(j₁ * i₂) • ((a₁ * a₂ : A) ⊗ₜ' (b₁ * b₂ : B)) := by
  dsimp only [mul_def, mulHom_apply, of_symm_of]
  dsimp [auxEquiv, tmul]
  erw [decompose_coe, decompose_coe, decompose_coe, decompose_coe]
  dsimp
  simp_rw [←lof_eq_of R]
  rw [gradedMul_of_tmul_of]
  simp_rw [lof_eq_of R]
  rw [LinearEquiv.symm_symm]
  rw [@Units.smul_def _ _ (_) (_), zsmul_eq_smul_cast R, map_smul, map_smul,
    ←zsmul_eq_smul_cast R, ←@Units.smul_def _ _ (_) (_)]
  rw [congr_symm_tmul]
  dsimp
  rw [decompose_symm_of, decompose_symm_of, SetLike.coe_gMul, SetLike.coe_gMul]

/-- The characterization of this multiplication on partially homogenous elements. -/
theorem tmul_coe_mul_coe_tmul {j₁ i₂ : ℤ₂} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ⊗ₜ'[R] (b₁ : B) * (a₂ : A) ⊗ₜ'[R] b₂ : 𝒜 ⊗'[R] ℬ) =
      (-1 : ℤˣ)^(j₁ * i₂) • ((a₁ * a₂ : A) ⊗ₜ' (b₁ * b₂ : B)) := by
  classical
  rw [←DirectSum.sum_support_decompose 𝒜 a₁, ←DirectSum.sum_support_decompose ℬ b₂]
  rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [tmul, sum_tmul, tmul_sum, map_sum, Finset.smul_sum]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, coe_tmul_coe_mul_coe_tmul_coe]

/-- A special case for when `b₁` has grade 0. -/
theorem tmul_zero_coe_mul_coe_tmul {i₂ : ℤ₂} (a₁ : A) (b₁ : ℬ 0) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ⊗ₜ'[R] (b₁ : B) * (a₂ : A) ⊗ₜ'[R] b₂ : 𝒜 ⊗'[R] ℬ) =
      ((a₁ * a₂ : A) ⊗ₜ' (b₁ * b₂ : B)) := by
  rw [tmul_coe_mul_coe_tmul, zero_mul, z₂pow_zero, one_smul]

/-- A special case for when `a₂` has grade 0. -/
theorem tmul_coe_mul_zero_coe_tmul {j₁ : ℤ₂} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 0) (b₂ : B) :
    (a₁ ⊗ₜ'[R] (b₁ : B) * (a₂ : A) ⊗ₜ'[R] b₂ : 𝒜 ⊗'[R] ℬ) =
      ((a₁ * a₂ : A) ⊗ₜ' (b₁ * b₂ : B)) := by
  rw [tmul_coe_mul_coe_tmul, mul_zero, z₂pow_zero, one_smul]

theorem tmul_one_mul_coe_tmul {i₂ : ℤ₂} (a₁ : A) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ⊗ₜ'[R] (1 : B) * (a₂ : A) ⊗ₜ'[R] b₂ : 𝒜 ⊗'[R] ℬ) = (a₁ * a₂ : A) ⊗ₜ' (b₂ : B) := by
  convert tmul_zero_coe_mul_coe_tmul 𝒜 ℬ a₁ (@GradedMonoid.GOne.one _ (ℬ ·) _ _) a₂ b₂
  rw [SetLike.coe_gOne, one_mul]

theorem tmul_coe_mul_one_tmul {j₁ : ℤ₂} (a₁ : A) (b₁ : ℬ j₁) (b₂ : B) :
    (a₁ ⊗ₜ'[R] (b₁ : B) * (1 : A) ⊗ₜ'[R] b₂ : 𝒜 ⊗'[R] ℬ) = (a₁ : A) ⊗ₜ' (b₁ * b₂ : B) := by
  convert tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ b₁ (@GradedMonoid.GOne.one _ (𝒜 ·) _ _) b₂
  rw [SetLike.coe_gOne, mul_one]

theorem tmul_one_mul_one_tmul (a₁ : A) (b₂ : B) :
    (a₁ ⊗ₜ'[R] (1 : B) * (1 : A) ⊗ₜ'[R] b₂ : 𝒜 ⊗'[R] ℬ) = (a₁ : A) ⊗ₜ' (b₂ : B) := by
  convert tmul_coe_mul_zero_coe_tmul 𝒜 ℬ
    a₁ (@GradedMonoid.GOne.one _ (ℬ ·) _ _) (@GradedMonoid.GOne.one _ (𝒜 ·) _ _) b₂
  · rw [SetLike.coe_gOne, mul_one]
  · rw [SetLike.coe_gOne, one_mul]

/-- The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps]
def includeLeftRingHom : A →+* 𝒜 ⊗'[R] ℬ where
  toFun a := a ⊗ₜ' 1
  map_zero' := by simp
  map_add' := by simp [tmul, TensorProduct.add_tmul]
  map_one' := rfl
  map_mul' a₁ a₂ := by
    dsimp
    classical
    rw [←DirectSum.sum_support_decompose 𝒜 a₂, Finset.mul_sum]
    simp_rw [tmul, sum_tmul, map_sum, Finset.mul_sum]
    congr
    ext i
    rw [←SetLike.coe_gOne ℬ, tmul_coe_mul_coe_tmul, zero_mul, z₂pow_zero, one_smul,
      SetLike.coe_gOne, one_mul]

noncomputable instance instAlgebra : Algebra R (𝒜 ⊗'[R] ℬ) where
  toRingHom := (includeLeftRingHom 𝒜 ℬ).comp (algebraMap R A)
  commutes' r x := by
    dsimp [mul_def, mulHom_apply, auxEquiv_tmul]
    simp_rw [DirectSum.decompose_algebraMap, DirectSum.decompose_one, algebraMap_gradedMul,
      gradedMul_algebraMap]
  smul_def' r x := by
    dsimp [mul_def, mulHom_apply, auxEquiv_tmul]
    simp_rw [DirectSum.decompose_algebraMap, DirectSum.decompose_one, algebraMap_gradedMul,
      map_smul, LinearEquiv.symm_apply_apply]

lemma algebraMap_def (r : R) : algebraMap R (𝒜 ⊗'[R] ℬ) r = algebraMap R A r ⊗ₜ'[R] 1 := rfl

theorem tmul_algebraMap_mul_coe_tmul {i₂ : ℤ₂} (a₁ : A) (r : R) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ⊗ₜ'[R] algebraMap R B r * (a₂ : A) ⊗ₜ'[R] b₂ : 𝒜 ⊗'[R] ℬ)
      = (a₁ * a₂ : A) ⊗ₜ' (algebraMap R B r * b₂ : B) :=
  tmul_zero_coe_mul_coe_tmul 𝒜 ℬ a₁ (GAlgebra.toFun (A := (ℬ ·)) r) a₂ b₂

theorem tmul_coe_mul_algebraMap_tmul {j₁ : ℤ₂} (a₁ : A) (b₁ : ℬ j₁) (r : R) (b₂ : B) :
    (a₁ ⊗ₜ'[R] (b₁ : B) * algebraMap R A r ⊗ₜ'[R] b₂ : 𝒜 ⊗'[R] ℬ)
      = (a₁ * algebraMap R A r : A) ⊗ₜ' (b₁ * b₂ : B) :=
  tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ b₁ (GAlgebra.toFun (A := (𝒜 ·)) r) b₂

/-- The algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps!]
def includeLeft : A →ₐ[R] 𝒜 ⊗'[R] ℬ where
  toRingHom := includeLeftRingHom 𝒜 ℬ
  commutes' _ := rfl

/-- The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`. -/
@[simps!]
def includeRight : B →ₐ[R] (𝒜 ⊗'[R] ℬ) :=
  AlgHom.ofLinearMap (R := R) (A := B) (B := 𝒜 ⊗'[R] ℬ)
    (f := {
       toFun := fun b => 1 ⊗ₜ' b
       map_add' := by simp [tmul, TensorProduct.tmul_add]
       map_smul' := by simp [tmul, TensorProduct.tmul_smul] })
    (map_one := rfl)
    (map_mul := by
      rw [LinearMap.map_mul_iff]
      refine DirectSum.decompose_lhom_ext ℬ fun i₁ => ?_
      ext b₁ b₂ : 2
      dsimp
      rw [tmul_coe_mul_one_tmul])

lemma algebraMap_def' (r : R) : algebraMap R (𝒜 ⊗'[R] ℬ) r = 1 ⊗ₜ'[R] algebraMap R B r :=
  (includeRight 𝒜 ℬ).commutes r |>.symm

variable {C} [Ring C] [Algebra R C]

/-- The forwards direction of the universal property; an algebra morphism out of the graded tensor
product can be assembed from maps on each component that (anti)commute on pure elements of the
corresponding graded algebras. -/
def lift (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h_anti_commutes : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j), f a * g b = (-1 : ℤˣ)^(j * i) • (g b * f a)) :
    (𝒜 ⊗'[R] ℬ) →ₐ[R] C :=
  AlgHom.ofLinearMap
    (LinearMap.mul' R C
      ∘ₗ (TensorProduct.map f.toLinearMap g.toLinearMap)
      ∘ₗ ((of R 𝒜 ℬ).symm : 𝒜 ⊗'[R] ℬ →ₗ[R] A ⊗[R] B))
    (by dsimp [Algebra.TensorProduct.one_def]; simp only [_root_.map_one, mul_one])
    (by
      rw [LinearMap.map_mul_iff]
      ext a₁ : 3
      refine DirectSum.decompose_lhom_ext ℬ fun j₁ => ?_
      ext b₁ : 3
      refine DirectSum.decompose_lhom_ext 𝒜 fun i₂ => ?_
      ext a₂ b₂ : 2
      dsimp
      rw [tmul_coe_mul_coe_tmul]
      rw [@Units.smul_def _ _ (_) (_), zsmul_eq_smul_cast R, map_smul, map_smul, map_smul]
      rw [←zsmul_eq_smul_cast R, ←@Units.smul_def _ _ (_) (_)]
      rw [of_symm_of, map_tmul, LinearMap.mul'_apply]
      simp_rw [AlgHom.toLinearMap_apply, _root_.map_mul]
      simp_rw [mul_assoc (f a₁), ←mul_assoc _ _ (g b₂), h_anti_commutes, mul_smul_comm,
        smul_mul_assoc, smul_smul, z₂pow_mul_self, one_smul])

@[simp]
theorem lift_tmul (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h_anti_commutes : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j), f a * g b = (-1 : ℤˣ)^(j * i) • (g b * f a))
    (a : A) (b : B) :
    lift 𝒜 ℬ f g h_anti_commutes (a ⊗ₜ' b) = f a * g b :=
  rfl

/-- The universal property of the graded tensor product; every algebra morphism uniquely factors
as a pair of algebra morphisms that anticommute with respect to the grading. -/
def liftEquiv :
    { fg : (A →ₐ[R] C) × (B →ₐ[R] C) //
        ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j), fg.1 a * fg.2 b = (-1 : ℤˣ)^(j * i) • (fg.2 b * fg.1 a)} ≃
      ((𝒜 ⊗'[R] ℬ) →ₐ[R] C) where
  toFun fg := lift 𝒜 ℬ _ _ fg.prop
  invFun F := ⟨(F.comp (includeLeft 𝒜 ℬ), F.comp (includeRight 𝒜 ℬ)), fun i j a b => by
    dsimp
    rw [←F.map_mul, ←F.map_mul, tmul_coe_mul_coe_tmul, one_mul, mul_one, AlgHom.map_smul_of_tower,
      tmul_one_mul_one_tmul, smul_smul, z₂pow_mul_self, one_smul]⟩
  left_inv fg := by ext <;> (dsimp; simp only [_root_.map_one, mul_one, one_mul])
  right_inv F := by
    apply AlgHom.toLinearMap_injective
    ext
    dsimp
    rw [←F.map_mul, tmul_one_mul_one_tmul]

/-- Two algebra morphism from the graded tensor product agree if their compositions with the left
and right inclusions agree. -/
@[ext]
lemma algHom_ext ⦃f g : (𝒜 ⊗'[R] ℬ) →ₐ[R] C⦄
    (ha : f.comp (includeLeft 𝒜 ℬ) = g.comp (includeLeft 𝒜 ℬ))
    (hb : f.comp (includeRight 𝒜 ℬ) = g.comp (includeRight 𝒜 ℬ)) : f = g :=
  (liftEquiv 𝒜 ℬ).symm.injective <| Subtype.ext <| Prod.ext ha hb

end SuperTensorProduct

end internal
