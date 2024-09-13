/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Algebraic operations on `SeparationQuotient`

In this file we define algebraic operations (multiplication, addition etc)
on the separation quotient of a topological space with corresponding operation,
provided that the original operation is continuous.

We also prove continuity of these operations
and show that they satisfy the same kind of laws (`Monoid` etc) as the original ones.

Finally, we construct a section of the quotient map
which is a continuous linear map `SeparationQuotient E →L[K] E`.
-/

namespace SeparationQuotient

section SMul

variable {M X : Type*} [TopologicalSpace X] [SMul M X] [ContinuousConstSMul M X]

@[to_additive]
instance instSMul : SMul M (SeparationQuotient X) where
  smul c := Quotient.map' (c • ·) fun _ _ h ↦ h.const_smul c

@[to_additive (attr := simp)]
theorem mk_smul (c : M) (x : X) : mk (c • x) = c • mk x := rfl

@[to_additive]
instance instContinuousConstSMul : ContinuousConstSMul M (SeparationQuotient X) where
  continuous_const_smul c := quotientMap_mk.continuous_iff.2 <|
    continuous_mk.comp <| continuous_const_smul c

@[to_additive]
instance instIsPretransitiveSMul [MulAction.IsPretransitive M X] :
    MulAction.IsPretransitive M (SeparationQuotient X) where
  exists_smul_eq := surjective_mk.forall₂.2 fun x y ↦
    (MulAction.exists_smul_eq M x y).imp fun _ ↦ congr_arg mk

@[to_additive]
instance instIsCentralScalar [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] :
    IsCentralScalar M (SeparationQuotient X) where
  op_smul_eq_smul a := surjective_mk.forall.2 (congr_arg mk <| op_smul_eq_smul a ·)

variable {N : Type*} [SMul N X]

@[to_additive]
instance instSMulCommClass [ContinuousConstSMul N X] [SMulCommClass M N X] :
    SMulCommClass M N (SeparationQuotient X) :=
  surjective_mk.smulCommClass mk_smul mk_smul

@[to_additive instVAddAssocClass]
instance instIsScalarTower [SMul M N] [ContinuousConstSMul N X] [IsScalarTower M N X] :
    IsScalarTower M N (SeparationQuotient X) where
  smul_assoc a b := surjective_mk.forall.2 fun x ↦ congr_arg mk <| smul_assoc a b x

end SMul

instance instSMulZeroClass {M X : Type*} [Zero X] [SMulZeroClass M X] [TopologicalSpace X]
    [ContinuousConstSMul M X] : SMulZeroClass M (SeparationQuotient X) :=
  ZeroHom.smulZeroClass ⟨mk, mk_zero⟩ mk_smul

@[to_additive]
instance instMulAction {M X : Type*} [Monoid M] [MulAction M X] [TopologicalSpace X]
    [ContinuousConstSMul M X] : MulAction M (SeparationQuotient X) :=
  surjective_mk.mulAction mk mk_smul

section Monoid

variable {M : Type*} [TopologicalSpace M]

@[to_additive]
instance instMul [Mul M] [ContinuousMul M] : Mul (SeparationQuotient M) where
  mul := Quotient.map₂' (· * ·) fun _ _ h₁ _ _ h₂ ↦ Inseparable.mul h₁ h₂

@[to_additive (attr := simp)]
theorem mk_mul [Mul M] [ContinuousMul M] (a b : M) : mk (a * b) = mk a * mk b := rfl


@[to_additive]
instance instContinuousMul [Mul M] [ContinuousMul M] : ContinuousMul (SeparationQuotient M) where
  continuous_mul := quotientMap_prodMap_mk.continuous_iff.2 <| continuous_mk.comp continuous_mul

@[to_additive]
instance instCommMagma [CommMagma M] [ContinuousMul M] : CommMagma (SeparationQuotient M) :=
  surjective_mk.commMagma mk mk_mul

@[to_additive]
instance instSemigroup [Semigroup M] [ContinuousMul M] : Semigroup (SeparationQuotient M) :=
  surjective_mk.semigroup mk mk_mul

@[to_additive]
instance instCommSemigroup [CommSemigroup M] [ContinuousMul M] :
    CommSemigroup (SeparationQuotient M) :=
  surjective_mk.commSemigroup mk mk_mul

@[to_additive]
instance instMulOneClass [MulOneClass M] [ContinuousMul M] :
    MulOneClass (SeparationQuotient M) :=
  surjective_mk.mulOneClass mk mk_one mk_mul

/-- `SeparationQuotient.mk` as a `MonoidHom`. -/
@[to_additive (attr := simps) "`SeparationQuotient.mk` as an `AddMonoidHom`."]
def mkMonoidHom [MulOneClass M] [ContinuousMul M] : M →* SeparationQuotient M where
  toFun := mk
  map_mul' := mk_mul
  map_one' := mk_one

instance (priority := 900) instNSmul [AddMonoid M] [ContinuousAdd M] :
    SMul ℕ (SeparationQuotient M) :=
  inferInstance

@[to_additive existing instNSmul]
instance instPow [Monoid M] [ContinuousMul M] : Pow (SeparationQuotient M) ℕ where
  pow x n := Quotient.map' (s₁ := inseparableSetoid M) (· ^ n) (fun _ _ h ↦ Inseparable.pow h n) x

@[to_additive, simp] -- `mk_nsmul` is not a `simp` lemma because we have `mk_smul`
theorem mk_pow [Monoid M] [ContinuousMul M] (x : M) (n : ℕ) : mk (x ^ n) = (mk x) ^ n := rfl

@[to_additive]
instance instMonoid [Monoid M] [ContinuousMul M] : Monoid (SeparationQuotient M) :=
  surjective_mk.monoid mk mk_one mk_mul mk_pow

@[to_additive]
instance instCommMonoid [CommMonoid M] [ContinuousMul M] : CommMonoid (SeparationQuotient M) :=
  surjective_mk.commMonoid mk mk_one mk_mul mk_pow

end Monoid

section Group

variable {G : Type*} [TopologicalSpace G]

@[to_additive]
instance instInv [Inv G] [ContinuousInv G] : Inv (SeparationQuotient G) where
  inv := Quotient.map' (·⁻¹) fun _ _ ↦ Inseparable.inv

@[to_additive (attr := simp)]
theorem mk_inv [Inv G] [ContinuousInv G] (x : G) : mk x⁻¹ = (mk x)⁻¹ := rfl

@[to_additive]
instance instContinuousInv [Inv G] [ContinuousInv G] : ContinuousInv (SeparationQuotient G) where
  continuous_inv := quotientMap_mk.continuous_iff.2 <| continuous_mk.comp continuous_inv

@[to_additive]
instance instInvolutiveInv [InvolutiveInv G] [ContinuousInv G] :
    InvolutiveInv (SeparationQuotient G) :=
  surjective_mk.involutiveInv mk mk_inv

@[to_additive]
instance instInvOneClass [InvOneClass G] [ContinuousInv G] :
    InvOneClass (SeparationQuotient G) where
  inv_one := congr_arg mk inv_one

@[to_additive]
instance instDiv [Div G] [ContinuousDiv G] : Div (SeparationQuotient G) where
  div := Quotient.map₂' (· / ·) fun _ _ h₁ _ _ h₂ ↦ (Inseparable.prod h₁ h₂).map continuous_div'

@[to_additive (attr := simp)]
theorem mk_div [Div G] [ContinuousDiv G] (x y : G) : mk (x / y) = mk x / mk y := rfl

@[to_additive]
instance instContinuousDiv [Div G] [ContinuousDiv G] : ContinuousDiv (SeparationQuotient G) where
  continuous_div' := quotientMap_prodMap_mk.continuous_iff.2 <| continuous_mk.comp continuous_div'

instance instZSMul [AddGroup G] [TopologicalAddGroup G] : SMul ℤ (SeparationQuotient G) :=
  inferInstance

@[to_additive existing]
instance instZPow [Group G] [TopologicalGroup G] : Pow (SeparationQuotient G) ℤ where
  pow x n := Quotient.map' (s₁ := inseparableSetoid G) (· ^ n) (fun _ _ h ↦ Inseparable.zpow h n) x

@[to_additive, simp] -- `mk_zsmul` is not a `simp` lemma because we have `mk_smul`
theorem mk_zpow [Group G] [TopologicalGroup G] (x : G) (n : ℤ) : mk (x ^ n) = (mk x) ^ n := rfl

@[to_additive]
instance instGroup [Group G] [TopologicalGroup G] : Group (SeparationQuotient G) :=
  surjective_mk.group mk mk_one mk_mul mk_inv mk_div mk_pow mk_zpow

@[to_additive]
instance instCommGroup [CommGroup G] [TopologicalGroup G] : CommGroup (SeparationQuotient G) :=
  surjective_mk.commGroup mk mk_one mk_mul mk_inv mk_div mk_pow mk_zpow

end Group

section MonoidWithZero

variable {M₀ : Type*} [TopologicalSpace M₀]

instance instMulZeroClass [MulZeroClass M₀] [ContinuousMul M₀] :
    MulZeroClass (SeparationQuotient M₀) :=
  surjective_mk.mulZeroClass mk mk_zero mk_mul

instance instSemigroupWithZero [SemigroupWithZero M₀] [ContinuousMul M₀] :
    SemigroupWithZero (SeparationQuotient M₀) :=
  surjective_mk.semigroupWithZero mk mk_zero mk_mul

instance instMulZeroOneClass [MulZeroOneClass M₀] [ContinuousMul M₀] :
    MulZeroOneClass (SeparationQuotient M₀) :=
  surjective_mk.mulZeroOneClass mk mk_zero mk_one mk_mul

instance instMonoidWithZero [MonoidWithZero M₀] [ContinuousMul M₀] :
    MonoidWithZero (SeparationQuotient M₀) :=
  surjective_mk.monoidWithZero mk mk_zero mk_one mk_mul mk_pow

instance instCommMonoidWithZero [CommMonoidWithZero M₀] [ContinuousMul M₀] :
    CommMonoidWithZero (SeparationQuotient M₀) :=
  surjective_mk.commMonoidWithZero mk mk_zero mk_one mk_mul mk_pow

end MonoidWithZero

section Ring

variable {R : Type*} [TopologicalSpace R]

instance instDistrib [Distrib R] [ContinuousMul R] [ContinuousAdd R] :
    Distrib (SeparationQuotient R) :=
  surjective_mk.distrib mk mk_add mk_mul

instance instLeftDistribClass [Mul R] [Add R] [LeftDistribClass R]
    [ContinuousMul R] [ContinuousAdd R] :
    LeftDistribClass (SeparationQuotient R) :=
  surjective_mk.leftDistribClass mk mk_add mk_mul

instance instRightDistribClass [Mul R] [Add R] [RightDistribClass R]
    [ContinuousMul R] [ContinuousAdd R] :
    RightDistribClass (SeparationQuotient R) :=
  surjective_mk.rightDistribClass mk mk_add mk_mul

instance instNonUnitalnonAssocSemiring [NonUnitalNonAssocSemiring R]
    [TopologicalSemiring R] : NonUnitalNonAssocSemiring (SeparationQuotient R) :=
  surjective_mk.nonUnitalNonAssocSemiring mk mk_zero mk_add mk_mul mk_smul

instance instNonUnitalSemiring [NonUnitalSemiring R] [TopologicalSemiring R] :
    NonUnitalSemiring (SeparationQuotient R) :=
  surjective_mk.nonUnitalSemiring mk mk_zero mk_add mk_mul mk_smul

instance instNatCast [NatCast R] : NatCast (SeparationQuotient R) where
  natCast n := mk n

@[simp, norm_cast]
theorem mk_natCast [NatCast R] (n : ℕ) : mk (n : R) = n := rfl

@[simp]
theorem mk_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    mk (no_index (OfNat.ofNat n) : R) = OfNat.ofNat n :=
  rfl

instance instIntCast [IntCast R] : IntCast (SeparationQuotient R) where
  intCast n := mk n

@[simp, norm_cast]
theorem mk_intCast [IntCast R] (n : ℤ) : mk (n : R) = n := rfl

instance instNonAssocSemiring [NonAssocSemiring R] [TopologicalSemiring R] :
    NonAssocSemiring (SeparationQuotient R) :=
  surjective_mk.nonAssocSemiring mk mk_zero mk_one mk_add mk_mul mk_smul mk_natCast

instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] [TopologicalRing R] :
    NonUnitalNonAssocRing (SeparationQuotient R) :=
  surjective_mk.nonUnitalNonAssocRing mk mk_zero mk_add mk_mul mk_neg mk_sub mk_smul mk_smul

instance instNonUnitalRing [NonUnitalRing R] [TopologicalRing R] :
    NonUnitalRing (SeparationQuotient R) :=
  surjective_mk.nonUnitalRing mk mk_zero mk_add mk_mul mk_neg mk_sub mk_smul mk_smul

instance instNonAssocRing [NonAssocRing R] [TopologicalRing R] :
    NonAssocRing (SeparationQuotient R) :=
  surjective_mk.nonAssocRing mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub mk_smul mk_smul
    mk_natCast mk_intCast

instance instSemiring [Semiring R] [TopologicalSemiring R] :
    Semiring (SeparationQuotient R) :=
  surjective_mk.semiring mk mk_zero mk_one mk_add mk_mul mk_smul mk_pow mk_natCast

instance instRing [Ring R] [TopologicalRing R] :
    Ring (SeparationQuotient R) :=
  surjective_mk.ring mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub mk_smul mk_smul mk_pow
    mk_natCast mk_intCast

instance instNonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring R]
    [TopologicalSemiring R] :
    NonUnitalNonAssocCommSemiring (SeparationQuotient R) :=
  surjective_mk.nonUnitalNonAssocCommSemiring mk mk_zero mk_add mk_mul mk_smul

instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] [TopologicalSemiring R] :
    NonUnitalCommSemiring (SeparationQuotient R) :=
  surjective_mk.nonUnitalCommSemiring mk mk_zero mk_add mk_mul mk_smul

instance instCommSemiring [CommSemiring R] [TopologicalSemiring R] :
    CommSemiring (SeparationQuotient R) :=
  surjective_mk.commSemiring mk mk_zero mk_one mk_add mk_mul mk_smul mk_pow mk_natCast

instance instHasDistribNeg [Mul R] [HasDistribNeg R] [ContinuousMul R] [ContinuousNeg R] :
    HasDistribNeg (SeparationQuotient R) :=
  surjective_mk.hasDistribNeg mk mk_neg mk_mul

instance instNonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing R] [TopologicalRing R] :
    NonUnitalNonAssocCommRing (SeparationQuotient R) :=
  surjective_mk.nonUnitalNonAssocCommRing mk mk_zero mk_add mk_mul mk_neg mk_sub mk_smul mk_smul

instance instNonUnitalCommRing [NonUnitalCommRing R] [TopologicalRing R] :
    NonUnitalCommRing (SeparationQuotient R) :=
  surjective_mk.nonUnitalCommRing mk mk_zero mk_add mk_mul mk_neg mk_sub mk_smul mk_smul

instance instCommRing [CommRing R] [TopologicalRing R] :
    CommRing (SeparationQuotient R) :=
  surjective_mk.commRing mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub mk_smul mk_smul mk_pow
    mk_natCast mk_intCast

end Ring

section DistribSMul

variable {M A : Type*} [TopologicalSpace A]

instance instDistribSMul [AddZeroClass A] [DistribSMul M A]
    [ContinuousAdd A] [ContinuousConstSMul M A] :
    DistribSMul M (SeparationQuotient A) :=
  surjective_mk.distribSMul mkAddMonoidHom mk_smul

instance instDistribMulAction [Monoid M] [AddMonoid A] [DistribMulAction M A]
    [ContinuousAdd A] [ContinuousConstSMul M A] :
    DistribMulAction M (SeparationQuotient A) :=
  surjective_mk.distribMulAction mkAddMonoidHom mk_smul

instance instMulDistribMulAction [Monoid M] [Monoid A] [MulDistribMulAction M A]
    [ContinuousMul A] [ContinuousConstSMul M A] :
    MulDistribMulAction M (SeparationQuotient A) :=
  surjective_mk.mulDistribMulAction mkMonoidHom mk_smul

end DistribSMul

section Module

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]

instance instModule : Module R (SeparationQuotient M) :=
  surjective_mk.module R mkAddMonoidHom mk_smul

variable (R M)

/-- `SeparationQuotient.mk` as a continuous linear map. -/
@[simps]
def mkCLM : M →L[R] SeparationQuotient M where
  toFun := mk
  map_add' := mk_add
  map_smul' := mk_smul

end Module

section VectorSpace

variable (K E : Type*) [DivisionRing K] [AddCommGroup E] [Module K E]
  [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousConstSMul K E]

/-- There exists a continuous `K`-linear map from `SeparationQuotient E` to `E`
such that `mk (outCLM x) = x` for all `x`.

Note that continuity of this map comes for free, because `mk` is a topology inducing map.
-/
theorem exists_out_continuousLinearMap :
    ∃ f : SeparationQuotient E →L[K] E, mkCLM K E ∘L f = .id K (SeparationQuotient E) := by
  rcases (mkCLM K E).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr surjective_mk) with ⟨f, hf⟩
  replace hf : mk ∘ f = id := congr_arg DFunLike.coe hf
  exact ⟨⟨f, inducing_mk.continuous_iff.2 (by continuity)⟩, DFunLike.ext' hf⟩

/-- A continuous `K`-linear map from `SeparationQuotient E` to `E`
such that `mk (outCLM x) = x` for all `x`. -/
noncomputable def outCLM : SeparationQuotient E →L[K] E :=
  (exists_out_continuousLinearMap K E).choose

@[simp]
theorem mkCLM_comp_outCLM : mkCLM K E ∘L outCLM K E = .id K (SeparationQuotient E) :=
  (exists_out_continuousLinearMap K E).choose_spec

variable {E} in
@[simp]
theorem mk_outCLM (x : SeparationQuotient E) : mk (outCLM K E x) = x :=
  DFunLike.congr_fun (mkCLM_comp_outCLM K E) x

@[simp]
theorem mk_comp_outCLM : mk ∘ outCLM K E = id := funext (mk_outCLM K)

/-- The `SeparationQuotient.outCLM K E` map is a topological embedding. -/
theorem outCLM_embedding : Embedding (outCLM K E) :=
  Function.LeftInverse.embedding (mk_outCLM K) continuous_mk (map_continuous _)

theorem outCLM_injective : Function.Injective (outCLM K E) :=
  (outCLM_embedding K E).injective

end VectorSpace

section VectorSpaceUniform

variable (K E : Type*) [DivisionRing K] [AddCommGroup E] [Module K E]
    [UniformSpace E] [UniformAddGroup E] [ContinuousConstSMul K E]

theorem outCLM_uniformInducing : UniformInducing (outCLM K E) := by
  rw [← uniformInducing_mk.uniformInducing_comp_iff, mk_comp_outCLM]
  exact uniformInducing_id

theorem outCLM_uniformEmbedding : UniformEmbedding (outCLM K E) where
  inj := outCLM_injective K E
  toUniformInducing := outCLM_uniformInducing K E

theorem outCLM_uniformContinuous : UniformContinuous (outCLM K E) :=
  (outCLM_uniformInducing K E).uniformContinuous

end VectorSpaceUniform

end SeparationQuotient
