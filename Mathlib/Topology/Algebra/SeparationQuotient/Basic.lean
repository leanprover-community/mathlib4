/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Algebra.Module.LinearMap

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

assert_not_exists LinearIndependent

open scoped Topology

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
  continuous_const_smul c := isQuotientMap_mk.continuous_iff.2 <|
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

@[to_additive]
instance instIsScalarTower [SMul M N] [ContinuousConstSMul N X] [IsScalarTower M N X] :
    IsScalarTower M N (SeparationQuotient X) where
  smul_assoc a b := surjective_mk.forall.2 fun x ↦ congr_arg mk <| smul_assoc a b x

end SMul

instance instContinuousSMul {M X : Type*} [SMul M X] [TopologicalSpace M] [TopologicalSpace X]
    [ContinuousSMul M X] : ContinuousSMul M (SeparationQuotient X) where
  continuous_smul := by
    rw [(IsOpenQuotientMap.id.prodMap isOpenQuotientMap_mk).isQuotientMap.continuous_iff]
    exact continuous_mk.comp continuous_smul

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
  mul := Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ ↦ Inseparable.mul h₁ h₂

@[to_additive (attr := simp)]
theorem mk_mul [Mul M] [ContinuousMul M] (a b : M) : mk (a * b) = mk a * mk b := rfl

@[to_additive]
instance instContinuousMul [Mul M] [ContinuousMul M] : ContinuousMul (SeparationQuotient M) where
  continuous_mul := isQuotientMap_prodMap_mk.continuous_iff.2 <| continuous_mk.comp continuous_mul

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
@[to_additive (attr := simps) /-- `SeparationQuotient.mk` as an `AddMonoidHom`. -/]
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
  continuous_inv := isQuotientMap_mk.continuous_iff.2 <| continuous_mk.comp continuous_inv

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
  div := Quotient.map₂ (· / ·) fun _ _ h₁ _ _ h₂ ↦ (Inseparable.prod h₁ h₂).map continuous_div'

@[to_additive (attr := simp)]
theorem mk_div [Div G] [ContinuousDiv G] (x y : G) : mk (x / y) = mk x / mk y := rfl

@[to_additive]
instance instContinuousDiv [Div G] [ContinuousDiv G] : ContinuousDiv (SeparationQuotient G) where
  continuous_div' := isQuotientMap_prodMap_mk.continuous_iff.2 <| continuous_mk.comp continuous_div'

instance instZSMul [AddGroup G] [IsTopologicalAddGroup G] : SMul ℤ (SeparationQuotient G) :=
  inferInstance

@[to_additive existing]
instance instZPow [Group G] [IsTopologicalGroup G] : Pow (SeparationQuotient G) ℤ where
  pow x n := Quotient.map' (s₁ := inseparableSetoid G) (· ^ n) (fun _ _ h ↦ Inseparable.zpow h n) x

@[to_additive, simp] -- `mk_zsmul` is not a `simp` lemma because we have `mk_smul`
theorem mk_zpow [Group G] [IsTopologicalGroup G] (x : G) (n : ℤ) : mk (x ^ n) = (mk x) ^ n := rfl

@[to_additive]
instance instGroup [Group G] [IsTopologicalGroup G] : Group (SeparationQuotient G) :=
  surjective_mk.group mk mk_one mk_mul mk_inv mk_div mk_pow mk_zpow

@[to_additive]
instance instCommGroup [CommGroup G] [IsTopologicalGroup G] : CommGroup (SeparationQuotient G) :=
  surjective_mk.commGroup mk mk_one mk_mul mk_inv mk_div mk_pow mk_zpow

@[to_additive]
instance instIsTopologicalGroup [Group G] [IsTopologicalGroup G] :
    IsTopologicalGroup (SeparationQuotient G) where

end Group

section IsUniformGroup

@[to_additive]
instance instIsUniformGroup {G : Type*} [Group G] [UniformSpace G] [IsUniformGroup G] :
    IsUniformGroup (SeparationQuotient G) where
  uniformContinuous_div := by
    rw [uniformContinuous_dom₂]
    exact uniformContinuous_mk.comp uniformContinuous_div

end IsUniformGroup

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
    [IsTopologicalSemiring R] : NonUnitalNonAssocSemiring (SeparationQuotient R) :=
  surjective_mk.nonUnitalNonAssocSemiring mk mk_zero mk_add mk_mul mk_smul

instance instNonUnitalSemiring [NonUnitalSemiring R] [IsTopologicalSemiring R] :
    NonUnitalSemiring (SeparationQuotient R) :=
  surjective_mk.nonUnitalSemiring mk mk_zero mk_add mk_mul mk_smul

instance instNatCast [NatCast R] : NatCast (SeparationQuotient R) where
  natCast n := mk n

@[simp, norm_cast]
theorem mk_natCast [NatCast R] (n : ℕ) : mk (n : R) = n := rfl

@[simp]
theorem mk_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    mk (ofNat(n) : R) = OfNat.ofNat n :=
  rfl

instance instIntCast [IntCast R] : IntCast (SeparationQuotient R) where
  intCast n := mk n

@[simp, norm_cast]
theorem mk_intCast [IntCast R] (n : ℤ) : mk (n : R) = n := rfl

instance instNonAssocSemiring [NonAssocSemiring R] [IsTopologicalSemiring R] :
    NonAssocSemiring (SeparationQuotient R) :=
  surjective_mk.nonAssocSemiring mk mk_zero mk_one mk_add mk_mul mk_smul mk_natCast

instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] [IsTopologicalRing R] :
    NonUnitalNonAssocRing (SeparationQuotient R) :=
  surjective_mk.nonUnitalNonAssocRing mk mk_zero mk_add mk_mul mk_neg mk_sub mk_smul mk_smul

instance instNonUnitalRing [NonUnitalRing R] [IsTopologicalRing R] :
    NonUnitalRing (SeparationQuotient R) :=
  surjective_mk.nonUnitalRing mk mk_zero mk_add mk_mul mk_neg mk_sub mk_smul mk_smul

instance instNonAssocRing [NonAssocRing R] [IsTopologicalRing R] :
    NonAssocRing (SeparationQuotient R) :=
  surjective_mk.nonAssocRing mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub mk_smul mk_smul
    mk_natCast mk_intCast

instance instSemiring [Semiring R] [IsTopologicalSemiring R] :
    Semiring (SeparationQuotient R) :=
  surjective_mk.semiring mk mk_zero mk_one mk_add mk_mul mk_smul mk_pow mk_natCast

instance instRing [Ring R] [IsTopologicalRing R] :
    Ring (SeparationQuotient R) :=
  surjective_mk.ring mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub mk_smul mk_smul mk_pow
    mk_natCast mk_intCast

instance instNonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring R]
    [IsTopologicalSemiring R] :
    NonUnitalNonAssocCommSemiring (SeparationQuotient R) :=
  surjective_mk.nonUnitalNonAssocCommSemiring mk mk_zero mk_add mk_mul mk_smul

instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] [IsTopologicalSemiring R] :
    NonUnitalCommSemiring (SeparationQuotient R) :=
  surjective_mk.nonUnitalCommSemiring mk mk_zero mk_add mk_mul mk_smul

instance instCommSemiring [CommSemiring R] [IsTopologicalSemiring R] :
    CommSemiring (SeparationQuotient R) :=
  surjective_mk.commSemiring mk mk_zero mk_one mk_add mk_mul mk_smul mk_pow mk_natCast

instance instHasDistribNeg [Mul R] [HasDistribNeg R] [ContinuousMul R] [ContinuousNeg R] :
    HasDistribNeg (SeparationQuotient R) :=
  surjective_mk.hasDistribNeg mk mk_neg mk_mul

instance instNonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing R] [IsTopologicalRing R] :
    NonUnitalNonAssocCommRing (SeparationQuotient R) :=
  surjective_mk.nonUnitalNonAssocCommRing mk mk_zero mk_add mk_mul mk_neg mk_sub mk_smul mk_smul

instance instNonUnitalCommRing [NonUnitalCommRing R] [IsTopologicalRing R] :
    NonUnitalCommRing (SeparationQuotient R) :=
  surjective_mk.nonUnitalCommRing mk mk_zero mk_add mk_mul mk_neg mk_sub mk_smul mk_smul

instance instCommRing [CommRing R] [IsTopologicalRing R] :
    CommRing (SeparationQuotient R) :=
  surjective_mk.commRing mk mk_zero mk_one mk_add mk_mul mk_neg mk_sub mk_smul mk_smul mk_pow
    mk_natCast mk_intCast

/-- `SeparationQuotient.mk` as a `RingHom`. -/
@[simps]
def mkRingHom [NonAssocSemiring R] [IsTopologicalSemiring R] : R →+* SeparationQuotient R where
  toFun := mk
  map_one' := mk_one; map_zero' := mk_zero; map_add' := mk_add; map_mul' := mk_mul

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

variable {R S M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
    [Semiring S] [AddCommMonoid N] [Module S N]
    [TopologicalSpace N]

instance instModule : Module R (SeparationQuotient M) :=
  surjective_mk.module R mkAddMonoidHom mk_smul

variable (R M)

/-- `SeparationQuotient.mk` as a continuous linear map. -/
@[simps]
def mkCLM : M →L[R] SeparationQuotient M where
  toFun := mk
  map_add' := mk_add
  map_smul' := mk_smul

variable {R M}

/-- The lift (as a continuous linear map) of `f` with `f x = f y` for `Inseparable x y`. -/
@[simps]
noncomputable def liftCLM {σ : R →+* S} (f : M →SL[σ] N) (hf : ∀ x y, Inseparable x y → f x = f y) :
    SeparationQuotient M →SL[σ] N where
  toFun := SeparationQuotient.lift f hf
  map_add' := Quotient.ind₂ <| map_add f
  map_smul' {r} := Quotient.ind <| map_smulₛₗ f r

@[simp]
theorem liftCLM_mk {σ : R →+* S} (f : M →SL[σ] N) (hf : ∀ x y, Inseparable x y → f x = f y)
    (x : M) : liftCLM f hf (mk x) = f x := rfl

end Module

section Algebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [TopologicalSpace A] [IsTopologicalSemiring A] [ContinuousConstSMul R A]

instance instAlgebra : Algebra R (SeparationQuotient A) where
  algebraMap := mkRingHom.comp (algebraMap R A)
  commutes' r := Quotient.ind fun a => congrArg _ <| Algebra.commutes r a
  smul_def' r := Quotient.ind fun a => congrArg _ <| Algebra.smul_def r a

@[simp]
theorem mk_algebraMap (r : R) : mk (algebraMap R A r) = algebraMap R (SeparationQuotient A) r :=
  rfl

end Algebra

end SeparationQuotient
