import Mathlib.Topology.Algebra.Ring.Basic

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
  continuous_mul := quotientMap_mk.continuous_iff.2 _

@[to_additive]
instance [CommMagma M] [ContinuousMul M] : CommMagma (SeparationQuotient M) :=
  surjective_mk.commMagma mk mk_mul

@[to_additive]
instance [Semigroup M] [ContinuousMul M] : Semigroup (SeparationQuotient M) :=
  surjective_mk.semigroup mk mk_mul

@[to_additive]
instance [CommSemigroup M] [ContinuousMul M] : CommSemigroup (SeparationQuotient M) :=
  surjective_mk.commSemigroup mk mk_mul

end Monoid

section Group

variable {G : Type*} [TopologicalSpace G]

@[to_additive]
instance [Inv G] [ContinuousInv G] : Inv

end Group

end SeparationQuotient
