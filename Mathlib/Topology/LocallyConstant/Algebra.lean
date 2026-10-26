/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.FunLike
public import Mathlib.Algebra.Module.FunLike
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Topology.LocallyConstant.Basic

import Mathlib.Algebra.GroupWithZero.Indicator

/-!
# Algebraic structure on locally constant functions

This file puts algebraic structure (`Group`, `AddGroup`, etc)
on the type of locally constant functions.

-/

@[expose] public section

namespace LocallyConstant

variable {X Y : Type*} [TopologicalSpace X]

@[to_additive]
instance [One Y] : One (LocallyConstant X Y) where one := const X 1

@[to_additive]
instance [One Y] : IsOneApply (LocallyConstant X Y) where

@[to_additive (attr := deprecated FunLike.coe_one +typeChanged (since := "2026-10-26"))]
theorem coe_one [One Y] : ⇑(1 : LocallyConstant X Y) = (1 : X → Y) :=
  rfl

@[to_additive (attr := deprecated one_apply +typeChanged (since := "2026-10-26"))]
protected theorem one_apply [One Y] (x : X) : (1 : LocallyConstant X Y) x = 1 :=
  rfl

@[to_additive]
instance [Inv Y] : Inv (LocallyConstant X Y) where inv f := ⟨f⁻¹, f.isLocallyConstant.inv⟩

@[to_additive]
instance [Inv Y] : IsInvApply (LocallyConstant X Y) where

@[to_additive (attr := deprecated FunLike.coe_inv +typeChanged (since := "2026-10-26"))]
theorem coe_inv [Inv Y] (f : LocallyConstant X Y) : ⇑(f⁻¹ : LocallyConstant X Y) = (f : X → Y)⁻¹ :=
  rfl

@[to_additive (attr := deprecated inv_apply +typeChanged (since := "2026-10-26"))]
protected theorem inv_apply [Inv Y] (f : LocallyConstant X Y) (x : X) : f⁻¹ x = (f x)⁻¹ :=
  rfl

@[to_additive]
instance [Mul Y] : Mul (LocallyConstant X Y) where
  mul f g := ⟨f * g, f.isLocallyConstant.mul g.isLocallyConstant⟩

@[to_additive]
instance [Mul Y] : IsMulApply (LocallyConstant X Y) where

@[to_additive (attr := deprecated FunLike.coe_mul +typeChanged (since := "2026-10-26"))]
theorem coe_mul [Mul Y] (f g : LocallyConstant X Y) : ⇑(f * g) = f * g :=
  rfl

@[to_additive (attr := deprecated mul_apply +typeChanged (since := "2026-10-26"))]
protected theorem mul_apply [Mul Y] (f g : LocallyConstant X Y) (x : X) : (f * g) x = f x * g x :=
  rfl

@[to_additive]
instance [MulOneClass Y] : MulOneClass (LocallyConstant X Y) := fast_instance% FunLike.mulOneClass

@[to_additive (attr := deprecated (since := "2026-10-26"))]
alias coeFnMonoidHom := FunLike.coeMonoidHom

@[to_additive (attr := deprecated (since := "2026-10-26"))]
alias coeFnMonoidHom_apply := FunLike.coeMonoidHom_apply

/-- The constant-function embedding, as a multiplicative monoid hom. -/
@[to_additive (attr := simps) /-- The constant-function embedding, as an additive monoid hom. -/]
def constMonoidHom [MulOneClass Y] : Y →* LocallyConstant X Y where
  toFun := const X
  map_one' := rfl
  map_mul' _ _ := rfl

instance [MulZeroClass Y] : MulZeroClass (LocallyConstant X Y) :=
  fast_instance% FunLike.mulZeroClass

instance [MulZeroOneClass Y] : MulZeroOneClass (LocallyConstant X Y) :=
  fast_instance% FunLike.mulZeroOneClass

section CharFn

variable (Y) [MulZeroOneClass Y] {U V : Set X}

/-- Characteristic functions are locally constant functions taking `x : X` to `1` if `x ∈ U`,
  where `U` is a clopen set, and `0` otherwise. -/
noncomputable def charFn (hU : IsClopen U) : LocallyConstant X Y :=
  indicator 1 hU

theorem coe_charFn (hU : IsClopen U) : (charFn Y hU : X → Y) = Set.indicator U 1 :=
  rfl

theorem charFn_eq_one [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (1 : Y) ↔ x ∈ U :=
  Set.indicator_eq_one_iff_mem _

theorem charFn_eq_zero [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (0 : Y) ↔ x ∉ U :=
  Set.indicator_eq_zero_iff_notMem _

theorem charFn_inj [Nontrivial Y] (hU : IsClopen U) (hV : IsClopen V)
    (h : charFn Y hU = charFn Y hV) : U = V :=
  Set.indicator_one_inj Y <| coe_inj.mpr h

end CharFn

@[to_additive]
instance [Div Y] : Div (LocallyConstant X Y) where
  div f g := ⟨f / g, f.isLocallyConstant.div g.isLocallyConstant⟩

@[to_additive]
instance [Div Y] : IsDivApply (LocallyConstant X Y) where

@[to_additive (attr := deprecated FunLike.coe_mul +typeChanged (since := "2026-10-26"))]
theorem coe_div [Div Y] (f g : LocallyConstant X Y) : ⇑(f / g) = f / g :=
  rfl

@[to_additive (attr := deprecated inv_apply +typeChanged (since := "2026-10-26"))]
protected theorem div_apply [Div Y] (f g : LocallyConstant X Y) (x : X) : (f / g) x = f x / g x :=
  rfl

@[to_additive]
instance [Semigroup Y] : Semigroup (LocallyConstant X Y) := fast_instance% FunLike.semigroup

instance [SemigroupWithZero Y] : SemigroupWithZero (LocallyConstant X Y) :=
  fast_instance% FunLike.semigroupWithZero

@[to_additive]
instance [CommSemigroup Y] : CommSemigroup (LocallyConstant X Y) :=
  fast_instance% FunLike.commSemigroup

variable {α R : Type*}

@[to_additive (attr := to_additive) instSMul]
instance [Pow Y α] : Pow (LocallyConstant X Y) α where
  pow f n := f.map (· ^ n)

@[to_additive]
instance [Pow Y α] : IsPowApply α (LocallyConstant X Y) where

@[to_additive (attr := deprecated FunLike.coe_mul +typeChanged (since := "2026-10-26"))]
theorem coe_pow [Pow Y R] (r : R) (f : LocallyConstant X Y) : ⇑(f ^ r) = (f : X → Y) ^ r := rfl

@[to_additive (attr := deprecated inv_apply +typeChanged (since := "2026-10-26"))]
protected theorem pow_apply [Pow Y R] (r : R) (f : LocallyConstant X Y) (x : X) :
    (f ^ r) x = f x ^ r := rfl

@[to_additive]
instance [Monoid Y] : Monoid (LocallyConstant X Y) := fast_instance% FunLike.monoid

instance [NatCast Y] : NatCast (LocallyConstant X Y) where
  natCast n := const X n

instance [NatCast Y] : IsNatCastApply (LocallyConstant X Y) where

instance [IntCast Y] : IntCast (LocallyConstant X Y) where
  intCast n := const X n

instance [IntCast Y] : IsIntCastApply (LocallyConstant X Y) where

instance [AddMonoidWithOne Y] : AddMonoidWithOne (LocallyConstant X Y) :=
  fast_instance% FunLike.addMonoidWithOne

@[to_additive]
instance [CommMonoid Y] : CommMonoid (LocallyConstant X Y) := fast_instance% FunLike.commMonoid

@[to_additive]
instance [Group Y] : Group (LocallyConstant X Y) := fast_instance% FunLike.group

@[to_additive]
instance [CommGroup Y] : CommGroup (LocallyConstant X Y) := fast_instance% FunLike.commGroup

instance [Distrib Y] : Distrib (LocallyConstant X Y) := fast_instance% FunLike.distrib

instance [NonUnitalNonAssocSemiring Y] : NonUnitalNonAssocSemiring (LocallyConstant X Y) :=
  fast_instance% FunLike.nonUnitalNonAssocSemiring

instance [NonUnitalSemiring Y] : NonUnitalSemiring (LocallyConstant X Y) :=
  fast_instance% FunLike.nonUnitalSemiring

instance [NonAssocSemiring Y] : NonAssocSemiring (LocallyConstant X Y) :=
  fast_instance% FunLike.nonAssocSemiring

/-- The constant-function embedding, as a ring hom. -/
@[simps]
def constRingHom [NonAssocSemiring Y] : Y →+* LocallyConstant X Y :=
  { constMonoidHom, constAddMonoidHom with toFun := const X }

instance [Semiring Y] : Semiring (LocallyConstant X Y) := fast_instance% FunLike.semiring

instance [NonUnitalCommSemiring Y] : NonUnitalCommSemiring (LocallyConstant X Y) :=
  fast_instance% FunLike.nonUnitalCommSemiring

instance [CommSemiring Y] : CommSemiring (LocallyConstant X Y) :=
  fast_instance% FunLike.commSemiring

instance [NonUnitalNonAssocRing Y] : NonUnitalNonAssocRing (LocallyConstant X Y) :=
  fast_instance% FunLike.nonUnitalNonAssocRing

instance [NonUnitalRing Y] : NonUnitalRing (LocallyConstant X Y) :=
  fast_instance% FunLike.nonUnitalRing

instance [NonAssocRing Y] : NonAssocRing (LocallyConstant X Y) :=
  fast_instance% FunLike.nonAssocRing

instance [Ring Y] : Ring (LocallyConstant X Y) := fast_instance% FunLike.ring

instance [NonUnitalCommRing Y] : NonUnitalCommRing (LocallyConstant X Y) :=
  fast_instance% FunLike.nonUnitalCommRing

instance [CommRing Y] : CommRing (LocallyConstant X Y) := fast_instance% FunLike.commRing

variable {R : Type*}

instance [Monoid R] [MulAction R Y] : MulAction R (LocallyConstant X Y) :=
  fast_instance% FunLike.mulAction

instance [Monoid R] [AddMonoid Y] [DistribMulAction R Y] :
    DistribMulAction R (LocallyConstant X Y) := fast_instance% FunLike.distribMulAction

instance [Semiring R] [AddCommMonoid Y] [Module R Y] : Module R (LocallyConstant X Y) :=
  fast_instance% FunLike.module

section Algebra

variable [CommSemiring R] [Semiring Y] [Algebra R Y]

instance : Algebra R (LocallyConstant X Y) where
  algebraMap := constRingHom.comp <| algebraMap R Y
  commutes' := by
    intros
    ext
    exact Algebra.commutes' _ _
  smul_def' := by
    intros
    ext
    exact Algebra.smul_def' _ _

@[simp]
theorem coe_algebraMap (r : R) : ⇑(algebraMap R (LocallyConstant X Y) r) = algebraMap R (X → Y) r :=
  rfl

end Algebra

section coeFn

@[deprecated (since := "2026-10-26")] alias coeFnRingHom := FunLike.coeRingHom
@[deprecated (since := "2026-10-26")] alias coeFnRingHom_apply := FunLike.coeRingHom_apply

@[deprecated (since := "2026-10-26")] alias coeFnₗ := FunLike.coeₗ
@[deprecated (since := "2026-10-26")] alias coeFnₗ_apply := FunLike.coeₗ_apply

@[deprecated (since := "2026-10-26")] alias coeFnAlgHom := FunLike.coeAlgHom
@[deprecated (since := "2026-10-26")] alias coeFnAlgHom_apply := FunLike.coeAlgHom_apply

end coeFn

section Eval

@[deprecated (since := "2026-10-26")] alias evalMonoidHom := FunLike.evalMonoidHom
@[deprecated (since := "2026-10-26")] alias evalMonoidHom_apply := FunLike.evalMonoidHom_apply

@[deprecated (since := "2026-10-26")] alias evalₗ := FunLike.evalₗ
@[deprecated (since := "2026-10-26")] alias evalₗ_apply := FunLike.evalₗ_apply

@[deprecated (since := "2026-10-26")] alias evalRingHom := FunLike.evalRingHom
@[deprecated (since := "2026-10-26")] alias evalRingHom_apply := FunLike.evalRingHom_apply

@[deprecated (since := "2026-10-26")] alias evalAlgHom := FunLike.evalRingHom
@[deprecated (since := "2026-10-26")] alias evalAlgHom_apply := FunLike.evalRingHom_apply

end Eval

section Comap

variable [TopologicalSpace Y] {Z : Type*}

/-- `LocallyConstant.comap` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `LocallyConstant.comap` as an `AddMonoidHom`. -/]
def comapMonoidHom [MulOneClass Z] (f : C(X, Y)) :
    LocallyConstant Y Z →* LocallyConstant X Z where
  toFun := comap f
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `LocallyConstant.comap` as a linear map. -/
@[simps!]
def comapₗ (R : Type*) [Semiring R] [AddCommMonoid Z] [Module R Z] (f : C(X, Y)) :
    LocallyConstant Y Z →ₗ[R] LocallyConstant X Z where
  toFun := comap f
  map_add' := map_add (comapAddMonoidHom f)
  map_smul' _ _ := rfl

/-- `LocallyConstant.comap` as a `RingHom`. -/
@[simps!]
def comapRingHom [Semiring Z] (f : C(X, Y)) :
    LocallyConstant Y Z →+* LocallyConstant X Z where
  toMonoidHom := comapMonoidHom f
  __ := (comapAddMonoidHom f)

/-- `LocallyConstant.comap` as an `AlgHom` -/
@[simps!]
def comapₐ (R : Type*) [CommSemiring R] [Semiring Z] [Algebra R Z]
    (f : C(X, Y)) : LocallyConstant Y Z →ₐ[R] LocallyConstant X Z where
  toRingHom := comapRingHom f
  commutes' _ := rfl

lemma ker_comapₗ [Semiring R] [AddCommMonoid Z] [Module R Z] (f : C(X, Y))
    (hfs : Function.Surjective f) :
    LinearMap.ker (comapₗ R f : LocallyConstant Y Z →ₗ[R] LocallyConstant X Z) = ⊥ :=
  LinearMap.ker_eq_bot_of_injective <| comap_injective _ hfs

/-- `LocallyConstant.congrLeft` as a linear equivalence. -/
@[simps!]
def congrLeftₗ (R : Type*) [Semiring R] [AddCommMonoid Z] [Module R Z] (e : X ≃ₜ Y) :
    LocallyConstant X Z ≃ₗ[R] LocallyConstant Y Z where
  toLinearMap := comapₗ R ⟨_, e.symm.continuous⟩
  __ := congrLeft e

/-- `LocallyConstant.congrLeft` as a `RingEquiv`. -/
@[simps!]
def congrLeftRingEquiv [Semiring Z] (e : X ≃ₜ Y) :
    LocallyConstant X Z ≃+* LocallyConstant Y Z where
  toEquiv := congrLeft e
  __ := comapMonoidHom ⟨_, e.symm.continuous⟩
  __ := comapAddMonoidHom ⟨_, e.symm.continuous⟩

/-- `LocallyConstant.congrLeft` as an `AlgEquiv`. -/
@[simps!]
def congrLeftₐ (R : Type*) [CommSemiring R] [Semiring Z] [Algebra R Z] (e : X ≃ₜ Y) :
    LocallyConstant X Z ≃ₐ[R] LocallyConstant Y Z where
  toEquiv := congrLeft e
  __ := comapₐ R ⟨_, e.symm.continuous⟩

end Comap

section Map

variable {Z : Type*}

/-- `LocallyConstant.map` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `LocallyConstant.map` as an `AddMonoidHom`. -/]
def mapMonoidHom [MulOneClass Y] [MulOneClass Z] (f : Y →* Z) :
    LocallyConstant X Y →* LocallyConstant X Z where
  toFun := map f
  map_one' := by aesop
  map_mul' := by aesop

/-- `LocallyConstant.map` as a linear map. -/
@[simps!]
def mapₗ (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
    [AddCommMonoid Z] [Module R Z] (f : Y →ₗ[R] Z) :
    LocallyConstant X Y →ₗ[R] LocallyConstant X Z where
  toFun := map f
  map_add' := by aesop
  map_smul' := by aesop

/-- `LocallyConstant.map` as a `RingHom`. -/
@[simps!]
def mapRingHom [Semiring Y] [Semiring Z] (f : Y →+* Z) :
    LocallyConstant X Y →+* LocallyConstant X Z where
  toMonoidHom := mapMonoidHom f
  __ := (mapAddMonoidHom f.toAddMonoidHom)

/-- `LocallyConstant.map` as an `AlgHom` -/
@[simps!]
def mapₐ (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] [Semiring Z] [Algebra R Z]
    (f : Y →ₐ[R] Z) : LocallyConstant X Y →ₐ[R] LocallyConstant X Z where
  toRingHom := mapRingHom f
  commutes' _ := by aesop

/-- `LocallyConstant.congrRight` as a linear equivalence. -/
@[simps!]
def congrRightₗ (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
    [AddCommMonoid Z] [Module R Z] (e : Y ≃ₗ[R] Z) :
    LocallyConstant X Y ≃ₗ[R] LocallyConstant X Z where
  toLinearMap := mapₗ R e
  __ := congrRight e.toEquiv

/-- `LocallyConstant.congrRight` as a `RingEquiv`. -/
@[simps!]
def congrRightRingEquiv [Semiring Y] [Semiring Z] (e : Y ≃+* Z) :
    LocallyConstant X Y ≃+* LocallyConstant X Z where
  toEquiv := congrRight e
  __ := mapMonoidHom e.toMonoidHom
  __ := mapAddMonoidHom e.toAddMonoidHom

/-- `LocallyConstant.congrRight` as an `AlgEquiv`. -/
@[simps!]
def congrRightₐ (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] [Semiring Z] [Algebra R Z]
    (e : Y ≃ₐ[R] Z) : LocallyConstant X Y ≃ₐ[R] LocallyConstant X Z where
  toEquiv := congrRight e
  __ := mapₐ R e.toAlgHom

end Map

section Const

/-- `LocallyConstant.const` as a linear map. -/
@[simps!]
def constₗ (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y] :
    Y →ₗ[R] LocallyConstant X Y where
  toFun := const X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `LocallyConstant.const` as an `AlgHom` -/
@[simps!]
def constₐ (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] :
    Y →ₐ[R] LocallyConstant X Y where
  toRingHom := constRingHom
  commutes' _ := rfl

end Const

end LocallyConstant
