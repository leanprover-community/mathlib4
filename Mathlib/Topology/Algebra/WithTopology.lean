/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.Algebra.GroupWithZero.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Star.TransferInstance
public import Mathlib.Topology.WithTopology

/-!
# Algebraic instances on `WithTopology`

`WithTopology X t` is a copy of `X` equipped with the topology `t`. In this file we transfer the
algebraic structure on `X` to `WithTopology X t` along `WithTopology.equiv X t`, so that
`WithTopology.ofTopology` and `WithTopology.toTopology` preserve all of the algebraic operations
definitionally.
-/

@[expose] public section

variable {X : Type*} (t : TopologicalSpace X)

namespace WithTopology

/-! ### Operations -/

@[to_additive]
instance [One X] : One (WithTopology X t) := (WithTopology.equiv X t).one

@[to_additive]
instance [Mul X] : Mul (WithTopology X t) := (WithTopology.equiv X t).mul

@[to_additive]
instance [Inv X] : Inv (WithTopology X t) := (WithTopology.equiv X t).Inv

@[to_additive]
instance [Div X] : Div (WithTopology X t) := (WithTopology.equiv X t).div

@[to_additive]
instance instSMul {M : Type*} [SMul M X] : SMul M (WithTopology X t) :=
  (WithTopology.equiv X t).smul M

@[to_additive existing instSMul]
instance instPow {M : Type*} [Pow X M] : Pow (WithTopology X t) M := (WithTopology.equiv X t).pow M

instance [NatCast X] : NatCast (WithTopology X t) where
  natCast n := toTopology t n

instance [IntCast X] : IntCast (WithTopology X t) where
  intCast n := toTopology t n

instance [NNRatCast X] : NNRatCast (WithTopology X t) := (WithTopology.equiv X t).nnratCast

instance [RatCast X] : RatCast (WithTopology X t) := (WithTopology.equiv X t).ratCast

instance [Star X] : Star (WithTopology X t) := (WithTopology.equiv X t).star

instance [Nontrivial X] : Nontrivial (WithTopology X t) := (WithTopology.equiv X t).nontrivial

/-! ### Lemmas about `ofTopology` and `toTopology` -/

section Lemmas

variable {M : Type*}

@[to_additive (attr := simp)]
lemma toTopology_one [One X] : toTopology t (1 : X) = 1 := rfl

@[to_additive (attr := simp)]
lemma ofTopology_one [One X] : ofTopology (1 : WithTopology X t) = 1 := rfl

@[to_additive (attr := simp)]
lemma toTopology_eq_one [One X] {x : X} : toTopology t x = 1 ↔ x = 1 :=
  toTopology_inj t

@[to_additive (attr := simp)]
lemma ofTopology_eq_one [One X] {x : WithTopology X t} : ofTopology x = 1 ↔ x = 1 :=
  ofTopology_inj t

@[to_additive (attr := simp)]
lemma toTopology_mul [Mul X] (x y : X) : toTopology t (x * y) = toTopology t x * toTopology t y :=
  rfl

@[to_additive (attr := simp)]
lemma ofTopology_mul [Mul X] (x y : WithTopology X t) :
    ofTopology (x * y) = ofTopology x * ofTopology y :=
  rfl

@[to_additive (attr := simp)]
lemma toTopology_inv [Inv X] (x : X) : toTopology t x⁻¹ = (toTopology t x)⁻¹ := rfl

@[to_additive (attr := simp)]
lemma ofTopology_inv [Inv X] (x : WithTopology X t) : ofTopology x⁻¹ = (ofTopology x)⁻¹ := rfl

@[to_additive (attr := simp)]
lemma toTopology_div [Div X] (x y : X) : toTopology t (x / y) = toTopology t x / toTopology t y :=
  rfl

@[to_additive (attr := simp)]
lemma ofTopology_div [Div X] (x y : WithTopology X t) :
    ofTopology (x / y) = ofTopology x / ofTopology y :=
  rfl

@[to_additive (attr := simp)]
lemma toTopology_smul [SMul M X] (c : M) (x : X) : toTopology t (c • x) = c • toTopology t x := rfl

@[to_additive (attr := simp)]
lemma ofTopology_smul [SMul M X] (c : M) (x : WithTopology X t) :
    ofTopology (c • x) = c • ofTopology x :=
  rfl

@[simp]
lemma toTopology_pow [Pow X M] (x : X) (n : M) : toTopology t (x ^ n) = toTopology t x ^ n := rfl

@[simp]
lemma ofTopology_pow [Pow X M] (x : WithTopology X t) (n : M) :
    ofTopology (x ^ n) = ofTopology x ^ n :=
  rfl

@[simp, norm_cast]
lemma toTopology_natCast [NatCast X] (n : ℕ) : toTopology t (n : X) = n := rfl

@[simp, norm_cast]
lemma ofTopology_natCast [NatCast X] (n : ℕ) : ofTopology (n : WithTopology X t) = n := rfl

@[simp]
lemma toTopology_ofNat [NatCast X] (n : ℕ) [n.AtLeastTwo] :
    toTopology t (ofNat(n) : X) = ofNat(n) :=
  rfl

@[simp]
lemma ofTopology_ofNat [NatCast X] (n : ℕ) [n.AtLeastTwo] :
    ofTopology (ofNat(n) : WithTopology X t) = ofNat(n) :=
  rfl

@[simp, norm_cast]
lemma toTopology_intCast [IntCast X] (n : ℤ) : toTopology t (n : X) = n := rfl

@[simp, norm_cast]
lemma ofTopology_intCast [IntCast X] (n : ℤ) : ofTopology (n : WithTopology X t) = n := rfl

@[simp, norm_cast]
lemma toTopology_nnratCast [NNRatCast X] (q : ℚ≥0) : toTopology t (q : X) = q := rfl

@[simp, norm_cast]
lemma ofTopology_nnratCast [NNRatCast X] (q : ℚ≥0) : ofTopology (q : WithTopology X t) = q := rfl

@[simp, norm_cast]
lemma toTopology_ratCast [RatCast X] (q : ℚ) : toTopology t (q : X) = q := rfl

@[simp, norm_cast]
lemma ofTopology_ratCast [RatCast X] (q : ℚ) : ofTopology (q : WithTopology X t) = q := rfl

@[simp]
lemma toTopology_star [Star X] (x : X) : toTopology t (star x) = star (toTopology t x) := rfl

@[simp]
lemma ofTopology_star [Star X] (x : WithTopology X t) : ofTopology (star x) = star (ofTopology x) :=
  rfl

end Lemmas

/-! ### Monoids and groups -/

@[to_additive]
instance [Semigroup X] : Semigroup (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).semigroup

@[to_additive]
instance [CommSemigroup X] : CommSemigroup (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).commSemigroup

@[to_additive]
instance [Mul X] [IsLeftCancelMul X] : IsLeftCancelMul (WithTopology X t) :=
  (WithTopology.equiv X t).isLeftCancelMul

@[to_additive]
instance [Mul X] [IsRightCancelMul X] : IsRightCancelMul (WithTopology X t) :=
  (WithTopology.equiv X t).isRightCancelMul

@[to_additive]
instance [Mul X] [IsCancelMul X] : IsCancelMul (WithTopology X t) :=
  (WithTopology.equiv X t).isCancelMul

@[to_additive]
instance [MulOneClass X] : MulOneClass (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).mulOneClass

@[to_additive]
instance [Monoid X] : Monoid (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).monoid

@[to_additive]
instance [CommMonoid X] : CommMonoid (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).commMonoid

@[to_additive]
instance [Group X] : Group (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).group

@[to_additive]
instance [CommGroup X] : CommGroup (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).commGroup

/-! ### Monoids and groups with zero -/

instance [SemigroupWithZero X] : SemigroupWithZero (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).semigroupWithZero

instance [MulZeroClass X] : MulZeroClass (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).mulZeroClass

instance [MulZeroOneClass X] : MulZeroOneClass (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).mulZeroOneClass

instance [MonoidWithZero X] : MonoidWithZero (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).monoidWithZero

instance [CommMonoidWithZero X] : CommMonoidWithZero (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).commMonoidWithZero

/-! ### Rings and fields -/

instance [AddMonoidWithOne X] : AddMonoidWithOne (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).addMonoidWithOne

instance [AddGroupWithOne X] : AddGroupWithOne (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).addGroupWithOne

instance [NonUnitalNonAssocSemiring X] : NonUnitalNonAssocSemiring (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).nonUnitalNonAssocSemiring

instance [NonUnitalSemiring X] : NonUnitalSemiring (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).nonUnitalSemiring

instance [NonAssocSemiring X] : NonAssocSemiring (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).nonAssocSemiring

instance [Semiring X] : Semiring (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).semiring

instance [NonUnitalCommSemiring X] : NonUnitalCommSemiring (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).nonUnitalCommSemiring

instance [CommSemiring X] : CommSemiring (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).commSemiring

instance [NonUnitalNonAssocRing X] : NonUnitalNonAssocRing (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).nonUnitalNonAssocRing

instance [NonUnitalRing X] : NonUnitalRing (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).nonUnitalRing

instance [NonAssocRing X] : NonAssocRing (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).nonAssocRing

instance [Ring X] : Ring (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).ring

instance [NonUnitalCommRing X] : NonUnitalCommRing (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).nonUnitalCommRing

instance [CommRing X] : CommRing (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).commRing

instance [Semiring X] [IsDomain X] : IsDomain (WithTopology X t) :=
  (WithTopology.equiv X t).isDomain

instance [DivisionRing X] : DivisionRing (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).divisionRing

instance [Field X] : Field (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).field

/-! ### Actions, modules and algebras -/

section Action

variable (M N : Type*)

@[to_additive]
instance [Monoid M] [MulAction M X] : MulAction M (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).mulAction M

@[to_additive]
instance [SMul M N] [SMul M X] [SMul N X] [IsScalarTower M N X] :
    IsScalarTower M N (WithTopology X t) :=
  (WithTopology.equiv X t).isScalarTower M N

@[to_additive]
instance [SMul M X] [SMul N X] [SMulCommClass M N X] : SMulCommClass M N (WithTopology X t) :=
  (WithTopology.equiv X t).smulCommClass M N

@[to_additive]
instance [SMul M X] [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] : IsCentralScalar M (WithTopology X t) :=
  (WithTopology.equiv X t).isCentralScalar M

@[to_additive]
instance [SMul M X] [FaithfulSMul M X] : FaithfulSMul M (WithTopology X t) :=
  (WithTopology.equiv X t).faithfulSMul M

instance [Monoid M] [Monoid X] [MulDistribMulAction M X] :
    MulDistribMulAction M (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).mulDistribMulAction M

instance [Zero X] [SMulZeroClass M X] : SMulZeroClass M (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).smulZeroClass M rfl

instance [Zero M] [Zero X] [SMulWithZero M X] : SMulWithZero M (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).smulWithZero M rfl

instance [MonoidWithZero M] [Zero X] [MulActionWithZero M X] :
    MulActionWithZero M (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).mulActionWithZero M rfl

instance [AddZeroClass X] [DistribSMul M X] : DistribSMul M (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).addEquiv.distribSMul M

instance [Monoid M] [AddMonoid X] [DistribMulAction M X] :
    DistribMulAction M (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).addEquiv.distribMulAction M

instance [Semiring M] [AddCommMonoid X] [Module M X] : Module M (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).addEquiv.module M

instance [Zero M] [Zero X] [SMul M X] [NoZeroSMulDivisors M X] :
    NoZeroSMulDivisors M (WithTopology X t) :=
  (WithTopology.equiv X t).noZeroSMulDivisors M rfl

instance [Semiring M] [AddCommMonoid X] [Module M X] [Module.IsTorsionFree M X] :
    Module.IsTorsionFree M (WithTopology X t) :=
  (WithTopology.equiv X t).addEquiv.moduleIsTorsionFree M

instance [CommSemiring M] [Semiring X] [Algebra M X] : Algebra M (WithTopology X t) :=
  (WithTopology.equiv X t).algebra M

end Action

/-! ### Star structures -/

instance [InvolutiveStar X] : InvolutiveStar (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).involutiveStar

instance [Mul X] [StarMul X] : StarMul (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).starMul

instance [AddMonoid X] [StarAddMonoid X] : StarAddMonoid (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).starAddMonoid

instance [NonUnitalNonAssocSemiring X] [StarRing X] : StarRing (WithTopology X t) :=
  fast_instance% (WithTopology.equiv X t).starRing

instance {M : Type*} [Star M] [Star X] [SMul M X] [StarModule M X] :
    StarModule M (WithTopology X t) :=
  (WithTopology.equiv X t).starModule M

/-! ### Bundled equivalences -/

section Equiv

variable (R X : Type*) (t : TopologicalSpace X)

/-- `WithTopology.equiv` as a multiplicative equivalence. -/
@[to_additive (attr := simps apply symm_apply)
  /-- `WithTopology.equiv` as an additive equivalence. -/]
protected def mulEquiv [Mul X] : WithTopology X t ≃* X where
  toFun := ofTopology
  invFun := toTopology t
  map_mul' _ _ := rfl

@[to_additive]
lemma coe_mulEquiv [Mul X] : ⇑(WithTopology.mulEquiv X t) = ofTopology := rfl

@[to_additive]
lemma coe_symm_mulEquiv [Mul X] : ⇑(WithTopology.mulEquiv X t).symm = toTopology t := rfl

@[to_additive (attr := simp)]
lemma toEquiv_mulEquiv [Mul X] :
    (WithTopology.mulEquiv X t).toEquiv = WithTopology.equiv X t :=
  rfl

/-- `WithTopology.equiv` as a ring equivalence. -/
@[simps apply symm_apply]
protected def ringEquiv [Add X] [Mul X] : WithTopology X t ≃+* X where
  toFun := ofTopology
  invFun := toTopology t
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

lemma coe_ringEquiv [Add X] [Mul X] : ⇑(WithTopology.ringEquiv X t) = ofTopology := rfl

lemma coe_symm_ringEquiv [Add X] [Mul X] :
    ⇑(WithTopology.ringEquiv X t).symm = toTopology t :=
  rfl

@[simp]
lemma toMulEquiv_ringEquiv [Add X] [Mul X] :
    (WithTopology.ringEquiv X t).toMulEquiv = WithTopology.mulEquiv X t :=
  rfl

@[simp]
lemma toAddEquiv_ringEquiv [Add X] [Mul X] :
    (WithTopology.ringEquiv X t).toAddEquiv = WithTopology.addEquiv X t :=
  rfl

/-- `WithTopology.equiv` as a linear equivalence. -/
@[simps apply symm_apply]
protected def linearEquiv [Semiring R] [AddCommMonoid X] [Module R X] :
    WithTopology X t ≃ₗ[R] X where
  __ := WithTopology.addEquiv X t
  map_smul' _ _ := rfl

lemma coe_linearEquiv [Semiring R] [AddCommMonoid X] [Module R X] :
    ⇑(WithTopology.linearEquiv R X t) = ofTopology :=
  rfl

lemma coe_symm_linearEquiv [Semiring R] [AddCommMonoid X] [Module R X] :
    ⇑(WithTopology.linearEquiv R X t).symm = toTopology t :=
  rfl

@[simp]
lemma toAddEquiv_linearEquiv [Semiring R] [AddCommMonoid X] [Module R X] :
    (WithTopology.linearEquiv R X t).toAddEquiv = WithTopology.addEquiv X t :=
  rfl

/-- `WithTopology.equiv` as an algebra equivalence. -/
@[simps apply symm_apply]
protected def algEquiv [CommSemiring R] [Semiring X] [Algebra R X] :
    WithTopology X t ≃ₐ[R] X where
  toFun := ofTopology
  invFun := toTopology t
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

lemma coe_algEquiv [CommSemiring R] [Semiring X] [Algebra R X] :
    ⇑(WithTopology.algEquiv R X t) = ofTopology :=
  rfl

lemma coe_symm_algEquiv [CommSemiring R] [Semiring X] [Algebra R X] :
    ⇑(WithTopology.algEquiv R X t).symm = toTopology t :=
  rfl

@[simp]
lemma toRingEquiv_algEquiv [CommSemiring R] [Semiring X] [Algebra R X] :
    (WithTopology.algEquiv R X t : WithTopology X t ≃+* X) = WithTopology.ringEquiv X t :=
  rfl

@[simp]
lemma toLinearEquiv_algEquiv [CommSemiring R] [Semiring X] [Algebra R X] :
    (WithTopology.algEquiv R X t).toLinearEquiv = WithTopology.linearEquiv R X t :=
  rfl

end Equiv

/-! ### Big operators -/

section BigOperators

variable {ι : Type*}

@[to_additive (attr := simp)]
lemma ofTopology_prod [CommMonoid X] (s : Finset ι) (f : ι → WithTopology X t) :
    ofTopology (∏ i ∈ s, f i) = ∏ i ∈ s, ofTopology (f i) :=
  map_prod (WithTopology.mulEquiv X t) _ _

@[to_additive (attr := simp)]
lemma toTopology_prod [CommMonoid X] (s : Finset ι) (f : ι → X) :
    toTopology t (∏ i ∈ s, f i) = ∏ i ∈ s, toTopology t (f i) :=
  map_prod (WithTopology.mulEquiv X t).symm _ _

@[to_additive (attr := simp)]
lemma ofTopology_listProd [Monoid X] (l : List (WithTopology X t)) :
    ofTopology l.prod = (l.map ofTopology).prod :=
  map_list_prod (WithTopology.mulEquiv X t) _

@[to_additive (attr := simp)]
lemma toTopology_listProd [Monoid X] (l : List X) :
    toTopology t l.prod = (l.map (toTopology t)).prod :=
  map_list_prod (WithTopology.mulEquiv X t).symm _

@[to_additive (attr := simp)]
lemma ofTopology_multisetProd [CommMonoid X] (s : Multiset (WithTopology X t)) :
    ofTopology s.prod = (s.map ofTopology).prod :=
  map_multiset_prod (WithTopology.mulEquiv X t) _

@[to_additive (attr := simp)]
lemma toTopology_multisetProd [CommMonoid X] (s : Multiset X) :
    toTopology t s.prod = (s.map (toTopology t)).prod :=
  map_multiset_prod (WithTopology.mulEquiv X t).symm _

end BigOperators

end WithTopology
