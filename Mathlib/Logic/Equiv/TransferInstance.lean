/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Field.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Small.Defs

#align_import logic.equiv.transfer_instance from "leanprover-community/mathlib"@"ec1c7d810034d4202b0dd239112d1792be9f6fdc"

/-!
# Transfer algebraic structures across `Equiv`s

In this file we prove theorems of the following form: if `β` has a
group structure and `α ≃ β` then `α` has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and
so on.

Note that most of these constructions can also be obtained using the `transport` tactic.

### Implementation details

When adding new definitions that transfer type-classes across an equivalence, please mark them
`@[reducible]`. See note [reducible non-instances].

## Tags

equiv, group, ring, field, module, algebra
-/


universe u v

variable {α : Type u} {β : Type v}

namespace Equiv

section Instances

variable (e : α ≃ β)

/-- Transfer `One` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `Zero` across an `Equiv`"]
protected def one [One β] : One α :=
  ⟨e.symm 1⟩
#align equiv.has_one Equiv.one
#align equiv.has_zero Equiv.zero

@[to_additive]
theorem one_def [One β] :
    letI := e.one
    1 = e.symm 1 :=
  rfl
#align equiv.one_def Equiv.one_def
#align equiv.zero_def Equiv.zero_def

@[to_additive]
noncomputable instance [Small.{v} α] [One α] : One (Shrink.{v} α) :=
  (equivShrink α).symm.one

/-- Transfer `Mul` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `Add` across an `Equiv`"]
protected def mul [Mul β] : Mul α :=
  ⟨fun x y => e.symm (e x * e y)⟩
#align equiv.has_mul Equiv.mul
#align equiv.has_add Equiv.add

@[to_additive]
theorem mul_def [Mul β] (x y : α) :
    letI := Equiv.mul e
    x * y = e.symm (e x * e y) :=
  rfl
#align equiv.mul_def Equiv.mul_def
#align equiv.add_def Equiv.add_def

@[to_additive]
noncomputable instance [Small.{v} α] [Mul α] : Mul (Shrink.{v} α) :=
  (equivShrink α).symm.mul

/-- Transfer `Div` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `Sub` across an `Equiv`"]
protected def div [Div β] : Div α :=
  ⟨fun x y => e.symm (e x / e y)⟩
#align equiv.has_div Equiv.div
#align equiv.has_sub Equiv.sub

@[to_additive]
theorem div_def [Div β] (x y : α) :
    letI := Equiv.div e
    x / y = e.symm (e x / e y) :=
  rfl
#align equiv.div_def Equiv.div_def
#align equiv.sub_def Equiv.sub_def

@[to_additive]
noncomputable instance [Small.{v} α] [Div α] : Div (Shrink.{v} α) :=
  (equivShrink α).symm.div

-- Porting note: this should be called `inv`,
-- but we already have an `Equiv.inv` (which perhaps should move to `Perm.inv`?)
/-- Transfer `Inv` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `Neg` across an `Equiv`"]
protected def Inv [Inv β] : Inv α :=
  ⟨fun x => e.symm (e x)⁻¹⟩
#align equiv.has_inv Equiv.Inv
#align equiv.has_neg Equiv.Neg

@[to_additive]
theorem inv_def [Inv β] (x : α) :
    letI := Equiv.Inv e
    x⁻¹ = e.symm (e x)⁻¹ :=
  rfl
#align equiv.inv_def Equiv.inv_def
#align equiv.neg_def Equiv.neg_def

@[to_additive]
noncomputable instance [Small.{v} α] [Inv α] : Inv (Shrink.{v} α) :=
  (equivShrink α).symm.Inv

/-- Transfer `SMul` across an `Equiv` -/
@[reducible]
protected def smul (R : Type*) [SMul R β] : SMul R α :=
  ⟨fun r x => e.symm (r • e x)⟩
#align equiv.has_smul Equiv.smul

theorem smul_def {R : Type*} [SMul R β] (r : R) (x : α) :
    letI := e.smul R
    r • x = e.symm (r • e x) :=
  rfl
#align equiv.smul_def Equiv.smul_def

noncomputable instance [Small.{v} α] (R : Type*) [SMul R α] : SMul R (Shrink.{v} α) :=
  (equivShrink α).symm.smul R

/-- Transfer `Pow` across an `Equiv` -/
@[to_additive (attr := reducible) existing smul]
protected def pow (N : Type*) [Pow β N] : Pow α N :=
  ⟨fun x n => e.symm (e x ^ n)⟩
#align equiv.has_pow Equiv.pow

theorem pow_def {N : Type*} [Pow β N] (n : N) (x : α) :
    letI := e.pow N
    x ^ n = e.symm (e x ^ n) :=
  rfl
#align equiv.pow_def Equiv.pow_def

noncomputable instance [Small.{v} α] (N : Type*) [Pow α N] : Pow (Shrink.{v} α) N :=
  (equivShrink α).symm.pow N

/-- An equivalence `e : α ≃ β` gives a multiplicative equivalence `α ≃* β` where
the multiplicative structure on `α` is the one obtained by transporting a multiplicative structure
on `β` back along `e`. -/
@[to_additive "An equivalence `e : α ≃ β` gives an additive equivalence `α ≃+ β` where
the additive structure on `α` is the one obtained by transporting an additive structure
on `β` back along `e`."]
def mulEquiv (e : α ≃ β) [Mul β] :
    let mul := Equiv.mul e
    α ≃* β := by
  intros
  exact
    { e with
      map_mul' := fun x y => by
        apply e.symm.injective
        simp [mul_def] }
#align equiv.mul_equiv Equiv.mulEquiv
#align equiv.add_equiv Equiv.addEquiv

@[to_additive (attr := simp)]
theorem mulEquiv_apply (e : α ≃ β) [Mul β] (a : α) : (mulEquiv e) a = e a :=
  rfl
#align equiv.mul_equiv_apply Equiv.mulEquiv_apply
#align equiv.add_equiv_apply Equiv.addEquiv_apply

@[to_additive]
theorem mulEquiv_symm_apply (e : α ≃ β) [Mul β] (b : β) :
    letI := Equiv.mul e
    (mulEquiv e).symm b = e.symm b :=
  rfl
#align equiv.mul_equiv_symm_apply Equiv.mulEquiv_symm_apply
#align equiv.add_equiv_symm_apply Equiv.addEquiv_symm_apply

/-- Shrink `α` to a smaller universe preserves multiplication. -/
@[to_additive "Shrink `α` to a smaller universe preserves addition."]
noncomputable def _root_.Shrink.mulEquiv [Small.{v} α] [Mul α] : Shrink.{v} α ≃* α :=
  (equivShrink α).symm.mulEquiv

/-- An equivalence `e : α ≃ β` gives a ring equivalence `α ≃+* β`
where the ring structure on `α` is
the one obtained by transporting a ring structure on `β` back along `e`.
-/
def ringEquiv (e : α ≃ β) [Add β] [Mul β] : by
    let add := Equiv.add e
    let mul := Equiv.mul e
    exact α ≃+* β := by
  intros
  exact
    { e with
      map_add' := fun x y => by
        apply e.symm.injective
        simp [add_def]
      map_mul' := fun x y => by
        apply e.symm.injective
        simp [mul_def] }
#align equiv.ring_equiv Equiv.ringEquiv

@[simp]
theorem ringEquiv_apply (e : α ≃ β) [Add β] [Mul β] (a : α) : (ringEquiv e) a = e a :=
  rfl
#align equiv.ring_equiv_apply Equiv.ringEquiv_apply

theorem ringEquiv_symm_apply (e : α ≃ β) [Add β] [Mul β] (b : β) : by
    letI := Equiv.add e
    letI := Equiv.mul e
    exact (ringEquiv e).symm b = e.symm b := rfl
#align equiv.ring_equiv_symm_apply Equiv.ringEquiv_symm_apply

variable (α) in
/-- Shrink `α` to a smaller universe preserves ring structure. -/
noncomputable def _root_.Shrink.ringEquiv [Small.{v} α] [Ring α] : Shrink.{v} α ≃+* α :=
  (equivShrink α).symm.ringEquiv

/-- Transfer `Semigroup` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `add_semigroup` across an `Equiv`"]
protected def semigroup [Semigroup β] : Semigroup α := by
  let mul := e.mul
  apply e.injective.semigroup _; intros; exact e.apply_symm_apply _
#align equiv.semigroup Equiv.semigroup
#align equiv.add_semigroup Equiv.addSemigroup

@[to_additive]
noncomputable instance [Small.{v} α] [Semigroup α] : Semigroup (Shrink.{v} α) :=
  (equivShrink α).symm.semigroup

/-- Transfer `SemigroupWithZero` across an `Equiv` -/
@[reducible]
protected def semigroupWithZero [SemigroupWithZero β] : SemigroupWithZero α := by
  let mul := e.mul
  let zero := e.zero
  apply e.injective.semigroupWithZero _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.semigroup_with_zero Equiv.semigroupWithZero

@[to_additive]
noncomputable instance [Small.{v} α] [SemigroupWithZero α] : SemigroupWithZero (Shrink.{v} α) :=
  (equivShrink α).symm.semigroupWithZero

/-- Transfer `CommSemigroup` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `AddCommSemigroup` across an `Equiv`"]
protected def commSemigroup [CommSemigroup β] : CommSemigroup α := by
  let mul := e.mul
  apply e.injective.commSemigroup _; intros; exact e.apply_symm_apply _
#align equiv.comm_semigroup Equiv.commSemigroup
#align equiv.add_comm_semigroup Equiv.addCommSemigroup

@[to_additive]
noncomputable instance [Small.{v} α] [CommSemigroup α] : CommSemigroup (Shrink.{v} α) :=
  (equivShrink α).symm.commSemigroup

/-- Transfer `MulZeroClass` across an `Equiv` -/
@[reducible]
protected def mulZeroClass [MulZeroClass β] : MulZeroClass α := by
  let zero := e.zero
  let mul := e.mul
  apply e.injective.mulZeroClass _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.mul_zero_class Equiv.mulZeroClass

noncomputable instance [Small.{v} α] [MulZeroClass α] : MulZeroClass (Shrink.{v} α) :=
  (equivShrink α).symm.mulZeroClass

/-- Transfer `MulOneClass` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `AddZeroClass` across an `Equiv`"]
protected def mulOneClass [MulOneClass β] : MulOneClass α := by
  let one := e.one
  let mul := e.mul
  apply e.injective.mulOneClass _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.mul_one_class Equiv.mulOneClass
#align equiv.add_zero_class Equiv.addZeroClass

@[to_additive]
noncomputable instance [Small.{v} α] [MulOneClass α] : MulOneClass (Shrink.{v} α) :=
  (equivShrink α).symm.mulOneClass

/-- Transfer `MulZeroOneClass` across an `Equiv` -/
@[reducible]
protected def mulZeroOneClass [MulZeroOneClass β] : MulZeroOneClass α := by
  let zero := e.zero
  let one := e.one
  let mul := e.mul
  apply e.injective.mulZeroOneClass _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.mul_zero_one_class Equiv.mulZeroOneClass

noncomputable instance [Small.{v} α] [MulZeroOneClass α] : MulZeroOneClass (Shrink.{v} α) :=
  (equivShrink α).symm.mulZeroOneClass

/-- Transfer `Monoid` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `AddMonoid` across an `Equiv`"]
protected def monoid [Monoid β] : Monoid α := by
  let one := e.one
  let mul := e.mul
  let pow := e.pow ℕ
  apply e.injective.monoid _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.monoid Equiv.monoid
#align equiv.add_monoid Equiv.addMonoid

@[to_additive]
noncomputable instance [Small.{v} α] [Monoid α] : Monoid (Shrink.{v} α) :=
  (equivShrink α).symm.monoid

/-- Transfer `CommMonoid` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `AddCommMonoid` across an `Equiv`"]
protected def commMonoid [CommMonoid β] : CommMonoid α := by
  let one := e.one
  let mul := e.mul
  let pow := e.pow ℕ
  apply e.injective.commMonoid _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_monoid Equiv.commMonoid
#align equiv.add_comm_monoid Equiv.addCommMonoid

@[to_additive]
noncomputable instance [Small.{v} α] [CommMonoid α] : CommMonoid (Shrink.{v} α) :=
  (equivShrink α).symm.commMonoid

/-- Transfer `Group` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `AddGroup` across an `Equiv`"]
protected def group [Group β] : Group α := by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  apply e.injective.group _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.group Equiv.group
#align equiv.add_group Equiv.addGroup

@[to_additive]
noncomputable instance [Small.{v} α] [Group α] : Group (Shrink.{v} α) :=
  (equivShrink α).symm.group

/-- Transfer `CommGroup` across an `Equiv` -/
@[to_additive (attr := reducible) "Transfer `AddCommGroup` across an `Equiv`"]
protected def commGroup [CommGroup β] : CommGroup α := by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  apply e.injective.commGroup _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_group Equiv.commGroup
#align equiv.add_comm_group Equiv.addCommGroup

@[to_additive]
noncomputable instance [Small.{v} α] [CommGroup α] : CommGroup (Shrink.{v} α) :=
  (equivShrink α).symm.commGroup

/-- Transfer `NonUnitalNonAssocSemiring` across an `Equiv` -/
@[reducible]
protected def nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] :
    NonUnitalNonAssocSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalNonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_non_assoc_semiring Equiv.nonUnitalNonAssocSemiring

noncomputable instance [Small.{v} α] [NonUnitalNonAssocSemiring α] :
    NonUnitalNonAssocSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalNonAssocSemiring

/-- Transfer `NonUnitalSemiring` across an `Equiv` -/
@[reducible]
protected def nonUnitalSemiring [NonUnitalSemiring β] : NonUnitalSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalSemiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_semiring Equiv.nonUnitalSemiring

noncomputable instance [Small.{v} α] [NonUnitalSemiring α] : NonUnitalSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalSemiring

/-- Transfer `AddMonoidWithOne` across an `Equiv` -/
@[reducible]
protected def addMonoidWithOne [AddMonoidWithOne β] : AddMonoidWithOne α :=
  { e.addMonoid, e.one with
    natCast := fun n => e.symm n
    natCast_zero := e.injective (by simp [zero_def])
    natCast_succ := fun n => e.injective (by simp [add_def, one_def]) }
#align equiv.add_monoid_with_one Equiv.addMonoidWithOne

noncomputable instance [Small.{v} α] [AddMonoidWithOne α] : AddMonoidWithOne (Shrink.{v} α) :=
  (equivShrink α).symm.addMonoidWithOne

/-- Transfer `AddGroupWithOne` across an `Equiv` -/
@[reducible]
protected def addGroupWithOne [AddGroupWithOne β] : AddGroupWithOne α :=
  { e.addMonoidWithOne,
    e.addGroup with
    intCast := fun n => e.symm n
    intCast_ofNat := fun n => by simp only [Int.cast_ofNat]; rfl
    intCast_negSucc := fun n =>
      congr_arg e.symm <| (Int.cast_negSucc _).trans <| congr_arg _ (e.apply_symm_apply _).symm }
#align equiv.add_group_with_one Equiv.addGroupWithOne

noncomputable instance [Small.{v} α] [AddGroupWithOne α] : AddGroupWithOne (Shrink.{v} α) :=
  (equivShrink α).symm.addGroupWithOne

/-- Transfer `NonAssocSemiring` across an `Equiv` -/
@[reducible]
protected def nonAssocSemiring [NonAssocSemiring β] : NonAssocSemiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  apply e.injective.nonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_assoc_semiring Equiv.nonAssocSemiring

noncomputable instance [Small.{v} α] [NonAssocSemiring α] : NonAssocSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonAssocSemiring

/-- Transfer `Semiring` across an `Equiv` -/
@[reducible]
protected def semiring [Semiring β] : Semiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow ℕ
  apply e.injective.semiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.semiring Equiv.semiring

noncomputable instance [Small.{v} α] [Semiring α] : Semiring (Shrink.{v} α) :=
  (equivShrink α).symm.semiring

/-- Transfer `NonUnitalCommSemiring` across an `Equiv` -/
@[reducible]
protected def nonUnitalCommSemiring [NonUnitalCommSemiring β] : NonUnitalCommSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalCommSemiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_comm_semiring Equiv.nonUnitalCommSemiring

noncomputable instance [Small.{v} α] [NonUnitalCommSemiring α] :
    NonUnitalCommSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalCommSemiring

/-- Transfer `CommSemiring` across an `Equiv` -/
@[reducible]
protected def commSemiring [CommSemiring β] : CommSemiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow ℕ
  apply e.injective.commSemiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_semiring Equiv.commSemiring

noncomputable instance [Small.{v} α] [CommSemiring α] : CommSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.commSemiring

/-- Transfer `NonUnitalNonAssocRing` across an `Equiv` -/
@[reducible]
protected def nonUnitalNonAssocRing [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalNonAssocRing _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_non_assoc_ring Equiv.nonUnitalNonAssocRing

noncomputable instance [Small.{v} α] [NonUnitalNonAssocRing α] :
    NonUnitalNonAssocRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalNonAssocRing

/-- Transfer `NonUnitalRing` across an `Equiv` -/
@[reducible]
protected def nonUnitalRing [NonUnitalRing β] : NonUnitalRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalRing _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_ring Equiv.nonUnitalRing

noncomputable instance [Small.{v} α] [NonUnitalRing α] : NonUnitalRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalRing

/-- Transfer `NonAssocRing` across an `Equiv` -/
@[reducible]
protected def nonAssocRing [NonAssocRing β] : NonAssocRing α := by
  let add_group_with_one := e.addGroupWithOne
  let mul := e.mul
  apply e.injective.nonAssocRing _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_assoc_ring Equiv.nonAssocRing

noncomputable instance [Small.{v} α] [NonAssocRing α] : NonAssocRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonAssocRing

/-- Transfer `Ring` across an `Equiv` -/
@[reducible]
protected def ring [Ring β] : Ring α := by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow ℕ
  apply e.injective.ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.ring Equiv.ring

noncomputable instance [Small.{v} α] [Ring α] : Ring (Shrink.{v} α) :=
  (equivShrink α).symm.ring

/-- Transfer `NonUnitalCommRing` across an `Equiv` -/
@[reducible]
protected def nonUnitalCommRing [NonUnitalCommRing β] : NonUnitalCommRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalCommRing _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_comm_ring Equiv.nonUnitalCommRing

noncomputable instance [Small.{v} α] [NonUnitalCommRing α] : NonUnitalCommRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalCommRing

/-- Transfer `CommRing` across an `Equiv` -/
@[reducible]
protected def commRing [CommRing β] : CommRing α := by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow ℕ
  apply e.injective.commRing _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_ring Equiv.commRing

noncomputable instance [Small.{v} α] [CommRing α] : CommRing (Shrink.{v} α) :=
  (equivShrink α).symm.commRing

/-- Transfer `Nontrivial` across an `Equiv` -/
@[reducible]
protected theorem nontrivial [Nontrivial β] : Nontrivial α :=
  e.surjective.nontrivial
#align equiv.nontrivial Equiv.nontrivial

noncomputable instance [Small.{v} α] [Nontrivial α] : Nontrivial (Shrink.{v} α) :=
  (equivShrink α).symm.nontrivial

/-- Transfer `IsDomain` across an `Equiv` -/
@[reducible]
protected theorem isDomain [Ring α] [Ring β] [IsDomain β] (e : α ≃+* β) : IsDomain α :=
  Function.Injective.isDomain e.toRingHom e.injective
#align equiv.is_domain Equiv.isDomain

noncomputable instance [Small.{v} α] [Ring α] [IsDomain α] : IsDomain (Shrink.{v} α) :=
  Equiv.isDomain  (Shrink.ringEquiv α)

/-- Transfer `RatCast` across an `Equiv` -/
@[reducible]
protected def RatCast [RatCast β] : RatCast α where ratCast n := e.symm n
#align equiv.has_rat_cast Equiv.RatCast

noncomputable instance [Small.{v} α] [RatCast α] : RatCast (Shrink.{v} α) :=
  (equivShrink α).symm.RatCast

/-- Transfer `DivisionRing` across an `Equiv` -/
@[reducible]
protected def divisionRing [DivisionRing β] : DivisionRing α := by
  let add_group_with_one := e.addGroupWithOne
  let inv := e.Inv
  let div := e.div
  let mul := e.mul
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  let rat_cast := e.RatCast
  let qsmul := e.smul ℚ
  apply e.injective.divisionRing _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.division_ring Equiv.divisionRing

noncomputable instance [Small.{v} α] [DivisionRing α] : DivisionRing (Shrink.{v} α) :=
  (equivShrink α).symm.divisionRing

/-- Transfer `Field` across an `Equiv` -/
@[reducible]
protected def field [Field β] : Field α := by
  let add_group_with_one := e.addGroupWithOne
  let neg := e.Neg
  let inv := e.Inv
  let div := e.div
  let mul := e.mul
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  let rat_cast := e.RatCast
  let qsmul := e.smul ℚ
  apply e.injective.field _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.field Equiv.field

noncomputable instance [Small.{v} α] [Field α] : Field (Shrink.{v} α) :=
  (equivShrink α).symm.field

section R

variable (R : Type*)

section

variable [Monoid R]

/-- Transfer `MulAction` across an `Equiv` -/
@[reducible]
protected def mulAction (e : α ≃ β) [MulAction R β] : MulAction R α :=
  { e.smul R with
    one_smul := by simp [smul_def]
    mul_smul := by simp [smul_def, mul_smul] }
#align equiv.mul_action Equiv.mulAction

noncomputable instance [Small.{v} α] [MulAction R α] : MulAction R (Shrink.{v} α) :=
  (equivShrink α).symm.mulAction R

/-- Transfer `DistribMulAction` across an `Equiv` -/
@[reducible]
protected def distribMulAction (e : α ≃ β) [AddCommMonoid β] :
    letI := Equiv.addCommMonoid e
    ∀ [DistribMulAction R β], DistribMulAction R α := by
  intros
  letI := Equiv.addCommMonoid e
  exact
    ({ Equiv.mulAction R e with
        smul_zero := by simp [zero_def, smul_def]
        smul_add := by simp [add_def, smul_def, smul_add] } :
      DistribMulAction R α)
#align equiv.distrib_mul_action Equiv.distribMulAction

noncomputable instance [Small.{v} α] [AddCommMonoid α] [DistribMulAction R α] :
    DistribMulAction R (Shrink.{v} α) :=
  (equivShrink α).symm.distribMulAction R

end

section

variable [Semiring R]

/-- Transfer `Module` across an `Equiv` -/
@[reducible]
protected def module (e : α ≃ β) [AddCommMonoid β] :
    let addCommMonoid := Equiv.addCommMonoid e
    ∀ [Module R β], Module R α := by
  intros
  exact
    ({ Equiv.distribMulAction R e with
        zero_smul := by simp [smul_def, zero_smul, zero_def]
        add_smul := by simp [add_def, smul_def, add_smul] } :
      Module R α)
#align equiv.module Equiv.module

noncomputable instance [Small.{v} α] [AddCommMonoid α] [Module R α] : Module R (Shrink.{v} α) :=
  (equivShrink α).symm.module R

/-- An equivalence `e : α ≃ β` gives a linear equivalence `α ≃ₗ[R] β`
where the `R`-module structure on `α` is
the one obtained by transporting an `R`-module structure on `β` back along `e`.
-/
def linearEquiv (e : α ≃ β) [AddCommMonoid β] [Module R β] : by
    let addCommMonoid := Equiv.addCommMonoid e
    let module := Equiv.module R e
    exact α ≃ₗ[R] β := by
  intros
  exact
    { Equiv.addEquiv e with
      map_smul' := fun r x => by
        apply e.symm.injective
        simp only [toFun_as_coe, RingHom.id_apply, EmbeddingLike.apply_eq_iff_eq]
        exact Iff.mpr (apply_eq_iff_eq_symm_apply _) rfl }
#align equiv.linear_equiv Equiv.linearEquiv

variable (α) in
/-- Shrink `α` to a smaller universe preserves module structure. -/
@[simps!]
noncomputable def _root_.Shrink.linearEquiv [Small.{v} α] [AddCommMonoid α] [Module R α] :
    Shrink.{v} α ≃ₗ[R] α :=
  Equiv.linearEquiv _ (equivShrink α).symm

end

section

variable [CommSemiring R]

/-- Transfer `Algebra` across an `Equiv` -/
@[reducible]
protected def algebra (e : α ≃ β) [Semiring β] :
    let semiring := Equiv.semiring e
    ∀ [Algebra R β], Algebra R α := by
  intros
  letI : Module R α := e.module R
  fapply Algebra.ofModule
  · intro r x y
    show e.symm (e (e.symm (r • e x)) * e y) = e.symm (r • e.ringEquiv (x * y))
    simp only [apply_symm_apply, Algebra.smul_mul_assoc, map_mul, ringEquiv_apply]
  · intro r x y
    show e.symm (e x * e (e.symm (r • e y))) = e.symm (r • e (e.symm (e x * e y)))
    simp only [apply_symm_apply, Algebra.mul_smul_comm]
#align equiv.algebra Equiv.algebra

lemma algebraMap_def (e : α ≃ β) [Semiring β] [Algebra R β] (r : R) :
    let semiring := Equiv.semiring e
    let algebra := Equiv.algebra R e
    (algebraMap R α) r = e.symm ((algebraMap R β) r) := by
  intros
  simp only [Algebra.algebraMap_eq_smul_one]
  show e.symm (r • e 1) = e.symm (r • 1)
  simp only [Equiv.one_def, apply_symm_apply]

noncomputable instance [Small.{v} α] [Semiring α] [Algebra R α] :
    Algebra R (Shrink.{v} α) :=
  (equivShrink α).symm.algebra _

/-- An equivalence `e : α ≃ β` gives an algebra equivalence `α ≃ₐ[R] β`
where the `R`-algebra structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`.
-/
def algEquiv (e : α ≃ β) [Semiring β] [Algebra R β] : by
    let semiring := Equiv.semiring e
    let algebra := Equiv.algebra R e
    exact α ≃ₐ[R] β := by
  intros
  exact
    { Equiv.ringEquiv e with
      commutes' := fun r => by
        apply e.symm.injective
        simp only [RingEquiv.toEquiv_eq_coe, toFun_as_coe, EquivLike.coe_coe, ringEquiv_apply,
          symm_apply_apply, algebraMap_def] }
#align equiv.alg_equiv Equiv.algEquiv

@[simp]
theorem algEquiv_apply (e : α ≃ β) [Semiring β] [Algebra R β] (a : α) : (algEquiv R e) a = e a :=
  rfl

theorem algEquiv_symm_apply (e : α ≃ β) [Semiring β] [Algebra R β] (b : β) : by
    letI := Equiv.semiring e
    letI := Equiv.algebra R e
    exact (algEquiv R e).symm b = e.symm b := by intros; rfl

variable (α) in
/-- Shrink `α` to a smaller universe preserves algebra structure. -/
@[simps!]
noncomputable def _root_.Shrink.algEquiv [Small.{v} α] [Semiring α] [Algebra R α] :
    Shrink.{v} α ≃ₐ[R] α :=
  Equiv.algEquiv _ (equivShrink α).symm

end

end R

end Instances

end Equiv

namespace Finite

attribute [-instance] Fin.instMulFin

/-- Any finite group in universe `u` is equivalent to some finite group in universe `0`. -/
lemma exists_type_zero_nonempty_mulEquiv (G : Type u) [Group G] [Finite G] :
    ∃ (G' : Type) (_ : Group G') (_ : Fintype G'), Nonempty (G ≃* G') := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
  letI groupH : Group (Fin n) := Equiv.group e.symm
  exact ⟨Fin n, inferInstance, inferInstance, ⟨MulEquiv.symm <| Equiv.mulEquiv e.symm⟩⟩

end Finite
