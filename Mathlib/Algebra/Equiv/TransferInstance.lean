/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Field.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Small.Defs
import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Transfer algebraic structures across `Equiv`s

In this file we prove theorems of the following form: if `β` has a
group structure and `α ≃ β` then `α` has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and
so on.

Note that most of these constructions can also be obtained using the `transport` tactic.

### Implementation details

When adding new definitions that transfer type-classes across an equivalence, please use
`abbrev`. See note [reducible non-instances].

## Tags

equiv, group, ring, field, module, algebra
-/


universe u v

variable {α : Type u} {β : Type v}

namespace Equiv

section Instances

variable (e : α ≃ β)

/-- Transfer `One` across an `Equiv` -/
@[to_additive "Transfer `Zero` across an `Equiv`"]
protected abbrev one [One β] : One α :=
  ⟨e.symm 1⟩

@[to_additive]
theorem one_def [One β] :
    letI := e.one
    1 = e.symm 1 :=
  rfl

@[to_additive]
noncomputable instance [Small.{v} α] [One α] : One (Shrink.{v} α) :=
  (equivShrink α).symm.one

/-- Transfer `Mul` across an `Equiv` -/
@[to_additive "Transfer `Add` across an `Equiv`"]
protected abbrev mul [Mul β] : Mul α :=
  ⟨fun x y => e.symm (e x * e y)⟩

@[to_additive]
theorem mul_def [Mul β] (x y : α) :
    letI := Equiv.mul e
    x * y = e.symm (e x * e y) :=
  rfl

@[to_additive]
noncomputable instance [Small.{v} α] [Mul α] : Mul (Shrink.{v} α) :=
  (equivShrink α).symm.mul

/-- Transfer `Div` across an `Equiv` -/
@[to_additive "Transfer `Sub` across an `Equiv`"]
protected abbrev div [Div β] : Div α :=
  ⟨fun x y => e.symm (e x / e y)⟩

@[to_additive]
theorem div_def [Div β] (x y : α) :
    letI := Equiv.div e
    x / y = e.symm (e x / e y) :=
  rfl

@[to_additive]
noncomputable instance [Small.{v} α] [Div α] : Div (Shrink.{v} α) :=
  (equivShrink α).symm.div

-- Porting note: this should be called `inv`,
-- but we already have an `Equiv.inv` (which perhaps should move to `Perm.inv`?)
/-- Transfer `Inv` across an `Equiv` -/
@[to_additive "Transfer `Neg` across an `Equiv`"]
protected abbrev Inv [Inv β] : Inv α :=
  ⟨fun x => e.symm (e x)⁻¹⟩

@[to_additive]
theorem inv_def [Inv β] (x : α) :
    letI := Equiv.Inv e
    x⁻¹ = e.symm (e x)⁻¹ :=
  rfl

@[to_additive]
noncomputable instance [Small.{v} α] [Inv α] : Inv (Shrink.{v} α) :=
  (equivShrink α).symm.Inv

/-- Transfer `SMul` across an `Equiv` -/
protected abbrev smul (R : Type*) [SMul R β] : SMul R α :=
  ⟨fun r x => e.symm (r • e x)⟩

theorem smul_def {R : Type*} [SMul R β] (r : R) (x : α) :
    letI := e.smul R
    r • x = e.symm (r • e x) :=
  rfl

noncomputable instance [Small.{v} α] (R : Type*) [SMul R α] : SMul R (Shrink.{v} α) :=
  (equivShrink α).symm.smul R

/-- Transfer `Pow` across an `Equiv` -/
@[reducible, to_additive existing smul]
protected def pow (N : Type*) [Pow β N] : Pow α N :=
  ⟨fun x n => e.symm (e x ^ n)⟩

theorem pow_def {N : Type*} [Pow β N] (n : N) (x : α) :
    letI := e.pow N
    x ^ n = e.symm (e x ^ n) :=
  rfl

noncomputable instance [Small.{v} α] (N : Type*) [Pow α N] : Pow (Shrink.{v} α) N :=
  (equivShrink α).symm.pow N

/-- An equivalence `e : α ≃ β` gives a multiplicative equivalence `α ≃* β` where
the multiplicative structure on `α` is the one obtained by transporting a multiplicative structure
on `β` back along `e`. -/
@[to_additive "An equivalence `e : α ≃ β` gives an additive equivalence `α ≃+ β` where
the additive structure on `α` is the one obtained by transporting an additive structure
on `β` back along `e`."]
def mulEquiv (e : α ≃ β) [Mul β] :
    let _ := Equiv.mul e
    α ≃* β := by
  intros
  exact
    { e with
      map_mul' := fun x y => by
        apply e.symm.injective
        simp [mul_def] }

@[to_additive (attr := simp)]
theorem mulEquiv_apply (e : α ≃ β) [Mul β] (a : α) : (mulEquiv e) a = e a :=
  rfl

@[to_additive]
theorem mulEquiv_symm_apply (e : α ≃ β) [Mul β] (b : β) :
    letI := Equiv.mul e
    (mulEquiv e).symm b = e.symm b :=
  rfl

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

@[simp]
theorem ringEquiv_apply (e : α ≃ β) [Add β] [Mul β] (a : α) : (ringEquiv e) a = e a :=
  rfl

theorem ringEquiv_symm_apply (e : α ≃ β) [Add β] [Mul β] (b : β) : by
    letI := Equiv.add e
    letI := Equiv.mul e
    exact (ringEquiv e).symm b = e.symm b := rfl

variable (α) in
/-- Shrink `α` to a smaller universe preserves ring structure. -/
noncomputable def _root_.Shrink.ringEquiv [Small.{v} α] [Add α] [Mul α] : Shrink.{v} α ≃+* α :=
  (equivShrink α).symm.ringEquiv

/-- Transfer `Semigroup` across an `Equiv` -/
@[to_additive "Transfer `add_semigroup` across an `Equiv`"]
protected abbrev semigroup [Semigroup β] : Semigroup α := by
  let mul := e.mul
  apply e.injective.semigroup _; intros; exact e.apply_symm_apply _

@[to_additive]
noncomputable instance [Small.{v} α] [Semigroup α] : Semigroup (Shrink.{v} α) :=
  (equivShrink α).symm.semigroup

/-- Transfer `SemigroupWithZero` across an `Equiv` -/
protected abbrev semigroupWithZero [SemigroupWithZero β] : SemigroupWithZero α := by
  let mul := e.mul
  let zero := e.zero
  apply e.injective.semigroupWithZero _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [SemigroupWithZero α] : SemigroupWithZero (Shrink.{v} α) :=
  (equivShrink α).symm.semigroupWithZero

/-- Transfer `CommSemigroup` across an `Equiv` -/
@[to_additive "Transfer `AddCommSemigroup` across an `Equiv`"]
protected abbrev commSemigroup [CommSemigroup β] : CommSemigroup α := by
  let mul := e.mul
  apply e.injective.commSemigroup _; intros; exact e.apply_symm_apply _

@[to_additive]
noncomputable instance [Small.{v} α] [CommSemigroup α] : CommSemigroup (Shrink.{v} α) :=
  (equivShrink α).symm.commSemigroup

/-- Transfer `MulZeroClass` across an `Equiv` -/
protected abbrev mulZeroClass [MulZeroClass β] : MulZeroClass α := by
  let zero := e.zero
  let mul := e.mul
  apply e.injective.mulZeroClass _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [MulZeroClass α] : MulZeroClass (Shrink.{v} α) :=
  (equivShrink α).symm.mulZeroClass

/-- Transfer `MulOneClass` across an `Equiv` -/
@[to_additive "Transfer `AddZeroClass` across an `Equiv`"]
protected abbrev mulOneClass [MulOneClass β] : MulOneClass α := by
  let one := e.one
  let mul := e.mul
  apply e.injective.mulOneClass _ <;> intros <;> exact e.apply_symm_apply _

@[to_additive]
noncomputable instance [Small.{v} α] [MulOneClass α] : MulOneClass (Shrink.{v} α) :=
  (equivShrink α).symm.mulOneClass

/-- Transfer `MulZeroOneClass` across an `Equiv` -/
protected abbrev mulZeroOneClass [MulZeroOneClass β] : MulZeroOneClass α := by
  let zero := e.zero
  let one := e.one
  let mul := e.mul
  apply e.injective.mulZeroOneClass _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [MulZeroOneClass α] : MulZeroOneClass (Shrink.{v} α) :=
  (equivShrink α).symm.mulZeroOneClass

/-- Transfer `Monoid` across an `Equiv` -/
@[to_additive "Transfer `AddMonoid` across an `Equiv`"]
protected abbrev monoid [Monoid β] : Monoid α := by
  let one := e.one
  let mul := e.mul
  let pow := e.pow ℕ
  apply e.injective.monoid _ <;> intros <;> exact e.apply_symm_apply _

@[to_additive]
noncomputable instance [Small.{v} α] [Monoid α] : Monoid (Shrink.{v} α) :=
  (equivShrink α).symm.monoid

/-- Transfer `CommMonoid` across an `Equiv` -/
@[to_additive "Transfer `AddCommMonoid` across an `Equiv`"]
protected abbrev commMonoid [CommMonoid β] : CommMonoid α := by
  let one := e.one
  let mul := e.mul
  let pow := e.pow ℕ
  apply e.injective.commMonoid _ <;> intros <;> exact e.apply_symm_apply _

@[to_additive]
noncomputable instance [Small.{v} α] [CommMonoid α] : CommMonoid (Shrink.{v} α) :=
  (equivShrink α).symm.commMonoid

/-- Transfer `Group` across an `Equiv` -/
@[to_additive "Transfer `AddGroup` across an `Equiv`"]
protected abbrev group [Group β] : Group α := by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  apply e.injective.group _ <;> intros <;> exact e.apply_symm_apply _

@[to_additive]
noncomputable instance [Small.{v} α] [Group α] : Group (Shrink.{v} α) :=
  (equivShrink α).symm.group

/-- Transfer `CommGroup` across an `Equiv` -/
@[to_additive "Transfer `AddCommGroup` across an `Equiv`"]
protected abbrev commGroup [CommGroup β] : CommGroup α := by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  apply e.injective.commGroup _ <;> intros <;> exact e.apply_symm_apply _

@[to_additive]
noncomputable instance [Small.{v} α] [CommGroup α] : CommGroup (Shrink.{v} α) :=
  (equivShrink α).symm.commGroup

/-- Transfer `NonUnitalNonAssocSemiring` across an `Equiv` -/
protected abbrev nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] :
    NonUnitalNonAssocSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalNonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [NonUnitalNonAssocSemiring α] :
    NonUnitalNonAssocSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalNonAssocSemiring

/-- Transfer `NonUnitalSemiring` across an `Equiv` -/
protected abbrev nonUnitalSemiring [NonUnitalSemiring β] : NonUnitalSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalSemiring _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [NonUnitalSemiring α] : NonUnitalSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalSemiring

/-- Transfer `AddMonoidWithOne` across an `Equiv` -/
protected abbrev addMonoidWithOne [AddMonoidWithOne β] : AddMonoidWithOne α :=
  { e.addMonoid, e.one with
    natCast := fun n => e.symm n
    natCast_zero := e.injective (by simp [zero_def])
    natCast_succ := fun n => e.injective (by simp [add_def, one_def]) }

noncomputable instance [Small.{v} α] [AddMonoidWithOne α] : AddMonoidWithOne (Shrink.{v} α) :=
  (equivShrink α).symm.addMonoidWithOne

/-- Transfer `AddGroupWithOne` across an `Equiv` -/
protected abbrev addGroupWithOne [AddGroupWithOne β] : AddGroupWithOne α :=
  { e.addMonoidWithOne,
    e.addGroup with
    intCast := fun n => e.symm n
    intCast_ofNat := fun n => by simp only [Int.cast_natCast]; rfl
    intCast_negSucc := fun _ =>
      congr_arg e.symm <| (Int.cast_negSucc _).trans <| congr_arg _ (e.apply_symm_apply _).symm }

noncomputable instance [Small.{v} α] [AddGroupWithOne α] : AddGroupWithOne (Shrink.{v} α) :=
  (equivShrink α).symm.addGroupWithOne

/-- Transfer `NonAssocSemiring` across an `Equiv` -/
protected abbrev nonAssocSemiring [NonAssocSemiring β] : NonAssocSemiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  apply e.injective.nonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [NonAssocSemiring α] : NonAssocSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonAssocSemiring

/-- Transfer `Semiring` across an `Equiv` -/
protected abbrev semiring [Semiring β] : Semiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow ℕ
  apply e.injective.semiring _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [Semiring α] : Semiring (Shrink.{v} α) :=
  (equivShrink α).symm.semiring

/-- Transfer `NonUnitalCommSemiring` across an `Equiv` -/
protected abbrev nonUnitalCommSemiring [NonUnitalCommSemiring β] : NonUnitalCommSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalCommSemiring _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [NonUnitalCommSemiring α] :
    NonUnitalCommSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalCommSemiring

/-- Transfer `CommSemiring` across an `Equiv` -/
protected abbrev commSemiring [CommSemiring β] : CommSemiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow ℕ
  apply e.injective.commSemiring _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [CommSemiring α] : CommSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.commSemiring

/-- Transfer `NonUnitalNonAssocRing` across an `Equiv` -/
protected abbrev nonUnitalNonAssocRing [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalNonAssocRing _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [NonUnitalNonAssocRing α] :
    NonUnitalNonAssocRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalNonAssocRing

/-- Transfer `NonUnitalRing` across an `Equiv` -/
protected abbrev nonUnitalRing [NonUnitalRing β] : NonUnitalRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalRing _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [NonUnitalRing α] : NonUnitalRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalRing

/-- Transfer `NonAssocRing` across an `Equiv` -/
protected abbrev nonAssocRing [NonAssocRing β] : NonAssocRing α := by
  let add_group_with_one := e.addGroupWithOne
  let mul := e.mul
  apply e.injective.nonAssocRing _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [NonAssocRing α] : NonAssocRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonAssocRing

/-- Transfer `Ring` across an `Equiv` -/
protected abbrev ring [Ring β] : Ring α := by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow ℕ
  apply e.injective.ring _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [Ring α] : Ring (Shrink.{v} α) :=
  (equivShrink α).symm.ring

/-- Transfer `NonUnitalCommRing` across an `Equiv` -/
protected abbrev nonUnitalCommRing [NonUnitalCommRing β] : NonUnitalCommRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalCommRing _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [NonUnitalCommRing α] : NonUnitalCommRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalCommRing

/-- Transfer `CommRing` across an `Equiv` -/
protected abbrev commRing [CommRing β] : CommRing α := by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow ℕ
  apply e.injective.commRing _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [CommRing α] : CommRing (Shrink.{v} α) :=
  (equivShrink α).symm.commRing

noncomputable instance [Small.{v} α] [Nontrivial α] : Nontrivial (Shrink.{v} α) :=
  (equivShrink α).symm.nontrivial

/-- Transfer `IsDomain` across an `Equiv` -/
protected theorem isDomain [Semiring α] [Semiring β] [IsDomain β] (e : α ≃+* β) : IsDomain α :=
  Function.Injective.isDomain e.toRingHom e.injective

noncomputable instance [Small.{v} α] [Semiring α] [IsDomain α] : IsDomain (Shrink.{v} α) :=
  Equiv.isDomain (Shrink.ringEquiv α)

/-- Transfer `NNRatCast` across an `Equiv` -/
protected abbrev nnratCast [NNRatCast β] : NNRatCast α where nnratCast q := e.symm q

/-- Transfer `RatCast` across an `Equiv` -/
protected abbrev ratCast [RatCast β] : RatCast α where ratCast n := e.symm n

noncomputable instance _root_.Shrink.instNNRatCast [Small.{v} α] [NNRatCast α] :
    NNRatCast (Shrink.{v} α) := (equivShrink α).symm.nnratCast

noncomputable instance _root_.Shrink.instRatCast [Small.{v} α] [RatCast α] :
    RatCast (Shrink.{v} α) := (equivShrink α).symm.ratCast

/-- Transfer `DivisionRing` across an `Equiv` -/
protected abbrev divisionRing [DivisionRing β] : DivisionRing α := by
  let add_group_with_one := e.addGroupWithOne
  let inv := e.Inv
  let div := e.div
  let mul := e.mul
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  let nnratCast := e.nnratCast
  let ratCast := e.ratCast
  let nnqsmul := e.smul ℚ≥0
  let qsmul := e.smul ℚ
  apply e.injective.divisionRing _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [DivisionRing α] : DivisionRing (Shrink.{v} α) :=
  (equivShrink α).symm.divisionRing

/-- Transfer `Field` across an `Equiv` -/
protected abbrev field [Field β] : Field α := by
  let add_group_with_one := e.addGroupWithOne
  let neg := e.Neg
  let inv := e.Inv
  let div := e.div
  let mul := e.mul
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  let nnratCast := e.nnratCast
  let ratCast := e.ratCast
  let nnqsmul := e.smul ℚ≥0
  let qsmul := e.smul ℚ
  apply e.injective.field _ <;> intros <;> exact e.apply_symm_apply _

noncomputable instance [Small.{v} α] [Field α] : Field (Shrink.{v} α) :=
  (equivShrink α).symm.field

section R

variable (R : Type*)

section

variable [Monoid R]

/-- Transfer `MulAction` across an `Equiv` -/
protected abbrev mulAction (e : α ≃ β) [MulAction R β] : MulAction R α :=
  { e.smul R with
    one_smul := by simp [smul_def]
    mul_smul := by simp [smul_def, mul_smul] }

noncomputable instance [Small.{v} α] [MulAction R α] : MulAction R (Shrink.{v} α) :=
  (equivShrink α).symm.mulAction R

/-- Transfer `DistribMulAction` across an `Equiv` -/
protected abbrev distribMulAction (e : α ≃ β) [AddCommMonoid β] :
    letI := Equiv.addCommMonoid e
    ∀ [DistribMulAction R β], DistribMulAction R α := by
  intros
  letI := Equiv.addCommMonoid e
  exact
    ({ Equiv.mulAction R e with
        smul_zero := by simp [zero_def, smul_def]
        smul_add := by simp [add_def, smul_def, smul_add] } :
      DistribMulAction R α)

noncomputable instance [Small.{v} α] [AddCommMonoid α] [DistribMulAction R α] :
    DistribMulAction R (Shrink.{v} α) :=
  (equivShrink α).symm.distribMulAction R

end

section

variable [Semiring R]

/-- Transfer `Module` across an `Equiv` -/
protected abbrev module (e : α ≃ β) [AddCommMonoid β] :
    let _ := Equiv.addCommMonoid e
    ∀ [Module R β], Module R α := by
  intros
  exact
    ({ Equiv.distribMulAction R e with
        zero_smul := by simp [smul_def, zero_smul, zero_def]
        add_smul := by simp [add_def, smul_def, add_smul] } :
      Module R α)

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
protected abbrev algebra (e : α ≃ β) [Semiring β] :
    let _ := Equiv.semiring e
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

lemma algebraMap_def (e : α ≃ β) [Semiring β] [Algebra R β] (r : R) :
    (@algebraMap R α _ (Equiv.semiring e) (Equiv.algebra R e)) r = e.symm ((algebraMap R β) r) := by
  let _ := Equiv.semiring e
  let _ := Equiv.algebra R e
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

@[simp]
theorem algEquiv_apply (e : α ≃ β) [Semiring β] [Algebra R β] (a : α) : (algEquiv R e) a = e a :=
  rfl

theorem algEquiv_symm_apply (e : α ≃ β) [Semiring β] [Algebra R β] (b : β) : by
    letI := Equiv.semiring e
    letI := Equiv.algebra R e
    exact (algEquiv R e).symm b = e.symm b := rfl

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

attribute [-instance] Fin.instMul

/-- Any finite group in universe `u` is equivalent to some finite group in universe `v`. -/
lemma exists_type_univ_nonempty_mulEquiv (G : Type u) [Group G] [Finite G] :
    ∃ (G' : Type v) (_ : Group G') (_ : Fintype G'), Nonempty (G ≃* G') := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
  let f : Fin n ≃ ULift (Fin n) := Equiv.ulift.symm
  let e : G ≃ ULift (Fin n) := e.trans f
  letI groupH : Group (ULift (Fin n)) := e.symm.group
  exact ⟨ULift (Fin n), groupH, inferInstance, ⟨MulEquiv.symm <| e.symm.mulEquiv⟩⟩

end Finite

section

variable {R : Type*} [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable [AddCommMonoid α] [AddCommMonoid β] [Module A β]

/-- Transport a module instance via an isomorphism of the underlying abelian groups.
This has better definitional properties than `Equiv.module` since here
the abelian group structure remains unmodified. -/
abbrev AddEquiv.module (e : α ≃+ β) :
    Module A α where
  toSMul := e.toEquiv.smul A
  one_smul := by simp [Equiv.smul_def]
  mul_smul := by simp [Equiv.smul_def, mul_smul]
  smul_zero := by simp [Equiv.smul_def]
  smul_add := by simp [Equiv.smul_def]
  add_smul := by simp [Equiv.smul_def, add_smul]
  zero_smul := by simp [Equiv.smul_def]

/-- The module instance from `AddEquiv.module` is compatible with the `R`-module structures,
if the `AddEquiv` is induced by an `R`-module isomorphism. -/
lemma LinearEquiv.isScalarTower [Module R α] [Module R β] [IsScalarTower R A β]
    (e : α ≃ₗ[R] β) :
    letI := e.toAddEquiv.module A
    IsScalarTower R A α := by
  letI := e.toAddEquiv.module A
  constructor
  intro x y z
  simp only [Equiv.smul_def, AddEquiv.toEquiv_eq_coe, smul_assoc]
  apply e.symm.map_smul

end
