/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module logic.equiv.transfer_instance
! leanprover-community/mathlib commit ec1c7d810034d4202b0dd239112d1792be9f6fdc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Equiv
import Mathbin.Algebra.Field.Basic
import Mathbin.Logic.Equiv.Defs

/-!
# Transfer algebraic structures across `equiv`s

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

/-- Transfer `has_one` across an `equiv` -/
@[reducible, to_additive "Transfer `has_zero` across an `equiv`"]
protected def hasOne [One β] : One α :=
  ⟨e.symm 1⟩
#align equiv.has_one Equiv.hasOne
#align equiv.has_zero Equiv.hasZero

@[to_additive]
theorem one_def [One β] : @One.one _ (Equiv.hasOne e) = e.symm 1 :=
  rfl
#align equiv.one_def Equiv.one_def
#align equiv.zero_def Equiv.zero_def

/-- Transfer `has_mul` across an `equiv` -/
@[reducible, to_additive "Transfer `has_add` across an `equiv`"]
protected def hasMul [Mul β] : Mul α :=
  ⟨fun x y => e.symm (e x * e y)⟩
#align equiv.has_mul Equiv.hasMul
#align equiv.has_add Equiv.hasAdd

@[to_additive]
theorem mul_def [Mul β] (x y : α) : @Mul.mul _ (Equiv.hasMul e) x y = e.symm (e x * e y) :=
  rfl
#align equiv.mul_def Equiv.mul_def
#align equiv.add_def Equiv.add_def

/-- Transfer `has_div` across an `equiv` -/
@[reducible, to_additive "Transfer `has_sub` across an `equiv`"]
protected def hasDiv [Div β] : Div α :=
  ⟨fun x y => e.symm (e x / e y)⟩
#align equiv.has_div Equiv.hasDiv
#align equiv.has_sub Equiv.hasSub

@[to_additive]
theorem div_def [Div β] (x y : α) : @Div.div _ (Equiv.hasDiv e) x y = e.symm (e x / e y) :=
  rfl
#align equiv.div_def Equiv.div_def
#align equiv.sub_def Equiv.sub_def

/-- Transfer `has_inv` across an `equiv` -/
@[reducible, to_additive "Transfer `has_neg` across an `equiv`"]
protected def hasInv [Inv β] : Inv α :=
  ⟨fun x => e.symm (e x)⁻¹⟩
#align equiv.has_inv Equiv.hasInv
#align equiv.has_neg Equiv.hasNeg

@[to_additive]
theorem inv_def [Inv β] (x : α) : @Inv.inv _ (Equiv.hasInv e) x = e.symm (e x)⁻¹ :=
  rfl
#align equiv.inv_def Equiv.inv_def
#align equiv.neg_def Equiv.neg_def

/-- Transfer `has_smul` across an `equiv` -/
@[reducible]
protected def hasSmul (R : Type _) [SMul R β] : SMul R α :=
  ⟨fun r x => e.symm (r • e x)⟩
#align equiv.has_smul Equiv.hasSmul

theorem smul_def {R : Type _} [SMul R β] (r : R) (x : α) :
    @SMul.smul _ _ (e.SMul R) r x = e.symm (r • e x) :=
  rfl
#align equiv.smul_def Equiv.smul_def

/-- Transfer `has_pow` across an `equiv` -/
@[reducible, to_additive SMul]
protected def hasPow (N : Type _) [Pow β N] : Pow α N :=
  ⟨fun x n => e.symm (e x ^ n)⟩
#align equiv.has_pow Equiv.hasPow
#align equiv.has_smul Equiv.hasSmul

theorem pow_def {N : Type _} [Pow β N] (n : N) (x : α) :
    @Pow.pow _ _ (e.Pow N) x n = e.symm (e x ^ n) :=
  rfl
#align equiv.pow_def Equiv.pow_def

/-- An equivalence `e : α ≃ β` gives a multiplicative equivalence `α ≃* β`
where the multiplicative structure on `α` is
the one obtained by transporting a multiplicative structure on `β` back along `e`.
-/
@[to_additive
      "An equivalence `e : α ≃ β` gives a additive equivalence `α ≃+ β`\nwhere the additive structure on `α` is\nthe one obtained by transporting an additive structure on `β` back along `e`."]
def mulEquiv (e : α ≃ β) [Mul β] :
    letI := Equiv.hasMul e
    α ≃* β :=
  by
  intros
  exact
    { e with
      map_mul' := fun x y => by
        apply e.symm.injective
        simp }
#align equiv.mul_equiv Equiv.mulEquiv
#align equiv.add_equiv Equiv.addEquiv

@[simp, to_additive]
theorem mulEquiv_apply (e : α ≃ β) [Mul β] (a : α) : (mulEquiv e) a = e a :=
  rfl
#align equiv.mul_equiv_apply Equiv.mulEquiv_apply
#align equiv.add_equiv_apply Equiv.add_equiv_apply

@[to_additive]
theorem mulEquiv_symm_apply (e : α ≃ β) [Mul β] (b : β) :
    letI := Equiv.hasMul e
    (MulEquiv e).symm b = e.symm b :=
  by intros ; rfl
#align equiv.mul_equiv_symm_apply Equiv.mulEquiv_symm_apply
#align equiv.add_equiv_symm_apply Equiv.add_equiv_symm_apply

/-- An equivalence `e : α ≃ β` gives a ring equivalence `α ≃+* β`
where the ring structure on `α` is
the one obtained by transporting a ring structure on `β` back along `e`.
-/
def ringEquiv (e : α ≃ β) [Add β] [Mul β] :
    by
    letI := Equiv.hasAdd e
    letI := Equiv.hasMul e
    exact α ≃+* β := by
  intros
  exact
    {
      e with
      map_add' := fun x y => by
        apply e.symm.injective
        simp
      map_mul' := fun x y => by
        apply e.symm.injective
        simp }
#align equiv.ring_equiv Equiv.ringEquiv

@[simp]
theorem ringEquiv_apply (e : α ≃ β) [Add β] [Mul β] (a : α) : (ringEquiv e) a = e a :=
  rfl
#align equiv.ring_equiv_apply Equiv.ringEquiv_apply

theorem ringEquiv_symm_apply (e : α ≃ β) [Add β] [Mul β] (b : β) :
    by
    letI := Equiv.hasAdd e
    letI := Equiv.hasMul e
    exact (RingEquiv e).symm b = e.symm b := by intros ; rfl
#align equiv.ring_equiv_symm_apply Equiv.ringEquiv_symm_apply

/-- Transfer `semigroup` across an `equiv` -/
@[reducible, to_additive "Transfer `add_semigroup` across an `equiv`"]
protected def semigroup [Semigroup β] : Semigroup α :=
  by
  let mul := e.Mul
  skip <;> apply e.injective.semigroup _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.semigroup Equiv.semigroup
#align equiv.add_semigroup Equiv.addSemigroup

/-- Transfer `semigroup_with_zero` across an `equiv` -/
@[reducible]
protected def semigroupWithZero [SemigroupWithZero β] : SemigroupWithZero α :=
  by
  let mul := e.Mul
  let zero := e.Zero
  skip <;> apply e.injective.semigroup_with_zero _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.semigroup_with_zero Equiv.semigroupWithZero

/-- Transfer `comm_semigroup` across an `equiv` -/
@[reducible, to_additive "Transfer `add_comm_semigroup` across an `equiv`"]
protected def commSemigroup [CommSemigroup β] : CommSemigroup α :=
  by
  let mul := e.Mul
  skip <;> apply e.injective.comm_semigroup _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_semigroup Equiv.commSemigroup
#align equiv.add_comm_semigroup Equiv.addCommSemigroup

/-- Transfer `mul_zero_class` across an `equiv` -/
@[reducible]
protected def mulZeroClass [MulZeroClass β] : MulZeroClass α :=
  by
  let zero := e.Zero
  let mul := e.Mul
  skip <;> apply e.injective.mul_zero_class _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.mul_zero_class Equiv.mulZeroClass

/-- Transfer `mul_one_class` across an `equiv` -/
@[reducible, to_additive "Transfer `add_zero_class` across an `equiv`"]
protected def mulOneClass [MulOneClass β] : MulOneClass α :=
  by
  let one := e.One
  let mul := e.Mul
  skip <;> apply e.injective.mul_one_class _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.mul_one_class Equiv.mulOneClass
#align equiv.add_zero_class Equiv.addZeroClass

/-- Transfer `mul_zero_one_class` across an `equiv` -/
@[reducible]
protected def mulZeroOneClass [MulZeroOneClass β] : MulZeroOneClass α :=
  by
  let zero := e.Zero
  let one := e.One
  let mul := e.Mul
  skip <;> apply e.injective.mul_zero_one_class _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.mul_zero_one_class Equiv.mulZeroOneClass

/-- Transfer `monoid` across an `equiv` -/
@[reducible, to_additive "Transfer `add_monoid` across an `equiv`"]
protected def monoid [Monoid β] : Monoid α :=
  by
  let one := e.One
  let mul := e.Mul
  let pow := e.Pow ℕ
  skip <;> apply e.injective.monoid _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.monoid Equiv.monoid
#align equiv.add_monoid Equiv.addMonoid

/-- Transfer `comm_monoid` across an `equiv` -/
@[reducible, to_additive "Transfer `add_comm_monoid` across an `equiv`"]
protected def commMonoid [CommMonoid β] : CommMonoid α :=
  by
  let one := e.One
  let mul := e.Mul
  let pow := e.Pow ℕ
  skip <;> apply e.injective.comm_monoid _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_monoid Equiv.commMonoid
#align equiv.add_comm_monoid Equiv.addCommMonoid

/-- Transfer `group` across an `equiv` -/
@[reducible, to_additive "Transfer `add_group` across an `equiv`"]
protected def group [Group β] : Group α :=
  by
  let one := e.One
  let mul := e.Mul
  let inv := e.Inv
  let div := e.Div
  let npow := e.Pow ℕ
  let zpow := e.Pow ℤ
  skip <;> apply e.injective.group _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.group Equiv.group
#align equiv.add_group Equiv.addGroup

/-- Transfer `comm_group` across an `equiv` -/
@[reducible, to_additive "Transfer `add_comm_group` across an `equiv`"]
protected def commGroup [CommGroup β] : CommGroup α :=
  by
  let one := e.One
  let mul := e.Mul
  let inv := e.Inv
  let div := e.Div
  let npow := e.Pow ℕ
  let zpow := e.Pow ℤ
  skip <;> apply e.injective.comm_group _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_group Equiv.commGroup
#align equiv.add_comm_group Equiv.addCommGroup

/-- Transfer `non_unital_non_assoc_semiring` across an `equiv` -/
@[reducible]
protected def nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] :
    NonUnitalNonAssocSemiring α := by
  let zero := e.Zero
  let add := e.Add
  let mul := e.Mul
  let nsmul := e.SMul ℕ
  skip <;> apply e.injective.non_unital_non_assoc_semiring _ <;> intros <;>
    exact e.apply_symm_apply _
#align equiv.non_unital_non_assoc_semiring Equiv.nonUnitalNonAssocSemiring

/-- Transfer `non_unital_semiring` across an `equiv` -/
@[reducible]
protected def nonUnitalSemiring [NonUnitalSemiring β] : NonUnitalSemiring α :=
  by
  let zero := e.Zero
  let add := e.Add
  let mul := e.Mul
  let nsmul := e.SMul ℕ
  skip <;> apply e.injective.non_unital_semiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_semiring Equiv.nonUnitalSemiring

/-- Transfer `add_monoid_with_one` across an `equiv` -/
@[reducible]
protected def addMonoidWithOne [AddMonoidWithOne β] : AddMonoidWithOne α :=
  { e.AddMonoid, e.One with
    natCast := fun n => e.symm n
    natCast_zero := show e.symm _ = _ by simp [zero_def]
    natCast_succ := fun n => show e.symm _ = e.symm (e (e.symm _) + _) by simp [add_def, one_def] }
#align equiv.add_monoid_with_one Equiv.addMonoidWithOne

/-- Transfer `add_group_with_one` across an `equiv` -/
@[reducible]
protected def addGroupWithOne [AddGroupWithOne β] : AddGroupWithOne α :=
  { e.AddMonoidWithOne,
    e.AddGroup with
    intCast := fun n => e.symm n
    intCast_ofNat := fun n => by rw [Int.cast_ofNat] <;> rfl
    intCast_negSucc := fun n =>
      congr_arg e.symm <| (Int.cast_negSucc _).trans <| congr_arg _ (e.apply_symm_apply _).symm }
#align equiv.add_group_with_one Equiv.addGroupWithOne

/-- Transfer `non_assoc_semiring` across an `equiv` -/
@[reducible]
protected def nonAssocSemiring [NonAssocSemiring β] : NonAssocSemiring α :=
  by
  let mul := e.Mul
  let add_monoid_with_one := e.AddMonoidWithOne
  skip <;> apply e.injective.non_assoc_semiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_assoc_semiring Equiv.nonAssocSemiring

/-- Transfer `semiring` across an `equiv` -/
@[reducible]
protected def semiring [Semiring β] : Semiring α :=
  by
  let mul := e.Mul
  let add_monoid_with_one := e.AddMonoidWithOne
  let npow := e.Pow ℕ
  skip <;> apply e.injective.semiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.semiring Equiv.semiring

/-- Transfer `non_unital_comm_semiring` across an `equiv` -/
@[reducible]
protected def nonUnitalCommSemiring [NonUnitalCommSemiring β] : NonUnitalCommSemiring α :=
  by
  let zero := e.Zero
  let add := e.Add
  let mul := e.Mul
  let nsmul := e.SMul ℕ
  skip <;> apply e.injective.non_unital_comm_semiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_comm_semiring Equiv.nonUnitalCommSemiring

/-- Transfer `comm_semiring` across an `equiv` -/
@[reducible]
protected def commSemiring [CommSemiring β] : CommSemiring α :=
  by
  let mul := e.Mul
  let add_monoid_with_one := e.AddMonoidWithOne
  let npow := e.Pow ℕ
  skip <;> apply e.injective.comm_semiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_semiring Equiv.commSemiring

/-- Transfer `non_unital_non_assoc_ring` across an `equiv` -/
@[reducible]
protected def nonUnitalNonAssocRing [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing α :=
  by
  let zero := e.Zero
  let add := e.Add
  let mul := e.Mul
  let neg := e.Neg
  let sub := e.Sub
  let nsmul := e.SMul ℕ
  let zsmul := e.SMul ℤ
  skip <;> apply e.injective.non_unital_non_assoc_ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_non_assoc_ring Equiv.nonUnitalNonAssocRing

/-- Transfer `non_unital_ring` across an `equiv` -/
@[reducible]
protected def nonUnitalRing [NonUnitalRing β] : NonUnitalRing α :=
  by
  let zero := e.Zero
  let add := e.Add
  let mul := e.Mul
  let neg := e.Neg
  let sub := e.Sub
  let nsmul := e.SMul ℕ
  let zsmul := e.SMul ℤ
  skip <;> apply e.injective.non_unital_ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_ring Equiv.nonUnitalRing

/-- Transfer `non_assoc_ring` across an `equiv` -/
@[reducible]
protected def nonAssocRing [NonAssocRing β] : NonAssocRing α :=
  by
  let add_group_with_one := e.AddGroupWithOne
  let mul := e.Mul
  skip <;> apply e.injective.non_assoc_ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_assoc_ring Equiv.nonAssocRing

/-- Transfer `ring` across an `equiv` -/
@[reducible]
protected def ring [Ring β] : Ring α := by
  let mul := e.Mul
  let add_group_with_one := e.AddGroupWithOne
  let npow := e.Pow ℕ
  skip <;> apply e.injective.ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.ring Equiv.ring

/-- Transfer `non_unital_comm_ring` across an `equiv` -/
@[reducible]
protected def nonUnitalCommRing [NonUnitalCommRing β] : NonUnitalCommRing α :=
  by
  let zero := e.Zero
  let add := e.Add
  let mul := e.Mul
  let neg := e.Neg
  let sub := e.Sub
  let nsmul := e.SMul ℕ
  let zsmul := e.SMul ℤ
  skip <;> apply e.injective.non_unital_comm_ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_comm_ring Equiv.nonUnitalCommRing

/-- Transfer `comm_ring` across an `equiv` -/
@[reducible]
protected def commRing [CommRing β] : CommRing α :=
  by
  let mul := e.Mul
  let add_group_with_one := e.AddGroupWithOne
  let npow := e.Pow ℕ
  skip <;> apply e.injective.comm_ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_ring Equiv.commRing

/-- Transfer `nontrivial` across an `equiv` -/
@[reducible]
protected theorem nontrivial [Nontrivial β] : Nontrivial α :=
  e.Surjective.Nontrivial
#align equiv.nontrivial Equiv.nontrivial

/-- Transfer `is_domain` across an `equiv` -/
@[reducible]
protected theorem isDomain [Ring α] [Ring β] [IsDomain β] (e : α ≃+* β) : IsDomain α :=
  Function.Injective.isDomain e.toRingHom e.Injective
#align equiv.is_domain Equiv.isDomain

/-- Transfer `has_rat_cast` across an `equiv` -/
@[reducible]
protected def hasRatCast [HasRatCast β] : HasRatCast α where ratCast n := e.symm n
#align equiv.has_rat_cast Equiv.hasRatCast

/-- Transfer `division_ring` across an `equiv` -/
@[reducible]
protected def divisionRing [DivisionRing β] : DivisionRing α :=
  by
  let add_group_with_one := e.AddGroupWithOne
  let mul := e.Mul
  let inv := e.Inv
  let div := e.Div
  let mul := e.Mul
  let npow := e.Pow ℕ
  let zpow := e.Pow ℤ
  let rat_cast := e.HasRatCast
  let qsmul := e.SMul ℚ
  skip <;> apply e.injective.division_ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.division_ring Equiv.divisionRing

/-- Transfer `field` across an `equiv` -/
@[reducible]
protected def field [Field β] : Field α :=
  by
  let add_group_with_one := e.AddGroupWithOne
  let mul := e.Mul
  let neg := e.Neg
  let inv := e.Inv
  let div := e.Div
  let mul := e.Mul
  let npow := e.Pow ℕ
  let zpow := e.Pow ℤ
  let rat_cast := e.HasRatCast
  let qsmul := e.SMul ℚ
  skip <;> apply e.injective.field _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.field Equiv.field

section R

variable (R : Type _)

include R

section

variable [Monoid R]

/-- Transfer `mul_action` across an `equiv` -/
@[reducible]
protected def mulAction (e : α ≃ β) [MulAction R β] : MulAction R α :=
  { e.SMul R with
    one_smul := by simp [smul_def]
    mul_smul := by simp [smul_def, mul_smul] }
#align equiv.mul_action Equiv.mulAction

/-- Transfer `distrib_mul_action` across an `equiv` -/
@[reducible]
protected def distribMulAction (e : α ≃ β) [AddCommMonoid β] :
    letI := Equiv.addCommMonoid e
    ∀ [DistribMulAction R β], DistribMulAction R α :=
  by
  intros
  letI := Equiv.addCommMonoid e
  exact
    ({ Equiv.mulAction R e with
        smul_zero := by simp [zero_def, smul_def]
        smul_add := by simp [add_def, smul_def, smul_add] } :
      DistribMulAction R α)
#align equiv.distrib_mul_action Equiv.distribMulAction

end

section

variable [Semiring R]

/-- Transfer `module` across an `equiv` -/
@[reducible]
protected def module (e : α ≃ β) [AddCommMonoid β] :
    letI := Equiv.addCommMonoid e
    ∀ [Module R β], Module R α :=
  by
  intros
  exact
    ({
        Equiv.distribMulAction R
          e with
        zero_smul := by simp [zero_def, smul_def]
        add_smul := by simp [add_def, smul_def, add_smul] } :
      Module R α)
#align equiv.module Equiv.module

/-- An equivalence `e : α ≃ β` gives a linear equivalence `α ≃ₗ[R] β`
where the `R`-module structure on `α` is
the one obtained by transporting an `R`-module structure on `β` back along `e`.
-/
def linearEquiv (e : α ≃ β) [AddCommMonoid β] [Module R β] :
    by
    letI := Equiv.addCommMonoid e
    letI := Equiv.module R e
    exact α ≃ₗ[R] β := by
  intros
  exact
    { Equiv.addEquiv e with
      map_smul' := fun r x => by
        apply e.symm.injective
        simp
        rfl }
#align equiv.linear_equiv Equiv.linearEquiv

end

section

variable [CommSemiring R]

/-- Transfer `algebra` across an `equiv` -/
@[reducible]
protected def algebra (e : α ≃ β) [Semiring β] :
    letI := Equiv.semiring e
    ∀ [Algebra R β], Algebra R α :=
  by
  intros
  fapply RingHom.toAlgebra'
  · exact ((RingEquiv e).symm : β →+* α).comp (algebraMap R β)
  · intro r x
    simp only [Function.comp_apply, RingHom.coe_comp]
    have p := ring_equiv_symm_apply e
    dsimp at p
    erw [p]
    clear p
    apply (RingEquiv e).Injective
    simp only [(RingEquiv e).map_mul]
    simp [Algebra.commutes]
#align equiv.algebra Equiv.algebra

/-- An equivalence `e : α ≃ β` gives an algebra equivalence `α ≃ₐ[R] β`
where the `R`-algebra structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`.
-/
def algEquiv (e : α ≃ β) [Semiring β] [Algebra R β] :
    by
    letI := Equiv.semiring e
    letI := Equiv.algebra R e
    exact α ≃ₐ[R] β := by
  intros
  exact
    { Equiv.ringEquiv e with
      commutes' := fun r => by
        apply e.symm.injective
        simp
        rfl }
#align equiv.alg_equiv Equiv.algEquiv

end

end R

end Instances

end Equiv

