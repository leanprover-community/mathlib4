/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.InjSurj
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Small.Defs

/-!
# Transfer algebraic structures across `Equiv`s

In this file we prove theorems of the following form: if `β` has a
group structure and `α ≃ β` then `α` has a group structure, and
similarly for monoids, semigroups. Similar results for rings, integral
domains, fields and so on are obtained in the file
`Mathlib.Algebra.Equiv.TransferInstanceRing`.

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

end Instances

end Equiv
