/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Data.Fintype.Basic

/-!
# Transfer algebraic structures across `Equiv`s

In this file we prove lemmas of the following form: if `β` has a group structure and `α ≃ β`
then `α` has a group structure, and similarly for monoids, semigroups and so on.

### Implementation details

When adding new definitions that transfer type-classes across an equivalence, please use
`abbrev`. See note [reducible non-instances].
-/

assert_not_exists MonoidWithZero

namespace Equiv
variable {M α β : Type*} (e : α ≃ β)

/-- Transfer `One` across an `Equiv` -/
@[to_additive /-- Transfer `Zero` across an `Equiv` -/]
protected abbrev one [One β] : One α where one := e.symm 1

@[to_additive]
lemma one_def [One β] :
    letI := e.one
    1 = e.symm 1 := rfl

/-- Transfer `Mul` across an `Equiv` -/
@[to_additive /-- Transfer `Add` across an `Equiv` -/]
protected abbrev mul [Mul β] : Mul α where mul x y := e.symm (e x * e y)

@[to_additive]
lemma mul_def [Mul β] (x y : α) :
    letI := Equiv.mul e
    x * y = e.symm (e x * e y) := rfl

/-- Transfer `Div` across an `Equiv` -/
@[to_additive /-- Transfer `Sub` across an `Equiv` -/]
protected abbrev div [Div β] : Div α :=
  ⟨fun x y => e.symm (e x / e y)⟩

@[to_additive]
lemma div_def [Div β] (x y : α) :
    letI := Equiv.div e
    x / y = e.symm (e x / e y) := rfl

-- Porting note: this should be called `inv`,
-- but we already have an `Equiv.inv` (which perhaps should move to `Perm.inv`?)
/-- Transfer `Inv` across an `Equiv` -/
@[to_additive /-- Transfer `Neg` across an `Equiv` -/]
protected abbrev Inv [Inv β] : Inv α where inv x := e.symm (e x)⁻¹

@[to_additive]
lemma inv_def [Inv β] (x : α) :
    letI := e.Inv
    x⁻¹ = e.symm (e x)⁻¹ := rfl

variable (M) in
/-- Transfer `SMul` across an `Equiv` -/
@[to_additive /-- Transfer `VAdd` across an `Equiv` -/]
protected abbrev smul [SMul M β] : SMul M α where smul r x := e.symm (r • e x)

@[to_additive]
lemma smul_def [SMul M β] (r : M) (x : α) :
    letI := e.smul M
    r • x = e.symm (r • e x) := rfl

variable (M) in
/-- Transfer `Pow` across an `Equiv` -/
@[to_additive existing smul]
protected abbrev pow [Pow β M] : Pow α M where pow x n := e.symm (e x ^ n)

@[to_additive existing smul_def]
lemma pow_def [Pow β M] (n : M) (x : α) :
    letI := e.pow M
    x ^ n = e.symm (e x ^ n) := rfl

/-- An equivalence `e : α ≃ β` gives a multiplicative equivalence `α ≃* β` where
the multiplicative structure on `α` is the one obtained by transporting a multiplicative structure
on `β` back along `e`. -/
@[to_additive /-- An equivalence `e : α ≃ β` gives an additive equivalence `α ≃+ β` where
the additive structure on `α` is the one obtained by transporting an additive structure
on `β` back along `e`. -/]
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
lemma mulEquiv_apply (e : α ≃ β) [Mul β] (a : α) : (mulEquiv e) a = e a := rfl

@[to_additive]
lemma mulEquiv_symm_apply (e : α ≃ β) [Mul β] (b : β) :
    letI := Equiv.mul e
    (mulEquiv e).symm b = e.symm b := rfl

/-- Transfer `Semigroup` across an `Equiv` -/
@[to_additive /-- Transfer `add_semigroup` across an `Equiv` -/]
protected abbrev semigroup [Semigroup β] : Semigroup α := by
  let mul := e.mul
  apply e.injective.semigroup _; intros; exact e.apply_symm_apply _

/-- Transfer `CommSemigroup` across an `Equiv` -/
@[to_additive /-- Transfer `AddCommSemigroup` across an `Equiv` -/]
protected abbrev commSemigroup [CommSemigroup β] : CommSemigroup α := by
  let mul := e.mul
  apply e.injective.commSemigroup _; intros; exact e.apply_symm_apply _

/-- Transfer `MulOneClass` across an `Equiv` -/
@[to_additive /-- Transfer `AddZeroClass` across an `Equiv` -/]
protected abbrev mulOneClass [MulOneClass β] : MulOneClass α := by
  let one := e.one
  let mul := e.mul
  apply e.injective.mulOneClass _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Monoid` across an `Equiv` -/
@[to_additive /-- Transfer `AddMonoid` across an `Equiv` -/]
protected abbrev monoid [Monoid β] : Monoid α := by
  let one := e.one
  let mul := e.mul
  let pow := e.pow ℕ
  apply e.injective.monoid _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `CommMonoid` across an `Equiv` -/
@[to_additive /-- Transfer `AddCommMonoid` across an `Equiv` -/]
protected abbrev commMonoid [CommMonoid β] : CommMonoid α := by
  let one := e.one
  let mul := e.mul
  let pow := e.pow ℕ
  apply e.injective.commMonoid _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Group` across an `Equiv` -/
@[to_additive /-- Transfer `AddGroup` across an `Equiv` -/]
protected abbrev group [Group β] : Group α := by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  apply e.injective.group _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `CommGroup` across an `Equiv` -/
@[to_additive /-- Transfer `AddCommGroup` across an `Equiv` -/]
protected abbrev commGroup [CommGroup β] : CommGroup α := by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  apply e.injective.commGroup _ <;> intros <;> exact e.apply_symm_apply _

variable (M) [Monoid M] in
/-- Transfer `MulAction` across an `Equiv` -/
@[to_additive /-- Transfer `AddAction` across an `Equiv` -/]
protected abbrev mulAction (e : α ≃ β) [MulAction M β] : MulAction M α where
  __ := e.smul M
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_smul]

end Equiv

namespace Finite

/-- Any finite group in universe `u` is equivalent to some finite group in universe `v`. -/
@[to_additive
/-- Any finite group in universe `u` is equivalent to some finite group in universe `v`. -/]
lemma exists_type_univ_nonempty_mulEquiv.{u, v} (G : Type u) [Group G] [Finite G] :
    ∃ (G' : Type v) (_ : Group G') (_ : Fintype G'), Nonempty (G ≃* G') := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
  let f : Fin n ≃ ULift (Fin n) := Equiv.ulift.symm
  let e : G ≃ ULift (Fin n) := e.trans f
  letI groupH : Group (ULift (Fin n)) := e.symm.group
  exact ⟨ULift (Fin n), groupH, inferInstance, ⟨MulEquiv.symm <| e.symm.mulEquiv⟩⟩

end Finite
