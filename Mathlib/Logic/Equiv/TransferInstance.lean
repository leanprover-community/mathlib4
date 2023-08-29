/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Field.Basic
import Mathlib.Logic.Equiv.Defs

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
@[reducible, to_additive "Transfer `Zero` across an `Equiv`"]
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

/-- Transfer `Mul` across an `Equiv` -/
@[reducible, to_additive "Transfer `Add` across an `Equiv`"]
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

/-- Transfer `Div` across an `Equiv` -/
@[reducible, to_additive "Transfer `Sub` across an `Equiv`"]
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

-- Porting note: this should be called `inv`,
-- but we already have an `Equiv.inv` (which perhaps should move to `Perm.inv`?)
/-- Transfer `Inv` across an `Equiv` -/
@[reducible, to_additive "Transfer `Neg` across an `Equiv`"]
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

/-- Transfer `Pow` across an `Equiv` -/
@[reducible, to_additive existing smul]
protected def pow (N : Type*) [Pow β N] : Pow α N :=
  ⟨fun x n => e.symm (e x ^ n)⟩
#align equiv.has_pow Equiv.pow

theorem pow_def {N : Type*} [Pow β N] (n : N) (x : α) :
    letI := e.pow N
    x ^ n = e.symm (e x ^ n) :=
  rfl
#align equiv.pow_def Equiv.pow_def

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
  -- ⊢ α ≃* β
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
  by intros; rfl
     -- ⊢ ↑(MulEquiv.symm (mulEquiv e)) b = ↑e.symm b
             -- 🎉 no goals
#align equiv.mul_equiv_symm_apply Equiv.mulEquiv_symm_apply
#align equiv.add_equiv_symm_apply Equiv.addEquiv_symm_apply

/-- An equivalence `e : α ≃ β` gives a ring equivalence `α ≃+* β`
where the ring structure on `α` is
the one obtained by transporting a ring structure on `β` back along `e`.
-/
def ringEquiv (e : α ≃ β) [Add β] [Mul β] : by
    let add := Equiv.add e
    -- ⊢ Sort ?u.112825
    let mul := Equiv.mul e
    -- ⊢ Sort ?u.112825
    exact α ≃+* β := by
    -- 🎉 no goals
  intros
  -- ⊢ α ≃+* β
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
    -- ⊢ Sort ?u.184035
    letI := Equiv.mul e
    -- ⊢ Sort ?u.184035
    exact (ringEquiv e).symm b = e.symm b := by intros; rfl
    -- 🎉 no goals
                                                -- ⊢ ↑(RingEquiv.symm (ringEquiv e)) b = ↑e.symm b
                                                        -- 🎉 no goals
#align equiv.ring_equiv_symm_apply Equiv.ringEquiv_symm_apply

/-- Transfer `Semigroup` across an `Equiv` -/
@[reducible, to_additive "Transfer `add_semigroup` across an `Equiv`"]
protected def semigroup [Semigroup β] : Semigroup α := by
  let mul := e.mul
  -- ⊢ Semigroup α
  apply e.injective.semigroup _; intros; exact e.apply_symm_apply _
  -- ⊢ ∀ (x y : α), ↑e (x * y) = ↑e x * ↑e y
                                 -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                         -- 🎉 no goals
#align equiv.semigroup Equiv.semigroup
#align equiv.add_semigroup Equiv.addSemigroup

/-- Transfer `SemigroupWithZero` across an `Equiv` -/
@[reducible]
protected def semigroupWithZero [SemigroupWithZero β] : SemigroupWithZero α := by
  let mul := e.mul
  -- ⊢ SemigroupWithZero α
  let zero := e.zero
  -- ⊢ SemigroupWithZero α
  apply e.injective.semigroupWithZero _ <;> intros <;> exact e.apply_symm_apply _
  -- ⊢ ↑e 0 = 0
                                            -- ⊢ ↑e 0 = 0
                                            -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
#align equiv.semigroup_with_zero Equiv.semigroupWithZero

/-- Transfer `CommSemigroup` across an `Equiv` -/
@[reducible, to_additive "Transfer `add_comm_semigroup` across an `Equiv`"]
protected def commSemigroup [CommSemigroup β] : CommSemigroup α := by
  let mul := e.mul
  -- ⊢ CommSemigroup α
  apply e.injective.commSemigroup _; intros; exact e.apply_symm_apply _
  -- ⊢ ∀ (x y : α), ↑e (x * y) = ↑e x * ↑e y
                                     -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                             -- 🎉 no goals
#align equiv.comm_semigroup Equiv.commSemigroup
#align equiv.add_comm_semigroup Equiv.addCommSemigroup

/-- Transfer `MulZeroClass` across an `Equiv` -/
@[reducible]
protected def mulZeroClass [MulZeroClass β] : MulZeroClass α := by
  let zero := e.zero
  -- ⊢ MulZeroClass α
  let mul := e.mul
  -- ⊢ MulZeroClass α
  apply e.injective.mulZeroClass _ <;> intros <;> exact e.apply_symm_apply _
  -- ⊢ ↑e 0 = 0
                                       -- ⊢ ↑e 0 = 0
                                       -- ⊢ ↑e (a✝ * b✝) = ↑e a✝ * ↑e b✝
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align equiv.mul_zero_class Equiv.mulZeroClass

/-- Transfer `MulOneClass` across an `Equiv` -/
@[reducible, to_additive "Transfer `AddZeroClass` across an `Equiv`"]
protected def mulOneClass [MulOneClass β] : MulOneClass α := by
  let one := e.one
  -- ⊢ MulOneClass α
  let mul := e.mul
  -- ⊢ MulOneClass α
  apply e.injective.mulOneClass _ <;> intros <;> exact e.apply_symm_apply _
  -- ⊢ ↑e 1 = 1
                                      -- ⊢ ↑e 1 = 1
                                      -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
#align equiv.mul_one_class Equiv.mulOneClass
#align equiv.add_zero_class Equiv.addZeroClass

/-- Transfer `MulZeroOneClass` across an `Equiv` -/
@[reducible]
protected def mulZeroOneClass [MulZeroOneClass β] : MulZeroOneClass α := by
  let zero := e.zero
  -- ⊢ MulZeroOneClass α
  let one := e.one
  -- ⊢ MulZeroOneClass α
  let mul := e.mul
  -- ⊢ MulZeroOneClass α
  apply e.injective.mulZeroOneClass _ <;> intros <;> exact e.apply_symm_apply _
                                          -- ⊢ ↑e 0 = 0
                                          -- ⊢ ↑e 1 = 1
                                          -- ⊢ ↑e (a✝ * b✝) = ↑e a✝ * ↑e b✝
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
#align equiv.mul_zero_one_class Equiv.mulZeroOneClass

/-- Transfer `Monoid` across an `Equiv` -/
@[reducible, to_additive "Transfer `AddMonoid` across an `Equiv`"]
protected def monoid [Monoid β] : Monoid α := by
  let one := e.one
  -- ⊢ Monoid α
  let mul := e.mul
  -- ⊢ Monoid α
  let pow := e.pow ℕ
  -- ⊢ Monoid α
  apply e.injective.monoid _ <;> intros <;> exact e.apply_symm_apply _
                                 -- ⊢ ↑e 1 = 1
                                 -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                 -- ⊢ ↑e (x✝ ^ n✝) = ↑e x✝ ^ n✝
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
#align equiv.monoid Equiv.monoid
#align equiv.add_monoid Equiv.addMonoid

/-- Transfer `CommMonoid` across an `Equiv` -/
@[reducible, to_additive "Transfer `AddCommMonoid` across an `Equiv`"]
protected def commMonoid [CommMonoid β] : CommMonoid α := by
  let one := e.one
  -- ⊢ CommMonoid α
  let mul := e.mul
  -- ⊢ CommMonoid α
  let pow := e.pow ℕ
  -- ⊢ CommMonoid α
  apply e.injective.commMonoid _ <;> intros <;> exact e.apply_symm_apply _
                                     -- ⊢ ↑e 1 = 1
                                     -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                     -- ⊢ ↑e (x✝ ^ n✝) = ↑e x✝ ^ n✝
                                                -- 🎉 no goals
                                                -- 🎉 no goals
                                                -- 🎉 no goals
#align equiv.comm_monoid Equiv.commMonoid
#align equiv.add_comm_monoid Equiv.addCommMonoid

/-- Transfer `Group` across an `Equiv` -/
@[reducible, to_additive "Transfer `AddGroup` across an `Equiv`"]
protected def group [Group β] : Group α := by
  let one := e.one
  -- ⊢ Group α
  let mul := e.mul
  -- ⊢ Group α
  let inv := e.Inv
  -- ⊢ Group α
  let div := e.div
  -- ⊢ Group α
  let npow := e.pow ℕ
  -- ⊢ Group α
  let zpow := e.pow ℤ
  -- ⊢ Group α
  apply e.injective.group _ <;> intros <;> exact e.apply_symm_apply _
                                -- ⊢ ↑e 1 = 1
                                -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                -- ⊢ ↑e x✝⁻¹ = (↑e x✝)⁻¹
                                -- ⊢ ↑e (x✝ / y✝) = ↑e x✝ / ↑e y✝
                                -- ⊢ ↑e (x✝ ^ n✝) = ↑e x✝ ^ n✝
                                -- ⊢ ↑e (x✝ ^ n✝) = ↑e x✝ ^ n✝
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
#align equiv.group Equiv.group
#align equiv.add_group Equiv.addGroup

/-- Transfer `CommGroup` across an `Equiv` -/
@[reducible, to_additive "Transfer `AddCommGroup` across an `Equiv`"]
protected def commGroup [CommGroup β] : CommGroup α := by
  let one := e.one
  -- ⊢ CommGroup α
  let mul := e.mul
  -- ⊢ CommGroup α
  let inv := e.Inv
  -- ⊢ CommGroup α
  let div := e.div
  -- ⊢ CommGroup α
  let npow := e.pow ℕ
  -- ⊢ CommGroup α
  let zpow := e.pow ℤ
  -- ⊢ CommGroup α
  apply e.injective.commGroup _ <;> intros <;> exact e.apply_symm_apply _
                                    -- ⊢ ↑e 1 = 1
                                    -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                    -- ⊢ ↑e x✝⁻¹ = (↑e x✝)⁻¹
                                    -- ⊢ ↑e (x✝ / y✝) = ↑e x✝ / ↑e y✝
                                    -- ⊢ ↑e (x✝ ^ n✝) = ↑e x✝ ^ n✝
                                    -- ⊢ ↑e (x✝ ^ n✝) = ↑e x✝ ^ n✝
                                               -- 🎉 no goals
                                               -- 🎉 no goals
                                               -- 🎉 no goals
                                               -- 🎉 no goals
                                               -- 🎉 no goals
                                               -- 🎉 no goals
#align equiv.comm_group Equiv.commGroup
#align equiv.add_comm_group Equiv.addCommGroup

/-- Transfer `NonUnitalNonAssocSemiring` across an `Equiv` -/
@[reducible]
protected def nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] :
    NonUnitalNonAssocSemiring α := by
  let zero := e.zero
  -- ⊢ NonUnitalNonAssocSemiring α
  let add := e.add
  -- ⊢ NonUnitalNonAssocSemiring α
  let mul := e.mul
  -- ⊢ NonUnitalNonAssocSemiring α
  let nsmul := e.smul ℕ
  -- ⊢ NonUnitalNonAssocSemiring α
  apply e.injective.nonUnitalNonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _
                                                    -- ⊢ ↑e 0 = 0
                                                    -- ⊢ ↑e (x✝ + y✝) = ↑e x✝ + ↑e y✝
                                                    -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                                    -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                                               -- 🎉 no goals
                                                               -- 🎉 no goals
                                                               -- 🎉 no goals
                                                               -- 🎉 no goals
#align equiv.non_unital_non_assoc_semiring Equiv.nonUnitalNonAssocSemiring

/-- Transfer `NonUnitalSemiring` across an `Equiv` -/
@[reducible]
protected def nonUnitalSemiring [NonUnitalSemiring β] : NonUnitalSemiring α := by
  let zero := e.zero
  -- ⊢ NonUnitalSemiring α
  let add := e.add
  -- ⊢ NonUnitalSemiring α
  let mul := e.mul
  -- ⊢ NonUnitalSemiring α
  let nsmul := e.smul ℕ
  -- ⊢ NonUnitalSemiring α
  apply e.injective.nonUnitalSemiring _ <;> intros <;> exact e.apply_symm_apply _
                                            -- ⊢ ↑e 0 = 0
                                            -- ⊢ ↑e (x✝ + y✝) = ↑e x✝ + ↑e y✝
                                            -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                            -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
#align equiv.non_unital_semiring Equiv.nonUnitalSemiring

/-- Transfer `AddMonoidWithOne` across an `Equiv` -/
@[reducible]
protected def addMonoidWithOne [AddMonoidWithOne β] : AddMonoidWithOne α :=
  { e.addMonoid, e.one with
    natCast := fun n => e.symm n
    natCast_zero := e.injective (by simp [zero_def])
                                    -- 🎉 no goals
    natCast_succ := fun n => e.injective (by simp [add_def, one_def]) }
                                             -- 🎉 no goals
#align equiv.add_monoid_with_one Equiv.addMonoidWithOne

/-- Transfer `AddGroupWithOne` across an `Equiv` -/
@[reducible]
protected def addGroupWithOne [AddGroupWithOne β] : AddGroupWithOne α :=
  { e.addMonoidWithOne,
    e.addGroup with
    intCast := fun n => e.symm n
    intCast_ofNat := fun n => by simp only [Int.cast_ofNat]; rfl
                                 -- ⊢ ↑e.symm ↑n = ↑n
                                                             -- 🎉 no goals
    intCast_negSucc := fun n =>
      congr_arg e.symm <| (Int.cast_negSucc _).trans <| congr_arg _ (e.apply_symm_apply _).symm }
#align equiv.add_group_with_one Equiv.addGroupWithOne

/-- Transfer `NonAssocSemiring` across an `Equiv` -/
@[reducible]
protected def nonAssocSemiring [NonAssocSemiring β] : NonAssocSemiring α := by
  let mul := e.mul
  -- ⊢ NonAssocSemiring α
  let add_monoid_with_one := e.addMonoidWithOne
  -- ⊢ NonAssocSemiring α
  apply e.injective.nonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _
                                           -- ⊢ ↑e 0 = 0
                                           -- ⊢ ↑e 1 = 1
                                           -- ⊢ ↑e (x✝ + y✝) = ↑e x✝ + ↑e y✝
                                           -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                           -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                           -- ⊢ ↑e ↑n✝ = ↑n✝
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
#align equiv.non_assoc_semiring Equiv.nonAssocSemiring

/-- Transfer `Semiring` across an `Equiv` -/
@[reducible]
protected def semiring [Semiring β] : Semiring α := by
  let mul := e.mul
  -- ⊢ Semiring α
  let add_monoid_with_one := e.addMonoidWithOne
  -- ⊢ Semiring α
  let npow := e.pow ℕ
  -- ⊢ Semiring α
  apply e.injective.semiring _ <;> intros <;> exact e.apply_symm_apply _
                                   -- ⊢ ↑e 0 = 0
                                   -- ⊢ ↑e 1 = 1
                                   -- ⊢ ↑e (x✝ + y✝) = ↑e x✝ + ↑e y✝
                                   -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                   -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                   -- ⊢ ↑e (x✝ ^ n✝) = ↑e x✝ ^ n✝
                                   -- ⊢ ↑e ↑n✝ = ↑n✝
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
#align equiv.semiring Equiv.semiring

/-- Transfer `NonUnitalCommSemiring` across an `Equiv` -/
@[reducible]
protected def nonUnitalCommSemiring [NonUnitalCommSemiring β] : NonUnitalCommSemiring α := by
  let zero := e.zero
  -- ⊢ NonUnitalCommSemiring α
  let add := e.add
  -- ⊢ NonUnitalCommSemiring α
  let mul := e.mul
  -- ⊢ NonUnitalCommSemiring α
  let nsmul := e.smul ℕ
  -- ⊢ NonUnitalCommSemiring α
  apply e.injective.nonUnitalCommSemiring _ <;> intros <;> exact e.apply_symm_apply _
                                                -- ⊢ ↑e 0 = 0
                                                -- ⊢ ↑e (x✝ + y✝) = ↑e x✝ + ↑e y✝
                                                -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                                -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                                           -- 🎉 no goals
                                                           -- 🎉 no goals
                                                           -- 🎉 no goals
                                                           -- 🎉 no goals
#align equiv.non_unital_comm_semiring Equiv.nonUnitalCommSemiring

/-- Transfer `CommSemiring` across an `Equiv` -/
@[reducible]
protected def commSemiring [CommSemiring β] : CommSemiring α := by
  let mul := e.mul
  -- ⊢ CommSemiring α
  let add_monoid_with_one := e.addMonoidWithOne
  -- ⊢ CommSemiring α
  let npow := e.pow ℕ
  -- ⊢ CommSemiring α
  apply e.injective.commSemiring _ <;> intros <;> exact e.apply_symm_apply _
                                       -- ⊢ ↑e 0 = 0
                                       -- ⊢ ↑e 1 = 1
                                       -- ⊢ ↑e (x✝ + y✝) = ↑e x✝ + ↑e y✝
                                       -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                       -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                       -- ⊢ ↑e (x✝ ^ n✝) = ↑e x✝ ^ n✝
                                       -- ⊢ ↑e ↑n✝ = ↑n✝
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align equiv.comm_semiring Equiv.commSemiring

/-- Transfer `NonUnitalNonAssocRing` across an `Equiv` -/
@[reducible]
protected def nonUnitalNonAssocRing [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing α := by
  let zero := e.zero
  -- ⊢ NonUnitalNonAssocRing α
  let add := e.add
  -- ⊢ NonUnitalNonAssocRing α
  let mul := e.mul
  -- ⊢ NonUnitalNonAssocRing α
  let neg := e.Neg
  -- ⊢ NonUnitalNonAssocRing α
  let sub := e.sub
  -- ⊢ NonUnitalNonAssocRing α
  let nsmul := e.smul ℕ
  -- ⊢ NonUnitalNonAssocRing α
  let zsmul := e.smul ℤ
  -- ⊢ NonUnitalNonAssocRing α
  apply e.injective.nonUnitalNonAssocRing _ <;> intros <;> exact e.apply_symm_apply _
                                                -- ⊢ ↑e 0 = 0
                                                -- ⊢ ↑e (x✝ + y✝) = ↑e x✝ + ↑e y✝
                                                -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                                -- ⊢ ↑e (-x✝) = -↑e x✝
                                                -- ⊢ ↑e (x✝ - y✝) = ↑e x✝ - ↑e y✝
                                                -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                                -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                                           -- 🎉 no goals
                                                           -- 🎉 no goals
                                                           -- 🎉 no goals
                                                           -- 🎉 no goals
                                                           -- 🎉 no goals
                                                           -- 🎉 no goals
                                                           -- 🎉 no goals
#align equiv.non_unital_non_assoc_ring Equiv.nonUnitalNonAssocRing

/-- Transfer `NonUnitalRing` across an `Equiv` -/
@[reducible]
protected def nonUnitalRing [NonUnitalRing β] : NonUnitalRing α := by
  let zero := e.zero
  -- ⊢ NonUnitalRing α
  let add := e.add
  -- ⊢ NonUnitalRing α
  let mul := e.mul
  -- ⊢ NonUnitalRing α
  let neg := e.Neg
  -- ⊢ NonUnitalRing α
  let sub := e.sub
  -- ⊢ NonUnitalRing α
  let nsmul := e.smul ℕ
  -- ⊢ NonUnitalRing α
  let zsmul := e.smul ℤ
  -- ⊢ NonUnitalRing α
  apply e.injective.nonUnitalRing _ <;> intros <;> exact e.apply_symm_apply _
                                        -- ⊢ ↑e 0 = 0
                                        -- ⊢ ↑e (x✝ + y✝) = ↑e x✝ + ↑e y✝
                                        -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                        -- ⊢ ↑e (-x✝) = -↑e x✝
                                        -- ⊢ ↑e (x✝ - y✝) = ↑e x✝ - ↑e y✝
                                        -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                        -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
#align equiv.non_unital_ring Equiv.nonUnitalRing

/-- Transfer `NonAssocRing` across an `Equiv` -/
@[reducible]
protected def nonAssocRing [NonAssocRing β] : NonAssocRing α := by
  let add_group_with_one := e.addGroupWithOne
  -- ⊢ NonAssocRing α
  let mul := e.mul
  -- ⊢ NonAssocRing α
  apply e.injective.nonAssocRing _ <;> intros <;> exact e.apply_symm_apply _
                                       -- ⊢ ↑e 0 = 0
                                       -- ⊢ ↑e 1 = 1
                                       -- ⊢ ↑e (x✝ + y✝) = ↑e x✝ + ↑e y✝
                                       -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                       -- ⊢ ↑e (-x✝) = -↑e x✝
                                       -- ⊢ ↑e (x✝ - y✝) = ↑e x✝ - ↑e y✝
                                       -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                       -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                       -- ⊢ ↑e ↑n✝ = ↑n✝
                                       -- ⊢ ↑e ↑n✝ = ↑n✝
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align equiv.non_assoc_ring Equiv.nonAssocRing

/-- Transfer `Ring` across an `Equiv` -/
@[reducible]
protected def ring [Ring β] : Ring α := by
  let mul := e.mul
  -- ⊢ Ring α
  let add_group_with_one := e.addGroupWithOne
  -- ⊢ Ring α
  let npow := e.pow ℕ
  -- ⊢ Ring α
  apply e.injective.ring _ <;> intros <;> exact e.apply_symm_apply _
                               -- ⊢ ↑e 0 = 0
                               -- ⊢ ↑e 1 = 1
                               -- ⊢ ↑e (x✝ + y✝) = ↑e x✝ + ↑e y✝
                               -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                               -- ⊢ ↑e (-x✝) = -↑e x✝
                               -- ⊢ ↑e (x✝ - y✝) = ↑e x✝ - ↑e y✝
                               -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                               -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                               -- ⊢ ↑e (x✝ ^ n✝) = ↑e x✝ ^ n✝
                               -- ⊢ ↑e ↑n✝ = ↑n✝
                               -- ⊢ ↑e ↑n✝ = ↑n✝
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- 🎉 no goals
#align equiv.ring Equiv.ring

/-- Transfer `NonUnitalCommRing` across an `Equiv` -/
@[reducible]
protected def nonUnitalCommRing [NonUnitalCommRing β] : NonUnitalCommRing α := by
  let zero := e.zero
  -- ⊢ NonUnitalCommRing α
  let add := e.add
  -- ⊢ NonUnitalCommRing α
  let mul := e.mul
  -- ⊢ NonUnitalCommRing α
  let neg := e.Neg
  -- ⊢ NonUnitalCommRing α
  let sub := e.sub
  -- ⊢ NonUnitalCommRing α
  let nsmul := e.smul ℕ
  -- ⊢ NonUnitalCommRing α
  let zsmul := e.smul ℤ
  -- ⊢ NonUnitalCommRing α
  apply e.injective.nonUnitalCommRing _ <;> intros <;> exact e.apply_symm_apply _
                                            -- ⊢ ↑e 0 = 0
                                            -- ⊢ ↑e (x✝ + y✝) = ↑e x✝ + ↑e y✝
                                            -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                            -- ⊢ ↑e (-x✝) = -↑e x✝
                                            -- ⊢ ↑e (x✝ - y✝) = ↑e x✝ - ↑e y✝
                                            -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                            -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
#align equiv.non_unital_comm_ring Equiv.nonUnitalCommRing

/-- Transfer `CommRing` across an `Equiv` -/
@[reducible]
protected def commRing [CommRing β] : CommRing α := by
  let mul := e.mul
  -- ⊢ CommRing α
  let add_group_with_one := e.addGroupWithOne
  -- ⊢ CommRing α
  let npow := e.pow ℕ
  -- ⊢ CommRing α
  apply e.injective.commRing _ <;> intros <;> exact e.apply_symm_apply _
                                   -- ⊢ ↑e 0 = 0
                                   -- ⊢ ↑e 1 = 1
                                   -- ⊢ ↑e (x✝ + y✝) = ↑e x✝ + ↑e y✝
                                   -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                   -- ⊢ ↑e (-x✝) = -↑e x✝
                                   -- ⊢ ↑e (x✝ - y✝) = ↑e x✝ - ↑e y✝
                                   -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                   -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                   -- ⊢ ↑e (x✝ ^ n✝) = ↑e x✝ ^ n✝
                                   -- ⊢ ↑e ↑n✝ = ↑n✝
                                   -- ⊢ ↑e ↑n✝ = ↑n✝
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                              -- 🎉 no goals
#align equiv.comm_ring Equiv.commRing

/-- Transfer `Nontrivial` across an `Equiv` -/
@[reducible]
protected theorem nontrivial [Nontrivial β] : Nontrivial α :=
  e.surjective.nontrivial
#align equiv.nontrivial Equiv.nontrivial

/-- Transfer `IsDomain` across an `Equiv` -/
@[reducible]
protected theorem isDomain [Ring α] [Ring β] [IsDomain β] (e : α ≃+* β) : IsDomain α :=
  Function.Injective.isDomain e.toRingHom e.injective
#align equiv.is_domain Equiv.isDomain

/-- Transfer `RatCast` across an `Equiv` -/
@[reducible]
protected def RatCast [RatCast β] : RatCast α where ratCast n := e.symm n
#align equiv.has_rat_cast Equiv.RatCast

/-- Transfer `DivisionRing` across an `Equiv` -/
@[reducible]
protected def divisionRing [DivisionRing β] : DivisionRing α := by
  let add_group_with_one := e.addGroupWithOne
  -- ⊢ DivisionRing α
  let inv := e.Inv
  -- ⊢ DivisionRing α
  let div := e.div
  -- ⊢ DivisionRing α
  let mul := e.mul
  -- ⊢ DivisionRing α
  let npow := e.pow ℕ
  -- ⊢ DivisionRing α
  let zpow := e.pow ℤ
  -- ⊢ DivisionRing α
  let rat_cast := e.RatCast
  -- ⊢ DivisionRing α
  let qsmul := e.smul ℚ
  -- ⊢ DivisionRing α
  apply e.injective.divisionRing _ <;> intros <;> exact e.apply_symm_apply _
                                       -- ⊢ ↑e 0 = 0
                                       -- ⊢ ↑e 1 = 1
                                       -- ⊢ ↑e (x✝ + y✝) = ↑e x✝ + ↑e y✝
                                       -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                       -- ⊢ ↑e (-x✝) = -↑e x✝
                                       -- ⊢ ↑e (x✝ - y✝) = ↑e x✝ - ↑e y✝
                                       -- ⊢ ↑e x✝⁻¹ = (↑e x✝)⁻¹
                                       -- ⊢ ↑e (x✝ / y✝) = ↑e x✝ / ↑e y✝
                                       -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                       -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                       -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                       -- ⊢ ↑e (x✝ ^ n✝) = ↑e x✝ ^ n✝
                                       -- ⊢ ↑e (x✝ ^ n✝) = ↑e x✝ ^ n✝
                                       -- ⊢ ↑e ↑n✝ = ↑n✝
                                       -- ⊢ ↑e ↑n✝ = ↑n✝
                                       -- ⊢ ↑e ↑n✝ = ↑n✝
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align equiv.division_ring Equiv.divisionRing

/-- Transfer `Field` across an `Equiv` -/
@[reducible]
protected def field [Field β] : Field α := by
  let add_group_with_one := e.addGroupWithOne
  -- ⊢ Field α
  let neg := e.Neg
  -- ⊢ Field α
  let inv := e.Inv
  -- ⊢ Field α
  let div := e.div
  -- ⊢ Field α
  let mul := e.mul
  -- ⊢ Field α
  let npow := e.pow ℕ
  -- ⊢ Field α
  let zpow := e.pow ℤ
  -- ⊢ Field α
  let rat_cast := e.RatCast
  -- ⊢ Field α
  let qsmul := e.smul ℚ
  -- ⊢ Field α
  apply e.injective.field _ <;> intros <;> exact e.apply_symm_apply _
                                -- ⊢ ↑e 0 = 0
                                -- ⊢ ↑e 1 = 1
                                -- ⊢ ↑e (x✝ + y✝) = ↑e x✝ + ↑e y✝
                                -- ⊢ ↑e (x✝ * y✝) = ↑e x✝ * ↑e y✝
                                -- ⊢ ↑e (-x✝) = -↑e x✝
                                -- ⊢ ↑e (x✝ - y✝) = ↑e x✝ - ↑e y✝
                                -- ⊢ ↑e x✝⁻¹ = (↑e x✝)⁻¹
                                -- ⊢ ↑e (x✝ / y✝) = ↑e x✝ / ↑e y✝
                                -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                -- ⊢ ↑e (n✝ • x✝) = n✝ • ↑e x✝
                                -- ⊢ ↑e (x✝ ^ n✝) = ↑e x✝ ^ n✝
                                -- ⊢ ↑e (x✝ ^ n✝) = ↑e x✝ ^ n✝
                                -- ⊢ ↑e ↑n✝ = ↑n✝
                                -- ⊢ ↑e ↑n✝ = ↑n✝
                                -- ⊢ ↑e ↑n✝ = ↑n✝
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
#align equiv.field Equiv.field

section R

variable (R : Type*)

section

variable [Monoid R]

/-- Transfer `MulAction` across an `Equiv` -/
@[reducible]
protected def mulAction (e : α ≃ β) [MulAction R β] : MulAction R α :=
  { e.smul R with
    one_smul := by simp [smul_def]
                   -- 🎉 no goals
    mul_smul := by simp [smul_def, mul_smul] }
                   -- 🎉 no goals
#align equiv.mul_action Equiv.mulAction

/-- Transfer `DistribMulAction` across an `Equiv` -/
@[reducible]
protected def distribMulAction (e : α ≃ β) [AddCommMonoid β] :
    letI := Equiv.addCommMonoid e
    ∀ [DistribMulAction R β], DistribMulAction R α := by
  intros
  -- ⊢ DistribMulAction R α
  letI := Equiv.addCommMonoid e
  -- ⊢ DistribMulAction R α
  exact
    ({ Equiv.mulAction R e with
        smul_zero := by simp [zero_def, smul_def]
        smul_add := by simp [add_def, smul_def, smul_add] } :
      DistribMulAction R α)
#align equiv.distrib_mul_action Equiv.distribMulAction

end

section

variable [Semiring R]

/-- Transfer `Module` across an `Equiv` -/
@[reducible]
protected def module (e : α ≃ β) [AddCommMonoid β] :
    let addCommMonoid := Equiv.addCommMonoid e
    ∀ [Module R β], Module R α := by
  intros
  -- ⊢ Module R α
  exact
    ({ Equiv.distribMulAction R e with
        zero_smul := by simp [smul_def, zero_smul, zero_def]
        add_smul := by simp [add_def, smul_def, add_smul] } :
      Module R α)
#align equiv.module Equiv.module

/-- An equivalence `e : α ≃ β` gives a linear equivalence `α ≃ₗ[R] β`
where the `R`-module structure on `α` is
the one obtained by transporting an `R`-module structure on `β` back along `e`.
-/
def linearEquiv (e : α ≃ β) [AddCommMonoid β] [Module R β] : by
    let addCommMonoid := Equiv.addCommMonoid e
    -- ⊢ Sort ?u.508797
    let module := Equiv.module R e
    -- ⊢ Sort ?u.508797
    exact α ≃ₗ[R] β := by
    -- 🎉 no goals
  intros
  -- ⊢ α ≃ₗ[R] β
  exact
    { Equiv.addEquiv e with
      map_smul' := fun r x => by
        apply e.symm.injective
        simp
        exact Iff.mpr (apply_eq_iff_eq_symm_apply _) rfl }
#align equiv.linear_equiv Equiv.linearEquiv

end

section

variable [CommSemiring R]

/-- Transfer `Algebra` across an `Equiv` -/
@[reducible]
protected def algebra (e : α ≃ β) [Semiring β] :
    let semiring := Equiv.semiring e
    ∀ [Algebra R β], Algebra R α := by
  intros
  -- ⊢ Algebra R α
  fapply RingHom.toAlgebra'
  -- ⊢ R →+* α
  · exact ((ringEquiv e).symm : β →+* α).comp (algebraMap R β)
    -- 🎉 no goals
  · intro r x
    -- ⊢ ↑(RingHom.comp (↑(RingEquiv.symm (ringEquiv e))) (algebraMap R β)) r * x = x …
    simp only [Function.comp_apply, RingHom.coe_comp]
    -- ⊢ ↑↑(RingEquiv.symm (ringEquiv e)) (↑(algebraMap R β) r) * x = x * ↑↑(RingEqui …
    have p := ringEquiv_symm_apply e
    -- ⊢ ↑↑(RingEquiv.symm (ringEquiv e)) (↑(algebraMap R β) r) * x = x * ↑↑(RingEqui …
    dsimp at p
    -- ⊢ ↑↑(RingEquiv.symm (ringEquiv e)) (↑(algebraMap R β) r) * x = x * ↑↑(RingEqui …
    erw [p]
    -- ⊢ ↑e.symm (↑(algebraMap R β) r) * x = x * ↑e.symm (↑(algebraMap R β) r)
    clear p
    -- ⊢ ↑e.symm (↑(algebraMap R β) r) * x = x * ↑e.symm (↑(algebraMap R β) r)
    apply (ringEquiv e).injective
    -- ⊢ ↑(ringEquiv e) (↑e.symm (↑(algebraMap R β) r) * x) = ↑(ringEquiv e) (x * ↑e. …
    simp only [(ringEquiv e).map_mul]
    -- ⊢ ↑(ringEquiv e) (↑e.symm (↑(algebraMap R β) r)) * ↑(ringEquiv e) x = ↑(ringEq …
    simp [Algebra.commutes]
    -- 🎉 no goals
#align equiv.algebra Equiv.algebra

/-- An equivalence `e : α ≃ β` gives an algebra equivalence `α ≃ₐ[R] β`
where the `R`-algebra structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`.
-/
def algEquiv (e : α ≃ β) [Semiring β] [Algebra R β] : by
    let semiring := Equiv.semiring e
    -- ⊢ Sort ?u.532380
    let algebra := Equiv.algebra R e
    -- ⊢ Sort ?u.532380
    exact α ≃ₐ[R] β := by
    -- 🎉 no goals
  intros
  -- ⊢ α ≃ₐ[R] β
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
