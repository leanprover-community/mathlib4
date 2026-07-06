/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Algebra.Ring.InjSurj

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

@[expose] public section

assert_not_exists Field Module

namespace Equiv
variable {α β : Type*} (e : α ≃ β)

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
        simp [add_def]
      map_mul' := fun x y => by
        simp [mul_def] }

@[simp]
lemma ringEquiv_apply (e : α ≃ β) [Add β] [Mul β] (a : α) : ringEquiv e a = e a := rfl

lemma ringEquiv_symm_apply (e : α ≃ β) [Add β] [Mul β] (b : β) : by
    letI := Equiv.add e
    letI := Equiv.mul e
    exact (ringEquiv e).symm b = e.symm b := rfl

/-- Transfer `NonUnitalNonAssocSemiring` across an `Equiv` -/
protected abbrev nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] :
    NonUnitalNonAssocSemiring α := reduceProj% zeta% unfoldReducible% by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalNonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonUnitalSemiring` across an `Equiv` -/
protected abbrev nonUnitalSemiring [NonUnitalSemiring β] :
    NonUnitalSemiring α := reduceProj% zeta% unfoldReducible% by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalSemiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NatCast` across an `Equiv` -/
protected abbrev natCast [NatCast β] : NatCast α :=
  { natCast := fun n => e.symm n }

/-- Transfer `AddMonoidWithOne` across an `Equiv` -/
protected abbrev addMonoidWithOne [AddMonoidWithOne β] : AddMonoidWithOne α :=
  reduceProj% zeta% unfoldReducible%
  { e.addMonoid, e.one, e.natCast with
    natCast_zero := e.injective (by simp +instances [Equiv.natCast, zero_def])
    natCast_succ := fun n => e.injective (by simp +instances [Equiv.natCast, add_def, one_def]) }

/-- Transfer `IntCast` across an `Equiv` -/
protected abbrev intCast [IntCast β] : IntCast α :=
  { intCast := fun n => e.symm n }

/-- Transfer `AddGroupWithOne` across an `Equiv` -/
protected abbrev addGroupWithOne [AddGroupWithOne β] : AddGroupWithOne α :=
  reduceProj% zeta% unfoldReducible%
  { e.addMonoidWithOne,
    e.addGroup, e.intCast with
    intCast_ofNat := fun n => by simp +instances only [Equiv.intCast, Int.cast_natCast]; rfl
    intCast_negSucc := fun _ =>
      congr_arg e.symm <| (Int.cast_negSucc _).trans <| congr_arg _ (e.apply_symm_apply _).symm }

/-- Transfer `NonAssocSemiring` across an `Equiv` -/
protected abbrev nonAssocSemiring [NonAssocSemiring β] :
    NonAssocSemiring α := reduceProj% zeta% unfoldReducible% by
  let zero := e.zero
  let add := e.add
  let one := e.one
  let mul := e.mul
  let nsmul := e.smul ℕ
  let natCast := e.natCast
  apply e.injective.nonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Semiring` across an `Equiv` -/
protected abbrev semiring [Semiring β] : Semiring α := reduceProj% zeta% unfoldReducible% by
  let zero := e.zero
  let add := e.add
  let one := e.one
  let mul := e.mul
  let nsmul := e.smul ℕ
  let natCast := e.natCast
  let npow := e.pow ℕ
  apply e.injective.semiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonUnitalCommSemiring` across an `Equiv` -/
protected abbrev nonUnitalCommSemiring [NonUnitalCommSemiring β] :
    NonUnitalCommSemiring α := reduceProj% zeta% unfoldReducible% by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalCommSemiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `CommSemiring` across an `Equiv` -/
protected abbrev commSemiring [CommSemiring β] :
    CommSemiring α := reduceProj% zeta% unfoldReducible% by
  let zero := e.zero
  let add := e.add
  let one := e.one
  let mul := e.mul
  let nsmul := e.smul ℕ
  let natCast := e.natCast
  let npow := e.pow ℕ
  apply e.injective.commSemiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonUnitalNonAssocRing` across an `Equiv` -/
protected abbrev nonUnitalNonAssocRing [NonUnitalNonAssocRing β] :
    NonUnitalNonAssocRing α := reduceProj% zeta% unfoldReducible% by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalNonAssocRing _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonUnitalRing` across an `Equiv` -/
protected abbrev nonUnitalRing [NonUnitalRing β] :
    NonUnitalRing α := reduceProj% zeta% unfoldReducible% by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalRing _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonAssocRing` across an `Equiv` -/
protected abbrev nonAssocRing [NonAssocRing β] :
    NonAssocRing α := reduceProj% zeta% unfoldReducible% by
  let zero := e.zero
  let add := e.add
  let one := e.one
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  let natCast := e.natCast
  let intCast := e.intCast
  apply e.injective.nonAssocRing _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Ring` across an `Equiv` -/
protected abbrev ring [Ring β] : Ring α := reduceProj% zeta% unfoldReducible% by
  let zero := e.zero
  let add := e.add
  let one := e.one
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  let natCast := e.natCast
  let intCast := e.intCast
  let npow := e.pow ℕ
  apply e.injective.ring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonUnitalCommRing` across an `Equiv` -/
protected abbrev nonUnitalCommRing [NonUnitalCommRing β] :
    NonUnitalCommRing α := reduceProj% zeta% unfoldReducible% by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalCommRing _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `CommRing` across an `Equiv` -/
protected abbrev commRing [CommRing β] : CommRing α := reduceProj% zeta% unfoldReducible% by
  let zero := e.zero
  let add := e.add
  let one := e.one
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  let natCast := e.natCast
  let intCast := e.intCast
  let npow := e.pow ℕ
  apply e.injective.commRing _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `IsDomain` across an `Equiv` -/
protected lemma isDomain [Semiring β] [IsDomain β] (e : α ≃ β) :
    letI := e.semiring
    IsDomain α :=
  letI := e.semiring; e.injective.isDomain e.ringEquiv

end Equiv
