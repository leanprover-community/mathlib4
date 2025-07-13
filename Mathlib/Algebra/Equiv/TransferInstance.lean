/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/


universe u v

variable {α : Type u} {β : Type v}

namespace Equiv

section Instances

variable (e : α ≃ β)

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

/-- Transfer `SemigroupWithZero` across an `Equiv` -/
protected abbrev semigroupWithZero [SemigroupWithZero β] : SemigroupWithZero α := by
  let mul := e.mul
  let zero := e.zero
  apply e.injective.semigroupWithZero _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `MulZeroClass` across an `Equiv` -/
protected abbrev mulZeroClass [MulZeroClass β] : MulZeroClass α := by
  let zero := e.zero
  let mul := e.mul
  apply e.injective.mulZeroClass _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `MulZeroOneClass` across an `Equiv` -/
protected abbrev mulZeroOneClass [MulZeroOneClass β] : MulZeroOneClass α := by
  let zero := e.zero
  let one := e.one
  let mul := e.mul
  apply e.injective.mulZeroOneClass _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonUnitalNonAssocSemiring` across an `Equiv` -/
protected abbrev nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] :
    NonUnitalNonAssocSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalNonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonUnitalSemiring` across an `Equiv` -/
protected abbrev nonUnitalSemiring [NonUnitalSemiring β] : NonUnitalSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalSemiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `AddMonoidWithOne` across an `Equiv` -/
protected abbrev addMonoidWithOne [AddMonoidWithOne β] : AddMonoidWithOne α :=
  { e.addMonoid, e.one with
    natCast := fun n => e.symm n
    natCast_zero := e.injective (by simp [zero_def])
    natCast_succ := fun n => e.injective (by simp [add_def, one_def]) }

/-- Transfer `AddGroupWithOne` across an `Equiv` -/
protected abbrev addGroupWithOne [AddGroupWithOne β] : AddGroupWithOne α :=
  { e.addMonoidWithOne,
    e.addGroup with
    intCast := fun n => e.symm n
    intCast_ofNat := fun n => by simp only [Int.cast_natCast]; rfl
    intCast_negSucc := fun _ =>
      congr_arg e.symm <| (Int.cast_negSucc _).trans <| congr_arg _ (e.apply_symm_apply _).symm }

/-- Transfer `NonAssocSemiring` across an `Equiv` -/
protected abbrev nonAssocSemiring [NonAssocSemiring β] : NonAssocSemiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  apply e.injective.nonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Semiring` across an `Equiv` -/
protected abbrev semiring [Semiring β] : Semiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow ℕ
  apply e.injective.semiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonUnitalCommSemiring` across an `Equiv` -/
protected abbrev nonUnitalCommSemiring [NonUnitalCommSemiring β] : NonUnitalCommSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalCommSemiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `CommSemiring` across an `Equiv` -/
protected abbrev commSemiring [CommSemiring β] : CommSemiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow ℕ
  apply e.injective.commSemiring _ <;> intros <;> exact e.apply_symm_apply _

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

/-- Transfer `NonAssocRing` across an `Equiv` -/
protected abbrev nonAssocRing [NonAssocRing β] : NonAssocRing α := by
  let add_group_with_one := e.addGroupWithOne
  let mul := e.mul
  apply e.injective.nonAssocRing _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Ring` across an `Equiv` -/
protected abbrev ring [Ring β] : Ring α := by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow ℕ
  apply e.injective.ring _ <;> intros <;> exact e.apply_symm_apply _

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

/-- Transfer `CommRing` across an `Equiv` -/
protected abbrev commRing [CommRing β] : CommRing α := by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow ℕ
  apply e.injective.commRing _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `IsDomain` across an `Equiv` -/
protected theorem isDomain [Semiring α] [Semiring β] [IsDomain β] (e : α ≃+* β) : IsDomain α :=
  Function.Injective.isDomain e.toRingHom e.injective

/-- Transfer `NNRatCast` across an `Equiv` -/
protected abbrev nnratCast [NNRatCast β] : NNRatCast α where nnratCast q := e.symm q

/-- Transfer `RatCast` across an `Equiv` -/
protected abbrev ratCast [RatCast β] : RatCast α where ratCast n := e.symm n

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

section R

variable (R : Type*)

section

variable [Monoid R]

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
    change e.symm (e (e.symm (r • e x)) * e y) = e.symm (r • e.ringEquiv (x * y))
    simp only [apply_symm_apply, Algebra.smul_mul_assoc, map_mul, ringEquiv_apply]
  · intro r x y
    change e.symm (e x * e (e.symm (r • e y))) = e.symm (r • e (e.symm (e x * e y)))
    simp only [apply_symm_apply, Algebra.mul_smul_comm]

lemma algebraMap_def (e : α ≃ β) [Semiring β] [Algebra R β] (r : R) :
    (@algebraMap R α _ (Equiv.semiring e) (Equiv.algebra R e)) r = e.symm ((algebraMap R β) r) := by
  let _ := Equiv.semiring e
  let _ := Equiv.algebra R e
  simp only [Algebra.algebraMap_eq_smul_one]
  change e.symm (r • e 1) = e.symm (r • 1)
  simp only [Equiv.one_def, apply_symm_apply]

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

end

end R

end Instances

end Equiv

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
  simp only [Equiv.smul_def, smul_assoc]
  apply e.symm.map_smul

end
