/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.punit_instances
! leanprover-community/mathlib commit 6cb77a8eaff0ddd100e87b1591c6d3ad319514ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.GcdMonoid.Basic
import Mathbin.Algebra.GroupRingAction.Basic
import Mathbin.GroupTheory.GroupAction.Defs
import Mathbin.Order.CompleteBooleanAlgebra

/-!
# Instances on punit

This file collects facts about algebraic structures on the one-element type, e.g. that it is a
commutative ring.
-/


universe u

namespace PUnit

variable {R S : Type _} (x y : PUnit.{u + 1}) (s : Set PUnit.{u + 1})

@[to_additive]
instance : CommGroup PUnit := by
  refine_struct
        { mul := fun _ _ => star
          one := star
          inv := fun _ => star
          div := fun _ _ => star
          npow := fun _ _ => star
          zpow := fun _ _ => star.. } <;>
      intros <;>
    exact Subsingleton.elim _ _

@[simp, to_additive]
theorem one_eq : (1 : PUnit) = star :=
  rfl
#align punit.one_eq PUnit.one_eq

@[simp, to_additive]
theorem mul_eq : x * y = star :=
  rfl
#align punit.mul_eq PUnit.mul_eq

-- `sub_eq` simplifies `punit.sub_eq`, but the latter is eligible for `dsimp`
@[simp, nolint simp_nf, to_additive]
theorem div_eq : x / y = star :=
  rfl
#align punit.div_eq PUnit.div_eq

-- `neg_eq` simplifies `punit.neg_eq`, but the latter is eligible for `dsimp`
@[simp, nolint simp_nf, to_additive]
theorem inv_eq : x⁻¹ = star :=
  rfl
#align punit.inv_eq PUnit.inv_eq

instance : CommRing PUnit := by
  refine' { PUnit.commGroup, PUnit.addCommGroup with natCast := fun _ => PUnit.unit.. } <;>
      intros <;>
    exact Subsingleton.elim _ _

instance : CancelCommMonoidWithZero PUnit := by
  refine' { PUnit.commRing with .. } <;> intros <;> exact Subsingleton.elim _ _

instance : NormalizedGcdMonoid PUnit := by
  refine' {
          gcd := fun _ _ => star
          lcm := fun _ _ => star
          normUnit := fun x => 1
          gcd_dvd_left := fun _ _ => ⟨star, Subsingleton.elim _ _⟩
          gcd_dvd_right := fun _ _ => ⟨star, Subsingleton.elim _ _⟩
          dvd_gcd := fun _ _ _ _ _ => ⟨star, Subsingleton.elim _ _⟩
          gcd_mul_lcm := fun _ _ => ⟨1, Subsingleton.elim _ _⟩.. } <;>
      intros <;>
    exact Subsingleton.elim _ _

@[simp]
theorem gcd_eq : gcd x y = star :=
  rfl
#align punit.gcd_eq PUnit.gcd_eq

@[simp]
theorem lcm_eq : lcm x y = star :=
  rfl
#align punit.lcm_eq PUnit.lcm_eq

@[simp]
theorem norm_unit_eq : normUnit x = 1 :=
  rfl
#align punit.norm_unit_eq PUnit.norm_unit_eq

instance : CanonicallyOrderedAddMonoid PUnit := by
  refine'
        { PUnit.commRing, PUnit.completeBooleanAlgebra with
          exists_add_of_le := fun _ _ _ => ⟨star, Subsingleton.elim _ _⟩.. } <;>
      intros <;>
    trivial

instance : LinearOrderedCancelAddCommMonoid PUnit :=
  { PUnit.canonicallyOrderedAddMonoid, PUnit.linearOrder with
    le_of_add_le_add_left := fun _ _ _ _ => trivial }

instance : LinearOrderedAddCommMonoidWithTop PUnit :=
  { PUnit.completeBooleanAlgebra, PUnit.linearOrderedCancelAddCommMonoid with
    top_add' := fun _ => rfl }

@[to_additive]
instance : HasSmul R PUnit :=
  ⟨fun _ _ => unit⟩

@[simp, to_additive]
theorem smul_eq (r : R) : r • y = star :=
  rfl
#align punit.smul_eq PUnit.smul_eq

@[to_additive]
instance : IsCentralScalar R PUnit :=
  ⟨fun _ _ => rfl⟩

@[to_additive]
instance : SMulCommClass R S PUnit :=
  ⟨fun _ _ _ => rfl⟩

@[to_additive]
instance [HasSmul R S] : IsScalarTower R S PUnit :=
  ⟨fun _ _ _ => rfl⟩

instance [Zero R] : SMulWithZero R PUnit := by
  refine' { PUnit.hasSmul with .. } <;> intros <;> exact Subsingleton.elim _ _

instance [Monoid R] : MulAction R PUnit := by
  refine' { PUnit.hasSmul with .. } <;> intros <;> exact Subsingleton.elim _ _

instance [Monoid R] : DistribMulAction R PUnit := by
  refine' { PUnit.mulAction with .. } <;> intros <;> exact Subsingleton.elim _ _

instance [Monoid R] : MulDistribMulAction R PUnit := by
  refine' { PUnit.mulAction with .. } <;> intros <;> exact Subsingleton.elim _ _

instance [Semiring R] : MulSemiringAction R PUnit :=
  { PUnit.distribMulAction, PUnit.mulDistribMulAction with }

instance [MonoidWithZero R] : MulActionWithZero R PUnit :=
  { PUnit.mulAction, PUnit.smulWithZero with }

instance [Semiring R] : Module R PUnit := by
  refine' { PUnit.distribMulAction with .. } <;> intros <;> exact Subsingleton.elim _ _

end PUnit

