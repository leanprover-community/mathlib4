/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.punit_instances
! leanprover-community/mathlib commit 6cb77a8eaff0ddd100e87b1591c6d3ad319514ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.GcdMonoid.Basic
import Mathlib.Algebra.GroupRingAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Instances on punit

This file collects facts about algebraic structures on the one-element type, e.g. that it is a
commutative ring.
-/


universe u

namespace PUnit

variable {R S : Type _} (x y : PUnit.{u + 1}) (s : Set PUnit.{u + 1})

@[to_additive]
instance commGroup: CommGroup PUnit where
  mul := fun _ _ => PUnit.unit
  one := PUnit.unit
  inv := fun _ => PUnit.unit
  div := fun _ _ => PUnit.unit
  npow := fun _ _ => PUnit.unit
  zpow := fun _ _ => PUnit.unit
  mul_assoc := by intros; rfl
  one_mul := by intros; rfl
  mul_one := by intros; rfl
  mul_left_inv := by intros; rfl
  mul_comm := by intros; rfl

@[simp, to_additive]
theorem one_eq : (1 : PUnit) = star :=
  rfl
#align punit.one_eq PUnit.one_eq

@[simp, to_additive]
theorem mul_eq : x * y = star :=
  rfl
#align punit.mul_eq PUnit.mul_eq

-- `sub_eq` simplifies `PUnit.sub_eq`, but the latter is eligible for `dsimp`
@[simp, nolint simpNF, to_additive]
theorem div_eq : x / y = star :=
  rfl
#align punit.div_eq PUnit.div_eq

-- `neg_eq` simplifies `PUnit.neg_eq`, but the latter is eligible for `dsimp`
@[simp, nolint simpNF, to_additive]
theorem inv_eq : x⁻¹ = star :=
  rfl
#align punit.inv_eq PUnit.inv_eq

instance commRing: CommRing PUnit where
  add := fun _ _ => PUnit.unit
  mul := fun _ _ => PUnit.unit
  one := PUnit.unit
  zero := PUnit.unit
  npow := fun _ _ => PUnit.unit
  mul_assoc := by intros; rfl
  one_mul := by intros; rfl
  mul_one := by intros; rfl
  mul_comm := by intros; rfl
  add_assoc := by intros; rfl
  zero_add := by intros; rfl
  add_zero := by intros; rfl
  add_comm := by intros; rfl
  left_distrib := by intros; rfl
  right_distrib := by intros; rfl
  zero_mul := by intros; rfl
  mul_zero := by intros; rfl
  neg := fun _ => PUnit.unit
  add_left_neg := by intros; rfl

instance cancelCommMonoidWithZero: CancelCommMonoidWithZero PUnit := by
  refine' { PUnit.commRing with .. } ; intros ; exact Subsingleton.elim _ _

instance normalizedGCDMonoid: NormalizedGCDMonoid PUnit where
  gcd := fun _ _ => PUnit.unit
  lcm := fun _ _ => PUnit.unit
  normUnit := fun _ => 1
  normUnit_zero := by rfl
  normUnit_mul := by intros; rfl
  normUnit_coe_units := by intros; rfl
  gcd_dvd_left := fun _ _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩
  gcd_dvd_right := fun _ _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩
  dvd_gcd := fun {_ _} _ _ _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩
  gcd_mul_lcm := fun _ _ => ⟨1, Subsingleton.elim _ _⟩
  lcm_zero_left := by intros; rfl
  lcm_zero_right := by intros; rfl
  normalize_gcd := by intros; rfl
  normalize_lcm := by intros; rfl

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

-- TODO: backport instance names
instance partialOrder : PartialOrder PUnit where
  le_antisymm := by intros; rfl

instance canonicallyOrderedAddMonoid: CanonicallyOrderedAddMonoid PUnit := by
  refine'
        { PUnit.commRing, PUnit.partialOrder with
          exists_add_of_le := fun {_ _} _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩.. } <;>
      intros <;>
    trivial

-- TODO: Backport instance names
instance linearOrder : LinearOrder PUnit where
  le_total := by intros; exact Or.inl (by rfl)
  decidable_eq := by infer_instance
  decidable_le := by infer_instance

instance linearOrderedCancelAddCommMonoid: LinearOrderedCancelAddCommMonoid PUnit := by
  refine'
        { PUnit.canonicallyOrderedAddMonoid (), PUnit.linearOrder with
    le_of_add_le_add_left := fun _ _ _ _ => trivial
    add_le_add_left := by intros; rfl }

-- TODO: Backport instance names
instance completeBooleanAlgebra : CompleteBooleanAlgebra PUnit := by
  refine'
    { PUnit.booleanAlgebra with
      supₛ := fun _ => unit
      infₛ := fun _ => unit
      .. } <;>
  intros <;>
  first|trivial

instance : LinearOrderedAddCommMonoidWithTop PUnit :=
  { PUnit.completeBooleanAlgebra, PUnit.linearOrderedCancelAddCommMonoid with
    top_add' := fun _ => rfl }

@[to_additive]
instance smul : SMul R PUnit :=
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
instance [SMul R S] : IsScalarTower R S PUnit :=
  ⟨fun _ _ _ => rfl⟩

instance smulWithZero [Zero R] : SMulWithZero R PUnit := by
  refine' { PUnit.smul with .. } <;> intros <;> exact Subsingleton.elim _ _

instance mulAction [Monoid R] : MulAction R PUnit := by
  refine' { PUnit.smul with .. } <;> intros <;> exact Subsingleton.elim _ _

instance distribMulAction [Monoid R] : DistribMulAction R PUnit := by
  refine' { PUnit.mulAction with .. } <;> intros <;> exact Subsingleton.elim _ _

instance mulDistribMulAction [Monoid R] : MulDistribMulAction R PUnit := by
  refine' { PUnit.mulAction with .. } <;> intros <;> exact Subsingleton.elim _ _

instance mulSemiringAction [Semiring R] : MulSemiringAction R PUnit :=
  { PUnit.distribMulAction, PUnit.mulDistribMulAction with }

instance mulActionWithZero [MonoidWithZero R] : MulActionWithZero R PUnit :=
  { PUnit.mulAction, PUnit.smulWithZero with }

instance module [Semiring R] : Module R PUnit := by
  refine' { PUnit.distribMulAction with .. } <;> intros <;> exact Subsingleton.elim _ _

end PUnit
