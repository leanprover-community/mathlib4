/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.GroupRingAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Order.CompleteBooleanAlgebra

#align_import algebra.punit_instances from "leanprover-community/mathlib"@"6cb77a8eaff0ddd100e87b1591c6d3ad319514ff"

/-!
# Instances on PUnit

This file collects facts about algebraic structures on the one-element type, e.g. that it is a
commutative ring.
-/

set_option autoImplicit true

namespace PUnit

@[to_additive]
instance commGroup: CommGroup PUnit where
  mul _ _ := unit
  one := unit
  inv _ := unit
  div _ _ := unit
  npow _ _ := unit
  zpow _ _ := unit
  mul_assoc := by intros; rfl
                  -- ⊢ a✝ * b✝ * c✝ = a✝ * (b✝ * c✝)
                          -- 🎉 no goals
  one_mul := by intros; rfl
                -- ⊢ 1 * a✝ = a✝
                        -- 🎉 no goals
  mul_one := by intros; rfl
                -- ⊢ a✝ * 1 = a✝
                        -- 🎉 no goals
  mul_left_inv := by intros; rfl
                     -- ⊢ a✝⁻¹ * a✝ = 1
                             -- 🎉 no goals
  mul_comm := by intros; rfl
                 -- ⊢ a✝ * b✝ = b✝ * a✝
                         -- 🎉 no goals

-- shortcut instances
@[to_additive] instance : One PUnit where one := ()
@[to_additive] instance : Mul PUnit where mul _ _ := ()
@[to_additive] instance : Div PUnit where div _ _ := ()
@[to_additive] instance : Inv PUnit where inv _ := ()

@[to_additive (attr := simp)]
theorem one_eq : (1 : PUnit) = unit :=
  rfl
#align punit.one_eq PUnit.one_eq
#align punit.zero_eq PUnit.zero_eq

-- note simp can prove this when the Boolean ring structure is introduced
@[to_additive]
theorem mul_eq : x * y = unit :=
  rfl
#align punit.mul_eq PUnit.mul_eq
#align punit.add_eq PUnit.add_eq

-- `sub_eq` simplifies `PUnit.sub_eq`, but the latter is eligible for `dsimp`
@[to_additive (attr := simp, nolint simpNF)]
theorem div_eq : x / y = unit :=
  rfl
#align punit.div_eq PUnit.div_eq
#align punit.sub_eq PUnit.sub_eq

-- `neg_eq` simplifies `PUnit.neg_eq`, but the latter is eligible for `dsimp`
@[to_additive (attr := simp, nolint simpNF)]
theorem inv_eq : x⁻¹ = unit :=
  rfl
#align punit.inv_eq PUnit.inv_eq
#align punit.neg_eq PUnit.neg_eq

instance commRing: CommRing PUnit where
  __ := PUnit.commGroup
  __ := PUnit.addCommGroup
  left_distrib := by intros; rfl
                     -- ⊢ a✝ * (b✝ + c✝) = a✝ * b✝ + a✝ * c✝
                             -- 🎉 no goals
  right_distrib := by intros; rfl
                      -- ⊢ (a✝ + b✝) * c✝ = a✝ * c✝ + b✝ * c✝
                              -- 🎉 no goals
  zero_mul := by intros; rfl
                 -- ⊢ 0 * a✝ = 0
                         -- 🎉 no goals
  mul_zero := by intros; rfl
                 -- ⊢ a✝ * 0 = 0
                         -- 🎉 no goals
  natCast _ := unit

instance cancelCommMonoidWithZero: CancelCommMonoidWithZero PUnit := by
  refine' { PUnit.commRing with .. }; intros; exact Subsingleton.elim _ _
  -- ⊢ ∀ {a b c : PUnit}, a ≠ 0 → a * b = a * c → b = c
                                      -- ⊢ b✝ = c✝
                                              -- 🎉 no goals

instance normalizedGCDMonoid: NormalizedGCDMonoid PUnit where
  gcd _ _ := unit
  lcm _ _ := unit
  normUnit _ := 1
  normUnit_zero := rfl
  normUnit_mul := by intros; rfl
                     -- ⊢ (fun x => 1) (a✝² * b✝) = (fun x => 1) a✝² * (fun x => 1) b✝
                             -- 🎉 no goals
  normUnit_coe_units := by intros; rfl
                           -- ⊢ (fun x => 1) ↑u✝ = u✝⁻¹
                                   -- 🎉 no goals
  gcd_dvd_left _ _ := ⟨unit, Subsingleton.elim _ _⟩
  gcd_dvd_right _ _ := ⟨unit, Subsingleton.elim _ _⟩
  dvd_gcd {_ _} _ _ _ := ⟨unit, Subsingleton.elim _ _⟩
  gcd_mul_lcm _ _ := ⟨1, Subsingleton.elim _ _⟩
  lcm_zero_left := by intros; rfl
                      -- ⊢ (fun x x => unit) 0 a✝ = 0
                              -- 🎉 no goals
  lcm_zero_right := by intros; rfl
                       -- ⊢ (fun x x => unit) a✝ 0 = 0
                               -- 🎉 no goals
  normalize_gcd := by intros; rfl
                      -- ⊢ ↑normalize (gcd a✝ b✝) = gcd a✝ b✝
                              -- 🎉 no goals
  normalize_lcm := by intros; rfl
                      -- ⊢ ↑normalize (lcm a✝ b✝) = lcm a✝ b✝
                              -- 🎉 no goals

--porting notes: simpNF lint: simp can prove this @[simp]
theorem gcd_eq : gcd x y = unit :=
  rfl
#align punit.gcd_eq PUnit.gcd_eq

--porting notes: simpNF lint: simp can prove this @[simp]
theorem lcm_eq : lcm x y = unit :=
  rfl
#align punit.lcm_eq PUnit.lcm_eq

@[simp]
theorem norm_unit_eq {x : PUnit} : normUnit x = 1 :=
  rfl
#align punit.norm_unit_eq PUnit.norm_unit_eq

instance canonicallyOrderedAddMonoid: CanonicallyOrderedAddMonoid PUnit := by
  refine'
    { PUnit.commRing, PUnit.completeBooleanAlgebra with
      exists_add_of_le := fun {_ _} _ => ⟨unit, Subsingleton.elim _ _⟩.. } <;>
    intros <;>
    -- ⊢ c✝ + a✝¹ ≤ c✝ + b✝
    -- ⊢ a✝ ≤ a✝ + b✝
    trivial
    -- 🎉 no goals
    -- 🎉 no goals

instance linearOrderedCancelAddCommMonoid: LinearOrderedCancelAddCommMonoid PUnit where
  __ := PUnit.canonicallyOrderedAddMonoid
  __ := PUnit.linearOrder
  le_of_add_le_add_left _ _ _ _ := trivial
  add_le_add_left := by intros; rfl
                        -- ⊢ c✝ + a✝¹ ≤ c✝ + b✝
                                -- 🎉 no goals

instance : LinearOrderedAddCommMonoidWithTop PUnit :=
  { PUnit.completeBooleanAlgebra, PUnit.linearOrderedCancelAddCommMonoid with
    top_add' := fun _ => rfl }

@[to_additive]
instance smul : SMul R PUnit :=
  ⟨fun _ _ => unit⟩

@[to_additive (attr := simp)]
theorem smul_eq {R : Type*} (y : PUnit) (r : R) : r • y = unit :=
  rfl
#align punit.smul_eq PUnit.smul_eq
#align punit.vadd_eq PUnit.vadd_eq

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
  -- ⊢ ∀ (a : R), a • 0 = 0
                                     -- ⊢ a✝ • 0 = 0
                                     -- ⊢ 0 • m✝ = 0
                                                -- 🎉 no goals
                                                -- 🎉 no goals

instance mulAction [Monoid R] : MulAction R PUnit := by
  refine' { PUnit.smul with .. } <;> intros <;> exact Subsingleton.elim _ _
  -- ⊢ ∀ (b : PUnit), 1 • b = b
                                     -- ⊢ 1 • b✝ = b✝
                                     -- ⊢ (x✝ * y✝) • b✝ = x✝ • y✝ • b✝
                                                -- 🎉 no goals
                                                -- 🎉 no goals

instance distribMulAction [Monoid R] : DistribMulAction R PUnit := by
  refine' { PUnit.mulAction with .. } <;> intros <;> exact Subsingleton.elim _ _
  -- ⊢ ∀ (a : R), a • 0 = 0
                                          -- ⊢ a✝ • 0 = 0
                                          -- ⊢ a✝ • (x✝ + y✝) = a✝ • x✝ + a✝ • y✝
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals

instance mulDistribMulAction [Monoid R] : MulDistribMulAction R PUnit := by
  refine' { PUnit.mulAction with .. } <;> intros <;> exact Subsingleton.elim _ _
  -- ⊢ ∀ (r : R) (x y : PUnit), r • (x * y) = r • x * r • y
                                          -- ⊢ r✝ • (x✝ * y✝) = r✝ • x✝ * r✝ • y✝
                                          -- ⊢ r✝ • 1 = 1
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals

instance mulSemiringAction [Semiring R] : MulSemiringAction R PUnit :=
  { PUnit.distribMulAction, PUnit.mulDistribMulAction with }

instance mulActionWithZero [MonoidWithZero R] : MulActionWithZero R PUnit :=
  { PUnit.mulAction, PUnit.smulWithZero with }

instance module [Semiring R] : Module R PUnit := by
  refine' { PUnit.distribMulAction with .. } <;> intros <;> exact Subsingleton.elim _ _
  -- ⊢ ∀ (r s : R) (x : PUnit), (r + s) • x = r • x + s • x
                                                 -- ⊢ (r✝ + s✝) • x✝ = r✝ • x✝ + s✝ • x✝
                                                 -- ⊢ 0 • x✝ = 0
                                                            -- 🎉 no goals
                                                            -- 🎉 no goals

end PUnit
