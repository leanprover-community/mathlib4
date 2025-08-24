/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Nonneg.Basic

/-!
# Modules over nonnegative elements

This file defines instances and prove some properties about modules over nonnegative elements
`{c : R // 0 ≤ c}` of an arbitrary `OrderedSemiring R`.

These instances are useful for working with `ConvexCone`.

-/

assert_not_exists Finset

variable {R S E : Type*}

local notation3 "R≥0" => {c : R // 0 ≤ c}

namespace Nonneg
variable [Semiring R] [PartialOrder R]

section SMul

variable [SMul R S]

instance instSMul : SMul R≥0 S where
  smul c x := c.val • x

@[simp, norm_cast]
lemma coe_smul (a : R≥0) (x : S) : (a : R) • x = a • x :=
  rfl

@[simp]
lemma mk_smul (a) (ha) (x : S) : (⟨a, ha⟩ : R≥0) • x = a • x :=
  rfl

end SMul

section IsScalarTower

variable [IsOrderedRing R] [SMul R S] [SMul R E] [SMul S E] [IsScalarTower R S E]

instance instIsScalarTower : IsScalarTower R≥0 S E :=
  SMul.comp.isScalarTower ↑Nonneg.coeRingHom

end IsScalarTower

section SMulWithZero

variable [Zero S] [SMulWithZero R S]

instance instSMulWithZero : SMulWithZero R≥0 S where
  smul_zero _ := smul_zero _
  zero_smul _ := zero_smul _ _

end SMulWithZero

section OrderedSMul

variable [IsOrderedRing R] [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E]
  [SMulWithZero R E]

instance instIsOrderedModule [hE : IsOrderedModule R E] : IsOrderedModule R≥0 E where
  smul_le_smul_of_nonneg_left _b hb _a₁ _a₂ ha := hE.1 hb ha
  smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha := hE.2 hb ha

instance instIsStrictOrderedModule [hE : IsStrictOrderedModule R E] :
    IsStrictOrderedModule R≥0 E where
  smul_lt_smul_of_pos_left _b hb _a₁ _a₂ ha := hE.1 hb ha
  smul_lt_smul_of_pos_right _b hb _a₁ _a₂ ha := hE.2 hb ha

end OrderedSMul

section Module

variable [IsOrderedRing R] [AddCommMonoid E] [Module R E]

/-- A module over an ordered semiring is also a module over just the non-negative scalars. -/
instance instModule : Module R≥0 E := .compHom E coeRingHom

end Module
end Nonneg
