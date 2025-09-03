/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Order.Module.OrderedSMul
import Mathlib.Algebra.Order.Nonneg.Basic

/-!
# Modules over nonnegative elements

For an ordered ring `R`, this file proves that any (ordered) `R`-module `M` is also an (ordered)
`R≥0`-module`.

Among other things, these instances are useful for working with `ConvexCone`.
-/

assert_not_exists Finset

variable {R S M : Type*}

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

variable [IsOrderedRing R] [SMul R S] [SMul R M] [SMul S M] [IsScalarTower R S M]

instance instIsScalarTower : IsScalarTower R≥0 S M :=
  SMul.comp.isScalarTower ↑Nonneg.coeRingHom

end IsScalarTower

section SMulWithZero

variable [Zero S] [SMulWithZero R S]

instance instSMulWithZero : SMulWithZero R≥0 S where
  smul_zero _ := smul_zero _
  zero_smul _ := zero_smul _ _

end SMulWithZero

section OrderedSMul

variable [IsOrderedRing R] [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [SMulWithZero R M] [hE : OrderedSMul R M]

instance instOrderedSMul : OrderedSMul R≥0 M :=
  ⟨hE.1, hE.2⟩

end OrderedSMul

section Module

variable [IsOrderedRing R] [AddCommMonoid M] [Module R M]

/-- A module over an ordered semiring is also a module over just the non-negative scalars. -/
instance instModule : Module R≥0 M := .compHom M coeRingHom

end Module
end Nonneg
