/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Algebra.Order.Module.OrderedSMul
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Modules over nonnegative elements

This file defines instances and prove some properties about modules over nonnegative elements
`{c : 𝕜 // 0 ≤ c}` of an arbitrary `OrderedSemiring 𝕜`.

These instances are useful for working with `ConvexCone`.

-/

variable {𝕜 𝕜' E : Type*}

local notation3 "𝕜≥0" => {c : 𝕜 // 0 ≤ c}

namespace Nonneg
section Semiring
variable [Semiring 𝕜] [PartialOrder 𝕜]

section SMul

variable [SMul 𝕜 𝕜']

instance instSMul : SMul 𝕜≥0 𝕜' where
  smul c x := c.val • x

@[simp, norm_cast]
lemma coe_smul (a : 𝕜≥0) (x : 𝕜') : (a : 𝕜) • x = a • x :=
  rfl

@[simp]
lemma mk_smul (a) (ha) (x : 𝕜') : (⟨a, ha⟩ : 𝕜≥0) • x = a • x :=
  rfl

end SMul

section IsScalarTower

variable [IsOrderedRing 𝕜] [SMul 𝕜 𝕜'] [SMul 𝕜 E] [SMul 𝕜' E] [IsScalarTower 𝕜 𝕜' E]

instance instIsScalarTower : IsScalarTower 𝕜≥0 𝕜' E :=
  SMul.comp.isScalarTower ↑Nonneg.coeRingHom

end IsScalarTower

section SMulWithZero

variable [Zero 𝕜'] [SMulWithZero 𝕜 𝕜']

instance instSMulWithZero : SMulWithZero 𝕜≥0 𝕜' where
  smul_zero _ := smul_zero _
  zero_smul _ := zero_smul _ _

end SMulWithZero

section OrderedSMul

variable [IsOrderedRing 𝕜] [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E]
  [SMulWithZero 𝕜 E] [hE : OrderedSMul 𝕜 E]

instance instOrderedSMul : OrderedSMul 𝕜≥0 E :=
  ⟨hE.1, hE.2⟩

end OrderedSMul

section Module

variable [IsOrderedRing 𝕜] [AddCommMonoid E] [Module 𝕜 E]

/-- A module over an ordered semiring is also a module over just the non-negative scalars. -/
instance instModule : Module 𝕜≥0 E :=
  Module.compHom E Nonneg.coeRingHom

end Module
end Semiring

section Ring
variable [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] [AddCommMonoid E] [Module 𝕜 E]

private instance instModuleFiniteAux : Module.Finite 𝕜≥0 𝕜 := by
  simp_rw [Module.finite_def, Submodule.fg_def, Submodule.eq_top_iff']
  refine ⟨{1, -1}, by simp, fun x ↦ ?_⟩
  obtain hx | hx := le_total 0 x
  · simpa using Submodule.smul_mem (M := 𝕜) (.span 𝕜≥0 {1, -1}) ⟨x, hx⟩ (x := 1)
      (Submodule.subset_span <| by simp)
  · simpa using Submodule.smul_mem (M := 𝕜) (.span 𝕜≥0 {1, -1}) ⟨-x, neg_nonneg.2 hx⟩ (x := -1)
      (Submodule.subset_span <| by simp)

/-- If a module is finite over a linearly ordered ring, then it is also finite over the non-negative
scalars. -/
instance instModuleFinite [Module.Finite 𝕜 E] : Module.Finite 𝕜≥0 E := .trans 𝕜 E

end Ring
end Nonneg
