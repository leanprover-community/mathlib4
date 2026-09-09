/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Vector spaces are torsion-free

In this file, we show that any module over a division semiring is torsion-free.

Note that more generally any reflexive module is torsion-free.
-/

public section

open Module

variable {𝕜 M : Type*} [DivisionSemiring 𝕜] [AddCommMonoid M] [Module 𝕜 M]

/-- Any (semi)vector space is torsion-free. -/
instance (priority := 100) DivisionSemiring.to_moduleIsTorsionFree : IsTorsionFree 𝕜 M where
  isSMulRegular r hr m₁ m₂ hm := by simpa [hr.ne_zero] using congr(r⁻¹ • $hm)
