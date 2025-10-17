/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Module.Torsion.Free

/-!
# Vector spaces are torsion-free

In this file, we show that any module over a semifield is torsion-free.
-/

open Module

variable {𝕜 M : Type*} [Semifield 𝕜] [AddCommMonoid M] [Module 𝕜 M]

/-- Any (semi)vector space is torsion-free. -/
instance Semifield.to_moduleIsTorsionFree : IsTorsionFree 𝕜 M where
  isSMulRegular r hr m₁ m₂ hm := by simpa [hr.ne_zero] using congr(r⁻¹ • $hm)
