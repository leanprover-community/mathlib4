/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Reinterpret an additive homomorphism as a `ℚ`-linear map.
-/

open Function

variable {F M M₂ : Type*}

/-- Reinterpret an additive homomorphism as a `ℚ`-linear map. -/
def AddMonoidHom.toRatLinearMap [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂] [Module ℚ M₂]
    (f : M →+ M₂) : M →ₗ[ℚ] M₂ :=
  { f with map_smul' := map_rat_smul f }

theorem AddMonoidHom.toRatLinearMap_injective [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂]
    [Module ℚ M₂] : Function.Injective (@AddMonoidHom.toRatLinearMap M M₂ _ _ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]
theorem AddMonoidHom.coe_toRatLinearMap [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂]
    [Module ℚ M₂] (f : M →+ M₂) : ⇑f.toRatLinearMap = f :=
  rfl

instance [AddCommMonoid M] [AddCommMonoid M₂]
    [Module ℚ≥0 M] [Module ℚ≥0 M₂] [FunLike F M M₂] [AddMonoidHomClass F M M₂] :
    MulActionHomClass F ℚ≥0 M M₂ where
  map_smulₛₗ := map_nnrat_smul

instance [AddCommGroup M] [AddCommGroup M₂]
    [Module ℚ M] [Module ℚ M₂] [FunLike F M M₂] [AddMonoidHomClass F M M₂] :
    MulActionHomClass F ℚ M M₂ where
  map_smulₛₗ := map_rat_smul
