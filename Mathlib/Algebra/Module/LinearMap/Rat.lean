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

variable {M M₂ : Type*}

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

instance {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module ℚ M] [Module ℚ N] :
    MulActionHomClass (M →ₗ[R] N) ℚ M N where
  map_smulₛₗ f q m := by
    suffices q.den • f (q • m) = q.den • (q • f m) from
      smul_right_injective N (c := q.den) q.den_nz <| by norm_cast
    simp only [← map_nsmul, ← smul_assoc, nsmul_eq_mul, Rat.den_mul_eq_num]
    norm_cast
    rw [map_zsmul]
