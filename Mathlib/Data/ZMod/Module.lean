/-
Copyright (c) 2023 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.LinearMap

/-!
# The `ZMod n`-module structure on Abelian groups whose elements have order dividing `n`
-/

variable {n : ℕ} {M M₁ : Type*} [AddCommGroup M] [AddCommGroup M₁]
  [Module (ZMod n) M] [Module (ZMod n) M₁]

namespace ZMod

theorem map_smul (f : M →+ M₁) (c : ZMod n) (x : M) : f (c • x) = c • f x := by
  cases n with
  | zero => exact map_int_cast_smul f _ _ c x
  | succ n =>
    induction c using Fin.induction with
    | zero => simp_rw [zero_smul, map_zero]
    | succ c hc => simp_rw [← Fin.coeSucc_eq_succ, add_smul, one_smul, f.map_add, hc]

end ZMod

namespace AddMonoidHom

variable (n)

/-- Reinterpret an additive homomorphism as a `ℤ/nℤ`-linear map.

See also:
`AddMonoidHom.toIntLinearMap`, `AddMonoidHom.toNatLinearMap`, `AddMonoidHom.toRatLinearMap` -/
def toZModLinearMap (f : M →+ M₁) : M →ₗ[ZMod n] M₁ := { f with map_smul' := ZMod.map_smul f }

theorem toZModLinearMap_injective: Function.Injective <| toZModLinearMap n (M := M) (M₁ := M₁) :=
  fun _ _ h ↦ ext fun x ↦ congr($h x)

@[simp]
theorem coe_toZModLinearMap (f : M →+ M₁) : ⇑(f.toZModLinearMap n) = f := rfl

end AddMonoidHom
