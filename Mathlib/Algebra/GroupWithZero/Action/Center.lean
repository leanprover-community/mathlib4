/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-!
# The center of a group with zero
-/

assert_not_exists Ring

/-- For a group with zero, the center of the units is the same as the units of the center. -/
@[simps! apply_val_coe symm_apply_coe_val]
def Subgroup.centerUnitsEquivUnitsCenter (G₀ : Type*) [GroupWithZero G₀] :
    center G₀ˣ ≃* (Submonoid.center G₀)ˣ where
  toFun := MonoidHom.toHomUnits
    { toFun u := by
        refine ⟨(u : G₀ˣ), Submonoid.mem_center_iff.mpr fun r ↦ ?_⟩
        obtain rfl | hr := eq_or_ne r 0
        · rw [mul_zero, zero_mul]
        · exact congrArg Units.val <| (u.2.comm <| Units.mk0 r hr).symm
      map_one' := rfl
      map_mul' _ _ := rfl }
  invFun u := unitsCenterToCenterUnits G₀ u
  map_mul' := map_mul _
