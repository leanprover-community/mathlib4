/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Ring.AddAut
public import Mathlib.Data.ZMod.Basic

/-!
# Automorphism Group of `ZMod`.
-/

@[expose] public section

assert_not_exists Field TwoSidedIdeal

namespace ZMod

variable (n : ℕ)

/-- The automorphism group of `ZMod n` is isomorphic to the group of units of `ZMod n`. -/
@[simps]
def AddAutEquivUnits : AddAut (ZMod n) ≃+ Additive (ZMod n)ˣ :=
  have h (f : AddAut (ZMod n)) (x : ZMod n) : f 1 * x = f x := by
    rw [mul_comm, ← x.intCast_zmod_cast, ← zsmul_eq_mul, ← map_zsmul, zsmul_one]
  { toFun f := .ofMul <| Units.mkOfMulEqOne (f 1) ((-f) 1) ((h f _).trans (f.apply_neg_self _ _))
    invFun x := AddAut.mulLeft x.toMul
    left_inv g := by simp [DFunLike.ext_iff, Units.smul_def, h]
    right_inv x := by simp [← Additive.toMul_symm_eq, Equiv.symm_apply_eq,
      Units.ext_iff, Units.smul_def, -toMul_smul]
    map_add' f g := by simp [← Additive.toMul_symm_eq, Equiv.symm_apply_eq, Units.ext_iff, h] }

end ZMod
