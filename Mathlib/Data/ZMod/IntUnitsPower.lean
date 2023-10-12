/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Data.ZMod.Basic

/-!
# The power operator by `ZMod 2` on `ℤˣ`
-/

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/-- There is a canonical power operation by `ℤˣ` on `ZMod 2`.

In lemma names, this operations is called `z₂pow` to match `zpow`. -/
instance : Pow ℤˣ (ZMod 2) where
  pow s z₂ := s ^ z₂.val

lemma z₂pow_def (s : ℤˣ) (x : ZMod 2) : s ^ x = s ^ x.val := rfl

@[simp] lemma z₂pow_zero (s : ℤˣ) : (s ^ (0 : ZMod 2) : ℤˣ) = (1 : ℤˣ) := pow_zero _

@[simp] lemma z₂pow_one (s : ℤˣ) : (s ^ (1 : ZMod 2) : ℤˣ) = s := pow_one _

lemma z₂pow_add (s : ℤˣ) (x y : ZMod 2) : s ^ (x + y) = s ^ x * s ^ y := by
  simp only [z₂pow_def]
  rw [ZMod.val_add, ←pow_eq_pow_mod, pow_add]
  fin_cases s <;> simp

lemma z₂pow_mul_self (s : ℤˣ) (x : ZMod 2) : s ^ x * s ^ x = 1 := by
  rw [←z₂pow_add, CharTwo.add_self_eq_zero, z₂pow_zero s]
