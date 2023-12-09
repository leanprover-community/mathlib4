/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.ZMod.Basic

/-!
# The power operator by `ZMod 2` on `ℤˣ`

See also the related `negOnePow`.

## TODO

* Generalize this to `Pow G (Zmod n)` where `orderOf g = n`.
* Abstract this with a `LawfulPow` typeclass such that we can reuse the same lemmas for `z₂pow`,
  `npow`, and `zpow`.
-/

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/-- There is a canonical power operation by `ℤˣ` on `ZMod 2`.

In lemma names, this operations is called `z₂pow` to match `zpow`. -/
instance : Pow ℤˣ (ZMod 2) where
  pow s z₂ := s ^ z₂.val

lemma z₂pow_def (s : ℤˣ) (x : ZMod 2) : s ^ x = s ^ x.val := rfl

lemma z₂pow_natCast (s : ℤˣ) (n : ℕ) : s ^ (n : ZMod 2) = s ^ n :=
  (Int.units_pow_eq_pow_mod_two s n).symm

lemma z₂pow_ofNat (s : ℤˣ) (n : ℕ) [n.AtLeastTwo] :
    s ^ (no_index (OfNat.ofNat n : ZMod 2)) = s ^ (no_index (OfNat.ofNat n : ℕ)) :=
  z₂pow_natCast _ _

@[simp] lemma one_z₂pow (x : ZMod 2) : (1 : ℤˣ) ^ x = 1 := one_pow _

lemma mul_z₂pow (s₁ s₂ : ℤˣ) (x : ZMod 2) : (s₁ * s₂) ^ x = s₁ ^ x * s₂ ^ x := mul_pow _ _ _

@[simp] lemma z₂pow_zero (s : ℤˣ) : (s ^ (0 : ZMod 2) : ℤˣ) = (1 : ℤˣ) := pow_zero _

@[simp] lemma z₂pow_one (s : ℤˣ) : (s ^ (1 : ZMod 2) : ℤˣ) = s := pow_one _

lemma z₂pow_mul (s : ℤˣ) (x y : ZMod 2) : s ^ (x * y) = (s ^ x) ^ y := by
  convert pow_mul s x.val y.val
  rw [←z₂pow_natCast, Nat.cast_mul, ZMod.nat_cast_zmod_val, ZMod.nat_cast_zmod_val]

lemma z₂pow_add (s : ℤˣ) (x y : ZMod 2) : s ^ (x + y) = s ^ x * s ^ y := by
  simp only [z₂pow_def]
  rw [ZMod.val_add, ←pow_eq_pow_mod, pow_add]
  fin_cases s <;> simp

/-! The next two lemmas are mathematically not interesting as `-` coincides with `+` and `/` with
`*`, but they match the api for powers by `ℤ`. -/

lemma z₂pow_sub (s : ℤˣ) (x y : ZMod 2) : s ^ (x - y) = s ^ x / s ^ y := by
  simp only [CharTwo.sub_eq_add, z₂pow_add, Int.units_div_eq_mul]

lemma z₂pow_neg (s : ℤˣ) (x : ZMod 2) : s ^ (-x) = (s ^ x)⁻¹ := by
  simp only [CharTwo.neg_eq, Int.units_inv_eq_self]
