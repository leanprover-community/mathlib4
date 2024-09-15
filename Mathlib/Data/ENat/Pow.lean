/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Lattice

/-!
# Extended natural power

-/

namespace ENat

instance : Pow ℕ∞ ℕ∞ where
  pow
    | m, (n : ℕ) => m ^ n
    | m, ⊤ =>
      match m with
      | 0 => 0
      | 1 => 1
      | _ => ⊤

@[simp, norm_cast]
theorem epow_natCast (m : ℕ∞) (n : ℕ) : m ^ (n : ℕ∞) = m ^ n := rfl

@[simp]
theorem zero_epow_top : (0 : ℕ∞) ^ (⊤ : ℕ∞) = 0 := rfl

@[simp]
theorem zero_epow {m : ℕ∞} (hm : m ≠ 0) : (0 : ℕ∞) ^ m = 0 := by
  induction m using recTopCoe with
  | top => rfl
  | coe m => exact zero_pow <| mod_cast hm

@[simp]
theorem one_epow : ∀ m : ℕ∞, (1 : ℕ∞) ^ m = 1
  | (m : ℕ) => one_pow m
  | ⊤ => rfl

@[simp]
theorem epow_zero (m : ℕ∞) : m ^ (0 : ℕ∞) = 1 := pow_zero m

@[simp]
theorem epow_top : ∀ {m : ℕ∞}, 1 < m → m^(⊤ : ℕ∞) = ⊤
  | (_ + 2 : ℕ), _ => rfl
  | ⊤, _ => rfl

end ENat
