/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Nat
import Mathlib.Order.UpperLower.Basic

/-!
# Images of intervals under `Nat.cast : ℕ → ℤ`

In this file we prove that the image of each `Set.Ixx` interval under `Nat.cast : ℕ → ℤ`
is the corresponding interval in `ℤ`.
-/

open Set

namespace Nat

@[simp]
theorem range_cast_int : range ((↑) : ℕ → ℤ) = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 Int.natCast_nonneg) CanLift.prf

theorem image_cast_int_Icc (a b : ℕ) : (↑) '' Icc a b = Icc (a : ℤ) b :=
  (castOrderEmbedding (α := ℤ)).image_Icc (by simp [ordConnected_Ici]) a b

theorem image_cast_int_Ico (a b : ℕ) : (↑) '' Ico a b = Ico (a : ℤ) b :=
  (castOrderEmbedding (α := ℤ)).image_Ico (by simp [ordConnected_Ici]) a b

theorem image_cast_int_Ioc (a b : ℕ) : (↑) '' Ioc a b = Ioc (a : ℤ) b :=
  (castOrderEmbedding (α := ℤ)).image_Ioc (by simp [ordConnected_Ici]) a b

theorem image_cast_int_Ioo (a b : ℕ) : (↑) '' Ioo a b = Ioo (a : ℤ) b :=
  (castOrderEmbedding (α := ℤ)).image_Ioo (by simp [ordConnected_Ici]) a b

theorem image_cast_int_Iic (a : ℕ) : (↑) '' Iic a = Icc (0 : ℤ) a := by
  rw [← Icc_bot, image_cast_int_Icc]; rfl

theorem image_cast_int_Iio (a : ℕ) : (↑) '' Iio a = Ico (0 : ℤ) a := by
  rw [← Ico_bot, image_cast_int_Ico]; rfl

theorem image_cast_int_Ici (a : ℕ) : (↑) '' Ici a = Ici (a : ℤ) :=
  (castOrderEmbedding (α := ℤ)).image_Ici (by simp [isUpperSet_Ici]) a

theorem image_cast_int_Ioi (a : ℕ) : (↑) '' Ioi a = Ioi (a : ℤ) :=
  (castOrderEmbedding (α := ℤ)).image_Ioi (by simp [isUpperSet_Ici]) a

end Nat
