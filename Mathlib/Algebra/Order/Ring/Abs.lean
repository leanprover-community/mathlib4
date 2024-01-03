/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Ring.Divisibility.Basic

#align_import algebra.order.ring.abs from "leanprover-community/mathlib"@"10b4e499f43088dd3bb7b5796184ad5216648ab1"

/-!
# Absolute values in linear ordered rings.
-/


variable {α : Type*}

section

variable [Ring α] [LinearOrder α] {a b : α}

@[simp]
theorem abs_dvd (a b : α) : |a| ∣ b ↔ a ∣ b := by
  cases' abs_choice a with h h <;> simp only [h, neg_dvd]
#align abs_dvd abs_dvd

theorem abs_dvd_self (a : α) : |a| ∣ a :=
  (abs_dvd a a).mpr (dvd_refl a)
#align abs_dvd_self abs_dvd_self

@[simp]
theorem dvd_abs (a b : α) : a ∣ |b| ↔ a ∣ b := by
  cases' abs_choice b with h h <;> simp only [h, dvd_neg]
#align dvd_abs dvd_abs

theorem self_dvd_abs (a : α) : a ∣ |a| :=
  (dvd_abs a a).mpr (dvd_refl a)
#align self_dvd_abs self_dvd_abs

theorem abs_dvd_abs (a b : α) : |a| ∣ |b| ↔ a ∣ b :=
  (abs_dvd _ _).trans (dvd_abs _ _)
#align abs_dvd_abs abs_dvd_abs

end
