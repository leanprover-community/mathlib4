/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Group.Defs

/-!
# The natural numbers form a monoid

This file contains the additive and multiplicative monoid instances on the natural numbers.

See note [foundational algebra order theory].
-/

assert_not_exists MonoidWithZero DenselyOrdered

namespace Nat

/-! ### Instances -/

instance instMulOneClass : MulOneClass ℕ where
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one

instance instAddCancelCommMonoid : AddCancelCommMonoid ℕ where
  add := Nat.add
  add_assoc := Nat.add_assoc
  zero := Nat.zero
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  add_comm := Nat.add_comm
  nsmul m n := m * n
  nsmul_zero := Nat.zero_mul
  nsmul_succ := succ_mul
  add_left_cancel _ _ _ := Nat.add_left_cancel

instance instCommMonoid : CommMonoid ℕ where
  mul := Nat.mul
  mul_assoc := Nat.mul_assoc
  one := Nat.succ Nat.zero
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  mul_comm := Nat.mul_comm
  npow m n := n ^ m
  npow_zero := Nat.pow_zero
  npow_succ _ _ := rfl

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

set_option linter.style.commandStart false

instance instAddCommMonoid    : AddCommMonoid ℕ    := by infer_instance
instance instAddMonoid        : AddMonoid ℕ        := by infer_instance
instance instMonoid           : Monoid ℕ           := by infer_instance
instance instCommSemigroup    : CommSemigroup ℕ    := by infer_instance
instance instSemigroup        : Semigroup ℕ        := by infer_instance
instance instAddCommSemigroup : AddCommSemigroup ℕ := by infer_instance
instance instAddSemigroup     : AddSemigroup ℕ     := by infer_instance
instance instOne : One ℕ := inferInstance

set_option linter.style.commandStart true

/-! ### Miscellaneous lemmas -/

-- We set the simp priority slightly lower than default; later more general lemmas will replace it.
@[simp 900] protected lemma nsmul_eq_mul (m n : ℕ) : m • n = m * n := rfl

lemma div_mul_div {m n k : ℕ} (hn : n > 0) (hkm : m ∣ k) (hkn : n ∣ m) :
    (k / m) * (m / n) = k / n := by
  refine Eq.symm (Nat.div_eq_of_eq_mul_left hn ?_)
  rw [mul_assoc, Nat.div_mul_cancel hkn, Nat.div_mul_cancel hkm]

lemma div_dvd_div' {m n k : ℕ} (hn : n > 0) (hkm : m ∣ k) (hkn : n ∣ m) :
    k / m ∣ k / n := Exists.intro (m / n) (Eq.symm (div_mul_div hn hkm hkn))

lemma lcm_div_div {m n k : ℕ} (hm : m > 0) (hn : n > 0) (hkm : m ∣ k) (hkn : n ∣ k) :
    (k / m).lcm (k / n) = k / (m.gcd n) := by
  rw [Nat.lcm_eq_iff]
  exact ⟨div_dvd_div' (gcd_pos_of_pos_left n hm) hkm (Nat.gcd_dvd_left m n),
        div_dvd_div' (gcd_pos_of_pos_left n hm) hkn (Nat.gcd_dvd_right m n), fun c hmc hnc ↦ by
    rw [Nat.div_dvd_iff_dvd_mul hkm hm] at hmc
    rw [Nat.div_dvd_iff_dvd_mul hkn hn] at hnc
    simpa [Nat.div_dvd_iff_dvd_mul (Nat.dvd_trans (Nat.gcd_dvd_left m n) hkm)
      (gcd_pos_of_pos_left n hm), Nat.gcd_mul_right m c n] using (Nat.dvd_gcd hmc hnc) ⟩

end Nat
