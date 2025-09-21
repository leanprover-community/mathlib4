/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Group.Int.Even

/-!
# Basic parity lemmas for the ring `ℤ`

See note [foundational algebra order theory].
-/

assert_not_exists DenselyOrdered Set.Subsingleton

namespace Int

/-! #### Parity -/

variable {m n : ℤ}

@[grind =]
lemma odd_iff : Odd n ↔ n % 2 = 1 where
  mp := fun ⟨m, hm⟩ ↦ by simp [hm, add_emod]
  mpr h := ⟨n / 2, by grind⟩

lemma not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by grind

@[simp] lemma not_odd_zero : ¬Odd (0 : ℤ) := by grind

@[simp, grind =] lemma not_odd_iff_even : ¬Odd n ↔ Even n := by grind
@[simp] lemma not_even_iff_odd : ¬Even n ↔ Odd n := by grind

lemma even_or_odd (n : ℤ) : Even n ∨ Odd n := by grind

lemma even_or_odd' (n : ℤ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by
  simpa only [two_mul, exists_or, Odd, Even] using even_or_odd n

lemma even_xor'_odd (n : ℤ) : Xor' (Even n) (Odd n) := by
  grind

lemma even_xor'_odd' (n : ℤ) : ∃ k, Xor' (n = 2 * k) (n = 2 * k + 1) := by
  rcases even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;>
  · use k
    simp only [Xor'] -- Perhaps `grind` needs a normalization rule for `Xor'`?
    grind

instance : DecidablePred (Odd : ℤ → Prop) := fun _ => decidable_of_iff _ not_even_iff_odd

lemma even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by grind

lemma not_even_two_mul_add_one (n : ℤ) : ¬ Even (2 * n + 1) := by grind

lemma even_sub' : Even (m - n) ↔ (Odd m ↔ Odd n) := by grind

lemma odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by simp [← not_even_iff_odd, not_or, parity_simps]

lemma Odd.of_mul_left (h : Odd (m * n)) : Odd m := (odd_mul.mp h).1

lemma Odd.of_mul_right (h : Odd (m * n)) : Odd n := (odd_mul.mp h).2

@[parity_simps] lemma odd_pow {n : ℕ} : Odd (m ^ n) ↔ Odd m ∨ n = 0 := by grind

lemma odd_pow' {n : ℕ} (h : n ≠ 0) : Odd (m ^ n) ↔ Odd m := by grind

@[parity_simps] lemma odd_add : Odd (m + n) ↔ (Odd m ↔ Even n) := by grind

lemma odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by grind

lemma ne_of_odd_add (h : Odd (m + n)) : m ≠ n := by grind

@[parity_simps] lemma odd_sub : Odd (m - n) ↔ (Odd m ↔ Even n) := by grind

lemma odd_sub' : Odd (m - n) ↔ (Odd n ↔ Even m) := by grind

lemma even_mul_succ_self (n : ℤ) : Even (n * (n + 1)) := by grind

lemma even_mul_pred_self (n : ℤ) : Even (n * (n - 1)) := by grind

@[simp, norm_cast] lemma odd_coe_nat (n : ℕ) : Odd (n : ℤ) ↔ Odd n := by grind

@[simp] lemma natAbs_even : Even n.natAbs ↔ Even n := by grind

@[simp]
lemma natAbs_odd : Odd n.natAbs ↔ Odd n := by grind

protected alias ⟨_, _root_.Even.natAbs⟩ := natAbs_even
protected alias ⟨_, _root_.Odd.natAbs⟩ := natAbs_odd

lemma four_dvd_add_or_sub_of_odd {a b : ℤ} (ha : Odd a) (hb : Odd b) :
    4 ∣ a + b ∨ 4 ∣ a - b := by grind

lemma two_dvd_mul_add_one (k : ℤ) : 2 ∣ k * (k + 1) :=
  even_iff_two_dvd.mp (even_mul_succ_self k)

lemma two_mul_ediv_two_add_one_of_odd : Odd n → 2 * (n / 2) + 1 = n := by grind

lemma ediv_two_mul_two_add_one_of_odd : Odd n → n / 2 * 2 + 1 = n := by grind

lemma add_one_ediv_two_mul_two_of_odd : Odd n → 1 + n / 2 * 2 = n := by grind

lemma two_mul_ediv_two_of_odd (h : Odd n) : 2 * (n / 2) = n - 1 := by grind

@[simp, grind =]
theorem even_sign_iff {z : ℤ} : Even z.sign ↔ z = 0 := by
  induction z using wlog_sign with
  | inv => simp
  | w n =>
    cases n
    · simp
    · norm_cast
      simp

@[simp]
theorem odd_sign_iff {z : ℤ} : Odd z.sign ↔ z ≠ 0 := by grind

@[norm_cast, simp]
theorem isSquare_natCast_iff {n : ℕ} : IsSquare (n : ℤ) ↔ IsSquare n := by
  constructor <;> rintro ⟨x, h⟩
  · exact ⟨x.natAbs, (natAbs_mul_natAbs_eq h.symm).symm⟩
  · exact ⟨x, mod_cast h⟩

@[simp]
theorem isSquare_ofNat_iff {n : ℕ} :
    IsSquare (ofNat(n) : ℤ) ↔ IsSquare (ofNat(n) : ℕ) :=
  isSquare_natCast_iff

end Int
