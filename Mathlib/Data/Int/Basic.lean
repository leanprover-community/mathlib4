/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Int.Init
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Lift
import Mathlib.Tactic.OfNat

/-!
# Basic operations on the integers

This file builds on `Data.Int.Init` by adding basic lemmas on natural numbers
depending on Mathlib definitions.
-/

open Nat

namespace Int
variable {a b c d m n : ℤ}

-- TODO: Tag in Lean
attribute [simp] natAbs_pos

instance instNontrivial : Nontrivial ℤ := ⟨⟨0, 1, Int.zero_ne_one⟩⟩

section inductionOn'

variable {C : ℤ → Sort*} (z b : ℤ)
  (H0 : C b) (Hs : ∀ k, b ≤ k → C k → C (k + 1)) (Hp : ∀ k ≤ b, C k → C (k - 1))

variable {z b H0 Hs Hp}

lemma inductionOn'_add_one (hz : b ≤ z) :
    (z + 1).inductionOn' b H0 Hs Hp = Hs z hz (z.inductionOn' b H0 Hs Hp) := by
  apply cast_eq_iff_heq.mpr
  lift z - b to ℕ using Int.sub_nonneg.mpr hz with zb hzb
  rw [show z + 1 - b = zb + 1 by omega]
  have : b + zb = z := by omega
  subst this
  convert cast_heq _ _
  rw [Int.inductionOn', cast_eq_iff_heq, ← hzb]

end inductionOn'

/-! ### nat abs -/

lemma natAbs_surjective : natAbs.Surjective := fun n => ⟨n, natAbs_ofNat n⟩

lemma pow_right_injective (h : 1 < a.natAbs) : ((a ^ ·) : ℕ → ℤ).Injective := by
  refine (?_ : (natAbs ∘ (a ^ · : ℕ → ℤ)).Injective).of_comp
  convert Nat.pow_right_injective h using 2
  rw [Function.comp_apply, natAbs_pow]

/-! ### dvd -/

@[norm_cast] lemma natCast_dvd_natCast {m n : ℕ} : (↑m : ℤ) ∣ ↑n ↔ m ∣ n where
  mp := by
    rintro ⟨a, h⟩
    obtain rfl | hm := m.eq_zero_or_pos
    · simpa using h
    have ha : 0 ≤ a := Int.not_lt.1 fun ha ↦ by
      simpa [← h, Int.not_lt.2 (Int.natCast_nonneg _)]
        using Int.mul_neg_of_pos_of_neg (natCast_pos.2 hm) ha
    lift a to ℕ using ha
    norm_cast at h
    exact ⟨a, h⟩
  mpr := by rintro ⟨a, rfl⟩; simp [Int.dvd_mul_right]

@[norm_cast] theorem ofNat_dvd_natCast {x y : ℕ} : (ofNat(x) : ℤ) ∣ (y : ℤ) ↔ OfNat.ofNat x ∣ y :=
  natCast_dvd_natCast

@[norm_cast] theorem natCast_dvd_ofNat {x y : ℕ} : (x : ℤ) ∣ (ofNat(y) : ℤ) ↔ x ∣ OfNat.ofNat y :=
  natCast_dvd_natCast

lemma natCast_dvd {m : ℕ} : (m : ℤ) ∣ n ↔ m ∣ n.natAbs := by
  obtain hn | hn := natAbs_eq n <;> rw [hn] <;> simp [← natCast_dvd_natCast, Int.dvd_neg]

lemma dvd_natCast {n : ℕ} : m ∣ (n : ℤ) ↔ m.natAbs ∣ n := by
  obtain hn | hn := natAbs_eq m <;> rw [hn] <;> simp [← natCast_dvd_natCast, Int.neg_dvd]

/-- If an integer with larger absolute value divides an integer, it is zero. -/
lemma eq_zero_of_dvd_of_natAbs_lt_natAbs (hmn : m ∣ n) (hnm : natAbs n < natAbs m) : n = 0 := by
  rw [← natAbs_dvd, ← dvd_natAbs, natCast_dvd_natCast] at hmn
  rw [← natAbs_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt hmn hnm

lemma eq_zero_of_dvd_of_nonneg_of_lt (hm : 0 ≤ m) (hmn : m < n) (hnm : n ∣ m) : m = 0 :=
  eq_zero_of_dvd_of_natAbs_lt_natAbs hnm (natAbs_lt_natAbs_of_nonneg_of_lt hm hmn)

/-- If two integers are congruent to a sufficiently large modulus, they are equal. -/
lemma eq_of_mod_eq_of_natAbs_sub_lt_natAbs {a b c : ℤ} (h1 : a % b = c)
    (h2 : natAbs (a - c) < natAbs b) : a = c :=
  Int.eq_of_sub_eq_zero (eq_zero_of_dvd_of_natAbs_lt_natAbs (dvd_sub_of_emod_eq h1) h2)

lemma natAbs_le_of_dvd_ne_zero (hmn : m ∣ n) (hn : n ≠ 0) : natAbs m ≤ natAbs n :=
  not_lt.mp (mt (eq_zero_of_dvd_of_natAbs_lt_natAbs hmn) hn)

end Int
