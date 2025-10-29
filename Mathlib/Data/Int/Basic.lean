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

This file builds on `Data.Int.Init` by adding basic lemmas on integers.
depending on Mathlib definitions.
-/

open Nat

namespace Int
variable {a b c d m n : ℤ}

-- TODO: Tag in Lean
attribute [simp] natAbs_pos

@[gcongr] alias ⟨_, GCongr.ofNat_le_ofNat⟩ := ofNat_le

instance instNontrivial : Nontrivial ℤ := ⟨⟨0, 1, Int.zero_ne_one⟩⟩

@[simp] lemma ofNat_injective : Function.Injective ofNat := @Int.ofNat.inj

section inductionOn'

variable {C : ℤ → Sort*} (z b : ℤ)
  (H0 : C b) (Hs : ∀ k, b ≤ k → C k → C (k + 1)) (Hp : ∀ k ≤ b, C k → C (k - 1))

variable {z b H0 Hs Hp}

lemma inductionOn'_add_one (hz : b ≤ z) :
    (z + 1).inductionOn' b H0 Hs Hp = Hs z hz (z.inductionOn' b H0 Hs Hp) := by
  apply cast_eq_iff_heq.mpr
  lift z - b to ℕ using Int.sub_nonneg.mpr hz with zb hzb
  rw [show z + 1 - b = zb + 1 by cutsat]
  have : b + zb = z := by omega
  subst this
  convert cast_heq _ _
  rw [Int.inductionOn', cast_eq_iff_heq, ← hzb]

end inductionOn'

section strongRec

variable {P : ℤ → Sort*} {lt : ∀ n < m, P n} {ge : ∀ n ≥ m, (∀ k < n, P k) → P n}

lemma strongRec_of_ge :
    ∀ hn : m ≤ n, m.strongRec lt ge n = ge n hn fun k _ ↦ m.strongRec lt ge k := by
  refine m.strongRec (fun n hnm hmn ↦ (Int.not_lt.mpr hmn hnm).elim) (fun n _ ih hn ↦ ?_) n
  rw [Int.strongRec, dif_neg (Int.not_lt.mpr hn)]
  congr; revert ih
  refine n.inductionOn' m (fun _ ↦ ?_) (fun k hmk ih' ih ↦ ?_) (fun k hkm ih' _ ↦ ?_) <;> ext l hl
  · rw [inductionOn'_self, strongRec_of_lt hl]
  · rw [inductionOn'_add_one hmk]; split_ifs with hlm
    · rw [strongRec_of_lt hlm]
    · rw [ih' fun l hl ↦ ih l (Int.lt_trans hl k.lt_succ), ih _ hl]
  · rw [inductionOn'_sub_one hkm, ih']
    exact fun l hlk hml ↦ (Int.not_lt.mpr hkm <| Int.lt_of_le_of_lt hml hlk).elim

end strongRec

/-! ### nat abs -/

lemma natAbs_surjective : natAbs.Surjective := fun n => ⟨n, natAbs_natCast n⟩

lemma pow_right_injective (h : 1 < a.natAbs) : ((a ^ ·) : ℕ → ℤ).Injective := by
  refine (?_ : (natAbs ∘ (a ^ · : ℕ → ℤ)).Injective).of_comp
  convert Nat.pow_right_injective h using 2
  rw [Function.comp_apply, natAbs_pow]

/-! ### dvd -/

@[norm_cast] theorem ofNat_dvd_natCast {x y : ℕ} : (ofNat(x) : ℤ) ∣ (y : ℤ) ↔ OfNat.ofNat x ∣ y :=
  natCast_dvd_natCast

@[norm_cast] theorem natCast_dvd_ofNat {x y : ℕ} : (x : ℤ) ∣ (ofNat(y) : ℤ) ↔ x ∣ OfNat.ofNat y :=
  natCast_dvd_natCast

lemma natCast_dvd {m : ℕ} : (m : ℤ) ∣ n ↔ m ∣ n.natAbs := by
  obtain hn | hn := natAbs_eq n <;> rw [hn] <;> simp [← natCast_dvd_natCast, Int.dvd_neg]

lemma dvd_natCast {n : ℕ} : m ∣ (n : ℤ) ↔ m.natAbs ∣ n := by
  obtain hn | hn := natAbs_eq m <;> rw [hn] <;> simp [← natCast_dvd_natCast, Int.neg_dvd]

lemma eq_zero_of_dvd_of_nonneg_of_lt (hm : 0 ≤ m) (hmn : m < n) (hnm : n ∣ m) : m = 0 :=
  eq_zero_of_dvd_of_natAbs_lt_natAbs hnm (natAbs_lt_natAbs_of_nonneg_of_lt hm hmn)

/-- If two integers are congruent to a sufficiently large modulus, they are equal. -/
lemma eq_of_mod_eq_of_natAbs_sub_lt_natAbs {a b c : ℤ} (h1 : a % b = c)
    (h2 : natAbs (a - c) < natAbs b) : a = c :=
  Int.eq_of_sub_eq_zero (eq_zero_of_dvd_of_natAbs_lt_natAbs (dvd_self_sub_of_emod_eq h1) h2)

lemma natAbs_le_of_dvd_ne_zero (hmn : m ∣ n) (hn : n ≠ 0) : natAbs m ≤ natAbs n :=
  not_lt.mp (mt (eq_zero_of_dvd_of_natAbs_lt_natAbs hmn) hn)

theorem gcd_emod (m n : ℤ) : (m % n).gcd n = m.gcd n := by
  conv_rhs => rw [← m.emod_add_mul_ediv n, gcd_add_mul_left_left]

end Int
