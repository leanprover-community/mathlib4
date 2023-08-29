/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr.Core

#align_import data.nat.modeq from "leanprover-community/mathlib"@"47a1a73351de8dd6c8d3d32b569c8e434b03ca47"

/-!
# Congruences modulo a natural number

This file defines the equivalence relation `a ≡ b [MOD n]` on the natural numbers,
and proves basic properties about it such as the Chinese Remainder Theorem
`modEq_and_modEq_iff_modEq_mul`.

## Notations

`a ≡ b [MOD n]` is notation for `nat.ModEq n a b`, which is defined to mean `a % n = b % n`.

## Tags

ModEq, congruence, mod, MOD, modulo
-/


namespace Nat

/-- Modular equality. `n.ModEq a b`, or `a ≡ b [MOD n]`, means that `a - b` is a multiple of `n`. -/
def ModEq (n a b : ℕ) :=
  a % n = b % n
#align nat.modeq Nat.ModEq

@[inherit_doc]
notation:50 a " ≡ " b " [MOD " n "]" => ModEq n a b

variable {m n a b c d : ℕ}

-- Porting note: This instance should be derivable automatically
instance : Decidable (ModEq n a b) := decEq (a % n) (b % n)

namespace ModEq

@[refl]
protected theorem refl (a : ℕ) : a ≡ a [MOD n] := rfl
#align nat.modeq.refl Nat.ModEq.refl

protected theorem rfl : a ≡ a [MOD n] :=
  ModEq.refl _
#align nat.modeq.rfl Nat.ModEq.rfl

instance : IsRefl _ (ModEq n) :=
  ⟨ModEq.refl⟩

@[symm]
protected theorem symm : a ≡ b [MOD n] → b ≡ a [MOD n] :=
  Eq.symm
#align nat.modeq.symm Nat.ModEq.symm

@[trans]
protected theorem trans : a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c [MOD n] :=
  Eq.trans
#align nat.modeq.trans Nat.ModEq.trans

instance : Trans (ModEq n) (ModEq n) (ModEq n) where
  trans := Nat.ModEq.trans

protected theorem comm : a ≡ b [MOD n] ↔ b ≡ a [MOD n] :=
  ⟨ModEq.symm, ModEq.symm⟩
#align nat.modeq.comm Nat.ModEq.comm

end ModEq

theorem modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a := by rw [ModEq, zero_mod, dvd_iff_mod_eq_zero]
                                                         -- 🎉 no goals
#align nat.modeq_zero_iff_dvd Nat.modEq_zero_iff_dvd

theorem _root_.Dvd.dvd.modEq_zero_nat (h : n ∣ a) : a ≡ 0 [MOD n] :=
  modEq_zero_iff_dvd.2 h
#align has_dvd.dvd.modeq_zero_nat Dvd.dvd.modEq_zero_nat

theorem _root_.Dvd.dvd.zero_modEq_nat (h : n ∣ a) : 0 ≡ a [MOD n] :=
  h.modEq_zero_nat.symm
#align has_dvd.dvd.zero_modeq_nat Dvd.dvd.zero_modEq_nat

theorem modEq_iff_dvd : a ≡ b [MOD n] ↔ (n : ℤ) ∣ b - a := by
  rw [ModEq, eq_comm, ← Int.coe_nat_inj', Int.coe_nat_mod, Int.coe_nat_mod,
    Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.dvd_iff_emod_eq_zero]
#align nat.modeq_iff_dvd Nat.modEq_iff_dvd

alias ⟨ModEq.dvd, modEq_of_dvd⟩ := modEq_iff_dvd
#align nat.modeq.dvd Nat.ModEq.dvd
#align nat.modeq_of_dvd Nat.modEq_of_dvd

/-- A variant of `modEq_iff_dvd` with `Nat` divisibility -/
theorem modEq_iff_dvd' (h : a ≤ b) : a ≡ b [MOD n] ↔ n ∣ b - a := by
  rw [modEq_iff_dvd, ← Int.coe_nat_dvd, Int.ofNat_sub h]
  -- 🎉 no goals
#align nat.modeq_iff_dvd' Nat.modEq_iff_dvd'

theorem mod_modEq (a n) : a % n ≡ a [MOD n] :=
  mod_mod _ _
#align nat.mod_modeq Nat.mod_modEq

namespace ModEq

lemma of_dvd (d : m ∣ n) (h : a ≡ b [MOD n]) : a ≡ b [MOD m] := modEq_of_dvd $ d.natCast.trans h.dvd
#align nat.modeq.of_dvd Nat.ModEq.of_dvd

protected theorem mul_left' (c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD c * n] := by
  unfold ModEq at *; rw [mul_mod_mul_left, mul_mod_mul_left, h]
  -- ⊢ c * a % (c * n) = c * b % (c * n)
                     -- 🎉 no goals
#align nat.modeq.mul_left' Nat.ModEq.mul_left'

@[gcongr]
protected theorem mul_left (c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD n] :=
  (h.mul_left' _).of_dvd (dvd_mul_left _ _)
#align nat.modeq.mul_left Nat.ModEq.mul_left

protected theorem mul_right' (c : ℕ) (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD n * c] := by
  rw [mul_comm a, mul_comm b, mul_comm n]; exact h.mul_left' c
  -- ⊢ c * a ≡ c * b [MOD c * n]
                                           -- 🎉 no goals
#align nat.modeq.mul_right' Nat.ModEq.mul_right'

@[gcongr]
protected theorem mul_right (c : ℕ) (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD n] := by
  rw [mul_comm a, mul_comm b]; exact h.mul_left c
  -- ⊢ c * a ≡ c * b [MOD n]
                               -- 🎉 no goals
#align nat.modeq.mul_right Nat.ModEq.mul_right

@[gcongr]
protected theorem mul (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a * c ≡ b * d [MOD n] :=
  (h₂.mul_left _).trans (h₁.mul_right _)
#align nat.modeq.mul Nat.ModEq.mul

@[gcongr]
protected theorem pow (m : ℕ) (h : a ≡ b [MOD n]) : a ^ m ≡ b ^ m [MOD n] := by
  induction m with
  | zero => rfl
  | succ d hd =>
    rw[pow_succ, pow_succ]
    exact hd.mul h
#align nat.modeq.pow Nat.ModEq.pow

@[gcongr]
protected theorem add (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a + c ≡ b + d [MOD n] := by
  rw [modEq_iff_dvd, Int.ofNat_add, Int.ofNat_add, add_sub_add_comm]
  -- ⊢ ↑n ∣ ↑b - ↑a + (↑d - ↑c)
  exact dvd_add h₁.dvd h₂.dvd
  -- 🎉 no goals
#align nat.modeq.add Nat.ModEq.add

@[gcongr]
protected theorem add_left (c : ℕ) (h : a ≡ b [MOD n]) : c + a ≡ c + b [MOD n] :=
  ModEq.rfl.add h
#align nat.modeq.add_left Nat.ModEq.add_left

@[gcongr]
protected theorem add_right (c : ℕ) (h : a ≡ b [MOD n]) : a + c ≡ b + c [MOD n] :=
  h.add ModEq.rfl
#align nat.modeq.add_right Nat.ModEq.add_right

protected theorem add_left_cancel (h₁ : a ≡ b [MOD n]) (h₂ : a + c ≡ b + d [MOD n]) :
    c ≡ d [MOD n] := by
  simp only [modEq_iff_dvd, Int.ofNat_add] at *
  -- ⊢ ↑n ∣ ↑d - ↑c
  rw [add_sub_add_comm] at h₂
  -- ⊢ ↑n ∣ ↑d - ↑c
  convert _root_.dvd_sub h₂ h₁ using 1
  -- ⊢ ↑d - ↑c = ↑b - ↑a + (↑d - ↑c) - (↑b - ↑a)
  rw [add_sub_cancel']
  -- 🎉 no goals
#align nat.modeq.add_left_cancel Nat.ModEq.add_left_cancel

protected theorem add_left_cancel' (c : ℕ) (h : c + a ≡ c + b [MOD n]) : a ≡ b [MOD n] :=
  ModEq.rfl.add_left_cancel h
#align nat.modeq.add_left_cancel' Nat.ModEq.add_left_cancel'

protected theorem add_right_cancel (h₁ : c ≡ d [MOD n]) (h₂ : a + c ≡ b + d [MOD n]) :
    a ≡ b [MOD n] := by
  rw [add_comm a, add_comm b] at h₂
  -- ⊢ a ≡ b [MOD n]
  exact h₁.add_left_cancel h₂
  -- 🎉 no goals
#align nat.modeq.add_right_cancel Nat.ModEq.add_right_cancel

protected theorem add_right_cancel' (c : ℕ) (h : a + c ≡ b + c [MOD n]) : a ≡ b [MOD n] :=
  ModEq.rfl.add_right_cancel h
#align nat.modeq.add_right_cancel' Nat.ModEq.add_right_cancel'

/-- Cancel left multiplication on both sides of the `≡` and in the modulus.

For cancelling left multiplication in the modulus, see `Nat.ModEq.of_mul_left`. -/
protected theorem mul_left_cancel' {a b c m : ℕ} (hc : c ≠ 0) :
    c * a ≡ c * b [MOD c * m] → a ≡ b [MOD m] := by
  simp [modEq_iff_dvd, ← mul_sub, mul_dvd_mul_iff_left (by simp [hc] : (c : ℤ) ≠ 0)]
  -- 🎉 no goals
#align nat.modeq.mul_left_cancel' Nat.ModEq.mul_left_cancel'

protected theorem mul_left_cancel_iff' {a b c m : ℕ} (hc : c ≠ 0) :
    c * a ≡ c * b [MOD c * m] ↔ a ≡ b [MOD m] :=
  ⟨ModEq.mul_left_cancel' hc, ModEq.mul_left' _⟩
#align nat.modeq.mul_left_cancel_iff' Nat.ModEq.mul_left_cancel_iff'

/-- Cancel right multiplication on both sides of the `≡` and in the modulus.

For cancelling right multiplication in the modulus, see `Nat.ModEq.of_mul_right`. -/
protected theorem mul_right_cancel' {a b c m : ℕ} (hc : c ≠ 0) :
    a * c ≡ b * c [MOD m * c] → a ≡ b [MOD m] := by
  simp [modEq_iff_dvd, ← sub_mul, mul_dvd_mul_iff_right (by simp [hc] : (c : ℤ) ≠ 0)]
  -- 🎉 no goals
#align nat.modeq.mul_right_cancel' Nat.ModEq.mul_right_cancel'

protected theorem mul_right_cancel_iff' {a b c m : ℕ} (hc : c ≠ 0) :
    a * c ≡ b * c [MOD m * c] ↔ a ≡ b [MOD m] :=
  ⟨ModEq.mul_right_cancel' hc, ModEq.mul_right' _⟩
#align nat.modeq.mul_right_cancel_iff' Nat.ModEq.mul_right_cancel_iff'

/-- Cancel left multiplication in the modulus.

For cancelling left multiplication on both sides of the `≡`, see `nat.modeq.mul_left_cancel'`. -/
lemma of_mul_left (m : ℕ) (h : a ≡ b [MOD m * n]) : a ≡ b [MOD n] := by
  rw [modEq_iff_dvd] at *
  -- ⊢ ↑n ∣ ↑b - ↑a
  exact (dvd_mul_left (n : ℤ) (m : ℤ)).trans h
  -- 🎉 no goals
#align nat.modeq.of_mul_left Nat.ModEq.of_mul_left

/-- Cancel right multiplication in the modulus.

For cancelling right multiplication on both sides of the `≡`, see `nat.modeq.mul_right_cancel'`. -/
lemma of_mul_right (m : ℕ) : a ≡ b [MOD n * m] → a ≡ b [MOD n] := mul_comm m n ▸ of_mul_left _
#align nat.modeq.of_mul_right Nat.ModEq.of_mul_right

theorem of_div (h : a / c ≡ b / c [MOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m) :
    a ≡ b [MOD m] := by convert h.mul_left' c <;> rwa [Nat.mul_div_cancel']
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align nat.modeq.of_div Nat.ModEq.of_div

end ModEq

lemma modEq_sub (h : b ≤ a) : a ≡ b [MOD a - b] := (modEq_of_dvd $ by rw [Int.ofNat_sub h]).symm
                                                                      -- 🎉 no goals
#align nat.modeq_sub Nat.modEq_sub

lemma modEq_one : a ≡ b [MOD 1] := modEq_of_dvd $ one_dvd _
#align nat.modeq_one Nat.modEq_one

@[simp] lemma modEq_zero_iff : a ≡ b [MOD 0] ↔ a = b := by rw [ModEq, mod_zero, mod_zero]
                                                           -- 🎉 no goals
#align nat.modeq_zero_iff Nat.modEq_zero_iff

@[simp] lemma add_modEq_left : n + a ≡ a [MOD n] := by rw [ModEq, add_mod_left]
                                                       -- 🎉 no goals
#align nat.add_modeq_left Nat.add_modEq_left

@[simp] lemma add_modEq_right : a + n ≡ a [MOD n] := by rw [ModEq, add_mod_right]
                                                        -- 🎉 no goals
#align nat.add_modeq_right Nat.add_modEq_right

namespace ModEq

theorem le_of_lt_add (h1 : a ≡ b [MOD m]) (h2 : a < b + m) : a ≤ b :=
  (le_total a b).elim id fun h3 =>
    Nat.le_of_sub_eq_zero
      (eq_zero_of_dvd_of_lt ((modEq_iff_dvd' h3).mp h1.symm) ((tsub_lt_iff_left h3).mpr h2))
#align nat.modeq.le_of_lt_add Nat.ModEq.le_of_lt_add

theorem add_le_of_lt (h1 : a ≡ b [MOD m]) (h2 : a < b) : a + m ≤ b :=
  le_of_lt_add (add_modEq_right.trans h1) (add_lt_add_right h2 m)
#align nat.modeq.add_le_of_lt Nat.ModEq.add_le_of_lt

theorem dvd_iff (h : a ≡ b [MOD m]) (hdm : d ∣ m) : d ∣ a ↔ d ∣ b := by
  simp only [← modEq_zero_iff_dvd]
  -- ⊢ a ≡ 0 [MOD d] ↔ b ≡ 0 [MOD d]
  replace h := h.of_dvd hdm
  -- ⊢ a ≡ 0 [MOD d] ↔ b ≡ 0 [MOD d]
  exact ⟨h.symm.trans, h.trans⟩
  -- 🎉 no goals
#align nat.modeq.dvd_iff Nat.ModEq.dvd_iff

theorem gcd_eq (h : a ≡ b [MOD m]) : gcd a m = gcd b m := by
  have h1 := gcd_dvd_right a m
  -- ⊢ gcd a m = gcd b m
  have h2 := gcd_dvd_right b m
  -- ⊢ gcd a m = gcd b m
  exact
    dvd_antisymm (dvd_gcd ((h.dvd_iff h1).mp (gcd_dvd_left a m)) h1)
      (dvd_gcd ((h.dvd_iff h2).mpr (gcd_dvd_left b m)) h2)
#align nat.modeq.gcd_eq Nat.ModEq.gcd_eq

lemma eq_of_abs_lt (h : a ≡ b [MOD m]) (h2 : |(b : ℤ) - a| < m) : a = b := by
  apply Int.ofNat.inj
  -- ⊢ Int.ofNat a = Int.ofNat b
  rw [eq_comm, ← sub_eq_zero]
  -- ⊢ Int.ofNat b - Int.ofNat a = 0
  exact Int.eq_zero_of_abs_lt_dvd h.dvd h2
  -- 🎉 no goals
#align nat.modeq.eq_of_abs_lt Nat.ModEq.eq_of_abs_lt

lemma eq_of_lt_of_lt (h : a ≡ b [MOD m]) (ha : a < m) (hb : b < m) : a = b :=
  h.eq_of_abs_lt $ abs_sub_lt_iff.2
    ⟨(sub_le_self _ $ Int.coe_nat_nonneg _).trans_lt $ Int.ofNat_lt.2 hb,
    (sub_le_self _ $ Int.coe_nat_nonneg _).trans_lt $ Int.ofNat_lt.2 ha⟩
#align nat.modeq.eq_of_lt_of_lt Nat.ModEq.eq_of_lt_of_lt

/-- To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `gcd m c` -/
lemma cancel_left_div_gcd (hm : 0 < m) (h : c * a ≡ c * b [MOD m]) :  a ≡ b [MOD m / gcd m c] := by
  let d := gcd m c
  -- ⊢ a ≡ b [MOD m / gcd m c]
  have hmd := gcd_dvd_left m c
  -- ⊢ a ≡ b [MOD m / gcd m c]
  have hcd := gcd_dvd_right m c
  -- ⊢ a ≡ b [MOD m / gcd m c]
  rw [modEq_iff_dvd]
  -- ⊢ ↑(m / gcd m c) ∣ ↑b - ↑a
  refine' @Int.dvd_of_dvd_mul_right_of_gcd_one (m / d) (c / d) (b - a) _ _
  -- ⊢ ↑m / ↑d ∣ ↑c / ↑d * (↑b - ↑a)
  show (m / d : ℤ) ∣ c / d * (b - a)
  -- ⊢ ↑m / ↑d ∣ ↑c / ↑d * (↑b - ↑a)
  · rw [mul_comm, ← Int.mul_ediv_assoc (b - a) (Int.coe_nat_dvd.mpr hcd), mul_comm]
    -- ⊢ ↑m / ↑d ∣ ↑c * (↑b - ↑a) / ↑(gcd m c)
    apply Int.ediv_dvd_ediv (Int.coe_nat_dvd.mpr hmd)
    -- ⊢ ↑m ∣ ↑c * (↑b - ↑a)
    rw [mul_sub]
    -- ⊢ ↑m ∣ ↑c * ↑b - ↑c * ↑a
    exact modEq_iff_dvd.mp h
    -- 🎉 no goals
  show Int.gcd (m / d) (c / d) = 1
  -- ⊢ Int.gcd (↑m / ↑d) (↑c / ↑d) = 1
  · simp only [← Int.coe_nat_div, Int.coe_nat_gcd (m / d) (c / d), gcd_div hmd hcd,
      Nat.div_self (gcd_pos_of_pos_left c hm)]
#align nat.modeq.cancel_left_div_gcd Nat.ModEq.cancel_left_div_gcd

/-- To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `gcd m c` -/
lemma cancel_right_div_gcd (hm : 0 < m) (h : a * c ≡ b * c [MOD m]) : a ≡ b [MOD m / gcd m c] := by
  apply cancel_left_div_gcd hm
  -- ⊢ c * a ≡ c * b [MOD m]
  simpa [mul_comm] using h
  -- 🎉 no goals
#align nat.modeq.cancel_right_div_gcd Nat.ModEq.cancel_right_div_gcd

lemma cancel_left_div_gcd' (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : c * a ≡ d * b [MOD m]) :
  a ≡ b [MOD m / gcd m c] :=
(h.trans $ hcd.symm.mul_right b).cancel_left_div_gcd hm
#align nat.modeq.cancel_left_div_gcd' Nat.ModEq.cancel_left_div_gcd'

lemma cancel_right_div_gcd' (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : a * c ≡ b * d [MOD m]) :
  a ≡ b [MOD m / gcd m c] :=
(h.trans $ hcd.symm.mul_left b).cancel_right_div_gcd hm
#align nat.modeq.cancel_right_div_gcd' Nat.ModEq.cancel_right_div_gcd'

/-- A common factor that's coprime with the modulus can be cancelled from a `ModEq` -/
lemma cancel_left_of_coprime (hmc : gcd m c = 1) (h : c * a ≡ c * b [MOD m]) : a ≡ b [MOD m] := by
  rcases m.eq_zero_or_pos with (rfl | hm)
  -- ⊢ a ≡ b [MOD 0]
  · simp only [gcd_zero_left] at hmc
    -- ⊢ a ≡ b [MOD 0]
    simp only [gcd_zero_left, hmc, one_mul, modEq_zero_iff] at h
    -- ⊢ a ≡ b [MOD 0]
    subst h
    -- ⊢ a ≡ a [MOD 0]
    rfl
    -- 🎉 no goals
  simpa [hmc] using h.cancel_left_div_gcd hm
  -- 🎉 no goals
#align nat.modeq.cancel_left_of_coprime Nat.ModEq.cancel_left_of_coprime

/-- A common factor that's coprime with the modulus can be cancelled from a `ModEq` -/
lemma cancel_right_of_coprime (hmc : gcd m c = 1) (h : a * c ≡ b * c [MOD m]) : a ≡ b [MOD m] :=
  cancel_left_of_coprime hmc $ by simpa [mul_comm] using h
                                  -- 🎉 no goals
#align nat.modeq.cancel_right_of_coprime Nat.ModEq.cancel_right_of_coprime

end ModEq

/-- The natural number less than `lcm n m` congruent to `a` mod `n` and `b` mod `m` -/
def chineseRemainder' (h : a ≡ b [MOD gcd n m]) : { k // k ≡ a [MOD n] ∧ k ≡ b [MOD m] } :=
  if hn : n = 0 then ⟨a, by rw [hn, gcd_zero_left] at h; constructor; rfl; exact h⟩
                            -- ⊢ a ≡ a [MOD n] ∧ a ≡ b [MOD m]
                                                         -- ⊢ a ≡ a [MOD n]
                                                                      -- ⊢ a ≡ b [MOD m]
                                                                           -- 🎉 no goals
  else
    if hm : m = 0 then ⟨b, by rw [hm, gcd_zero_right] at h; constructor; exact h.symm; rfl⟩
                              -- ⊢ b ≡ a [MOD n] ∧ b ≡ b [MOD m]
                                                            -- ⊢ b ≡ a [MOD n]
                                                                         -- ⊢ b ≡ b [MOD m]
                                                                                       -- 🎉 no goals
    else
      ⟨let (c, d) := xgcd n m; Int.toNat ((n * c * b + m * d * a) / gcd n m % lcm n m), by
        rw [xgcd_val]
        -- ⊢ (match (gcdA n m, gcdB n m) with
        dsimp
        -- ⊢ Int.toNat ((↑n * gcdA n m * ↑b + ↑m * gcdB n m * ↑a) / ↑(gcd n m) % ↑(lcm n  …
        rw [modEq_iff_dvd, modEq_iff_dvd,
          Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.coe_nat_ne_zero.2 (lcm_ne_zero hn hm)))]
        have hnonzero : (gcd n m : ℤ) ≠ 0 := by
          norm_cast
          rw [Nat.gcd_eq_zero_iff, not_and]
          exact fun _ => hm
        have hcoedvd : ∀ t, (gcd n m : ℤ) ∣ t * (b - a) := fun t => h.dvd.mul_left _
        -- ⊢ ↑n ∣ ↑a - (↑n * gcdA n m * ↑b + ↑m * gcdB n m * ↑a) / ↑(gcd n m) % ↑(lcm n m …
        have := gcd_eq_gcd_ab n m
        -- ⊢ ↑n ∣ ↑a - (↑n * gcdA n m * ↑b + ↑m * gcdB n m * ↑a) / ↑(gcd n m) % ↑(lcm n m …
        constructor <;> rw [Int.emod_def, ← sub_add] <;>
        -- ⊢ ↑n ∣ ↑a - (↑n * gcdA n m * ↑b + ↑m * gcdB n m * ↑a) / ↑(gcd n m) % ↑(lcm n m)
                        -- ⊢ ↑n ∣ ↑a - (↑n * gcdA n m * ↑b + ↑m * gcdB n m * ↑a) / ↑(gcd n m) + ↑(lcm n m …
                        -- ⊢ ↑m ∣ ↑b - (↑n * gcdA n m * ↑b + ↑m * gcdB n m * ↑a) / ↑(gcd n m) + ↑(lcm n m …
            refine' dvd_add _ (dvd_mul_of_dvd_left _ _) <;>
            -- ⊢ ↑n ∣ ↑a - (↑n * gcdA n m * ↑b + ↑m * gcdB n m * ↑a) / ↑(gcd n m)
            -- ⊢ ↑m ∣ ↑b - (↑n * gcdA n m * ↑b + ↑m * gcdB n m * ↑a) / ↑(gcd n m)
          try norm_cast
          -- ⊢ ↑n ∣ ↑a - (↑n * gcdA n m * ↑b + ↑m * gcdB n m * ↑a) / ↑(gcd n m)
          -- ⊢ n ∣ lcm n m
          -- ⊢ ↑m ∣ ↑b - (↑n * gcdA n m * ↑b + ↑m * gcdB n m * ↑a) / ↑(gcd n m)
          -- ⊢ m ∣ lcm n m
        · rw [← sub_eq_iff_eq_add'] at this
          -- ⊢ ↑n ∣ ↑a - (↑n * gcdA n m * ↑b + ↑m * gcdB n m * ↑a) / ↑(gcd n m)
          rw [← this, sub_mul, ← add_sub_assoc, add_comm, add_sub_assoc, ← mul_sub,
            Int.add_ediv_of_dvd_left, Int.mul_ediv_cancel_left _ hnonzero,
            Int.mul_ediv_assoc _ h.dvd, ← sub_sub, sub_self, zero_sub, dvd_neg, mul_assoc]
          exact dvd_mul_right _ _
          -- ⊢ ↑(gcd n m) ∣ ↑(gcd n m) * ↑a
          norm_cast
          -- ⊢ gcd n m ∣ gcd n m * a
          exact dvd_mul_right _ _
          -- 🎉 no goals
        · exact dvd_lcm_left n m
          -- 🎉 no goals
        · rw [← sub_eq_iff_eq_add] at this
          -- ⊢ ↑m ∣ ↑b - (↑n * gcdA n m * ↑b + ↑m * gcdB n m * ↑a) / ↑(gcd n m)
          rw [← this, sub_mul, sub_add, ← mul_sub, Int.sub_ediv_of_dvd,
            Int.mul_ediv_cancel_left _ hnonzero, Int.mul_ediv_assoc _ h.dvd, ← sub_add, sub_self,
            zero_add, mul_assoc]
          exact dvd_mul_right _ _
          -- ⊢ ↑(gcd n m) ∣ ↑m * gcdB n m * (↑b - ↑a)
          exact hcoedvd _
          -- 🎉 no goals
        · exact dvd_lcm_right n m⟩
          -- 🎉 no goals
#align nat.chinese_remainder' Nat.chineseRemainder'

/-- The natural number less than `n*m` congruent to `a` mod `n` and `b` mod `m` -/
def chineseRemainder (co : n.coprime m) (a b : ℕ) : { k // k ≡ a [MOD n] ∧ k ≡ b [MOD m] } :=
  chineseRemainder' (by convert @modEq_one a b)
                        -- 🎉 no goals
#align nat.chinese_remainder Nat.chineseRemainder

theorem chineseRemainder'_lt_lcm (h : a ≡ b [MOD gcd n m]) (hn : n ≠ 0) (hm : m ≠ 0) :
    ↑(chineseRemainder' h) < lcm n m := by
  dsimp only [chineseRemainder']
  -- ⊢ ↑(if hn : n = 0 then { val := a, property := (_ : a ≡ a [MOD n] ∧ a ≡ b [MOD …
  rw [dif_neg hn, dif_neg hm, Subtype.coe_mk, xgcd_val, ← Int.toNat_coe_nat (lcm n m)]
  -- ⊢ Int.toNat ((↑n * (gcdA n m, gcdB n m).fst * ↑b + ↑m * (gcdA n m, gcdB n m).s …
  have lcm_pos := Int.coe_nat_pos.mpr (Nat.pos_of_ne_zero (lcm_ne_zero hn hm))
  -- ⊢ Int.toNat ((↑n * (gcdA n m, gcdB n m).fst * ↑b + ↑m * (gcdA n m, gcdB n m).s …
  exact (Int.toNat_lt_toNat lcm_pos).mpr (Int.emod_lt_of_pos _ lcm_pos)
  -- 🎉 no goals
#align nat.chinese_remainder'_lt_lcm Nat.chineseRemainder'_lt_lcm

theorem chineseRemainder_lt_mul (co : n.coprime m) (a b : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    ↑(chineseRemainder co a b) < n * m :=
  lt_of_lt_of_le (chineseRemainder'_lt_lcm _ hn hm) (le_of_eq co.lcm_eq_mul)
#align nat.chinese_remainder_lt_mul Nat.chineseRemainder_lt_mul

theorem modEq_and_modEq_iff_modEq_mul {a b m n : ℕ} (hmn : m.coprime n) :
    a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ a ≡ b [MOD m * n] :=
  ⟨fun h => by
    rw [Nat.modEq_iff_dvd, Nat.modEq_iff_dvd, ← Int.dvd_natAbs, Int.coe_nat_dvd, ← Int.dvd_natAbs,
      Int.coe_nat_dvd] at h
    rw [Nat.modEq_iff_dvd, ← Int.dvd_natAbs, Int.coe_nat_dvd]
    -- ⊢ m * n ∣ Int.natAbs (↑b - ↑a)
    exact hmn.mul_dvd_of_dvd_of_dvd h.1 h.2, fun h =>
    -- 🎉 no goals
    ⟨h.of_mul_right _, h.of_mul_left _⟩⟩
#align nat.modeq_and_modeq_iff_modeq_mul Nat.modEq_and_modEq_iff_modEq_mul

theorem coprime_of_mul_modEq_one (b : ℕ) {a n : ℕ} (h : a * b ≡ 1 [MOD n]) : a.coprime n := by
  obtain ⟨g, hh⟩ := Nat.gcd_dvd_right a n
  -- ⊢ coprime a n
  rw [Nat.coprime_iff_gcd_eq_one, ← Nat.dvd_one, ← Nat.modEq_zero_iff_dvd]
  -- ⊢ 1 ≡ 0 [MOD gcd a n]
  calc
    1 ≡ a * b [MOD a.gcd n] := (hh ▸ h).symm.of_mul_right g
    _ ≡ 0 * b [MOD a.gcd n] := (Nat.modEq_zero_iff_dvd.mpr (Nat.gcd_dvd_left _ _)).mul_right b
    _ = 0 := by rw [zero_mul]
#align nat.coprime_of_mul_modeq_one Nat.coprime_of_mul_modEq_one

@[simp 1100]
theorem mod_mul_right_mod (a b c : ℕ) : a % (b * c) % b = a % b :=
  (mod_modEq _ _).of_mul_right _
#align nat.mod_mul_right_mod Nat.mod_mul_right_mod

@[simp 1100]
theorem mod_mul_left_mod (a b c : ℕ) : a % (b * c) % c = a % c :=
  (mod_modEq _ _).of_mul_left _
#align nat.mod_mul_left_mod Nat.mod_mul_left_mod

theorem div_mod_eq_mod_mul_div (a b c : ℕ) : a / b % c = a % (b * c) / b :=
  if hb0 : b = 0 then by simp [hb0]
                         -- 🎉 no goals
  else by
    rw [← @add_right_cancel_iff _ _ _ (c * (a / b / c)), mod_add_div, Nat.div_div_eq_div_mul, ←
      mul_right_inj' hb0, ← @add_left_cancel_iff _ _ _ (a % b), mod_add_div, mul_add, ←
      @add_left_cancel_iff _ _ _ (a % (b * c) % b), add_left_comm, ← add_assoc (a % (b * c) % b),
      mod_add_div, ← mul_assoc, mod_add_div, mod_mul_right_mod]
#align nat.div_mod_eq_mod_mul_div Nat.div_mod_eq_mod_mul_div

theorem add_mod_add_ite (a b c : ℕ) :
    ((a + b) % c + if c ≤ a % c + b % c then c else 0) = a % c + b % c :=
  have : (a + b) % c = (a % c + b % c) % c := ((mod_modEq _ _).add <| mod_modEq _ _).symm
  if hc0 : c = 0 then by simp [hc0, Nat.mod_zero]
                         -- 🎉 no goals
  else by
    rw [this]
    -- ⊢ ((a % c + b % c) % c + if c ≤ a % c + b % c then c else 0) = a % c + b % c
    split_ifs with h
    -- ⊢ (a % c + b % c) % c + c = a % c + b % c
    · have h2 : (a % c + b % c) / c < 2 :=
        Nat.div_lt_of_lt_mul
          (by
            rw [mul_two]
            exact
              add_lt_add (Nat.mod_lt _ (Nat.pos_of_ne_zero hc0))
                (Nat.mod_lt _ (Nat.pos_of_ne_zero hc0)))
      have h0 : 0 < (a % c + b % c) / c := Nat.div_pos h (Nat.pos_of_ne_zero hc0)
      -- ⊢ (a % c + b % c) % c + c = a % c + b % c
      rw [← @add_right_cancel_iff _ _ _ (c * ((a % c + b % c) / c)), add_comm _ c, add_assoc,
        mod_add_div, le_antisymm (le_of_lt_succ h2) h0, mul_one, add_comm]
    · rw [Nat.mod_eq_of_lt (lt_of_not_ge h), add_zero]
      -- 🎉 no goals
#align nat.add_mod_add_ite Nat.add_mod_add_ite

theorem add_mod_of_add_mod_lt {a b c : ℕ} (hc : a % c + b % c < c) : (a + b) % c = a % c + b % c :=
  by rw [← add_mod_add_ite, if_neg (not_le_of_lt hc), add_zero]
     -- 🎉 no goals
#align nat.add_mod_of_add_mod_lt Nat.add_mod_of_add_mod_lt

theorem add_mod_add_of_le_add_mod {a b c : ℕ} (hc : c ≤ a % c + b % c) :
    (a + b) % c + c = a % c + b % c := by rw [← add_mod_add_ite, if_pos hc]
                                          -- 🎉 no goals
#align nat.add_mod_add_of_le_add_mod Nat.add_mod_add_of_le_add_mod

theorem add_div {a b c : ℕ} (hc0 : 0 < c) :
    (a + b) / c = a / c + b / c + if c ≤ a % c + b % c then 1 else 0 := by
  rw [← mul_right_inj' hc0.ne', ← @add_left_cancel_iff _ _ _ ((a + b) % c + a % c + b % c)]
  -- ⊢ (a + b) % c + a % c + b % c + c * ((a + b) / c) = (a + b) % c + a % c + b %  …
  suffices
    (a + b) % c + c * ((a + b) / c) + a % c + b % c =
      (a % c + c * (a / c) + (b % c + c * (b / c)) + c * if c ≤ a % c + b % c then 1 else 0) +
        (a + b) % c
    by simpa only [mul_add, add_comm, add_left_comm, add_assoc]
  rw [mod_add_div, mod_add_div, mod_add_div, mul_ite, add_assoc, add_assoc]
  -- ⊢ a + (b + (a % c + b % c)) = (a + b + if c ≤ a % c + b % c then c * 1 else c  …
  conv_lhs => rw [← add_mod_add_ite]
  -- ⊢ a + (b + ((a + b) % c + if c ≤ a % c + b % c then c else 0)) = (a + b + if c …
  simp
  -- ⊢ a + (b + ((a + b) % c + if c ≤ a % c + b % c then c else 0)) = (a + b + if c …
  ac_rfl
  -- 🎉 no goals
#align nat.add_div Nat.add_div

theorem add_div_eq_of_add_mod_lt {a b c : ℕ} (hc : a % c + b % c < c) :
    (a + b) / c = a / c + b / c :=
  if hc0 : c = 0 then by simp [hc0]
                         -- 🎉 no goals
  else by rw [add_div (Nat.pos_of_ne_zero hc0), if_neg (not_le_of_lt hc), add_zero]
          -- 🎉 no goals
#align nat.add_div_eq_of_add_mod_lt Nat.add_div_eq_of_add_mod_lt

protected theorem add_div_of_dvd_right {a b c : ℕ} (hca : c ∣ a) : (a + b) / c = a / c + b / c :=
  if h : c = 0 then by simp [h]
                       -- 🎉 no goals
  else
    add_div_eq_of_add_mod_lt
      (by
        rw [Nat.mod_eq_zero_of_dvd hca, zero_add]
        -- ⊢ b % c < c
        exact Nat.mod_lt _ (pos_iff_ne_zero.mpr h))
        -- 🎉 no goals
#align nat.add_div_of_dvd_right Nat.add_div_of_dvd_right

protected theorem add_div_of_dvd_left {a b c : ℕ} (hca : c ∣ b) : (a + b) / c = a / c + b / c := by
  rwa [add_comm, Nat.add_div_of_dvd_right, add_comm]
  -- 🎉 no goals
#align nat.add_div_of_dvd_left Nat.add_div_of_dvd_left

theorem add_div_eq_of_le_mod_add_mod {a b c : ℕ} (hc : c ≤ a % c + b % c) (hc0 : 0 < c) :
    (a + b) / c = a / c + b / c + 1 := by rw [add_div hc0, if_pos hc]
                                          -- 🎉 no goals
#align nat.add_div_eq_of_le_mod_add_mod Nat.add_div_eq_of_le_mod_add_mod

theorem add_div_le_add_div (a b c : ℕ) : a / c + b / c ≤ (a + b) / c :=
  if hc0 : c = 0 then by simp [hc0]
                         -- 🎉 no goals
  else by rw [Nat.add_div (Nat.pos_of_ne_zero hc0)]; exact Nat.le_add_right _ _
          -- ⊢ a / c + b / c ≤ a / c + b / c + if c ≤ a % c + b % c then 1 else 0
                                                     -- 🎉 no goals
#align nat.add_div_le_add_div Nat.add_div_le_add_div

theorem le_mod_add_mod_of_dvd_add_of_not_dvd {a b c : ℕ} (h : c ∣ a + b) (ha : ¬c ∣ a) :
    c ≤ a % c + b % c :=
  by_contradiction fun hc => by
    have : (a + b) % c = a % c + b % c := add_mod_of_add_mod_lt (lt_of_not_ge hc)
    -- ⊢ False
    simp_all [dvd_iff_mod_eq_zero]
    -- 🎉 no goals
#align nat.le_mod_add_mod_of_dvd_add_of_not_dvd Nat.le_mod_add_mod_of_dvd_add_of_not_dvd

theorem odd_mul_odd {n m : ℕ} : n % 2 = 1 → m % 2 = 1 → n * m % 2 = 1 := by
  simpa [Nat.ModEq] using @ModEq.mul 2 n 1 m 1
  -- 🎉 no goals
#align nat.odd_mul_odd Nat.odd_mul_odd

theorem odd_mul_odd_div_two {m n : ℕ} (hm1 : m % 2 = 1) (hn1 : n % 2 = 1) :
    m * n / 2 = m * (n / 2) + m / 2 :=
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by simp_all
                                                     -- 🎉 no goals
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by simp_all
                                                     -- 🎉 no goals
  mul_right_injective₀ two_ne_zero <| by
    dsimp
    -- ⊢ 2 * (m * n / 2) = 2 * (m * (n / 2) + m / 2)
    rw [mul_add, two_mul_odd_div_two hm1, mul_left_comm, two_mul_odd_div_two hn1,
      two_mul_odd_div_two (Nat.odd_mul_odd hm1 hn1), mul_tsub, mul_one, ←
      add_tsub_assoc_of_le (succ_le_of_lt hm0),
      tsub_add_cancel_of_le (le_mul_of_one_le_right (Nat.zero_le _) hn0)]
#align nat.odd_mul_odd_div_two Nat.odd_mul_odd_div_two

theorem odd_of_mod_four_eq_one {n : ℕ} : n % 4 = 1 → n % 2 = 1 := by
  simpa [ModEq, show 2 * 2 = 4 by norm_num] using @ModEq.of_mul_left 2 n 1 2
  -- 🎉 no goals
#align nat.odd_of_mod_four_eq_one Nat.odd_of_mod_four_eq_one

theorem odd_of_mod_four_eq_three {n : ℕ} : n % 4 = 3 → n % 2 = 1 := by
  simpa [ModEq, show 2 * 2 = 4 by norm_num, show 3 % 4 = 3 by norm_num] using
    @ModEq.of_mul_left 2 n 3 2
#align nat.odd_of_mod_four_eq_three Nat.odd_of_mod_four_eq_three

/-- A natural number is odd iff it has residue `1` or `3` mod `4`-/
theorem odd_mod_four_iff {n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3 :=
  have help : ∀ m : ℕ, m < 4 → m % 2 = 1 → m = 1 ∨ m = 3 := by decide
                                                               -- 🎉 no goals
  ⟨fun hn =>
    help (n % 4) (mod_lt n (by norm_num)) <| (mod_mod_of_dvd n (by norm_num : 2 ∣ 4)).trans hn,
                               -- 🎉 no goals
                                                                   -- 🎉 no goals
    fun h => Or.elim h odd_of_mod_four_eq_one odd_of_mod_four_eq_three⟩
#align nat.odd_mod_four_iff Nat.odd_mod_four_iff

end Nat
