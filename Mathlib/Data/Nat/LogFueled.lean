/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Data.Nat.Log

/-!
# Fueled version of natural numbers logarithms

(Draft)

-/

assert_not_exists OrderTop

namespace Nat

theorem le_pow_self (b n : ℕ) (hb : 2 ≤ b) : n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n h =>
    rw [Nat.pow_succ]
    apply le_trans (b := b ^ n * 2)
    · rw [Nat.mul_two]
      exact add_le_add h (one_le_pow _ _ (zero_lt_of_lt hb))
    exact mul_le_mul_left _ hb

lemma clog_fueled_lt (fuel b n : ℕ) (hn : 2 ≤ n) (hb : 2 ≤ b) :
    (n + b - 1) / b < n := by
  rw [Nat.div_lt_iff_lt_mul (zero_lt_of_lt hb)]
  apply Nat.sub_one_lt_of_le
  · apply lt_of_lt_of_le Nat.zero_lt_two
    rw [Nat.add_comm]
    apply Nat.le_add_right_of_le hb
  · exact Nat.add_le_mul hn hb

lemma clog_fueled_le (fuel b n : ℕ) (h : n ≤ b ^ (fuel + 1)) :
    (n + b - 1) / b ≤ b ^ fuel := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · simp [hb]
  · rw [Nat.div_le_iff_le_mul hb]
    apply Nat.sub_le_sub_right
    apply Nat.add_le_add_right
    rwa [← Nat.pow_succ]

def clog_fueled (b n : ℕ) : ℕ :=
  if hb : b ≤ 1 then 0
  else
  let rec go (fuel : ℕ) (b : ℕ) (hb : 2 ≤ b) (a n : ℕ) (h : n ≤ b ^ fuel) : ℕ :=
  match fuel with
  | 0 => a
  | fuel + 1 =>
    if n ≤ 1
      then a
      else go fuel b hb
        (a + 1) ((n + b - 1) / b)
        (clog_fueled_le fuel b n h)
  go n b (not_le.mp hb) 0 n (Nat.le_pow_self _ _ (not_le.mp hb))

theorem clog_fueled_of_left_le_one {b n : ℕ} (hb : b ≤ 1) :
    clog_fueled b n = 0 := by
  simp [clog_fueled, dif_pos hb]

variable {b : ℕ} (hb : 2 ≤ b)

theorem clog_fueled.go_eq_of_zero (fuel : ℕ) (a n : ℕ) (h : n ≤ b ^ fuel) :
    fuel = 0 → clog_fueled.go fuel b hb a n h = a := by
  intro h0
  simp_rw [h0, go]

theorem clog_fueled.go_eq_of_succ_of_le_one
    (fuel : ℕ) (a n : ℕ) (h : n ≤ b ^ (fuel + 1)) (hn : n ≤ 1) :
    clog_fueled.go (fuel + 1) b hb a n h = a := by
  simp_rw [go, if_pos hn]

theorem clog_fueled.go_eq_of_le_one
    (fuel : ℕ) (a n : ℕ) (h : n ≤ b ^ fuel) (hn : n ≤ 1) :
    clog_fueled.go fuel b hb a n h = a :=
  match fuel with
  | 0 => by rw [clog_fueled.go_eq_of_zero]; rfl
  | fuel + 1 => by
    rw [clog_fueled.go_eq_of_succ_of_le_one (hn := hn)]

theorem clog_fueled.go_eq_of_succ_of_one_lt
    (fuel : ℕ) (a n : ℕ) (h : n ≤ b ^ (fuel + 1)) (hn : 1 < n) :
    clog_fueled.go (fuel + 1) b hb a n h =
      clog_fueled.go fuel b hb (a + 1) ((n + b - 1) / b) (clog_fueled_le fuel b n h) := by
  simp_rw [go, if_neg (not_le.mpr hn)]

theorem clog_fueled.go_eq_add_of_zero
    (fuel : ℕ) (a n : ℕ) (h : n ≤ b ^ fuel) :
    clog_fueled.go fuel b hb a n h = clog_fueled.go fuel b hb 0 n h + a := by
  induction n using Nat.strong_induction_on generalizing fuel a with
  | h n ind =>
    by_cases hn : n ≤ 1
    · simp [clog_fueled.go_eq_of_le_one (hn := hn)]
    · have hfuel : fuel ≠ 0 := fun hf ↦ hn (by
        rwa [hf, Nat.pow_zero] at h)
      obtain ⟨fuel, rfl⟩ := exists_eq_succ_of_ne_zero hfuel
      simp only [clog_fueled.go, if_neg hn]
      have hlt : ((n + b - 1) / b) < n := by
        refine clog_fueled_lt b b n ?_ hb
        rwa [not_le] at hn
      rw [ind ((n + b - 1)/ b) hlt fuel _ (clog_fueled_le fuel b n h)]
      rw [ind ((n + b - 1)/ b) hlt fuel 1 (clog_fueled_le fuel b n h)]
      rw [Nat.succ_add_eq_add_succ]

theorem clog_fueled_of_right_le_one {b n : ℕ} (hn : n ≤ 1) :
    clog_fueled b n = 0 := by
  by_cases hb : b ≤ 1
  · rw [clog_fueled_of_left_le_one hb]
  · simp [clog_fueled, dif_pos hb]
    intro hb
    match n with
    | 0 => apply clog_fueled.go_eq_of_zero; rfl
    | n + 1 => simp_rw [clog_fueled.go, if_pos hn]

theorem clog_fueled.go_no_fuel
    (f f') {b a n : ℕ}(hb : 2 ≤ b) (hn : n ≤ b ^ f) (hn' : n ≤ b ^ f') :
    clog_fueled.go f b hb a n hn = clog_fueled.go f' b hb a n hn' := by
  induction n using Nat.strong_induction_on generalizing a f f' with
  | h n ind =>
    by_cases hn1 : n ≤ 1
    · simp [clog_fueled.go_eq_of_le_one (hn := hn1)]
    · have hf : f ≠ 0 := fun hf ↦ hn1 (by
        rwa [hf, Nat.pow_zero] at hn)
      have hf' : f' ≠ 0 := fun hf ↦ hn1 (by
        rwa [hf, Nat.pow_zero] at hn')
      obtain ⟨f, rfl⟩ := exists_eq_succ_of_ne_zero hf
      obtain ⟨f', rfl⟩ := exists_eq_succ_of_ne_zero hf'
      simp only [clog_fueled.go, if_neg hn1]
      rw [not_le] at hn1
      rw [ind ((n + b - 1)/ b) (clog_fueled_lt b b n hn1 hb) f f']

theorem clog_fueled_of_two_le {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) :
    clog_fueled b n = clog_fueled b ((n + b - 1) / b) + 1 := by
  simp only [clog_fueled, dif_neg (not_le_of_lt hb)]
  obtain ⟨n, rfl⟩ :=
    exists_eq_add_one_of_ne_zero (Nat.ne_zero_of_lt hn)
  rw [clog_fueled.go, if_neg (Nat.not_le_of_lt hn)]
  rw [clog_fueled.go_eq_add_of_zero]
  simp
  apply clog_fueled.go_no_fuel

theorem clog_fueled_eq_clog (b n : ℕ) :
    clog_fueled b n = clog b n :=  by
  by_cases hb : b ≤ 1
  · rw [Nat.clog_of_left_le_one hb]
    rw [Nat.clog_fueled_of_left_le_one hb]
  replace hb : 2 ≤ b := gt_of_not_le hb
  induction n using Nat.strong_induction_on with
  | h n ind =>
    by_cases hn : n ≤ 1
    · rw [clog_fueled_of_right_le_one hn, clog_of_right_le_one hn]
    · replace hn : 2 ≤ n := gt_of_not_le hn
      rw [clog_of_two_le hb hn]
      rw [clog_fueled_of_two_le hb hn]
      apply congr_arg₂ _ _ rfl
      apply ind
      exact clog_fueled_lt b b n hn hb

section Tests

set_option linter.style.longLine false
set_option linter.style.setOption false

set_option trace.profiler true

-- 0.046
#eval clog_fueled 2 123456789012345667890123456789012345667890123456789012345667890123456789012345667890

-- max recursion depth is reached
example : clog_fueled 2 123456789012345667890123456789012345667890123456789012345667890123456789012345667890 = 277 := rfl

-- 900 steps are enough
set_option maxRecDepth 900 in
example : clog_fueled 2 123456789012345667890123456789012345667890123456789012345667890123456789012345667890 = 277 := rfl


-- 0.0450
#eval clog_fueled 2 123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890
-- = 556

set_option maxRecDepth 5200 in
example : clog' 2 123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890 = 556 := rfl

set_option maxRecDepth 5200 in
#reduce clog_fueled 2 123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890

set_option maxRecDepth 1700 in
example : clog_fueled 2 123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890 = 556 := rfl

-- 0.042
#eval logC 2 123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890123456789012345667890
-- = 555

end Tests

end Nat
