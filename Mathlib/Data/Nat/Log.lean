/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yaël Dillies
-/
import Mathlib.Data.Nat.Pow

#align_import data.nat.log from "leanprover-community/mathlib"@"3e00d81bdcbf77c8188bbd18f5524ddc3ed8cac6"

/-!
# Natural number logarithms

This file defines two `ℕ`-valued analogs of the logarithm of `n` with base `b`:
* `log b n`: Lower logarithm, or floor **log**. Greatest `k` such that `b^k ≤ n`.
* `clog b n`: Upper logarithm, or **c**eil **log**. Least `k` such that `n ≤ b^k`.

These are interesting because, for `1 < b`, `Nat.log b` and `Nat.clog b` are respectively right and
left adjoints of `Nat.pow b`. See `pow_le_iff_le_log` and `le_pow_iff_clog_le`.
-/


namespace Nat

/-! ### Floor logarithm -/


/-- `log b n`, is the logarithm of natural number `n` in base `b`. It returns the largest `k : ℕ`
such that `b^k ≤ n`, so if `b^k = n`, it returns exactly `k`. -/
--@[pp_nodot] porting note: unknown attribute
def log (b : ℕ) : ℕ → ℕ
  | n =>
    if h : b ≤ n ∧ 1 < b then
      have : n / b < n := div_lt_self ((zero_lt_one.trans h.2).trans_le h.1) h.2
      log b (n / b) + 1
    else 0
#align nat.log Nat.log

@[simp]
theorem log_eq_zero_iff {b n : ℕ} : log b n = 0 ↔ n < b ∨ b ≤ 1 := by
  rw [log, dite_eq_right_iff]
  -- ⊢ (∀ (h : b ≤ n ∧ 1 < b),
  simp only [Nat.succ_ne_zero, imp_false, not_and_or, not_le, not_lt]
  -- 🎉 no goals
#align nat.log_eq_zero_iff Nat.log_eq_zero_iff

theorem log_of_lt {b n : ℕ} (hb : n < b) : log b n = 0 :=
  log_eq_zero_iff.2 (Or.inl hb)
#align nat.log_of_lt Nat.log_of_lt

theorem log_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n) : log b n = 0 :=
  log_eq_zero_iff.2 (Or.inr hb)
#align nat.log_of_left_le_one Nat.log_of_left_le_one

@[simp]
theorem log_pos_iff {b n : ℕ} : 0 < log b n ↔ b ≤ n ∧ 1 < b := by
  rw [pos_iff_ne_zero, Ne.def, log_eq_zero_iff, not_or, not_lt, not_le]
  -- 🎉 no goals
#align nat.log_pos_iff Nat.log_pos_iff

theorem log_pos {b n : ℕ} (hb : 1 < b) (hbn : b ≤ n) : 0 < log b n :=
  log_pos_iff.2 ⟨hbn, hb⟩
#align nat.log_pos Nat.log_pos

theorem log_of_one_lt_of_le {b n : ℕ} (h : 1 < b) (hn : b ≤ n) : log b n = log b (n / b) + 1 := by
  rw [log]
  -- ⊢ (if h : b ≤ n ∧ 1 < b then
  exact if_pos ⟨hn, h⟩
  -- 🎉 no goals
#align nat.log_of_one_lt_of_le Nat.log_of_one_lt_of_le

@[simp]
theorem log_zero_left : ∀ n, log 0 n = 0 :=
  log_of_left_le_one zero_le_one
#align nat.log_zero_left Nat.log_zero_left

@[simp]
theorem log_zero_right (b : ℕ) : log b 0 = 0 :=
  log_eq_zero_iff.2 (le_total 1 b)
#align nat.log_zero_right Nat.log_zero_right

@[simp]
theorem log_one_left : ∀ n, log 1 n = 0 :=
  log_of_left_le_one le_rfl
#align nat.log_one_left Nat.log_one_left

@[simp]
theorem log_one_right (b : ℕ) : log b 1 = 0 :=
  log_eq_zero_iff.2 (lt_or_le _ _)
#align nat.log_one_right Nat.log_one_right

/-- `pow b` and `log b` (almost) form a Galois connection. See also `Nat.pow_le_of_le_log` and
`Nat.le_log_of_pow_le` for individual implications under weaker assumptions. -/
theorem pow_le_iff_le_log {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) :
    b ^ x ≤ y ↔ x ≤ log b y := by
  induction' y using Nat.strong_induction_on with y ih generalizing x
  -- ⊢ b ^ x ≤ y ↔ x ≤ log b y
  cases x with
  | zero => exact iff_of_true hy.bot_lt (zero_le _)
  | succ x =>
    rw [log]; split_ifs with h
    · have b_pos : 0 < b := zero_le_one.trans_lt hb
      rw [succ_eq_add_one, add_le_add_iff_right, ←
        ih (y / b) (div_lt_self hy.bot_lt hb) (Nat.div_pos h.1 b_pos).ne', le_div_iff_mul_le b_pos,
        pow_succ', mul_comm]
    · exact iff_of_false (fun hby => h ⟨(le_self_pow x.succ_ne_zero _).trans hby, hb⟩)
        (not_succ_le_zero _)
#align nat.pow_le_iff_le_log Nat.pow_le_iff_le_log

theorem lt_pow_iff_log_lt {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) : y < b ^ x ↔ log b y < x :=
  lt_iff_lt_of_le_iff_le (pow_le_iff_le_log hb hy)
#align nat.lt_pow_iff_log_lt Nat.lt_pow_iff_log_lt

theorem pow_le_of_le_log {b x y : ℕ} (hy : y ≠ 0) (h : x ≤ log b y) : b ^ x ≤ y := by
  refine' (le_or_lt b 1).elim (fun hb => _) fun hb => (pow_le_iff_le_log hb hy).2 h
  -- ⊢ b ^ x ≤ y
  rw [log_of_left_le_one hb, nonpos_iff_eq_zero] at h
  -- ⊢ b ^ x ≤ y
  rwa [h, pow_zero, one_le_iff_ne_zero]
  -- 🎉 no goals
#align nat.pow_le_of_le_log Nat.pow_le_of_le_log

theorem le_log_of_pow_le {b x y : ℕ} (hb : 1 < b) (h : b ^ x ≤ y) : x ≤ log b y := by
  rcases ne_or_eq y 0 with (hy | rfl)
  -- ⊢ x ≤ log b y
  exacts [(pow_le_iff_le_log hb hy).1 h, (h.not_lt (pow_pos (zero_lt_one.trans hb) _)).elim]
  -- 🎉 no goals
#align nat.le_log_of_pow_le Nat.le_log_of_pow_le

theorem pow_log_le_self (b : ℕ) {x : ℕ} (hx : x ≠ 0) : b ^ log b x ≤ x :=
  pow_le_of_le_log hx le_rfl
#align nat.pow_log_le_self Nat.pow_log_le_self

theorem log_lt_of_lt_pow {b x y : ℕ} (hy : y ≠ 0) : y < b ^ x → log b y < x :=
  lt_imp_lt_of_le_imp_le (pow_le_of_le_log hy)
#align nat.log_lt_of_lt_pow Nat.log_lt_of_lt_pow

theorem lt_pow_of_log_lt {b x y : ℕ} (hb : 1 < b) : log b y < x → y < b ^ x :=
  lt_imp_lt_of_le_imp_le (le_log_of_pow_le hb)
#align nat.lt_pow_of_log_lt Nat.lt_pow_of_log_lt

theorem lt_pow_succ_log_self {b : ℕ} (hb : 1 < b) (x : ℕ) : x < b ^ (log b x).succ :=
  lt_pow_of_log_lt hb (lt_succ_self _)
#align nat.lt_pow_succ_log_self Nat.lt_pow_succ_log_self

theorem log_eq_iff {b m n : ℕ} (h : m ≠ 0 ∨ 1 < b ∧ n ≠ 0) :
    log b n = m ↔ b ^ m ≤ n ∧ n < b ^ (m + 1) := by
  rcases em (1 < b ∧ n ≠ 0) with (⟨hb, hn⟩ | hbn)
  -- ⊢ log b n = m ↔ b ^ m ≤ n ∧ n < b ^ (m + 1)
  · rw [le_antisymm_iff, ← lt_succ_iff, ← pow_le_iff_le_log, ← lt_pow_iff_log_lt, and_comm] <;>
      assumption
      -- 🎉 no goals
      -- 🎉 no goals
      -- 🎉 no goals
      -- 🎉 no goals
  · have hm : m ≠ 0 := h.resolve_right hbn
    -- ⊢ log b n = m ↔ b ^ m ≤ n ∧ n < b ^ (m + 1)
    rw [not_and_or, not_lt, Ne.def, not_not] at hbn
    -- ⊢ log b n = m ↔ b ^ m ≤ n ∧ n < b ^ (m + 1)
    rcases hbn with (hb | rfl)
    -- ⊢ log b n = m ↔ b ^ m ≤ n ∧ n < b ^ (m + 1)
    · simpa only [log_of_left_le_one hb, hm.symm, false_iff_iff, not_and, not_lt] using
        le_trans (pow_le_pow_of_le_one' hb m.le_succ)
    · simpa only [log_zero_right, hm.symm, nonpos_iff_eq_zero, false_iff, not_and, not_lt,
        add_pos_iff, or_true, pow_eq_zero_iff] using pow_eq_zero
#align nat.log_eq_iff Nat.log_eq_iff

theorem log_eq_of_pow_le_of_lt_pow {b m n : ℕ} (h₁ : b ^ m ≤ n) (h₂ : n < b ^ (m + 1)) :
    log b n = m := by
  rcases eq_or_ne m 0 with (rfl | hm)
  -- ⊢ log b n = 0
  · rw [pow_one] at h₂
    -- ⊢ log b n = 0
    exact log_of_lt h₂
    -- 🎉 no goals
  · exact (log_eq_iff (Or.inl hm)).2 ⟨h₁, h₂⟩
    -- 🎉 no goals
#align nat.log_eq_of_pow_le_of_lt_pow Nat.log_eq_of_pow_le_of_lt_pow

theorem log_pow {b : ℕ} (hb : 1 < b) (x : ℕ) : log b (b ^ x) = x :=
  log_eq_of_pow_le_of_lt_pow le_rfl (pow_lt_pow hb x.lt_succ_self)
#align nat.log_pow Nat.log_pow

theorem log_eq_one_iff' {b n : ℕ} : log b n = 1 ↔ b ≤ n ∧ n < b * b := by
  rw [log_eq_iff (Or.inl one_ne_zero), pow_add, pow_one]
  -- 🎉 no goals
#align nat.log_eq_one_iff' Nat.log_eq_one_iff'

theorem log_eq_one_iff {b n : ℕ} : log b n = 1 ↔ n < b * b ∧ 1 < b ∧ b ≤ n :=
  log_eq_one_iff'.trans
    ⟨fun h => ⟨h.2, lt_mul_self_iff.1 (h.1.trans_lt h.2), h.1⟩, fun h => ⟨h.2.2, h.1⟩⟩
#align nat.log_eq_one_iff Nat.log_eq_one_iff

theorem log_mul_base {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) : log b (n * b) = log b n + 1 := by
  apply log_eq_of_pow_le_of_lt_pow <;> rw [pow_succ', mul_comm b]
  -- ⊢ b ^ (log b n + 1) ≤ n * b
                                       -- ⊢ b ^ log b n * b ≤ n * b
                                       -- ⊢ n * b < b ^ (log b n + 1) * b
  exacts [mul_le_mul_right' (pow_log_le_self _ hn) _,
    (mul_lt_mul_right (zero_lt_one.trans hb)).2 (lt_pow_succ_log_self hb _)]
#align nat.log_mul_base Nat.log_mul_base

theorem pow_log_le_add_one (b : ℕ) : ∀ x, b ^ log b x ≤ x + 1
  | 0 => by rw [log_zero_right, pow_zero]
            -- 🎉 no goals
  | x + 1 => (pow_log_le_self b x.succ_ne_zero).trans (x + 1).le_succ
#align nat.pow_log_le_add_one Nat.pow_log_le_add_one

theorem log_monotone {b : ℕ} : Monotone (log b) := by
  refine' monotone_nat_of_le_succ fun n => _
  -- ⊢ log b n ≤ log b (n + 1)
  cases' le_or_lt b 1 with hb hb
  -- ⊢ log b n ≤ log b (n + 1)
  · rw [log_of_left_le_one hb]
    -- ⊢ 0 ≤ log b (n + 1)
    exact zero_le _
    -- 🎉 no goals
  · exact le_log_of_pow_le hb (pow_log_le_add_one _ _)
    -- 🎉 no goals
#align nat.log_monotone Nat.log_monotone

@[mono]
theorem log_mono_right {b n m : ℕ} (h : n ≤ m) : log b n ≤ log b m :=
  log_monotone h
#align nat.log_mono_right Nat.log_mono_right

@[mono]
theorem log_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : log b n ≤ log c n := by
  rcases eq_or_ne n 0 with (rfl | hn); · rw [log_zero_right, log_zero_right]
  -- ⊢ log b 0 ≤ log c 0
                                         -- 🎉 no goals
  apply le_log_of_pow_le hc
  -- ⊢ c ^ log b n ≤ n
  calc
    c ^ log b n ≤ b ^ log b n := pow_le_pow_of_le_left' hb _
    _ ≤ n := pow_log_le_self _ hn
#align nat.log_anti_left Nat.log_anti_left

theorem log_antitone_left {n : ℕ} : AntitoneOn (fun b => log b n) (Set.Ioi 1) := fun _ hc _ _ hb =>
  log_anti_left (Set.mem_Iio.1 hc) hb
#align nat.log_antitone_left Nat.log_antitone_left

@[simp]
theorem log_div_base (b n : ℕ) : log b (n / b) = log b n - 1 := by
  cases' le_or_lt b 1 with hb hb
  -- ⊢ log b (n / b) = log b n - 1
  · rw [log_of_left_le_one hb, log_of_left_le_one hb, Nat.zero_sub]
    -- 🎉 no goals
  cases' lt_or_le n b with h h
  -- ⊢ log b (n / b) = log b n - 1
  · rw [div_eq_of_lt h, log_of_lt h, log_zero_right]
    -- 🎉 no goals
  rw [log_of_one_lt_of_le hb h, add_tsub_cancel_right]
  -- 🎉 no goals
#align nat.log_div_base Nat.log_div_base

@[simp]
theorem log_div_mul_self (b n : ℕ) : log b (n / b * b) = log b n := by
  cases' le_or_lt b 1 with hb hb
  -- ⊢ log b (n / b * b) = log b n
  · rw [log_of_left_le_one hb, log_of_left_le_one hb]
    -- 🎉 no goals
  cases' lt_or_le n b with h h
  -- ⊢ log b (n / b * b) = log b n
  · rw [div_eq_of_lt h, zero_mul, log_zero_right, log_of_lt h]
    -- 🎉 no goals
  rw [log_mul_base hb (Nat.div_pos h (zero_le_one.trans_lt hb)).ne', log_div_base,
    tsub_add_cancel_of_le (succ_le_iff.2 <| log_pos hb h)]
#align nat.log_div_mul_self Nat.log_div_mul_self

theorem add_pred_div_lt {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : (n + b - 1) / b < n := by
  rw [div_lt_iff_lt_mul (zero_lt_one.trans hb), ← succ_le_iff, ← pred_eq_sub_one,
    succ_pred_eq_of_pos (add_pos (zero_lt_one.trans hn) (zero_lt_one.trans hb))]
  exact add_le_mul hn hb
  -- 🎉 no goals
-- Porting note: Was private in mathlib 3
-- #align nat.add_pred_div_lt Nat.add_pred_div_lt

/-! ### Ceil logarithm -/


/-- `clog b n`, is the upper logarithm of natural number `n` in base `b`. It returns the smallest
`k : ℕ` such that `n ≤ b^k`, so if `b^k = n`, it returns exactly `k`. -/
--@[pp_nodot]
def clog (b : ℕ) : ℕ → ℕ
  | n =>
    if h : 1 < b ∧ 1 < n then
      have : (n + b - 1) / b < n := add_pred_div_lt h.1 h.2
      clog b ((n + b - 1) / b) + 1
    else 0
#align nat.clog Nat.clog

theorem clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n : ℕ) : clog b n = 0 := by
  rw [clog, dif_neg fun h : 1 < b ∧ 1 < n => h.1.not_le hb]
  -- 🎉 no goals
#align nat.clog_of_left_le_one Nat.clog_of_left_le_one

theorem clog_of_right_le_one {n : ℕ} (hn : n ≤ 1) (b : ℕ) : clog b n = 0 := by
  rw [clog, dif_neg fun h : 1 < b ∧ 1 < n => h.2.not_le hn]
  -- 🎉 no goals
#align nat.clog_of_right_le_one Nat.clog_of_right_le_one

@[simp]
theorem clog_zero_left (n : ℕ) : clog 0 n = 0 :=
  clog_of_left_le_one zero_le_one _
#align nat.clog_zero_left Nat.clog_zero_left

@[simp]
theorem clog_zero_right (b : ℕ) : clog b 0 = 0 :=
  clog_of_right_le_one zero_le_one _
#align nat.clog_zero_right Nat.clog_zero_right

@[simp]
theorem clog_one_left (n : ℕ) : clog 1 n = 0 :=
  clog_of_left_le_one le_rfl _
#align nat.clog_one_left Nat.clog_one_left

@[simp]
theorem clog_one_right (b : ℕ) : clog b 1 = 0 :=
  clog_of_right_le_one le_rfl _
#align nat.clog_one_right Nat.clog_one_right

theorem clog_of_two_le {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) :
    clog b n = clog b ((n + b - 1) / b) + 1 := by rw [clog, dif_pos (⟨hb, hn⟩ : 1 < b ∧ 1 < n)]
                                                  -- 🎉 no goals
#align nat.clog_of_two_le Nat.clog_of_two_le

theorem clog_pos {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : 0 < clog b n := by
  rw [clog_of_two_le hb hn]
  -- ⊢ 0 < clog b ((n + b - 1) / b) + 1
  exact zero_lt_succ _
  -- 🎉 no goals
#align nat.clog_pos Nat.clog_pos

theorem clog_eq_one {b n : ℕ} (hn : 2 ≤ n) (h : n ≤ b) : clog b n = 1 := by
  rw [clog_of_two_le (hn.trans h) hn, clog_of_right_le_one]
  -- ⊢ (n + b - 1) / b ≤ 1
  have n_pos : 0 < n := (zero_lt_two' ℕ).trans_le hn
  -- ⊢ (n + b - 1) / b ≤ 1
  rw [← lt_succ_iff, Nat.div_lt_iff_lt_mul (n_pos.trans_le h), ← succ_le_iff, ← pred_eq_sub_one,
    succ_pred_eq_of_pos (add_pos n_pos (n_pos.trans_le h)), succ_mul, one_mul]
  exact add_le_add_right h _
  -- 🎉 no goals
#align nat.clog_eq_one Nat.clog_eq_one

/-- `clog b` and `pow b` form a Galois connection. -/
theorem le_pow_iff_clog_le {b : ℕ} (hb : 1 < b) {x y : ℕ} : x ≤ b ^ y ↔ clog b x ≤ y := by
  induction' x using Nat.strong_induction_on with x ih generalizing y
  -- ⊢ x ≤ b ^ y ↔ clog b x ≤ y
  cases y
  -- ⊢ x ≤ b ^ zero ↔ clog b x ≤ zero
  · rw [pow_zero]
    -- ⊢ x ≤ 1 ↔ clog b x ≤ zero
    refine' ⟨fun h => (clog_of_right_le_one h b).le, _⟩
    -- ⊢ clog b x ≤ zero → x ≤ 1
    simp_rw [← not_lt]
    -- ⊢ ¬zero < clog b x → ¬1 < x
    contrapose!
    -- ⊢ 1 < x → zero < clog b x
    exact clog_pos hb
    -- 🎉 no goals
  have b_pos : 0 < b := (zero_lt_one' ℕ).trans hb
  -- ⊢ x ≤ b ^ succ n✝ ↔ clog b x ≤ succ n✝
  rw [clog]; split_ifs with h
  -- ⊢ x ≤ b ^ succ n✝ ↔
             -- ⊢ x ≤ b ^ succ n✝ ↔
  · rw [succ_eq_add_one, add_le_add_iff_right, ← ih ((x + b - 1) / b) (add_pred_div_lt hb h.2),
      Nat.div_le_iff_le_mul_add_pred b_pos, mul_comm b, ← pow_succ,
      add_tsub_assoc_of_le (Nat.succ_le_of_lt b_pos), add_le_add_iff_right]
  · exact iff_of_true ((not_lt.1 (not_and.1 h hb)).trans <| succ_le_of_lt <| pow_pos b_pos _)
      (zero_le _)
#align nat.le_pow_iff_clog_le Nat.le_pow_iff_clog_le

theorem pow_lt_iff_lt_clog {b : ℕ} (hb : 1 < b) {x y : ℕ} : b ^ y < x ↔ y < clog b x :=
  lt_iff_lt_of_le_iff_le (le_pow_iff_clog_le hb)
#align nat.pow_lt_iff_lt_clog Nat.pow_lt_iff_lt_clog

theorem clog_pow (b x : ℕ) (hb : 1 < b) : clog b (b ^ x) = x :=
  eq_of_forall_ge_iff fun z => by
    rw [← le_pow_iff_clog_le hb]
    -- ⊢ b ^ x ≤ b ^ z ↔ x ≤ z
    exact (pow_right_strictMono hb).le_iff_le
    -- 🎉 no goals
#align nat.clog_pow Nat.clog_pow

theorem pow_pred_clog_lt_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 1 < x) :
  b ^ (clog b x).pred < x := by
  rw [← not_le, le_pow_iff_clog_le hb, not_le]
  -- ⊢ pred (clog b x) < clog b x
  exact pred_lt (clog_pos hb hx).ne'
  -- 🎉 no goals
#align nat.pow_pred_clog_lt_self Nat.pow_pred_clog_lt_self

theorem le_pow_clog {b : ℕ} (hb : 1 < b) (x : ℕ) : x ≤ b ^ clog b x :=
  (le_pow_iff_clog_le hb).2 le_rfl
#align nat.le_pow_clog Nat.le_pow_clog

@[mono]
theorem clog_mono_right (b : ℕ) {n m : ℕ} (h : n ≤ m) : clog b n ≤ clog b m := by
  cases' le_or_lt b 1 with hb hb
  -- ⊢ clog b n ≤ clog b m
  · rw [clog_of_left_le_one hb]
    -- ⊢ 0 ≤ clog b m
    exact zero_le _
    -- 🎉 no goals
  · rw [← le_pow_iff_clog_le hb]
    -- ⊢ n ≤ b ^ clog b m
    exact h.trans (le_pow_clog hb _)
    -- 🎉 no goals
#align nat.clog_mono_right Nat.clog_mono_right

@[mono]
theorem clog_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : clog b n ≤ clog c n := by
  rw [← le_pow_iff_clog_le (lt_of_lt_of_le hc hb)]
  -- ⊢ n ≤ b ^ clog c n
  calc
    n ≤ c ^ clog c n := le_pow_clog hc _
    _ ≤ b ^ clog c n := pow_le_pow_of_le_left hb _
#align nat.clog_anti_left Nat.clog_anti_left

theorem clog_monotone (b : ℕ) : Monotone (clog b) := fun _ _ => clog_mono_right _
#align nat.clog_monotone Nat.clog_monotone

theorem clog_antitone_left {n : ℕ} : AntitoneOn (fun b : ℕ => clog b n) (Set.Ioi 1) :=
  fun _ hc _ _ hb => clog_anti_left (Set.mem_Iio.1 hc) hb
#align nat.clog_antitone_left Nat.clog_antitone_left

theorem log_le_clog (b n : ℕ) : log b n ≤ clog b n := by
  obtain hb | hb := le_or_lt b 1
  -- ⊢ log b n ≤ clog b n
  · rw [log_of_left_le_one hb]
    -- ⊢ 0 ≤ clog b n
    exact zero_le _
    -- 🎉 no goals
  cases n with
  | zero =>
    rw [log_zero_right]
    exact zero_le _
  | succ n =>
    exact (pow_right_strictMono hb).le_iff_le.1
      ((pow_log_le_self b n.succ_ne_zero).trans <| le_pow_clog hb _)
#align nat.log_le_clog Nat.log_le_clog

end Nat
