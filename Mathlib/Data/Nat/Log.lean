/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yaël Dillies
-/
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Monotonicity.Attr

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
  | n => if h : b ≤ n ∧ 1 < b then log b (n / b) + 1 else 0
decreasing_by
  -- putting this in the def triggers the `unusedHavesSuffices` linter:
  -- https://github.com/leanprover-community/batteries/issues/428
  have : n / b < n := div_lt_self ((Nat.zero_lt_one.trans h.2).trans_le h.1) h.2
  decreasing_trivial
#align nat.log Nat.log

@[simp]
theorem log_eq_zero_iff {b n : ℕ} : log b n = 0 ↔ n < b ∨ b ≤ 1 := by
  rw [log, dite_eq_right_iff]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, imp_false, not_and_or, not_le, not_lt]
#align nat.log_eq_zero_iff Nat.log_eq_zero_iff

theorem log_of_lt {b n : ℕ} (hb : n < b) : log b n = 0 :=
  log_eq_zero_iff.2 (Or.inl hb)
#align nat.log_of_lt Nat.log_of_lt

theorem log_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n) : log b n = 0 :=
  log_eq_zero_iff.2 (Or.inr hb)
#align nat.log_of_left_le_one Nat.log_of_left_le_one

@[simp]
theorem log_pos_iff {b n : ℕ} : 0 < log b n ↔ b ≤ n ∧ 1 < b := by
  rw [Nat.pos_iff_ne_zero, Ne, log_eq_zero_iff, not_or, not_lt, not_le]
#align nat.log_pos_iff Nat.log_pos_iff

theorem log_pos {b n : ℕ} (hb : 1 < b) (hbn : b ≤ n) : 0 < log b n :=
  log_pos_iff.2 ⟨hbn, hb⟩
#align nat.log_pos Nat.log_pos

theorem log_of_one_lt_of_le {b n : ℕ} (h : 1 < b) (hn : b ≤ n) : log b n = log b (n / b) + 1 := by
  rw [log]
  exact if_pos ⟨hn, h⟩
#align nat.log_of_one_lt_of_le Nat.log_of_one_lt_of_le

@[simp] lemma log_zero_left : ∀ n, log 0 n = 0 := log_of_left_le_one $ Nat.zero_le _
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
  cases x with
  | zero => dsimp; omega
  | succ x =>
    rw [log]; split_ifs with h
    · have b_pos : 0 < b := lt_of_succ_lt hb
      rw [Nat.add_le_add_iff_right, ← ih (y / b) (div_lt_self
        (Nat.pos_iff_ne_zero.2 hy) hb) (Nat.div_pos h.1 b_pos).ne', le_div_iff_mul_le b_pos,
        pow_succ', Nat.mul_comm]
    · exact iff_of_false (fun hby => h ⟨(le_self_pow x.succ_ne_zero _).trans hby, hb⟩)
        (not_succ_le_zero _)
#align nat.pow_le_iff_le_log Nat.pow_le_iff_le_log

theorem lt_pow_iff_log_lt {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) : y < b ^ x ↔ log b y < x :=
  lt_iff_lt_of_le_iff_le (pow_le_iff_le_log hb hy)
#align nat.lt_pow_iff_log_lt Nat.lt_pow_iff_log_lt

theorem pow_le_of_le_log {b x y : ℕ} (hy : y ≠ 0) (h : x ≤ log b y) : b ^ x ≤ y := by
  refine (le_or_lt b 1).elim (fun hb => ?_) fun hb => (pow_le_iff_le_log hb hy).2 h
  rw [log_of_left_le_one hb, Nat.le_zero] at h
  rwa [h, Nat.pow_zero, one_le_iff_ne_zero]
#align nat.pow_le_of_le_log Nat.pow_le_of_le_log

theorem le_log_of_pow_le {b x y : ℕ} (hb : 1 < b) (h : b ^ x ≤ y) : x ≤ log b y := by
  rcases ne_or_eq y 0 with (hy | rfl)
  exacts [(pow_le_iff_le_log hb hy).1 h, (h.not_lt (Nat.pow_pos (Nat.zero_lt_one.trans hb))).elim]
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
  · rw [le_antisymm_iff, ← Nat.lt_succ_iff, ← pow_le_iff_le_log, ← lt_pow_iff_log_lt, and_comm] <;>
      assumption
  have hm : m ≠ 0 := h.resolve_right hbn
  rw [not_and_or, not_lt, Ne, not_not] at hbn
  rcases hbn with (hb | rfl)
  · obtain rfl | rfl := le_one_iff_eq_zero_or_eq_one.1 hb
    any_goals
      simp only [ne_eq, zero_eq, reduceSucc, lt_self_iff_false,  not_lt_zero, false_and, or_false]
        at h
      simp [h, eq_comm (a := 0), Nat.zero_pow (Nat.pos_iff_ne_zero.2 _)] <;> omega
  · simp [@eq_comm _ 0, hm]
#align nat.log_eq_iff Nat.log_eq_iff

theorem log_eq_of_pow_le_of_lt_pow {b m n : ℕ} (h₁ : b ^ m ≤ n) (h₂ : n < b ^ (m + 1)) :
    log b n = m := by
  rcases eq_or_ne m 0 with (rfl | hm)
  · rw [Nat.pow_one] at h₂
    exact log_of_lt h₂
  · exact (log_eq_iff (Or.inl hm)).2 ⟨h₁, h₂⟩
#align nat.log_eq_of_pow_le_of_lt_pow Nat.log_eq_of_pow_le_of_lt_pow

theorem log_pow {b : ℕ} (hb : 1 < b) (x : ℕ) : log b (b ^ x) = x :=
  log_eq_of_pow_le_of_lt_pow le_rfl (Nat.pow_lt_pow_right hb x.lt_succ_self)
#align nat.log_pow Nat.log_pow

theorem log_eq_one_iff' {b n : ℕ} : log b n = 1 ↔ b ≤ n ∧ n < b * b := by
  rw [log_eq_iff (Or.inl Nat.one_ne_zero), Nat.pow_add, Nat.pow_one]
#align nat.log_eq_one_iff' Nat.log_eq_one_iff'

theorem log_eq_one_iff {b n : ℕ} : log b n = 1 ↔ n < b * b ∧ 1 < b ∧ b ≤ n :=
  log_eq_one_iff'.trans
    ⟨fun h => ⟨h.2, lt_mul_self_iff.1 (h.1.trans_lt h.2), h.1⟩, fun h => ⟨h.2.2, h.1⟩⟩
#align nat.log_eq_one_iff Nat.log_eq_one_iff

theorem log_mul_base {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) : log b (n * b) = log b n + 1 := by
  apply log_eq_of_pow_le_of_lt_pow <;> rw [pow_succ', Nat.mul_comm b]
  exacts [Nat.mul_le_mul_right _ (pow_log_le_self _ hn),
    (Nat.mul_lt_mul_right (Nat.zero_lt_one.trans hb)).2 (lt_pow_succ_log_self hb _)]
#align nat.log_mul_base Nat.log_mul_base

theorem pow_log_le_add_one (b : ℕ) : ∀ x, b ^ log b x ≤ x + 1
  | 0 => by rw [log_zero_right, Nat.pow_zero]
  | x + 1 => (pow_log_le_self b x.succ_ne_zero).trans (x + 1).le_succ
#align nat.pow_log_le_add_one Nat.pow_log_le_add_one

theorem log_monotone {b : ℕ} : Monotone (log b) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases le_or_lt b 1 with hb | hb
  · rw [log_of_left_le_one hb]
    exact zero_le _
  · exact le_log_of_pow_le hb (pow_log_le_add_one _ _)
#align nat.log_monotone Nat.log_monotone

@[mono]
theorem log_mono_right {b n m : ℕ} (h : n ≤ m) : log b n ≤ log b m :=
  log_monotone h
#align nat.log_mono_right Nat.log_mono_right

@[mono]
theorem log_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : log b n ≤ log c n := by
  rcases eq_or_ne n 0 with (rfl | hn); · rw [log_zero_right, log_zero_right]
  apply le_log_of_pow_le hc
  calc
    c ^ log b n ≤ b ^ log b n := Nat.pow_le_pow_left hb _
    _ ≤ n := pow_log_le_self _ hn
#align nat.log_anti_left Nat.log_anti_left

theorem log_antitone_left {n : ℕ} : AntitoneOn (fun b => log b n) (Set.Ioi 1) := fun _ hc _ _ hb =>
  log_anti_left (Set.mem_Iio.1 hc) hb
#align nat.log_antitone_left Nat.log_antitone_left

@[simp]
theorem log_div_base (b n : ℕ) : log b (n / b) = log b n - 1 := by
  rcases le_or_lt b 1 with hb | hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb, Nat.zero_sub]
  cases' lt_or_le n b with h h
  · rw [div_eq_of_lt h, log_of_lt h, log_zero_right]
  rw [log_of_one_lt_of_le hb h, Nat.add_sub_cancel_right]
#align nat.log_div_base Nat.log_div_base

@[simp]
theorem log_div_mul_self (b n : ℕ) : log b (n / b * b) = log b n := by
  rcases le_or_lt b 1 with hb | hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb]
  cases' lt_or_le n b with h h
  · rw [div_eq_of_lt h, Nat.zero_mul, log_zero_right, log_of_lt h]
  rw [log_mul_base hb (Nat.div_pos h (by omega)).ne', log_div_base,
    Nat.sub_add_cancel (succ_le_iff.2 <| log_pos hb h)]
#align nat.log_div_mul_self Nat.log_div_mul_self

theorem add_pred_div_lt {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : (n + b - 1) / b < n := by
  rw [div_lt_iff_lt_mul (by omega), ← succ_le_iff, ← pred_eq_sub_one,
    succ_pred_eq_of_pos (by omega)]
  exact Nat.add_le_mul hn hb
-- Porting note: Was private in mathlib 3
-- #align nat.add_pred_div_lt Nat.add_pred_div_lt

/-! ### Ceil logarithm -/


/-- `clog b n`, is the upper logarithm of natural number `n` in base `b`. It returns the smallest
`k : ℕ` such that `n ≤ b^k`, so if `b^k = n`, it returns exactly `k`. -/
--@[pp_nodot]
def clog (b : ℕ) : ℕ → ℕ
  | n => if h : 1 < b ∧ 1 < n then clog b ((n + b - 1) / b) + 1 else 0
decreasing_by
  -- putting this in the def triggers the `unusedHavesSuffices` linter:
  -- https://github.com/leanprover-community/batteries/issues/428
  have : (n + b - 1) / b < n := add_pred_div_lt h.1 h.2
  decreasing_trivial

#align nat.clog Nat.clog

theorem clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n : ℕ) : clog b n = 0 := by
  rw [clog, dif_neg fun h : 1 < b ∧ 1 < n => h.1.not_le hb]
#align nat.clog_of_left_le_one Nat.clog_of_left_le_one

theorem clog_of_right_le_one {n : ℕ} (hn : n ≤ 1) (b : ℕ) : clog b n = 0 := by
  rw [clog, dif_neg fun h : 1 < b ∧ 1 < n => h.2.not_le hn]
#align nat.clog_of_right_le_one Nat.clog_of_right_le_one

@[simp] lemma clog_zero_left (n : ℕ) : clog 0 n = 0 := clog_of_left_le_one (Nat.zero_le _) _
#align nat.clog_zero_left Nat.clog_zero_left

@[simp] lemma clog_zero_right (b : ℕ) : clog b 0 = 0 := clog_of_right_le_one (Nat.zero_le _) _
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
#align nat.clog_of_two_le Nat.clog_of_two_le

theorem clog_pos {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : 0 < clog b n := by
  rw [clog_of_two_le hb hn]
  exact zero_lt_succ _
#align nat.clog_pos Nat.clog_pos

theorem clog_eq_one {b n : ℕ} (hn : 2 ≤ n) (h : n ≤ b) : clog b n = 1 := by
  rw [clog_of_two_le (hn.trans h) hn, clog_of_right_le_one]
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul] <;> omega
#align nat.clog_eq_one Nat.clog_eq_one

/-- `clog b` and `pow b` form a Galois connection. -/
theorem le_pow_iff_clog_le {b : ℕ} (hb : 1 < b) {x y : ℕ} : x ≤ b ^ y ↔ clog b x ≤ y := by
  induction' x using Nat.strong_induction_on with x ih generalizing y
  cases y
  · rw [Nat.pow_zero]
    refine ⟨fun h => (clog_of_right_le_one h b).le, ?_⟩
    simp_rw [← not_lt]
    contrapose!
    exact clog_pos hb
  have b_pos : 0 < b := zero_lt_of_lt hb
  rw [clog]; split_ifs with h
  · rw [Nat.add_le_add_iff_right, ← ih ((x + b - 1) / b) (add_pred_div_lt hb h.2),
      Nat.div_le_iff_le_mul_add_pred b_pos, Nat.mul_comm b, ← Nat.pow_succ,
      Nat.add_sub_assoc (Nat.succ_le_of_lt b_pos), Nat.add_le_add_iff_right]
  · exact iff_of_true ((not_lt.1 (not_and.1 h hb)).trans <| succ_le_of_lt <| Nat.pow_pos b_pos)
      (zero_le _)
#align nat.le_pow_iff_clog_le Nat.le_pow_iff_clog_le

theorem pow_lt_iff_lt_clog {b : ℕ} (hb : 1 < b) {x y : ℕ} : b ^ y < x ↔ y < clog b x :=
  lt_iff_lt_of_le_iff_le (le_pow_iff_clog_le hb)
#align nat.pow_lt_iff_lt_clog Nat.pow_lt_iff_lt_clog

theorem clog_pow (b x : ℕ) (hb : 1 < b) : clog b (b ^ x) = x :=
  eq_of_forall_ge_iff fun z ↦ by rw [← le_pow_iff_clog_le hb, Nat.pow_le_pow_iff_right hb]
#align nat.clog_pow Nat.clog_pow

theorem pow_pred_clog_lt_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 1 < x) :
    b ^ (clog b x).pred < x := by
  rw [← not_le, le_pow_iff_clog_le hb, not_le]
  exact pred_lt (clog_pos hb hx).ne'
#align nat.pow_pred_clog_lt_self Nat.pow_pred_clog_lt_self

theorem le_pow_clog {b : ℕ} (hb : 1 < b) (x : ℕ) : x ≤ b ^ clog b x :=
  (le_pow_iff_clog_le hb).2 le_rfl
#align nat.le_pow_clog Nat.le_pow_clog

@[mono]
theorem clog_mono_right (b : ℕ) {n m : ℕ} (h : n ≤ m) : clog b n ≤ clog b m := by
  rcases le_or_lt b 1 with hb | hb
  · rw [clog_of_left_le_one hb]
    exact zero_le _
  · rw [← le_pow_iff_clog_le hb]
    exact h.trans (le_pow_clog hb _)
#align nat.clog_mono_right Nat.clog_mono_right

@[mono]
theorem clog_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : clog b n ≤ clog c n := by
  rw [← le_pow_iff_clog_le (lt_of_lt_of_le hc hb)]
  calc
    n ≤ c ^ clog c n := le_pow_clog hc _
    _ ≤ b ^ clog c n := Nat.pow_le_pow_left hb _
#align nat.clog_anti_left Nat.clog_anti_left

theorem clog_monotone (b : ℕ) : Monotone (clog b) := fun _ _ => clog_mono_right _
#align nat.clog_monotone Nat.clog_monotone

theorem clog_antitone_left {n : ℕ} : AntitoneOn (fun b : ℕ => clog b n) (Set.Ioi 1) :=
  fun _ hc _ _ hb => clog_anti_left (Set.mem_Iio.1 hc) hb
#align nat.clog_antitone_left Nat.clog_antitone_left

theorem log_le_clog (b n : ℕ) : log b n ≤ clog b n := by
  obtain hb | hb := le_or_lt b 1
  · rw [log_of_left_le_one hb]
    exact zero_le _
  cases n with
  | zero =>
    rw [log_zero_right]
    exact zero_le _
  | succ n =>
    exact (Nat.pow_le_pow_iff_right hb).1
      ((pow_log_le_self b n.succ_ne_zero).trans <| le_pow_clog hb _)
#align nat.log_le_clog Nat.log_le_clog

end Nat
