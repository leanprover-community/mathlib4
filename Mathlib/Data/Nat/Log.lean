/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yaël Dillies
-/
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Bound.Attribute
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Monotonicity.Attr

/-!
# Natural number logarithms

This file defines two `ℕ`-valued analogs of the logarithm of `n` with base `b`:
* `log b n`: Lower logarithm, or floor **log**. Greatest `k` such that `b^k ≤ n`.
* `clog b n`: Upper logarithm, or **c**eil **log**. Least `k` such that `n ≤ b^k`.

These are interesting because, for `1 < b`, `Nat.log b` and `Nat.clog b` are respectively right and
left adjoints of `Nat.pow b`. See `pow_le_iff_le_log` and `le_pow_iff_clog_le`.
-/

assert_not_exists OrderTop

namespace Nat

/-! ### Floor logarithm -/


/-- `log b n`, is the logarithm of natural number `n` in base `b`. It returns the largest `k : ℕ`
such that `b^k ≤ n`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot]
def log (b : ℕ) : ℕ → ℕ
  | n => if h : b ≤ n ∧ 1 < b then log b (n / b) + 1 else 0
decreasing_by
  -- putting this in the def triggers the `unusedHavesSuffices` linter:
  -- https://github.com/leanprover-community/batteries/issues/428
  have : n / b < n := div_lt_self ((Nat.zero_lt_one.trans h.2).trans_le h.1) h.2
  decreasing_trivial

@[simp]
theorem log_eq_zero_iff {b n : ℕ} : log b n = 0 ↔ n < b ∨ b ≤ 1 := by
  rw [log, dite_eq_right_iff]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, imp_false, not_and_or, not_le, not_lt]

theorem log_of_lt {b n : ℕ} (hb : n < b) : log b n = 0 :=
  log_eq_zero_iff.2 (Or.inl hb)

theorem log_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n) : log b n = 0 :=
  log_eq_zero_iff.2 (Or.inr hb)

@[simp]
theorem log_pos_iff {b n : ℕ} : 0 < log b n ↔ b ≤ n ∧ 1 < b := by
  rw [Nat.pos_iff_ne_zero, Ne, log_eq_zero_iff, not_or, not_lt, not_le]

@[bound]
theorem log_pos {b n : ℕ} (hb : 1 < b) (hbn : b ≤ n) : 0 < log b n :=
  log_pos_iff.2 ⟨hbn, hb⟩

theorem log_of_one_lt_of_le {b n : ℕ} (h : 1 < b) (hn : b ≤ n) : log b n = log b (n / b) + 1 := by
  rw [log]
  exact if_pos ⟨hn, h⟩

@[simp] lemma log_zero_left : ∀ n, log 0 n = 0 := log_of_left_le_one <| Nat.zero_le _

@[simp]
theorem log_zero_right (b : ℕ) : log b 0 = 0 :=
  log_eq_zero_iff.2 (le_total 1 b)

@[simp]
theorem log_one_left : ∀ n, log 1 n = 0 :=
  log_of_left_le_one le_rfl

@[simp]
theorem log_one_right (b : ℕ) : log b 1 = 0 :=
  log_eq_zero_iff.2 (lt_or_ge _ _)

/-- `pow b` and `log b` (almost) form a Galois connection. See also `Nat.pow_le_of_le_log` and
`Nat.le_log_of_pow_le` for individual implications under weaker assumptions. -/
theorem pow_le_iff_le_log {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) :
    b ^ x ≤ y ↔ x ≤ log b y := by
  induction y using Nat.strong_induction_on generalizing x with | h y ih => ?_
  cases x with
  | zero => dsimp; cutsat
  | succ x =>
    rw [log]; split_ifs with h
    · have b_pos : 0 < b := lt_of_succ_lt hb
      rw [Nat.add_le_add_iff_right, ← ih (y / b) (div_lt_self
        (Nat.pos_iff_ne_zero.2 hy) hb) (Nat.div_pos h.1 b_pos).ne', le_div_iff_mul_le b_pos,
        pow_succ', Nat.mul_comm]
    · exact iff_of_false (fun hby => h ⟨(le_self_pow x.succ_ne_zero _).trans hby, hb⟩)
        (not_succ_le_zero _)

theorem lt_pow_iff_log_lt {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) : y < b ^ x ↔ log b y < x :=
  lt_iff_lt_of_le_iff_le (pow_le_iff_le_log hb hy)

theorem pow_le_of_le_log {b x y : ℕ} (hy : y ≠ 0) (h : x ≤ log b y) : b ^ x ≤ y := by
  refine (le_or_gt b 1).elim (fun hb => ?_) fun hb => (pow_le_iff_le_log hb hy).2 h
  rw [log_of_left_le_one hb, Nat.le_zero] at h
  rwa [h, Nat.pow_zero, one_le_iff_ne_zero]

theorem le_log_of_pow_le {b x y : ℕ} (hb : 1 < b) (h : b ^ x ≤ y) : x ≤ log b y := by
  rcases ne_or_eq y 0 with (hy | rfl)
  exacts [(pow_le_iff_le_log hb hy).1 h, (h.not_gt (Nat.pow_pos (Nat.zero_lt_one.trans hb))).elim]

theorem pow_log_le_self (b : ℕ) {x : ℕ} (hx : x ≠ 0) : b ^ log b x ≤ x :=
  pow_le_of_le_log hx le_rfl

theorem log_lt_of_lt_pow {b x y : ℕ} (hy : y ≠ 0) : y < b ^ x → log b y < x :=
  lt_imp_lt_of_le_imp_le (pow_le_of_le_log hy)

theorem lt_pow_of_log_lt {b x y : ℕ} (hb : 1 < b) : log b y < x → y < b ^ x :=
  lt_imp_lt_of_le_imp_le (le_log_of_pow_le hb)

lemma log_lt_self (b : ℕ) {x : ℕ} (hx : x ≠ 0) : log b x < x :=
  match le_or_gt b 1 with
  | .inl h => log_of_left_le_one h x ▸ Nat.pos_iff_ne_zero.2 hx
  | .inr h => log_lt_of_lt_pow hx <| Nat.lt_pow_self h

lemma log_le_self (b x : ℕ) : log b x ≤ x :=
  if hx : x = 0 then by simp [hx]
  else (log_lt_self b hx).le

theorem lt_pow_succ_log_self {b : ℕ} (hb : 1 < b) (x : ℕ) : x < b ^ (log b x).succ :=
  lt_pow_of_log_lt hb (lt_succ_self _)

theorem log_eq_iff {b m n : ℕ} (h : m ≠ 0 ∨ 1 < b ∧ n ≠ 0) :
    log b n = m ↔ b ^ m ≤ n ∧ n < b ^ (m + 1) := by
  rcases em (1 < b ∧ n ≠ 0) with (⟨hb, hn⟩ | hbn)
  · rw [le_antisymm_iff, ← Nat.lt_succ_iff, ← pow_le_iff_le_log, ← lt_pow_iff_log_lt,
      and_comm] <;> assumption
  have hm : m ≠ 0 := h.resolve_right hbn
  rw [not_and_or, not_lt, Ne, not_not] at hbn
  rcases hbn with (hb | rfl)
  · obtain rfl | rfl := le_one_iff_eq_zero_or_eq_one.1 hb
    any_goals
      simp only [ne_eq, lt_self_iff_false, not_lt_zero, false_and, or_false]
        at h
      simp [h, eq_comm (a := 0), Nat.zero_pow (Nat.pos_iff_ne_zero.2 _)] <;> omega
  · simp [@eq_comm _ 0, hm]

theorem log_eq_of_pow_le_of_lt_pow {b m n : ℕ} (h₁ : b ^ m ≤ n) (h₂ : n < b ^ (m + 1)) :
    log b n = m := by
  rcases eq_or_ne m 0 with (rfl | hm)
  · rw [Nat.pow_one] at h₂
    exact log_of_lt h₂
  · exact (log_eq_iff (Or.inl hm)).2 ⟨h₁, h₂⟩

@[simp]
theorem log_pow {b : ℕ} (hb : 1 < b) (x : ℕ) : log b (b ^ x) = x :=
  log_eq_of_pow_le_of_lt_pow le_rfl (Nat.pow_lt_pow_right hb x.lt_succ_self)

theorem log_eq_one_iff' {b n : ℕ} : log b n = 1 ↔ b ≤ n ∧ n < b * b := by
  rw [log_eq_iff (Or.inl Nat.one_ne_zero), Nat.pow_add, Nat.pow_one]

theorem log_eq_one_iff {b n : ℕ} : log b n = 1 ↔ n < b * b ∧ 1 < b ∧ b ≤ n :=
  log_eq_one_iff'.trans
    ⟨fun h => ⟨h.2, lt_mul_self_iff.1 (h.1.trans_lt h.2), h.1⟩, fun h => ⟨h.2.2, h.1⟩⟩

@[simp]
theorem log_mul_base {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) : log b (n * b) = log b n + 1 := by
  apply log_eq_of_pow_le_of_lt_pow <;> rw [pow_succ', Nat.mul_comm b]
  exacts [Nat.mul_le_mul_right _ (pow_log_le_self _ hn),
    (Nat.mul_lt_mul_right (Nat.zero_lt_one.trans hb)).2 (lt_pow_succ_log_self hb _)]

theorem pow_log_le_add_one (b : ℕ) : ∀ x, b ^ log b x ≤ x + 1
  | 0 => by rw [log_zero_right, Nat.pow_zero]
  | x + 1 => (pow_log_le_self b x.succ_ne_zero).trans (x + 1).le_succ

theorem log_monotone {b : ℕ} : Monotone (log b) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb]
    exact zero_le _
  · exact le_log_of_pow_le hb (pow_log_le_add_one _ _)

@[mono, gcongr]
theorem log_mono_right {b n m : ℕ} (h : n ≤ m) : log b n ≤ log b m :=
  log_monotone h

theorem log_lt_log_succ_iff {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    log b n < log b (n + 1) ↔ b ^ log b (n + 1) = n + 1 := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · apply le_antisymm _ (Nat.lt_pow_of_log_lt hb H)
    exact Nat.pow_log_le_self b (Ne.symm (Nat.zero_ne_add_one n))
  · apply Nat.log_lt_of_lt_pow hn
    simp [H]

theorem log_eq_log_succ_iff {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    log b n = log b (n + 1) ↔ b ^ log b (n + 1) ≠ n + 1 := by
  rw [ne_eq, ← log_lt_log_succ_iff hb hn, not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun  _ ↦ log_monotone (le_add_right n 1)

theorem log_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : log b n ≤ log c n := by
  rcases eq_or_ne n 0 with (rfl | hn); · rw [log_zero_right, log_zero_right]
  apply le_log_of_pow_le hc
  calc
    c ^ log b n ≤ b ^ log b n := Nat.pow_le_pow_left hb _
    _ ≤ n := pow_log_le_self _ hn

theorem log_antitone_left {n : ℕ} : AntitoneOn (fun b => log b n) (Set.Ioi 1) := fun _ hc _ _ hb =>
  log_anti_left (Set.mem_Iio.1 hc) hb

@[gcongr, mono]
theorem log_mono {b c m n : ℕ} (hc : 1 < c) (hb : c ≤ b) (hmn : m ≤ n) :
    log b m ≤ log c n :=
  (log_anti_left hc hb).trans <| by gcongr

@[simp]
theorem log_div_base (b n : ℕ) : log b (n / b) = log b n - 1 := by
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb, Nat.zero_sub]
  rcases lt_or_ge n b with h | h
  · rw [div_eq_of_lt h, log_of_lt h, log_zero_right]
  rw [log_of_one_lt_of_le hb h, Nat.add_sub_cancel_right]

@[simp]
theorem log_div_mul_self (b n : ℕ) : log b (n / b * b) = log b n := by
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb]
  rcases lt_or_ge n b with h | h
  · rw [div_eq_of_lt h, Nat.zero_mul, log_zero_right, log_of_lt h]
  rw [log_mul_base hb (Nat.div_pos h (by cutsat)).ne', log_div_base,
    Nat.sub_add_cancel (succ_le_iff.2 <| log_pos hb h)]

theorem add_pred_div_lt {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : (n + b - 1) / b < n := by
  rw [div_lt_iff_lt_mul (by cutsat), ← succ_le_iff, ← pred_eq_sub_one,
    succ_pred_eq_of_pos (by cutsat)]
  exact Nat.add_le_mul hn hb

lemma log2_eq_log_two {n : ℕ} : Nat.log2 n = Nat.log 2 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [log2_zero, log_zero_right]
  apply eq_of_forall_le_iff
  intro m
  rw [Nat.le_log2 hn, ← Nat.pow_le_iff_le_log Nat.one_lt_two hn]

/-! ### Ceil logarithm -/


/-- `clog b n`, is the upper logarithm of natural number `n` in base `b`. It returns the smallest
`k : ℕ` such that `n ≤ b^k`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot]
def clog (b : ℕ) : ℕ → ℕ
  | n => if h : 1 < b ∧ 1 < n then clog b ((n + b - 1) / b) + 1 else 0
decreasing_by
  -- putting this in the def triggers the `unusedHavesSuffices` linter:
  -- https://github.com/leanprover-community/batteries/issues/428
  have : (n + b - 1) / b < n := add_pred_div_lt h.1 h.2
  decreasing_trivial

theorem clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n : ℕ) : clog b n = 0 := by
  rw [clog, dif_neg fun h : 1 < b ∧ 1 < n => h.1.not_ge hb]

theorem clog_of_right_le_one {n : ℕ} (hn : n ≤ 1) (b : ℕ) : clog b n = 0 := by
  rw [clog, dif_neg fun h : 1 < b ∧ 1 < n => h.2.not_ge hn]

@[simp] lemma clog_zero_left (n : ℕ) : clog 0 n = 0 := clog_of_left_le_one (Nat.zero_le _) _

@[simp] lemma clog_zero_right (b : ℕ) : clog b 0 = 0 := clog_of_right_le_one (Nat.zero_le _) _

@[simp]
theorem clog_one_left (n : ℕ) : clog 1 n = 0 :=
  clog_of_left_le_one le_rfl _

@[simp]
theorem clog_one_right (b : ℕ) : clog b 1 = 0 :=
  clog_of_right_le_one le_rfl _

theorem clog_of_two_le {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) :
    clog b n = clog b ((n + b - 1) / b) + 1 := by rw [clog, dif_pos (⟨hb, hn⟩ : 1 < b ∧ 1 < n)]

theorem clog_pos {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : 0 < clog b n := by
  rw [clog_of_two_le hb hn]
  exact zero_lt_succ _

theorem clog_eq_one {b n : ℕ} (hn : 2 ≤ n) (h : n ≤ b) : clog b n = 1 := by
  rw [clog_of_two_le (hn.trans h) hn, clog_of_right_le_one]
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul] <;> omega

/-- `clog b` and `pow b` form a Galois connection. -/
theorem le_pow_iff_clog_le {b : ℕ} (hb : 1 < b) {x y : ℕ} : x ≤ b ^ y ↔ clog b x ≤ y := by
  induction x using Nat.strong_induction_on generalizing y with | h x ih => ?_
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

theorem pow_lt_iff_lt_clog {b : ℕ} (hb : 1 < b) {x y : ℕ} : b ^ y < x ↔ y < clog b x :=
  lt_iff_lt_of_le_iff_le (le_pow_iff_clog_le hb)

@[simp]
theorem clog_pow (b x : ℕ) (hb : 1 < b) : clog b (b ^ x) = x :=
  eq_of_forall_ge_iff fun z ↦ by rw [← le_pow_iff_clog_le hb, Nat.pow_le_pow_iff_right hb]

theorem pow_pred_clog_lt_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 1 < x) :
    b ^ (clog b x).pred < x := by
  rw [← not_le, le_pow_iff_clog_le hb, not_le]
  exact pred_lt (clog_pos hb hx).ne'

theorem le_pow_clog {b : ℕ} (hb : 1 < b) (x : ℕ) : x ≤ b ^ clog b x :=
  (le_pow_iff_clog_le hb).2 le_rfl

@[mono, gcongr]
theorem clog_mono_right (b : ℕ) {n m : ℕ} (h : n ≤ m) : clog b n ≤ clog b m := by
  rcases le_or_gt b 1 with hb | hb
  · rw [clog_of_left_le_one hb]
    exact zero_le _
  · rw [← le_pow_iff_clog_le hb]
    exact h.trans (le_pow_clog hb _)

theorem clog_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : clog b n ≤ clog c n := by
  rw [← le_pow_iff_clog_le (lt_of_lt_of_le hc hb)]
  calc
    n ≤ c ^ clog c n := le_pow_clog hc _
    _ ≤ b ^ clog c n := Nat.pow_le_pow_left hb _

theorem clog_monotone (b : ℕ) : Monotone (clog b) := fun _ _ => clog_mono_right _

theorem clog_antitone_left {n : ℕ} : AntitoneOn (fun b : ℕ => clog b n) (Set.Ioi 1) :=
  fun _ hc _ _ hb => clog_anti_left (Set.mem_Iio.1 hc) hb

@[mono, gcongr]
theorem clog_mono {b c m n : ℕ} (hc : 1 < c) (hb : c ≤ b) (hmn : m ≤ n) :
    clog b m ≤ clog c n :=
  (clog_anti_left hc hb).trans <| by gcongr

@[simp]
theorem log_le_clog (b n : ℕ) : log b n ≤ clog b n := by
  obtain hb | hb := le_or_gt b 1
  · rw [log_of_left_le_one hb]
    exact zero_le _
  cases n with
  | zero =>
    rw [log_zero_right]
    exact zero_le _
  | succ n =>
    exact (Nat.pow_le_pow_iff_right hb).1
      ((pow_log_le_self b n.succ_ne_zero).trans <| le_pow_clog hb _)

theorem clog_lt_clog_succ_iff {b n : ℕ} (hb : 1 < b) :
    clog b n < clog b (n + 1) ↔ b ^ clog b n = n := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · apply le_antisymm _ (le_pow_clog hb n)
    apply le_of_lt_succ
    exact (pow_lt_iff_lt_clog hb).mpr H
  · rw [← pow_lt_iff_lt_clog hb, H]
    exact n.lt_add_one

theorem clog_eq_clog_succ_iff {b n : ℕ} (hb : 1 < b) :
    clog b n = clog b (n + 1) ↔ b ^ clog b n ≠ n := by
  rw [ne_eq, ← clog_lt_clog_succ_iff hb, not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun _ ↦ clog_monotone b (le_add_right n 1)

/-! ### Computating the logarithm efficiently -/
section computation

private lemma logC_aux {m b : ℕ} (hb : 1 < b) (hbm : b ≤ m) : m / (b * b) < m / b := by
  have hb' : 0 < b := zero_lt_of_lt hb
  rw [div_lt_iff_lt_mul (Nat.mul_pos hb' hb'), ← Nat.mul_assoc, ← div_lt_iff_lt_mul hb']
  exact (Nat.lt_mul_iff_one_lt_right (Nat.div_pos hbm hb')).2 hb

/-
The linter complains about `h : m < pw` being unused, but we need it in the `decreasing_by`.
-/
set_option linter.unusedVariables false in
/--
An alternate definition for `Nat.log` which computes more efficiently. For mathematical purposes,
use `Nat.log` instead, and see `Nat.log_eq_logC`.

Note a tail-recursive version of `Nat.log` is also possible:
```
def logTR (b n : ℕ) : ℕ :=
  let rec go : ℕ → ℕ → ℕ | n, acc => if h : b ≤ n ∧ 1 < b then go (n / b) (acc + 1) else acc
  decreasing_by
    have : n / b < n := Nat.div_lt_self (by omega) h.2
    decreasing_trivial
  go n 0
```
but performs worse for large numbers than `Nat.logC`:
```
#eval Nat.logTR 2 (2 ^ 1000000)
#eval Nat.logC 2 (2 ^ 1000000)
```

The definition `Nat.logC` is not tail-recursive, however, but the stack limit will only be reached
if the output size is around 2^10000, meaning the input will be around 2^(2^10000), which will
take far too long to compute in the first place.

Adapted from https://downloads.haskell.org/~ghc/9.0.1/docs/html/libraries/ghc-bignum-1.0/GHC-Num-BigNat.html#v:bigNatLogBase-35-
-/
@[pp_nodot] def logC (b m : ℕ) : ℕ :=
  if h : 1 < b then let (_, e) := step b h; e else 0 where
  /--
  An auxiliary definition for `Nat.logC`, where the base of the logarithm is _squared_ in each
  loop. This allows significantly faster computation of the logarithm: it takes logarithmic time
  in the size of the output, rather than linear time.
  -/
  step (pw : ℕ) (hpw : 1 < pw) : ℕ × ℕ :=
    if h : m < pw then (m, 0)
    else
      let (q, e) := step (pw * pw) (Nat.mul_lt_mul_of_lt_of_lt hpw hpw)
      if q < pw then (q, 2 * e) else (q / pw, 2 * e + 1)
  termination_by m / pw
  decreasing_by
    have : m / (pw * pw) < m / pw := logC_aux hpw (le_of_not_gt h)
    decreasing_trivial

private lemma logC_step {m pw q e : ℕ} (hpw : 1 < pw) (hqe : logC.step m pw hpw = (q, e)) :
    pw ^ e * q ≤ m ∧ q < pw ∧ (m < pw ^ e * (q + 1)) ∧ (0 < m → 0 < q) := by
  induction pw, hpw using logC.step.induct m generalizing q e with
  | case1 pw hpw hmpw =>
      rw [logC.step, dif_pos hmpw] at hqe
      cases hqe
      simpa
  | case2 pw hpw hmpw q' e' hqe' hqpw ih =>
      simp only [logC.step, dif_neg hmpw, hqe', if_pos hqpw] at hqe
      cases hqe
      rw [Nat.pow_mul, Nat.pow_two]
      exact ⟨(ih hqe').1, hqpw, (ih hqe').2.2⟩
  | case3 pw hpw hmpw q' e' hqe' hqpw ih =>
      simp only [Nat.logC.step, dif_neg hmpw, hqe', if_neg hqpw] at hqe
      cases hqe
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.pow_mul, Nat.pow_two, Nat.mul_assoc]
      refine ⟨(ih hqe').1.trans' (Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)),
        Nat.div_lt_of_lt_mul (ih hqe').2.1, (ih hqe').2.2.1.trans_le ?_,
        fun _ => Nat.div_pos (le_of_not_gt hqpw) (by cutsat)⟩
      exact Nat.mul_le_mul_left _ (Nat.lt_mul_div_succ _ (zero_lt_of_lt hpw))

private lemma logC_spec {b m : ℕ} (hb : 1 < b) (hm : 0 < m) :
    b ^ logC b m ≤ m ∧ m < b ^ (logC b m + 1) := by
  rw [logC, dif_pos hb]
  split
  next q e heq =>
  obtain ⟨h₁, h₂, h₃, h₄⟩ := logC_step hb heq
  exact ⟨h₁.trans' (Nat.le_mul_of_pos_right _ (h₄ hm)), h₃.trans_le (Nat.mul_le_mul_left _ h₂)⟩

private lemma logC_of_left_le_one {b m : ℕ} (hb : b ≤ 1) : logC b m = 0 := by
  rw [logC, dif_neg hb.not_gt]

private lemma logC_zero {b : ℕ} :
    logC b 0 = 0 := by
  rcases le_or_gt b 1 with hb | hb
  case inl => exact logC_of_left_le_one hb
  case inr =>
    rw [logC, dif_pos hb]
    split
    next q e heq =>
    rw [logC.step, dif_pos (zero_lt_of_lt hb)] at heq
    rw [(Prod.mk.inj heq).2]

/--
The result of `Nat.log` agrees with the result of `Nat.logC`. The latter will be computed more
efficiently, but the former is easier to prove things about and has more lemmas.
This lemma is tagged @[csimp] so that the code generated for `Nat.log` uses `Nat.logC` instead.
-/
@[csimp] theorem log_eq_logC : log = logC := by
  ext b m
  rcases le_or_gt b 1 with hb | hb
  case inl => rw [logC_of_left_le_one hb, Nat.log_of_left_le_one hb]
  case inr =>
    rcases eq_or_ne m 0 with rfl | hm
    case inl => rw [Nat.log_zero_right, logC_zero]
    case inr =>
      rw [Nat.log_eq_iff (Or.inr ⟨hb, hm⟩)]
      exact logC_spec hb (zero_lt_of_ne_zero hm)

end computation

end Nat
