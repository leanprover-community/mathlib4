/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yaël Dillies, Yury Kudryashov
-/
module

public import Mathlib.Data.Nat.BinaryRec
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Natural number logarithms

This file defines two `ℕ`-valued analogs of the logarithm of `n` with base `b`:
* `log b n`: Lower logarithm, or floor **log**. Greatest `k` such that `b^k ≤ n`.
* `clog b n`: Upper logarithm, or **c**eil **log**. Least `k` such that `n ≤ b^k`.

These are interesting because, for `1 < b`, `Nat.log b` and `Nat.clog b` are respectively right and
left adjoints of `(b ^ ·)`. See `le_log_iff_pow_le` and `clog_le_iff_le_pow`.

## Implementation notes

We define both functions using recursion on `b`.
In order to compute, e.g., `Nat.log b n`, we compute `e = Nat.log (b * b) n` first,
then figure out whether the answer is `2 * e` or `2 * e + 1`.
The actual implementations use fuel recursion so that `(by decide : Nat.log 2 20 = 4)` works.

Adapted from https://downloads.haskell.org/~ghc/9.0.1/docs/html/libraries/ghc-bignum-1.0/GHC-Num-BigNat.html#v:bigNatLogBase-35-

Note a tail-recursive version of `Nat.log` is also possible:
```
def logTR (b n : ℕ) : ℕ :=
  let rec go : ℕ → ℕ → ℕ | n, acc => if h : b ≤ n ∧ 1 < b then go (n / b) (acc + 1) else acc
  decreasing_by
    have : n / b < n := Nat.div_lt_self (by lia) h.2
    decreasing_trivial
  go n 0
```
but performs worse for large numbers than `Nat.log`:
```
#eval Nat.logTR 2 (2 ^ 1000000)
#eval Nat.log 2 (2 ^ 1000000)
```
-/

@[expose] public section

assert_not_exists OrderTop

namespace Nat

/-! ### Floor logarithm -/


/-- `log b n`, is the logarithm of natural number `n` in base `b`. It returns the largest `k : ℕ`
such that `b^k ≤ n`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot]
def log (b n : ℕ) : ℕ :=
  if b ≤ 1 then 0 else (go b n).2 where
  /-- An auxiliary definition for `Nat.log`.

  For `b > 1`, `n ≠ 0`, `n < b ^ fuel`, `Nat.log.go n b fuel = (n / b ^ b.log n, b.log n)`. -/
  go : ℕ → ℕ → ℕ × ℕ
  | _, 0 => (n, 0)
  | b, fuel + 1 =>
    if n < b then
      (n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e) else (q / b, 2 * e + 1)

theorem log_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n) : log b n = 0 := by
  rw [log, if_pos hb]

theorem log_of_lt {b n : ℕ} (hb : n < b) : log b n = 0 := by
  fun_cases log with
  | case1 => rfl
  | case2 => fun_cases log.go with grind

private theorem log.go_aux {n b fuel : ℕ} (hb : 1 < b) (hfuel : n < b ^ (fuel + 1)) (hbn : b ≤ n) :
    n < (b * b) ^ fuel := by
  obtain hfuel₀ : fuel ≠ 0 := by rintro rfl; simp [Nat.not_lt_of_le hbn] at hfuel
  rw [← Nat.pow_two, ← Nat.pow_mul]
  exact Nat.lt_of_lt_of_le hfuel <| Nat.pow_le_pow_right (by grind) (by grind)

lemma log.go_spec {b n fuel : ℕ} (hb : 1 < b) (hn : n ≠ 0) (hfuel : n < b ^ fuel) :
    (log.go n b fuel).1 = n / b ^ (log.go n b fuel).2 ∧
      b ^ (log.go n b fuel).2 ≤ n ∧ n < b ^ ((log.go n b fuel).2 + 1) := by
  induction fuel generalizing b with
  | zero => simp_all
  | succ fuel ih =>
    cases Nat.lt_or_ge n b with
    | inl hnb =>
      simp [go, hnb, one_le_iff_ne_zero, hn]
    | inr hnb =>
      rcases ih (Nat.one_mul 1 ▸ Nat.mul_lt_mul_of_lt_of_lt hb hb) (go_aux hb hfuel hnb)
        with ⟨ih₁, ih₂, ih₃⟩
      simp_all only [go, if_neg (Nat.not_lt_of_le hnb), ← Nat.pow_two, ← Nat.pow_mul,
        Nat.div_lt_iff_lt_mul, Nat.pow_pos (Nat.zero_lt_of_lt hb), Nat.div_div_eq_div_mul,
        ← Nat.pow_add_one, ← Nat.pow_add_one', Nat.mul_add_one]
      split <;> simp_all

theorem log_lt_iff_lt_pow {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) :
    log b y < x ↔ y < b ^ x := by
  rcases log.go_spec hb hy (Nat.lt_pow_self hb) with ⟨-, H₁, H₂⟩
  rw [log, if_neg (Nat.not_le_of_lt hb)]
  cases Nat.lt_or_ge (log.go y b y).snd x with
  | inl h =>
    exact iff_of_true h <| Nat.lt_of_lt_of_le H₂ <| Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) h
  | inr h =>
    refine iff_of_false (Nat.not_lt_of_ge h) <| Nat.not_lt_of_ge <| Nat.le_trans ?_ H₁
    exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) h

@[simp]
theorem log_eq_zero_iff {b n : ℕ} : log b n = 0 ↔ n < b ∨ b ≤ 1 := by
  rcases Nat.lt_or_ge 1 b with hb | hb
  · rcases eq_or_ne n 0 with rfl | hn
    · grind [log_of_lt]
    · rw [← Nat.lt_one_iff, log_lt_iff_lt_pow hb hn, Nat.pow_one, or_iff_left (Nat.not_le_of_lt hb)]
  · simp [hb, log_of_left_le_one]

@[simp]
theorem log_pos_iff {b n : ℕ} : 0 < log b n ↔ b ≤ n ∧ 1 < b := by
  rw [Nat.pos_iff_ne_zero, Ne, log_eq_zero_iff, not_or, not_lt, not_le]

@[bound]
theorem log_pos {b n : ℕ} (hb : 1 < b) (hbn : b ≤ n) : 0 < log b n :=
  log_pos_iff.2 ⟨hbn, hb⟩

theorem log_of_one_lt_of_le {b n : ℕ} (h : 1 < b) (hn : b ≤ n) : log b n = log b (n / b) + 1 := by
  apply eq_of_forall_gt_iff
  rintro (_ | c)
  · simp
  · have : n / b ≠ 0 := by simp [*, Nat.ne_zero_of_lt h]
    rw [log_lt_iff_lt_pow, Nat.add_lt_add_iff_right, log_lt_iff_lt_pow,
      Nat.pow_add_one, Nat.div_lt_iff_lt_mul] <;> grind

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

/-- `(b ^ ·)` and `log b` (almost) form a Galois connection. See also `Nat.pow_le_of_le_log` and
`Nat.le_log_of_pow_le` for individual implications under weaker assumptions. -/
theorem le_log_iff_pow_le {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) :
    x ≤ log b y ↔ b ^ x ≤ y :=
  le_iff_le_iff_lt_iff_lt.mpr <| log_lt_iff_lt_pow hb hy

@[deprecated le_log_iff_pow_le (since := "2025-10-05")]
theorem pow_le_iff_le_log {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) :
    b ^ x ≤ y ↔ x ≤ log b y :=
  (le_log_iff_pow_le hb hy).symm

@[deprecated log_lt_iff_lt_pow (since := "2025-10-05")]
theorem lt_pow_iff_log_lt {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) : y < b ^ x ↔ log b y < x :=
  (log_lt_iff_lt_pow hb hy).symm

theorem pow_le_of_le_log {b x y : ℕ} (hy : y ≠ 0) (h : x ≤ log b y) : b ^ x ≤ y := by
  refine (le_or_gt b 1).elim (fun hb => ?_) fun hb => (le_log_iff_pow_le hb hy).1 h
  rw [log_of_left_le_one hb, Nat.le_zero] at h
  rwa [h, Nat.pow_zero, one_le_iff_ne_zero]

theorem le_log_of_pow_le {b x y : ℕ} (hb : 1 < b) (h : b ^ x ≤ y) : x ≤ log b y := by
  rcases ne_or_eq y 0 with (hy | rfl)
  exacts [(le_log_iff_pow_le hb hy).2 h, (h.not_gt (Nat.pow_pos (Nat.zero_lt_one.trans hb))).elim]

theorem pow_log_le_self (b : ℕ) {x : ℕ} (hx : x ≠ 0) : b ^ log b x ≤ x :=
  pow_le_of_le_log hx le_rfl

/-- See also `log_lt_of_lt_pow'` for a version that assumes `x ≠ 0` instead of `y ≠ 0`. -/
theorem log_lt_of_lt_pow {b x y : ℕ} (hy : y ≠ 0) : y < b ^ x → log b y < x :=
  lt_imp_lt_of_le_imp_le (pow_le_of_le_log hy)

/-- A version of `log_lt_of_lt_pow` that assumes `x ≠ 0` instead of `y ≠ 0`. -/
theorem log_lt_of_lt_pow' {b x y : ℕ} (hx : x ≠ 0) (hlt : y < b ^ x) : log b y < x := by
  rcases eq_or_ne y 0 with rfl | hy
  · grind [log_zero_right]
  · exact log_lt_of_lt_pow hy hlt

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
  · rw [le_antisymm_iff, ← Nat.lt_succ_iff, le_log_iff_pow_le, log_lt_iff_lt_pow,
      and_comm] <;> assumption
  have hm : m ≠ 0 := h.resolve_right hbn
  rw [not_and_or, not_lt, Ne, not_not] at hbn
  rcases hbn with (hb | rfl)
  · obtain rfl | rfl := le_one_iff_eq_zero_or_eq_one.1 hb
    any_goals
      simp only [ne_eq, lt_self_iff_false, not_lt_zero, false_and, or_false]
        at h
      simp [h, eq_comm (a := 0), Nat.zero_pow (Nat.pos_iff_ne_zero.2 _)] <;> lia
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
  exact fun _ ↦ log_monotone (le_add_right n 1)

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

lemma log_div_base_pow (b n k : ℕ) : log b (n / b ^ k) = log b n - k := by
  induction k with
  | zero => grind
  | succ k hk => rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, log_div_base, hk, sub_add_eq]

@[simp]
theorem log_div_mul_self (b n : ℕ) : log b (n / b * b) = log b n := by
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb]
  rcases lt_or_ge n b with h | h
  · rw [div_eq_of_lt h, Nat.zero_mul, log_zero_right, log_of_lt h]
  rw [log_mul_base hb (Nat.div_pos h (by lia)).ne', log_div_base,
    Nat.sub_add_cancel (succ_le_iff.2 <| log_pos hb h)]

theorem add_pred_div_lt {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : (n + b - 1) / b < n := by
  rw [div_lt_iff_lt_mul (by lia), ← succ_le_iff, ← pred_eq_sub_one,
    succ_pred_eq_of_pos (by lia)]
  exact Nat.add_le_mul hn hb

lemma log_two_bit {b n} (hn : n ≠ 0) : Nat.log 2 (n.bit b) = Nat.log 2 n + 1 := by
  rw [← log_div_mul_self, bit_div_two, log_mul_base Nat.one_lt_two hn]

lemma log2_eq_log_two {n : ℕ} : Nat.log2 n = Nat.log 2 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [log2_zero, log_zero_right]
  apply eq_of_forall_le_iff
  intro m
  rw [Nat.le_log2 hn, Nat.le_log_iff_pow_le Nat.one_lt_two hn]

@[simp]
lemma log_pow_left (b k n : ℕ) : log (b ^ k) n = log b n / k := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rcases k.eq_zero_or_pos with rfl | hk
    · simp
    · rcases Nat.lt_or_ge 1 b with hb | hb
      · refine eq_of_forall_le_iff fun c ↦ ?_
        rw [le_log_iff_pow_le (Nat.one_lt_pow (Nat.ne_of_gt hk) hb) hn, Nat.le_div_iff_mul_le hk,
          le_log_iff_pow_le hb hn, Nat.pow_mul']
      · rw [log_of_left_le_one hb, Nat.zero_div, log_of_left_le_one]
        rwa [Nat.pow_le_one_iff (Nat.ne_of_gt hk)]

/-! ### Ceil logarithm -/


/-- `clog b n`, is the upper logarithm of natural number `n` in base `b`. It returns the smallest
`k : ℕ` such that `n ≤ b^k`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot]
def clog (b n : ℕ) : ℕ :=
  if 1 < b ∧ 1 < n then (go b n).2 + 1 else 0 where
  /-- An auxiliary definition for `Nat.clog`.

  For `n > 1`, `b > 1`, `n ≤ b ^ fuel`, returns `(b ^ clog b n / n, clog b n - 1)`.
  -/
  go : ℕ → ℕ → ℕ × ℕ
  | b, 0 => (b / n, 0)
  | b, fuel + 1 =>
    if n ≤ b then (b / n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e + 1) else (q / b, 2 * e)

theorem clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n : ℕ) : clog b n = 0 := by
  grind [clog]

theorem clog_of_right_le_one {n : ℕ} (hn : n ≤ 1) (b : ℕ) : clog b n = 0 := by
  grind [clog]

@[simp] lemma clog_zero_left (n : ℕ) : clog 0 n = 0 := clog_of_left_le_one (Nat.zero_le _) _

@[simp] lemma clog_zero_right (b : ℕ) : clog b 0 = 0 := clog_of_right_le_one (Nat.zero_le _) _

@[simp]
theorem clog_one_left (n : ℕ) : clog 1 n = 0 :=
  clog_of_left_le_one le_rfl _

@[simp]
theorem clog_one_right (b : ℕ) : clog b 1 = 0 :=
  clog_of_right_le_one le_rfl _

theorem clog.go_spec {n b fuel} (hn : 1 < n) (hb : 1 < b) (hfuel : n < b ^ fuel) :
    (go n b fuel).1 = b ^ ((go n b fuel).2 + 1) / n ∧
      b ^ (go n b fuel).2 < n ∧ n ≤ b ^ ((go n b fuel).2 + 1) := by
  induction fuel generalizing b with
  | zero => simp_all
  | succ fuel ih =>
    cases Nat.lt_or_ge b n with
    | inr hbn => simp_all [go]
    | inl hbn =>
      rcases ih (Nat.one_mul 1 ▸ Nat.mul_lt_mul_of_lt_of_lt hb hb)
        (log.go_aux hb hfuel (Nat.le_of_lt hbn)) with ⟨ih₁, ih₂, ih₃⟩
      simp_all only [go, if_neg (Nat.not_le_of_gt hbn), ← Nat.pow_two, ← Nat.pow_mul,
        Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hbn), Nat.div_div_eq_div_mul,
        Nat.mul_comm n b, Nat.mul_add_one, @Nat.pow_add_one' _ (2 * _ + 1),
        Nat.mul_lt_mul_left, Nat.mul_div_mul_left, Nat.zero_lt_of_lt hb]
      split <;> simp_all [Nat.mul_add_one, Nat.pow_add_one']

/-- For `b > 1`, `clog b` and `(b ^ ·)` form a Galois connection.

See also `clog_le_of_le_pow` for the implication that does not require `1 < b`. -/
theorem clog_le_iff_le_pow {b : ℕ} (hb : 1 < b) {x y : ℕ} : clog b x ≤ y ↔ x ≤ b ^ y := by
  fun_cases clog with
  | case1 h =>
    rcases clog.go_spec h.2 hb (Nat.lt_pow_self hb) with ⟨-, H₁, H₂⟩
    cases Nat.lt_or_ge (clog.go x b x).2 y with
    | inl hy =>
      rw [← Nat.add_one_le_iff] at hy
      exact iff_of_true hy <| Nat.le_trans H₂ <| Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) hy
    | inr hy =>
      apply_rules [iff_of_false, Nat.not_le_of_gt, Nat.lt_add_one_of_le]
      exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) hy) H₁
  | case2 h => grind [Nat.one_le_pow]

theorem clog_pos {b n : ℕ} (hb : 1 < b) (hn : 1 < n) : 0 < clog b n := by
  rw [clog, if_pos]
  exacts [Nat.succ_pos _, ⟨hb, hn⟩]

theorem clog_of_one_lt {b n : ℕ} (hb : 1 < b) (hn : 1 < n) :
    clog b n = clog b ((n + b - 1) / b) + 1 := by
  apply eq_of_forall_ge_iff
  rintro (_ | c)
  · simp [Nat.ne_of_gt <| clog_pos hb hn]
  · simp only [clog_le_iff_le_pow, Nat.pow_add_one, Nat.add_le_add_iff_right, Nat.zero_lt_of_lt hb,
      div_le_iff_le_mul, hb]
    grind

theorem clog_of_two_le {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) :
    clog b n = clog b ((n + b - 1) / b) + 1 :=
  clog_of_one_lt hb hn

theorem clog_eq_one {b n : ℕ} (hn : 2 ≤ n) (h : n ≤ b) : clog b n = 1 := by
  rw [clog_of_two_le (hn.trans h) hn, clog_of_right_le_one]
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul] <;> lia

theorem clog_le_of_le_pow {b x y : ℕ} (h : x ≤ b ^ y) : clog b x ≤ y := by
  rcases Nat.lt_or_ge 1 b with hb | hb
  · rwa [clog_le_iff_le_pow hb]
  · grind [clog_of_left_le_one]

@[deprecated clog_le_iff_le_pow (since := "2025-10-05")]
theorem le_pow_iff_clog_le {b : ℕ} (hb : 1 < b) {x y : ℕ} : x ≤ b ^ y ↔ clog b x ≤ y :=
  (clog_le_iff_le_pow hb).symm

theorem lt_clog_iff_pow_lt {b : ℕ} (hb : 1 < b) {x y : ℕ} : y < clog b x ↔ b ^ y < x :=
  lt_iff_lt_of_le_iff_le (clog_le_iff_le_pow hb)

@[deprecated lt_clog_iff_pow_lt (since := "2025-10-05")]
theorem pow_lt_iff_lt_clog {b : ℕ} (hb : 1 < b) {x y : ℕ} : b ^ y < x ↔ y < clog b x :=
  (lt_clog_iff_pow_lt hb).symm

theorem pow_lt_of_lt_clog {b x y : ℕ} (h : y < clog b x) : b ^ y < x :=
  lt_imp_lt_of_le_imp_le clog_le_of_le_pow h

@[simp]
theorem clog_pow (b x : ℕ) (hb : 1 < b) : clog b (b ^ x) = x :=
  eq_of_forall_ge_iff fun z ↦ by rw [clog_le_iff_le_pow hb, Nat.pow_le_pow_iff_right hb]

theorem pow_pred_clog_lt_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 1 < x) :
    b ^ (clog b x).pred < x := by
  rw [← lt_clog_iff_pow_lt hb]
  exact pred_lt (clog_pos hb hx).ne'

theorem le_pow_clog {b : ℕ} (hb : 1 < b) (x : ℕ) : x ≤ b ^ clog b x :=
  (clog_le_iff_le_pow hb).1 le_rfl

@[mono, gcongr]
theorem clog_mono_right (b : ℕ) {n m : ℕ} (h : n ≤ m) : clog b n ≤ clog b m := by
  rcases le_or_gt b 1 with hb | hb
  · rw [clog_of_left_le_one hb]
    exact zero_le _
  · rw [clog_le_iff_le_pow hb]
    exact h.trans (le_pow_clog hb _)

theorem clog_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : clog b n ≤ clog c n := by
  rw [clog_le_iff_le_pow (lt_of_lt_of_le hc hb)]
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
    exact (lt_clog_iff_pow_lt hb).mp H
  · rw [lt_clog_iff_pow_lt hb, H]
    exact n.lt_add_one

theorem clog_eq_clog_succ_iff {b n : ℕ} (hb : 1 < b) :
    clog b n = clog b (n + 1) ↔ b ^ clog b n ≠ n := by
  rw [ne_eq, ← clog_lt_clog_succ_iff hb, not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun _ ↦ clog_monotone b (le_add_right n 1)

/-- This lemma says that `⌈log (b ^ k) n⌉ = ⌈(⌈log b n⌉ / k)⌉, using operations on natural numbers
to express this equality.

Since Lean has no dedicated function for the ceiling division,
we use `(a + (b - 1)) / b` for `⌈a / b⌉`. -/
theorem clog_pow_left (b k n : ℕ) : clog (b ^ k) n = (clog b n + (k - 1)) / k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  · rcases Nat.lt_or_ge 1 b with hb | hb
    · refine eq_of_forall_lt_iff fun c ↦ ?_
      rw [lt_clog_iff_pow_lt (Nat.one_lt_pow (Nat.ne_of_gt hk) hb), Nat.lt_div_iff_mul_lt hk,
        Nat.add_sub_cancel, lt_clog_iff_pow_lt hb, Nat.pow_mul']
    · suffices (k - 1) / k = 0 by grind [clog_of_left_le_one, Nat.pow_le_one_iff]
      apply Nat.div_eq_of_lt
      grind

end Nat
