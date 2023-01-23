/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module data.int.log
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Floor
import Mathbin.Data.Nat.Log

/-!
# Integer logarithms in a field with respect to a natural base

This file defines two `ℤ`-valued analogs of the logarithm of `r : R` with base `b : ℕ`:

* `int.log b r`: Lower logarithm, or floor **log**. Greatest `k` such that `↑b^k ≤ r`.
* `int.clog b r`: Upper logarithm, or **c**eil **log**. Least `k` such that `r ≤ ↑b^k`.

Note that `int.log` gives the position of the left-most non-zero digit:
```lean
#eval (int.log 10 (0.09 : ℚ), int.log 10 (0.10 : ℚ), int.log 10 (0.11 : ℚ))
--    (-2,                    -1,                    -1)
#eval (int.log 10 (9 : ℚ),    int.log 10 (10 : ℚ),   int.log 10 (11 : ℚ))
--    (0,                     1,                     1)
```
which means it can be used for computing digit expansions
```lean
import data.fin.vec_notation

def digits (b : ℕ) (q : ℚ) (n : ℕ) : ℕ :=
⌊q*b^(↑n - int.log b q)⌋₊ % b

#eval digits 10 (1/7) ∘ (coe : fin 8 → ℕ)
-- ![1, 4, 2, 8, 5, 7, 1, 4]
```

## Main results

* For `int.log`:
  * `int.zpow_log_le_self`, `int.lt_zpow_succ_log_self`: the bounds formed by `int.log`,
    `(b : R) ^ log b r ≤ r < (b : R) ^ (log b r + 1)`.
  * `int.zpow_log_gi`: the galois coinsertion between `zpow` and `int.log`.
* For `int.clog`:
  * `int.zpow_pred_clog_lt_self`, `int.self_le_zpow_clog`: the bounds formed by `int.clog`,
    `(b : R) ^ (clog b r - 1) < r ≤ (b : R) ^ clog b r`.
  * `int.clog_zpow_gi`:  the galois insertion between `int.clog` and `zpow`.
* `int.neg_log_inv_eq_clog`, `int.neg_clog_inv_eq_log`: the link between the two definitions.
-/


variable {R : Type _} [LinearOrderedSemifield R] [FloorSemiring R]

namespace Int

/-- The greatest power of `b` such that `b ^ log b r ≤ r`. -/
def log (b : ℕ) (r : R) : ℤ :=
  if 1 ≤ r then Nat.log b ⌊r⌋₊ else -Nat.clog b ⌈r⁻¹⌉₊
#align int.log Int.log

theorem log_of_one_le_right (b : ℕ) {r : R} (hr : 1 ≤ r) : log b r = Nat.log b ⌊r⌋₊ :=
  if_pos hr
#align int.log_of_one_le_right Int.log_of_one_le_right

theorem log_of_right_le_one (b : ℕ) {r : R} (hr : r ≤ 1) : log b r = -Nat.clog b ⌈r⁻¹⌉₊ :=
  by
  obtain rfl | hr := hr.eq_or_lt
  ·
    rw [log, if_pos hr, inv_one, Nat.ceil_one, Nat.floor_one, Nat.log_one_right, Nat.clog_one_right,
      Int.ofNat_zero, neg_zero]
  · exact if_neg hr.not_le
#align int.log_of_right_le_one Int.log_of_right_le_one

@[simp, norm_cast]
theorem log_nat_cast (b : ℕ) (n : ℕ) : log b (n : R) = Nat.log b n :=
  by
  cases n
  · simp [log_of_right_le_one _ _, Nat.log_zero_right]
  · have : 1 ≤ (n.succ : R) := by simp
    simp [log_of_one_le_right _ this, ← Nat.cast_succ]
#align int.log_nat_cast Int.log_nat_cast

theorem log_of_left_le_one {b : ℕ} (hb : b ≤ 1) (r : R) : log b r = 0 :=
  by
  cases le_total 1 r
  · rw [log_of_one_le_right _ h, Nat.log_of_left_le_one hb, Int.ofNat_zero]
  · rw [log_of_right_le_one _ h, Nat.clog_of_left_le_one hb, Int.ofNat_zero, neg_zero]
#align int.log_of_left_le_one Int.log_of_left_le_one

theorem log_of_right_le_zero (b : ℕ) {r : R} (hr : r ≤ 0) : log b r = 0 := by
  rw [log_of_right_le_one _ (hr.trans zero_le_one),
    Nat.clog_of_right_le_one ((nat.ceil_eq_zero.mpr <| inv_nonpos.2 hr).trans_le zero_le_one),
    Int.ofNat_zero, neg_zero]
#align int.log_of_right_le_zero Int.log_of_right_le_zero

theorem zpow_log_le_self {b : ℕ} {r : R} (hb : 1 < b) (hr : 0 < r) : (b : R) ^ log b r ≤ r :=
  by
  cases' le_total 1 r with hr1 hr1
  · rw [log_of_one_le_right _ hr1]
    rw [zpow_ofNat, ← Nat.cast_pow, ← Nat.le_floor_iff hr.le]
    exact Nat.pow_log_le_self b (nat.floor_pos.mpr hr1).ne'
  · rw [log_of_right_le_one _ hr1, zpow_neg, zpow_ofNat, ← Nat.cast_pow]
    exact inv_le_of_inv_le hr (Nat.ceil_le.1 <| Nat.le_pow_clog hb _)
#align int.zpow_log_le_self Int.zpow_log_le_self

theorem lt_zpow_succ_log_self {b : ℕ} (hb : 1 < b) (r : R) : r < (b : R) ^ (log b r + 1) :=
  by
  cases' le_or_lt r 0 with hr hr
  · rw [log_of_right_le_zero _ hr, zero_add, zpow_one]
    exact hr.trans_lt (zero_lt_one.trans_le <| by exact_mod_cast hb.le)
  cases' le_or_lt 1 r with hr1 hr1
  · rw [log_of_one_le_right _ hr1]
    rw [Int.ofNat_add_one_out, zpow_ofNat, ← Nat.cast_pow]
    apply Nat.lt_of_floor_lt
    exact Nat.lt_pow_succ_log_self hb _
  · rw [log_of_right_le_one _ hr1.le]
    have hcri : 1 < r⁻¹ := one_lt_inv hr hr1
    have : 1 ≤ Nat.clog b ⌈r⁻¹⌉₊ :=
      Nat.succ_le_of_lt (Nat.clog_pos hb <| Nat.one_lt_cast.1 <| hcri.trans_le (Nat.le_ceil _))
    rw [neg_add_eq_sub, ← neg_sub, ← Int.ofNat_one, ← Int.ofNat_sub this, zpow_neg, zpow_ofNat,
      lt_inv hr (pow_pos (nat.cast_pos.mpr <| zero_lt_one.trans hb) _), ← Nat.cast_pow]
    refine' Nat.lt_ceil.1 _
    exact Nat.pow_pred_clog_lt_self hb <| Nat.one_lt_cast.1 <| hcri.trans_le <| Nat.le_ceil _
#align int.lt_zpow_succ_log_self Int.lt_zpow_succ_log_self

@[simp]
theorem log_zero_right (b : ℕ) : log b (0 : R) = 0 :=
  log_of_right_le_zero b le_rfl
#align int.log_zero_right Int.log_zero_right

@[simp]
theorem log_one_right (b : ℕ) : log b (1 : R) = 0 := by
  rw [log_of_one_le_right _ le_rfl, Nat.floor_one, Nat.log_one_right, Int.ofNat_zero]
#align int.log_one_right Int.log_one_right

theorem log_zpow {b : ℕ} (hb : 1 < b) (z : ℤ) : log b (b ^ z : R) = z :=
  by
  obtain ⟨n, rfl | rfl⟩ := z.eq_coe_or_neg
  · rw [log_of_one_le_right _ (one_le_zpow_of_nonneg _ <| Int.coe_nat_nonneg _), zpow_ofNat, ←
      Nat.cast_pow, Nat.floor_coe, Nat.log_pow hb]
    exact_mod_cast hb.le
  · rw [log_of_right_le_one _ (zpow_le_one_of_nonpos _ <| neg_nonpos.mpr (Int.coe_nat_nonneg _)),
      zpow_neg, inv_inv, zpow_ofNat, ← Nat.cast_pow, Nat.ceil_natCast, Nat.clog_pow _ _ hb]
    exact_mod_cast hb.le
#align int.log_zpow Int.log_zpow

@[mono]
theorem log_mono_right {b : ℕ} {r₁ r₂ : R} (h₀ : 0 < r₁) (h : r₁ ≤ r₂) : log b r₁ ≤ log b r₂ :=
  by
  cases' le_or_lt b 1 with hb hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb]
  cases' le_total r₁ 1 with h₁ h₁ <;> cases' le_total r₂ 1 with h₂ h₂
  · rw [log_of_right_le_one _ h₁, log_of_right_le_one _ h₂, neg_le_neg_iff, Int.ofNat_le]
    exact Nat.clog_mono_right _ (Nat.ceil_mono <| inv_le_inv_of_le h₀ h)
  · rw [log_of_right_le_one _ h₁, log_of_one_le_right _ h₂]
    exact (neg_nonpos.mpr (Int.coe_nat_nonneg _)).trans (Int.coe_nat_nonneg _)
  · obtain rfl := le_antisymm h (h₂.trans h₁)
    rfl
  · rw [log_of_one_le_right _ h₁, log_of_one_le_right _ h₂, Int.ofNat_le]
    exact Nat.log_mono_right (Nat.floor_mono h)
#align int.log_mono_right Int.log_mono_right

variable (R)

/-- Over suitable subtypes, `zpow` and `int.log` form a galois coinsertion -/
def zpowLogGi {b : ℕ} (hb : 1 < b) :
    GaloisCoinsertion
      (fun z : ℤ =>
        Subtype.mk ((b : R) ^ z) <| zpow_pos_of_pos (by exact_mod_cast zero_lt_one.trans hb) z)
      fun r : Set.Ioi (0 : R) => Int.log b (r : R) :=
  GaloisCoinsertion.monotoneIntro (fun r₁ r₂ => log_mono_right r₁.Prop)
    (fun z₁ z₂ hz => Subtype.coe_le_coe.mp <| (zpow_strictMono <| by exact_mod_cast hb).Monotone hz)
    (fun r => Subtype.coe_le_coe.mp <| zpow_log_le_self hb r.Prop) fun _ => log_zpow hb _
#align int.zpow_log_gi Int.zpowLogGi

variable {R}

/-- `zpow b` and `int.log b` (almost) form a Galois connection. -/
theorem lt_zpow_iff_log_lt {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
    r < (b : R) ^ x ↔ log b r < x :=
  @GaloisConnection.lt_iff_lt _ _ _ _ _ _ (zpowLogGi R hb).gc x ⟨r, hr⟩
#align int.lt_zpow_iff_log_lt Int.lt_zpow_iff_log_lt

/-- `zpow b` and `int.log b` (almost) form a Galois connection. -/
theorem zpow_le_iff_le_log {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
    (b : R) ^ x ≤ r ↔ x ≤ log b r :=
  @GaloisConnection.le_iff_le _ _ _ _ _ _ (zpowLogGi R hb).gc x ⟨r, hr⟩
#align int.zpow_le_iff_le_log Int.zpow_le_iff_le_log

/-- The least power of `b` such that `r ≤ b ^ log b r`. -/
def clog (b : ℕ) (r : R) : ℤ :=
  if 1 ≤ r then Nat.clog b ⌈r⌉₊ else -Nat.log b ⌊r⁻¹⌋₊
#align int.clog Int.clog

theorem clog_of_one_le_right (b : ℕ) {r : R} (hr : 1 ≤ r) : clog b r = Nat.clog b ⌈r⌉₊ :=
  if_pos hr
#align int.clog_of_one_le_right Int.clog_of_one_le_right

theorem clog_of_right_le_one (b : ℕ) {r : R} (hr : r ≤ 1) : clog b r = -Nat.log b ⌊r⁻¹⌋₊ :=
  by
  obtain rfl | hr := hr.eq_or_lt
  ·
    rw [clog, if_pos hr, inv_one, Nat.ceil_one, Nat.floor_one, Nat.log_one_right,
      Nat.clog_one_right, Int.ofNat_zero, neg_zero]
  · exact if_neg hr.not_le
#align int.clog_of_right_le_one Int.clog_of_right_le_one

theorem clog_of_right_le_zero (b : ℕ) {r : R} (hr : r ≤ 0) : clog b r = 0 :=
  by
  rw [clog, if_neg (hr.trans_lt zero_lt_one).not_le, neg_eq_zero, Int.coe_nat_eq_zero,
    Nat.log_eq_zero_iff]
  cases' le_or_lt b 1 with hb hb
  · exact Or.inr hb
  · refine' Or.inl (lt_of_le_of_lt _ hb)
    exact Nat.floor_le_one_of_le_one ((inv_nonpos.2 hr).trans zero_le_one)
#align int.clog_of_right_le_zero Int.clog_of_right_le_zero

@[simp]
theorem clog_inv (b : ℕ) (r : R) : clog b r⁻¹ = -log b r :=
  by
  cases' lt_or_le 0 r with hrp hrp
  · obtain hr | hr := le_total 1 r
    · rw [clog_of_right_le_one _ (inv_le_one hr), log_of_one_le_right _ hr, inv_inv]
    · rw [clog_of_one_le_right _ (one_le_inv hrp hr), log_of_right_le_one _ hr, neg_neg]
  · rw [clog_of_right_le_zero _ (inv_nonpos.mpr hrp), log_of_right_le_zero _ hrp, neg_zero]
#align int.clog_inv Int.clog_inv

@[simp]
theorem log_inv (b : ℕ) (r : R) : log b r⁻¹ = -clog b r := by
  rw [← inv_inv r, clog_inv, neg_neg, inv_inv]
#align int.log_inv Int.log_inv

-- note this is useful for writing in reverse
theorem neg_log_inv_eq_clog (b : ℕ) (r : R) : -log b r⁻¹ = clog b r := by rw [log_inv, neg_neg]
#align int.neg_log_inv_eq_clog Int.neg_log_inv_eq_clog

theorem neg_clog_inv_eq_log (b : ℕ) (r : R) : -clog b r⁻¹ = log b r := by rw [clog_inv, neg_neg]
#align int.neg_clog_inv_eq_log Int.neg_clog_inv_eq_log

@[simp, norm_cast]
theorem clog_nat_cast (b : ℕ) (n : ℕ) : clog b (n : R) = Nat.clog b n :=
  by
  cases n
  · simp [clog_of_right_le_one _ _, Nat.clog_zero_right]
  · have : 1 ≤ (n.succ : R) := by simp
    simp [clog_of_one_le_right _ this, ← Nat.cast_succ]
#align int.clog_nat_cast Int.clog_nat_cast

theorem clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (r : R) : clog b r = 0 := by
  rw [← neg_log_inv_eq_clog, log_of_left_le_one hb, neg_zero]
#align int.clog_of_left_le_one Int.clog_of_left_le_one

theorem self_le_zpow_clog {b : ℕ} (hb : 1 < b) (r : R) : r ≤ (b : R) ^ clog b r :=
  by
  cases' le_or_lt r 0 with hr hr
  · rw [clog_of_right_le_zero _ hr, zpow_zero]
    exact hr.trans zero_le_one
  rw [← neg_log_inv_eq_clog, zpow_neg, le_inv hr (zpow_pos_of_pos _ _)]
  · exact zpow_log_le_self hb (inv_pos.mpr hr)
  · exact nat.cast_pos.mpr (zero_le_one.trans_lt hb)
#align int.self_le_zpow_clog Int.self_le_zpow_clog

theorem zpow_pred_clog_lt_self {b : ℕ} {r : R} (hb : 1 < b) (hr : 0 < r) :
    (b : R) ^ (clog b r - 1) < r :=
  by
  rw [← neg_log_inv_eq_clog, ← neg_add', zpow_neg, inv_lt _ hr]
  · exact lt_zpow_succ_log_self hb _
  · exact zpow_pos_of_pos (nat.cast_pos.mpr <| zero_le_one.trans_lt hb) _
#align int.zpow_pred_clog_lt_self Int.zpow_pred_clog_lt_self

@[simp]
theorem clog_zero_right (b : ℕ) : clog b (0 : R) = 0 :=
  clog_of_right_le_zero _ le_rfl
#align int.clog_zero_right Int.clog_zero_right

@[simp]
theorem clog_one_right (b : ℕ) : clog b (1 : R) = 0 := by
  rw [clog_of_one_le_right _ le_rfl, Nat.ceil_one, Nat.clog_one_right, Int.ofNat_zero]
#align int.clog_one_right Int.clog_one_right

theorem clog_zpow {b : ℕ} (hb : 1 < b) (z : ℤ) : clog b (b ^ z : R) = z := by
  rw [← neg_log_inv_eq_clog, ← zpow_neg, log_zpow hb, neg_neg]
#align int.clog_zpow Int.clog_zpow

@[mono]
theorem clog_mono_right {b : ℕ} {r₁ r₂ : R} (h₀ : 0 < r₁) (h : r₁ ≤ r₂) : clog b r₁ ≤ clog b r₂ :=
  by
  rw [← neg_log_inv_eq_clog, ← neg_log_inv_eq_clog, neg_le_neg_iff]
  exact log_mono_right (inv_pos.mpr <| h₀.trans_le h) (inv_le_inv_of_le h₀ h)
#align int.clog_mono_right Int.clog_mono_right

variable (R)

/-- Over suitable subtypes, `int.clog` and `zpow` form a galois insertion -/
def clogZpowGi {b : ℕ} (hb : 1 < b) :
    GaloisInsertion (fun r : Set.Ioi (0 : R) => Int.clog b (r : R)) fun z : ℤ =>
      ⟨(b : R) ^ z, zpow_pos_of_pos (by exact_mod_cast zero_lt_one.trans hb) z⟩ :=
  GaloisInsertion.monotoneIntro
    (fun z₁ z₂ hz => Subtype.coe_le_coe.mp <| (zpow_strictMono <| by exact_mod_cast hb).Monotone hz)
    (fun r₁ r₂ => clog_mono_right r₁.Prop)
    (fun r => Subtype.coe_le_coe.mp <| self_le_zpow_clog hb _) fun _ => clog_zpow hb _
#align int.clog_zpow_gi Int.clogZpowGi

variable {R}

/-- `int.clog b` and `zpow b` (almost) form a Galois connection. -/
theorem zpow_lt_iff_lt_clog {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
    (b : R) ^ x < r ↔ x < clog b r :=
  (@GaloisConnection.lt_iff_lt _ _ _ _ _ _ (clogZpowGi R hb).gc ⟨r, hr⟩ x).symm
#align int.zpow_lt_iff_lt_clog Int.zpow_lt_iff_lt_clog

/-- `int.clog b` and `zpow b` (almost) form a Galois connection. -/
theorem le_zpow_iff_clog_le {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
    r ≤ (b : R) ^ x ↔ clog b r ≤ x :=
  (@GaloisConnection.le_iff_le _ _ _ _ _ _ (clogZpowGi R hb).gc ⟨r, hr⟩ x).symm
#align int.le_zpow_iff_clog_le Int.le_zpow_iff_clog_le

end Int

