/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Log

/-!
# Integer logarithms in a field with respect to a natural base

This file defines two `ℤ`-valued analogs of the logarithm of `r : R` with base `b : ℕ`:

* `Int.log b r`: Lower logarithm, or floor **log**. Greatest `k` such that `↑b^k ≤ r`.
* `Int.clog b r`: Upper logarithm, or **c**eil **log**. Least `k` such that `r ≤ ↑b^k`.

Note that `Int.log` gives the position of the left-most non-zero digit:
```lean
#eval (Int.log 10 (0.09 : ℚ), Int.log 10 (0.10 : ℚ), Int.log 10 (0.11 : ℚ))
--    (-2,                    -1,                    -1)
#eval (Int.log 10 (9 : ℚ),    Int.log 10 (10 : ℚ),   Int.log 10 (11 : ℚ))
--    (0,                     1,                     1)
```
which means it can be used for computing digit expansions
```lean
import Data.Fin.VecNotation
import Mathlib.Data.Rat.Floor

def digits (b : ℕ) (q : ℚ) (n : ℕ) : ℕ :=
  ⌊q * ((b : ℚ) ^ (n - Int.log b q))⌋₊ % b

#eval digits 10 (1/7) ∘ ((↑) : Fin 8 → ℕ)
-- ![1, 4, 2, 8, 5, 7, 1, 4]
```

## Main results

* For `Int.log`:
  * `Int.zpow_log_le_self`, `Int.lt_zpow_succ_log_self`: the bounds formed by `Int.log`,
    `(b : R) ^ log b r ≤ r < (b : R) ^ (log b r + 1)`.
  * `Int.zpow_log_gi`: the Galois coinsertion between `zpow` and `Int.log`.
* For `Int.clog`:
  * `Int.zpow_pred_clog_lt_self`, `Int.self_le_zpow_clog`: the bounds formed by `Int.clog`,
    `(b : R) ^ (clog b r - 1) < r ≤ (b : R) ^ clog b r`.
  * `Int.clog_zpow_gi`:  the Galois insertion between `Int.clog` and `zpow`.
* `Int.neg_log_inv_eq_clog`, `Int.neg_clog_inv_eq_log`: the link between the two definitions.
-/

assert_not_exists Finset

variable {R : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

namespace Int

/-- The greatest power of `b` such that `b ^ log b r ≤ r`. -/
def log (b : ℕ) (r : R) : ℤ :=
  if 1 ≤ r then Nat.log b ⌊r⌋₊ else -Nat.clog b ⌈r⁻¹⌉₊

omit [IsStrictOrderedRing R] in
theorem log_of_one_le_right (b : ℕ) {r : R} (hr : 1 ≤ r) : log b r = Nat.log b ⌊r⌋₊ :=
  if_pos hr

theorem log_of_right_le_one (b : ℕ) {r : R} (hr : r ≤ 1) : log b r = -Nat.clog b ⌈r⁻¹⌉₊ := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [log, if_pos hr, inv_one, Nat.ceil_one, Nat.floor_one, Nat.log_one_right, Nat.clog_one_right,
      Int.ofNat_zero, neg_zero]
  · exact if_neg hr.not_ge

@[simp, norm_cast]
theorem log_natCast (b : ℕ) (n : ℕ) : log b (n : R) = Nat.log b n := by
  cases n
  · simp [log_of_right_le_one]
  · rw [log_of_one_le_right, Nat.floor_natCast]
    simp

@[simp]
theorem log_ofNat (b : ℕ) (n : ℕ) [n.AtLeastTwo] :
    log b (ofNat(n) : R) = Nat.log b ofNat(n) :=
  log_natCast b n

theorem log_of_left_le_one {b : ℕ} (hb : b ≤ 1) (r : R) : log b r = 0 := by
  rcases le_total 1 r with h | h
  · rw [log_of_one_le_right _ h, Nat.log_of_left_le_one hb, Int.ofNat_zero]
  · rw [log_of_right_le_one _ h, Nat.clog_of_left_le_one hb, Int.ofNat_zero, neg_zero]

theorem log_of_right_le_zero (b : ℕ) {r : R} (hr : r ≤ 0) : log b r = 0 := by
  rw [log_of_right_le_one _ (hr.trans zero_le_one),
    Nat.clog_of_right_le_one ((Nat.ceil_eq_zero.mpr <| inv_nonpos.2 hr).trans_le zero_le_one),
    Int.ofNat_zero, neg_zero]

theorem zpow_log_le_self {b : ℕ} {r : R} (hb : 1 < b) (hr : 0 < r) : (b : R) ^ log b r ≤ r := by
  rcases le_total 1 r with hr1 | hr1
  · rw [log_of_one_le_right _ hr1]
    rw [zpow_natCast, ← Nat.cast_pow, ← Nat.le_floor_iff hr.le]
    exact Nat.pow_log_le_self b (Nat.floor_pos.mpr hr1).ne'
  · rw [log_of_right_le_one _ hr1, zpow_neg, zpow_natCast, ← Nat.cast_pow]
    exact inv_le_of_inv_le₀ hr (Nat.ceil_le.1 <| Nat.le_pow_clog hb _)

theorem lt_zpow_succ_log_self {b : ℕ} (hb : 1 < b) (r : R) : r < (b : R) ^ (log b r + 1) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [log_of_right_le_zero _ hr, zero_add, zpow_one]
    exact hr.trans_lt (zero_lt_one.trans_le <| mod_cast hb.le)
  rcases le_or_gt 1 r with hr1 | hr1
  · rw [log_of_one_le_right _ hr1]
    rw [Int.ofNat_add_one_out, zpow_natCast, ← Nat.cast_pow]
    apply Nat.lt_of_floor_lt
    exact Nat.lt_pow_succ_log_self hb _
  · rw [log_of_right_le_one _ hr1.le]
    have hcri : 1 < r⁻¹ := (one_lt_inv₀ hr).2 hr1
    have : 1 ≤ Nat.clog b ⌈r⁻¹⌉₊ :=
      Nat.succ_le_of_lt (Nat.clog_pos hb <| Nat.one_lt_cast.1 <| hcri.trans_le (Nat.le_ceil _))
    rw [neg_add_eq_sub, ← neg_sub, ← Int.ofNat_one, ← Int.ofNat_sub this, zpow_neg, zpow_natCast,
      lt_inv_comm₀ hr (pow_pos (Nat.cast_pos.mpr <| zero_lt_one.trans hb) _), ← Nat.cast_pow]
    refine Nat.lt_ceil.1 ?_
    exact Nat.pow_pred_clog_lt_self hb <| Nat.one_lt_cast.1 <| hcri.trans_le <| Nat.le_ceil _

@[simp]
theorem log_zero_right (b : ℕ) : log b (0 : R) = 0 :=
  log_of_right_le_zero b le_rfl

@[simp]
theorem log_one_right (b : ℕ) : log b (1 : R) = 0 := by
  rw [log_of_one_le_right _ le_rfl, Nat.floor_one, Nat.log_one_right, Int.ofNat_zero]

omit [IsStrictOrderedRing R] in
@[simp]
theorem log_zero_left (r : R) : log 0 r = 0 := by
  simp only [log, Nat.log_zero_left, Nat.cast_zero, Nat.clog_zero_left, neg_zero, ite_self]

omit [IsStrictOrderedRing R] in
@[simp]
theorem log_one_left (r : R) : log 1 r = 0 := by
  by_cases hr : 1 ≤ r
  · simp_all only [log, ↓reduceIte, Nat.log_one_left, Nat.cast_zero]
  · simp only [log, Nat.log_one_left, Nat.cast_zero, Nat.clog_one_left, neg_zero, ite_self]

theorem log_zpow {b : ℕ} (hb : 1 < b) (z : ℤ) : log b (b ^ z : R) = z := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [log_of_one_le_right _ (one_le_zpow₀ (mod_cast hb.le) <| Int.natCast_nonneg _), zpow_natCast,
      ← Nat.cast_pow, Nat.floor_natCast, Nat.log_pow hb]
  · rw [log_of_right_le_one _ (zpow_le_one_of_nonpos₀ (mod_cast hb.le) <|
      neg_nonpos.2 (Int.natCast_nonneg _)),
      zpow_neg, inv_inv, zpow_natCast, ← Nat.cast_pow, Nat.ceil_natCast, Nat.clog_pow _ _ hb]

@[mono, gcongr]
theorem log_mono_right {b : ℕ} {r₁ r₂ : R} (h₀ : 0 < r₁) (h : r₁ ≤ r₂) : log b r₁ ≤ log b r₂ := by
  rcases le_total r₁ 1 with h₁ | h₁ <;> rcases le_total r₂ 1 with h₂ | h₂
  · have h₀' : 0 < r₂ := lt_of_lt_of_le h₀ h
    rw [log_of_right_le_one _ h₁, log_of_right_le_one _ h₂, neg_le_neg_iff, Nat.cast_le]
    exact Nat.clog_mono_right b <| Nat.ceil_mono <| (inv_le_inv₀ h₀' h₀).2 h
  · rw [log_of_right_le_one _ h₁, log_of_one_le_right _ h₂]
    exact (neg_nonpos.mpr (Int.natCast_nonneg _)).trans (Int.natCast_nonneg _)
  · obtain rfl := le_antisymm h (h₂.trans h₁)
    rfl
  · rw [log_of_one_le_right _ h₁, log_of_one_le_right _ h₂, Nat.cast_le]
    exact Nat.log_mono_right (Nat.floor_mono h)

variable (R) in
/-- Over suitable subtypes, `zpow` and `Int.log` form a Galois coinsertion -/
def zpowLogGi {b : ℕ} (hb : 1 < b) :
    GaloisCoinsertion
      (fun z : ℤ =>
        Subtype.mk ((b : R) ^ z) <| zpow_pos (mod_cast zero_lt_one.trans hb) z)
      fun r : Set.Ioi (0 : R) => Int.log b (r : R) :=
  GaloisCoinsertion.monotoneIntro (fun r₁ _ => log_mono_right r₁.2)
    (fun _ _ hz => Subtype.coe_le_coe.mp <| (zpow_right_strictMono₀ <| mod_cast hb).monotone hz)
    (fun r => Subtype.coe_le_coe.mp <| zpow_log_le_self hb r.2) fun _ => log_zpow (R := R) hb _

/-- `zpow b` and `Int.log b` (almost) form a Galois connection. -/
theorem lt_zpow_iff_log_lt {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
    r < (b : R) ^ x ↔ log b r < x :=
  @GaloisConnection.lt_iff_lt _ _ _ _ _ _ (zpowLogGi R hb).gc x ⟨r, hr⟩

/-- `zpow b` and `Int.log b` (almost) form a Galois connection. -/
theorem zpow_le_iff_le_log {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
    (b : R) ^ x ≤ r ↔ x ≤ log b r :=
  @GaloisConnection.le_iff_le _ _ _ _ _ _ (zpowLogGi R hb).gc x ⟨r, hr⟩

/-- The least power of `b` such that `r ≤ b ^ log b r`. -/
def clog (b : ℕ) (r : R) : ℤ :=
  if 1 ≤ r then Nat.clog b ⌈r⌉₊ else -Nat.log b ⌊r⁻¹⌋₊

omit [IsStrictOrderedRing R] in
theorem clog_of_one_le_right (b : ℕ) {r : R} (hr : 1 ≤ r) : clog b r = Nat.clog b ⌈r⌉₊ :=
  if_pos hr

theorem clog_of_right_le_one (b : ℕ) {r : R} (hr : r ≤ 1) : clog b r = -Nat.log b ⌊r⁻¹⌋₊ := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [clog, if_pos hr, inv_one, Nat.ceil_one, Nat.floor_one, Nat.log_one_right,
      Nat.clog_one_right, Int.ofNat_zero, neg_zero]
  · exact if_neg hr.not_ge

theorem clog_of_right_le_zero (b : ℕ) {r : R} (hr : r ≤ 0) : clog b r = 0 := by
  rw [clog, if_neg (hr.trans_lt zero_lt_one).not_ge, neg_eq_zero, Int.natCast_eq_zero,
    Nat.log_eq_zero_iff]
  rcases le_or_gt b 1 with hb | hb
  · exact Or.inr hb
  · refine Or.inl (lt_of_le_of_lt ?_ hb)
    exact Nat.floor_le_one_of_le_one ((inv_nonpos.2 hr).trans zero_le_one)

@[simp]
theorem clog_inv (b : ℕ) (r : R) : clog b r⁻¹ = -log b r := by
  rcases lt_or_ge 0 r with hrp | hrp
  · obtain hr | hr := le_total 1 r
    · rw [clog_of_right_le_one _ (inv_le_one_of_one_le₀ hr), log_of_one_le_right _ hr, inv_inv]
    · rw [clog_of_one_le_right _ ((one_le_inv₀ hrp).2 hr), log_of_right_le_one _ hr, neg_neg]
  · rw [clog_of_right_le_zero _ (inv_nonpos.mpr hrp), log_of_right_le_zero _ hrp, neg_zero]

@[simp]
theorem log_inv (b : ℕ) (r : R) : log b r⁻¹ = -clog b r := by
  rw [← inv_inv r, clog_inv, neg_neg, inv_inv]

-- note this is useful for writing in reverse
theorem neg_log_inv_eq_clog (b : ℕ) (r : R) : -log b r⁻¹ = clog b r := by rw [log_inv, neg_neg]

theorem neg_clog_inv_eq_log (b : ℕ) (r : R) : -clog b r⁻¹ = log b r := by rw [clog_inv, neg_neg]

@[simp, norm_cast]
theorem clog_natCast (b : ℕ) (n : ℕ) : clog b (n : R) = Nat.clog b n := by
  rcases n with - | n
  · simp [clog_of_right_le_one]
  · rw [clog_of_one_le_right, (Nat.ceil_eq_iff (Nat.succ_ne_zero n)).mpr] <;> simp

@[simp]
theorem clog_ofNat (b : ℕ) (n : ℕ) [n.AtLeastTwo] :
    clog b (ofNat(n) : R) = Nat.clog b ofNat(n) :=
  clog_natCast b n

theorem clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (r : R) : clog b r = 0 := by
  rw [← neg_log_inv_eq_clog, log_of_left_le_one hb, neg_zero]

theorem self_le_zpow_clog {b : ℕ} (hb : 1 < b) (r : R) : r ≤ (b : R) ^ clog b r := by
  rcases le_or_gt r 0 with hr | hr
  · rw [clog_of_right_le_zero _ hr, zpow_zero]
    exact hr.trans zero_le_one
  rw [← neg_log_inv_eq_clog, zpow_neg, le_inv_comm₀ hr (zpow_pos ..)]
  · exact zpow_log_le_self hb (inv_pos.mpr hr)
  · exact Nat.cast_pos.mpr (zero_le_one.trans_lt hb)

theorem zpow_pred_clog_lt_self {b : ℕ} {r : R} (hb : 1 < b) (hr : 0 < r) :
    (b : R) ^ (clog b r - 1) < r := by
  rw [← neg_log_inv_eq_clog, ← neg_add', zpow_neg, inv_lt_comm₀ _ hr]
  · exact lt_zpow_succ_log_self hb _
  · exact zpow_pos (Nat.cast_pos.mpr <| zero_le_one.trans_lt hb) _

@[simp]
theorem clog_zero_right (b : ℕ) : clog b (0 : R) = 0 :=
  clog_of_right_le_zero _ le_rfl

@[simp]
theorem clog_one_right (b : ℕ) : clog b (1 : R) = 0 := by
  rw [clog_of_one_le_right _ le_rfl, Nat.ceil_one, Nat.clog_one_right, Int.ofNat_zero]

omit [IsStrictOrderedRing R] in
@[simp]
theorem clog_zero_left (r : R) : clog 0 r = 0 := by
  by_cases hr : 1 ≤ r
  · simp only [clog, Nat.clog_zero_left, Nat.cast_zero, Nat.log_zero_left, neg_zero, ite_self]
  · simp only [clog, hr, ite_cond_eq_false, Nat.log_zero_left, Nat.cast_zero, neg_zero]

omit [IsStrictOrderedRing R] in
@[simp]
theorem clog_one_left (r : R) : clog 1 r = 0 := by
  simp only [clog, Nat.log_one_left, Nat.cast_zero, Nat.clog_one_left, neg_zero, ite_self]

theorem clog_zpow {b : ℕ} (hb : 1 < b) (z : ℤ) : clog b (b ^ z : R) = z := by
  rw [← neg_log_inv_eq_clog, ← zpow_neg, log_zpow hb, neg_neg]

@[mono]
theorem clog_mono_right {b : ℕ} {r₁ r₂ : R} (h₀ : 0 < r₁) (h : r₁ ≤ r₂) :
    clog b r₁ ≤ clog b r₂ := by
  have h₀' : 0 < r₂ := lt_of_lt_of_le h₀ h
  rw [← neg_log_inv_eq_clog, ← neg_log_inv_eq_clog, neg_le_neg_iff]
  exact log_mono_right (inv_pos_of_pos h₀') <| (inv_le_inv₀ h₀' h₀).2 h

variable (R) in
/-- Over suitable subtypes, `Int.clog` and `zpow` form a Galois insertion -/
def clogZPowGi {b : ℕ} (hb : 1 < b) :
    GaloisInsertion (fun r : Set.Ioi (0 : R) => Int.clog b (r : R)) fun z : ℤ =>
      ⟨(b : R) ^ z, zpow_pos (mod_cast zero_lt_one.trans hb) z⟩ :=
  GaloisInsertion.monotoneIntro
    (fun _ _ hz => Subtype.coe_le_coe.mp <| (zpow_right_strictMono₀ <| mod_cast hb).monotone hz)
    (fun r₁ _ => clog_mono_right r₁.2)
    (fun _ => Subtype.coe_le_coe.mp <| self_le_zpow_clog hb _) fun _ => clog_zpow (R := R) hb _

/-- `Int.clog b` and `zpow b` (almost) form a Galois connection. -/
theorem zpow_lt_iff_lt_clog {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
    (b : R) ^ x < r ↔ x < clog b r :=
  (@GaloisConnection.lt_iff_lt _ _ _ _ _ _ (clogZPowGi R hb).gc ⟨r, hr⟩ x).symm

/-- `Int.clog b` and `zpow b` (almost) form a Galois connection. -/
theorem le_zpow_iff_clog_le {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
    r ≤ (b : R) ^ x ↔ clog b r ≤ x :=
  (@GaloisConnection.le_iff_le _ _ _ _ _ _ (clogZPowGi R hb).gc ⟨r, hr⟩ x).symm

end Int
