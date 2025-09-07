/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Log

/-!
# Real logarithm base `b`

In this file we define `Real.logb` to be the logarithm of a real number in a given base `b`. We
define this as the division of the natural logarithms of the argument and the base, so that we have
a globally defined function with `logb b 0 = 0`, `logb b (-x) = logb b x` `logb 0 x = 0` and
`logb (-b) x = logb b x`.

We prove some basic properties of this function and its relation to `rpow`.

## Tags

logarithm, continuity
-/


open Set Filter Function

open Topology

noncomputable section

namespace Real

variable {b x y : ℝ}

/-- The real logarithm in a given base. As with the natural logarithm, we define `logb b x` to
be `logb b |x|` for `x < 0`, and `0` for `x = 0`. -/
@[pp_nodot]
noncomputable def logb (b x : ℝ) : ℝ :=
  log x / log b

theorem log_div_log : log x / log b = logb b x :=
  rfl

@[simp]
theorem logb_zero : logb b 0 = 0 := by simp [logb]

@[simp]
theorem logb_one : logb b 1 = 0 := by simp [logb]

theorem logb_zero_left : logb 0 x = 0 := by simp only [← log_div_log, log_zero, div_zero]

@[simp] theorem logb_zero_left_eq_zero : logb 0 = 0 := by ext; rw [logb_zero_left, Pi.zero_apply]

theorem logb_one_left : logb 1 x = 0 := by simp only [← log_div_log, log_one, div_zero]

@[simp] theorem logb_one_left_eq_zero : logb 1 = 0 := by ext; rw [logb_one_left, Pi.zero_apply]

@[simp]
lemma logb_self_eq_one (hb : 1 < b) : logb b b = 1 :=
  div_self (log_pos hb).ne'

lemma logb_self_eq_one_iff : logb b b = 1 ↔ b ≠ 0 ∧ b ≠ 1 ∧ b ≠ -1 :=
  Iff.trans ⟨fun h h' => by simp [logb, h'] at h, div_self⟩ log_ne_zero

@[simp]
theorem logb_abs_base (b x : ℝ) : logb |b| x = logb b x := by rw [logb, logb, log_abs]

@[simp]
theorem logb_abs (b x : ℝ) : logb b |x| = logb b x := by rw [logb, logb, log_abs]

@[simp]
theorem logb_neg_base_eq_logb (b x : ℝ) : logb (-b) x = logb b x := by
  rw [← logb_abs_base b x, ← logb_abs_base (-b) x, abs_neg]

@[simp]
theorem logb_neg_eq_logb (b x : ℝ) : logb b (-x) = logb b x := by
  rw [← logb_abs b x, ← logb_abs b (-x), abs_neg]

theorem logb_mul (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x * y) = logb b x + logb b y := by
  simp_rw [logb, log_mul hx hy, add_div]

theorem logb_div (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x / y) = logb b x - logb b y := by
  simp_rw [logb, log_div hx hy, sub_div]

@[simp]
theorem logb_inv (b x : ℝ) : logb b x⁻¹ = -logb b x := by simp [logb, neg_div]

@[simp]
theorem logb_inv_base (b x : ℝ) : logb b⁻¹ x = -logb b x := by simp [logb, div_neg]

theorem inv_logb (a b : ℝ) : (logb a b)⁻¹ = logb b a := by simp_rw [logb, inv_div]

theorem inv_logb_mul_base {a b : ℝ} (h₁ : a ≠ 0) (h₂ : b ≠ 0) (c : ℝ) :
    (logb (a * b) c)⁻¹ = (logb a c)⁻¹ + (logb b c)⁻¹ := by
  simp_rw [inv_logb]; exact logb_mul h₁ h₂

theorem inv_logb_div_base {a b : ℝ} (h₁ : a ≠ 0) (h₂ : b ≠ 0) (c : ℝ) :
    (logb (a / b) c)⁻¹ = (logb a c)⁻¹ - (logb b c)⁻¹ := by
  simp_rw [inv_logb]; exact logb_div h₁ h₂

theorem logb_mul_base {a b : ℝ} (h₁ : a ≠ 0) (h₂ : b ≠ 0) (c : ℝ) :
    logb (a * b) c = ((logb a c)⁻¹ + (logb b c)⁻¹)⁻¹ := by rw [← inv_logb_mul_base h₁ h₂ c, inv_inv]

theorem logb_div_base {a b : ℝ} (h₁ : a ≠ 0) (h₂ : b ≠ 0) (c : ℝ) :
    logb (a / b) c = ((logb a c)⁻¹ - (logb b c)⁻¹)⁻¹ := by rw [← inv_logb_div_base h₁ h₂ c, inv_inv]

theorem mul_logb {a b c : ℝ} (h₁ : b ≠ 0) (h₂ : b ≠ 1) (h₃ : b ≠ -1) :
    logb a b * logb b c = logb a c := by
  unfold logb
  rw [mul_comm, div_mul_div_cancel₀ (log_ne_zero.mpr ⟨h₁, h₂, h₃⟩)]

theorem div_logb {a b c : ℝ} (h₁ : c ≠ 0) (h₂ : c ≠ 1) (h₃ : c ≠ -1) :
    logb a c / logb b c = logb a b :=
  div_div_div_cancel_left' _ _ <| log_ne_zero.mpr ⟨h₁, h₂, h₃⟩

theorem logb_rpow_eq_mul_logb_of_pos (hx : 0 < x) : logb b (x ^ y) = y * logb b x := by
  rw [logb, log_rpow hx, logb, mul_div_assoc]

theorem logb_pow (b x : ℝ) (k : ℕ) : logb b (x ^ k) = k * logb b x := by
  rw [logb, logb, log_pow, mul_div_assoc]

section BPosAndNeOne

variable (b_pos : 0 < b) (b_ne_one : b ≠ 1)
include b_pos b_ne_one

@[simp]
theorem logb_rpow : logb b (b ^ x) = x := by
  rw [logb, div_eq_iff, log_rpow b_pos]
  exact log_ne_zero_of_pos_of_ne_one b_pos b_ne_one

theorem rpow_logb_eq_abs (hx : x ≠ 0) : b ^ logb b x = |x| := by
  apply log_injOn_pos
  · simp only [Set.mem_Ioi]
    apply rpow_pos_of_pos b_pos
  · simp only [abs_pos, mem_Ioi, Ne, hx, not_false_iff]
  rw [log_rpow b_pos, logb, log_abs]
  field_simp [log_ne_zero_of_pos_of_ne_one b_pos b_ne_one]

@[simp]
theorem rpow_logb (hx : 0 < x) : b ^ logb b x = x := by
  rw [rpow_logb_eq_abs b_pos b_ne_one hx.ne']
  exact abs_of_pos hx

theorem rpow_logb_of_neg (hx : x < 0) : b ^ logb b x = -x := by
  rw [rpow_logb_eq_abs b_pos b_ne_one (ne_of_lt hx)]
  exact abs_of_neg hx

theorem logb_eq_iff_rpow_eq (hy : 0 < y) : logb b y = x ↔ b ^ x = y := by
  constructor <;> rintro rfl
  · exact rpow_logb b_pos b_ne_one hy
  · exact logb_rpow b_pos b_ne_one

theorem surjOn_logb : SurjOn (logb b) (Ioi 0) univ := fun x _ =>
  ⟨b ^ x, rpow_pos_of_pos b_pos x, logb_rpow b_pos b_ne_one⟩

theorem logb_surjective : Surjective (logb b) := fun x => ⟨b ^ x, logb_rpow b_pos b_ne_one⟩

@[simp]
theorem range_logb : range (logb b) = univ :=
  (logb_surjective b_pos b_ne_one).range_eq

theorem surjOn_logb' : SurjOn (logb b) (Iio 0) univ := by
  intro x _
  use -b ^ x
  constructor
  · simp only [Right.neg_neg_iff, Set.mem_Iio]
    apply rpow_pos_of_pos b_pos
  · rw [logb_neg_eq_logb, logb_rpow b_pos b_ne_one]

end BPosAndNeOne

section OneLtB

variable (hb : 1 < b)
include hb

private theorem b_pos : 0 < b := by linarith

-- Name has a prime added to avoid clashing with `b_ne_one` further down the file
private theorem b_ne_one' : b ≠ 1 := by linarith

@[simp]
theorem logb_le_logb (h : 0 < x) (h₁ : 0 < y) : logb b x ≤ logb b y ↔ x ≤ y := by
  rw [logb, logb, div_le_div_iff_of_pos_right (log_pos hb), log_le_log_iff h h₁]

@[gcongr]
theorem logb_le_logb_of_le (h : 0 < x) (hxy : x ≤ y) : logb b x ≤ logb b y :=
  (logb_le_logb hb h (by linarith)).mpr hxy

@[gcongr]
theorem logb_lt_logb (hx : 0 < x) (hxy : x < y) : logb b x < logb b y := by
  rw [logb, logb, div_lt_div_iff_of_pos_right (log_pos hb)]
  exact log_lt_log hx hxy

@[simp]
theorem logb_lt_logb_iff (hx : 0 < x) (hy : 0 < y) : logb b x < logb b y ↔ x < y := by
  rw [logb, logb, div_lt_div_iff_of_pos_right (log_pos hb)]
  exact log_lt_log_iff hx hy

theorem logb_le_iff_le_rpow (hx : 0 < x) : logb b x ≤ y ↔ x ≤ b ^ y := by
  rw [← rpow_le_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hx]

theorem logb_lt_iff_lt_rpow (hx : 0 < x) : logb b x < y ↔ x < b ^ y := by
  rw [← rpow_lt_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hx]

theorem le_logb_iff_rpow_le (hy : 0 < y) : x ≤ logb b y ↔ b ^ x ≤ y := by
  rw [← rpow_le_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hy]

theorem lt_logb_iff_rpow_lt (hy : 0 < y) : x < logb b y ↔ b ^ x < y := by
  rw [← rpow_lt_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hy]

theorem logb_pos_iff (hx : 0 < x) : 0 < logb b x ↔ 1 < x := by
  rw [← @logb_one b]
  rw [logb_lt_logb_iff hb zero_lt_one hx]

theorem logb_pos (hx : 1 < x) : 0 < logb b x := by
  rw [logb_pos_iff hb (lt_trans zero_lt_one hx)]
  exact hx

theorem logb_neg_iff (h : 0 < x) : logb b x < 0 ↔ x < 1 := by
  rw [← logb_one]
  exact logb_lt_logb_iff hb h zero_lt_one

theorem logb_neg (h0 : 0 < x) (h1 : x < 1) : logb b x < 0 :=
  (logb_neg_iff hb h0).2 h1

theorem logb_nonneg_iff (hx : 0 < x) : 0 ≤ logb b x ↔ 1 ≤ x := by
  rw [← not_lt, logb_neg_iff hb hx, not_lt]

theorem logb_nonneg (hx : 1 ≤ x) : 0 ≤ logb b x :=
  (logb_nonneg_iff hb (zero_lt_one.trans_le hx)).2 hx

theorem logb_nonpos_iff (hx : 0 < x) : logb b x ≤ 0 ↔ x ≤ 1 := by
  rw [← not_lt, logb_pos_iff hb hx, not_lt]

theorem logb_nonpos_iff' (hx : 0 ≤ x) : logb b x ≤ 0 ↔ x ≤ 1 := by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [le_refl, zero_le_one]
  exact logb_nonpos_iff hb hx

theorem logb_nonpos (hx : 0 ≤ x) (h'x : x ≤ 1) : logb b x ≤ 0 :=
  (logb_nonpos_iff' hb hx).2 h'x

theorem strictMonoOn_logb : StrictMonoOn (logb b) (Set.Ioi 0) := fun _ hx _ _ hxy =>
  logb_lt_logb hb hx hxy

theorem strictAntiOn_logb : StrictAntiOn (logb b) (Set.Iio 0) := by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← logb_abs b y, ← logb_abs b x]
  refine logb_lt_logb hb (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

theorem logb_injOn_pos : Set.InjOn (logb b) (Set.Ioi 0) :=
  (strictMonoOn_logb hb).injOn

theorem eq_one_of_pos_of_logb_eq_zero (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1 :=
  logb_injOn_pos hb (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.logb_one.symm)

theorem logb_ne_zero_of_pos_of_ne_one (hx_pos : 0 < x) (hx : x ≠ 1) : logb b x ≠ 0 :=
  mt (eq_one_of_pos_of_logb_eq_zero hb hx_pos) hx

theorem tendsto_logb_atTop : Tendsto (logb b) atTop atTop :=
  Tendsto.atTop_div_const (log_pos hb) tendsto_log_atTop

end OneLtB

section BPosAndBLtOne

variable (b_pos : 0 < b) (b_lt_one : b < 1)
include b_lt_one

private theorem b_ne_one : b ≠ 1 := by linarith

include b_pos

@[simp]
theorem logb_le_logb_of_base_lt_one (h : 0 < x) (h₁ : 0 < y) : logb b x ≤ logb b y ↔ y ≤ x := by
  rw [logb, logb, div_le_div_right_of_neg (log_neg b_pos b_lt_one), log_le_log_iff h₁ h]

theorem logb_lt_logb_of_base_lt_one (hx : 0 < x) (hxy : x < y) : logb b y < logb b x := by
  rw [logb, logb, div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log hx hxy

@[simp]
theorem logb_lt_logb_iff_of_base_lt_one (hx : 0 < x) (hy : 0 < y) :
    logb b x < logb b y ↔ y < x := by
  rw [logb, logb, div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log_iff hy hx

theorem logb_le_iff_le_rpow_of_base_lt_one (hx : 0 < x) : logb b x ≤ y ↔ b ^ y ≤ x := by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hx]

theorem logb_lt_iff_lt_rpow_of_base_lt_one (hx : 0 < x) : logb b x < y ↔ b ^ y < x := by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hx]

theorem le_logb_iff_rpow_le_of_base_lt_one (hy : 0 < y) : x ≤ logb b y ↔ y ≤ b ^ x := by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hy]

theorem lt_logb_iff_rpow_lt_of_base_lt_one (hy : 0 < y) : x < logb b y ↔ y < b ^ x := by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hy]

theorem logb_pos_iff_of_base_lt_one (hx : 0 < x) : 0 < logb b x ↔ x < 1 := by
  rw [← @logb_one b, logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one zero_lt_one hx]

theorem logb_pos_of_base_lt_one (hx : 0 < x) (hx' : x < 1) : 0 < logb b x := by
  rw [logb_pos_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'

theorem logb_neg_iff_of_base_lt_one (h : 0 < x) : logb b x < 0 ↔ 1 < x := by
  rw [← @logb_one b, logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one h zero_lt_one]

theorem logb_neg_of_base_lt_one (h1 : 1 < x) : logb b x < 0 :=
  (logb_neg_iff_of_base_lt_one b_pos b_lt_one (lt_trans zero_lt_one h1)).2 h1

theorem logb_nonneg_iff_of_base_lt_one (hx : 0 < x) : 0 ≤ logb b x ↔ x ≤ 1 := by
  rw [← not_lt, logb_neg_iff_of_base_lt_one b_pos b_lt_one hx, not_lt]

theorem logb_nonneg_of_base_lt_one (hx : 0 < x) (hx' : x ≤ 1) : 0 ≤ logb b x := by
  rw [logb_nonneg_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'

theorem logb_nonpos_iff_of_base_lt_one (hx : 0 < x) : logb b x ≤ 0 ↔ 1 ≤ x := by
  rw [← not_lt, logb_pos_iff_of_base_lt_one b_pos b_lt_one hx, not_lt]

theorem strictAntiOn_logb_of_base_lt_one : StrictAntiOn (logb b) (Set.Ioi 0) := fun _ hx _ _ hxy =>
  logb_lt_logb_of_base_lt_one b_pos b_lt_one hx hxy

theorem strictMonoOn_logb_of_base_lt_one : StrictMonoOn (logb b) (Set.Iio 0) := by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← logb_abs b y, ← logb_abs b x]
  refine logb_lt_logb_of_base_lt_one b_pos b_lt_one (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

theorem logb_injOn_pos_of_base_lt_one : Set.InjOn (logb b) (Set.Ioi 0) :=
  (strictAntiOn_logb_of_base_lt_one b_pos b_lt_one).injOn

theorem eq_one_of_pos_of_logb_eq_zero_of_base_lt_one (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1 :=
  logb_injOn_pos_of_base_lt_one b_pos b_lt_one (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one)
    (h₂.trans Real.logb_one.symm)

theorem logb_ne_zero_of_pos_of_ne_one_of_base_lt_one (hx_pos : 0 < x) (hx : x ≠ 1) : logb b x ≠ 0 :=
  mt (eq_one_of_pos_of_logb_eq_zero_of_base_lt_one b_pos b_lt_one hx_pos) hx

theorem tendsto_logb_atTop_of_base_lt_one : Tendsto (logb b) atTop atBot := by
  rw [tendsto_atTop_atBot]
  intro e
  use 1 ⊔ b ^ e
  intro a
  simp only [and_imp, sup_le_iff]
  intro ha
  rw [logb_le_iff_le_rpow_of_base_lt_one b_pos b_lt_one]
  · tauto
  · exact lt_of_lt_of_le zero_lt_one ha

end BPosAndBLtOne

@[norm_cast]
theorem floor_logb_natCast {b : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    ⌊logb b r⌋ = Int.log b r := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [logb_zero, Int.log_zero_right, Int.floor_zero]
  by_cases hb : 1 < b
  · have hb1' : 1 < (b : ℝ) := Nat.one_lt_cast.mpr hb
    apply le_antisymm
    · rw [← Int.zpow_le_iff_le_log hb hr, ← rpow_intCast b]
      refine le_of_le_of_eq ?_ (rpow_logb (zero_lt_one.trans hb1') hb1'.ne' hr)
      exact rpow_le_rpow_of_exponent_le hb1'.le (Int.floor_le _)
    · rw [Int.le_floor, le_logb_iff_rpow_le hb1' hr, rpow_intCast]
      exact Int.zpow_log_le_self hb hr
  · rw [Nat.one_lt_iff_ne_zero_and_ne_one, ← or_iff_not_and_not] at hb
    cases hb
    · simp_all only [CharP.cast_eq_zero, logb_zero_left, Int.floor_zero, Int.log_zero_left]
    · simp_all only [Nat.cast_one, logb_one_left, Int.floor_zero, Int.log_one_left]

@[norm_cast]
theorem ceil_logb_natCast {b : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    ⌈logb b r⌉ = Int.clog b r := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [logb_zero, Int.clog_zero_right, Int.ceil_zero]
  by_cases hb : 1 < b
  · have hb1' : 1 < (b : ℝ) := Nat.one_lt_cast.mpr hb
    apply le_antisymm
    · rw [Int.ceil_le, logb_le_iff_le_rpow hb1' hr, rpow_intCast]
      exact Int.self_le_zpow_clog hb r
    · rw [← Int.le_zpow_iff_clog_le hb hr, ← rpow_intCast b]
      refine (rpow_logb (zero_lt_one.trans hb1') hb1'.ne' hr).symm.trans_le ?_
      exact rpow_le_rpow_of_exponent_le hb1'.le (Int.le_ceil _)
  · rw [Nat.one_lt_iff_ne_zero_and_ne_one, ← or_iff_not_and_not] at hb
    cases hb
    · simp_all only [CharP.cast_eq_zero, logb_zero_left, Int.ceil_zero, Int.clog_zero_left]
    · simp_all only [Nat.cast_one, logb_one_left, Int.ceil_zero, Int.clog_one_left]

@[norm_cast]
theorem natFloor_logb_natCast (b : ℕ) (n : ℕ) : ⌊logb b n⌋₊ = Nat.log b n := by
  obtain _ | _ | b := b
  · simp [Real.logb]
  · simp [Real.logb]
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [← Nat.cast_inj (R := ℤ), Int.natCast_floor_eq_floor, floor_logb_natCast (by simp),
    Int.log_natCast]
  exact logb_nonneg (by simp [Nat.cast_add_one_pos]) (Nat.one_le_cast.2 (by omega))

@[norm_cast]
theorem natCeil_logb_natCast (b : ℕ) (n : ℕ) : ⌈logb b n⌉₊ = Nat.clog b n := by
  obtain _ | _ | b := b
  · simp [Real.logb]
  · simp [Real.logb]
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [← Nat.cast_inj (R := ℤ), Int.natCast_ceil_eq_ceil, ceil_logb_natCast (by simp),
    Int.clog_natCast]
  exact logb_nonneg (by simp [Nat.cast_add_one_pos]) (Nat.one_le_cast.2 (by omega))

lemma natLog_le_logb (a b : ℕ) : Nat.log b a ≤ Real.logb b a := by
  apply le_trans _ (Int.floor_le ((b : ℝ).logb a))
  rw [Real.floor_logb_natCast (Nat.cast_nonneg a), Int.log_natCast, Int.cast_natCast]

lemma log2_le_logb (n : ℕ) : Nat.log2 n ≤ Real.logb 2 n := by
  calc (Nat.log2 n : ℝ) = Nat.log 2 n := mod_cast Nat.log2_eq_log_two
  _ ≤ Real.logb 2 n := natLog_le_logb _ _

@[simp]
theorem logb_eq_zero : logb b x = 0 ↔ b = 0 ∨ b = 1 ∨ b = -1 ∨ x = 0 ∨ x = 1 ∨ x = -1 := by
  simp_rw [logb, div_eq_zero_iff, log_eq_zero]
  tauto

theorem tendsto_logb_nhdsNE_zero (hb : 1 < b) : Tendsto (logb b) (𝓝[≠] 0) atBot :=
  tendsto_log_nhdsNE_zero.atBot_div_const (log_pos hb)

@[deprecated (since := "2025-03-18")]
alias tendsto_logb_nhdsWithin_zero := tendsto_logb_nhdsNE_zero

theorem tendsto_logb_nhdsNE_zero_of_base_lt_one (hb₀ : 0 < b) (hb : b < 1) :
    Tendsto (logb b) (𝓝[≠] 0) atTop :=
  tendsto_log_nhdsNE_zero.atBot_mul_const_of_neg (inv_lt_zero.2 (log_neg hb₀ hb))

@[deprecated (since := "2025-03-18")]
alias tendsto_logb_nhdsWithin_zero_of_base_lt_one := tendsto_logb_nhdsNE_zero_of_base_lt_one

lemma tendsto_logb_nhdsGT_zero (hb : 1 < b) : Tendsto (logb b) (𝓝[>] 0) atBot :=
  tendsto_log_nhdsGT_zero.atBot_div_const (log_pos hb)

@[deprecated (since := "2025-03-18")]
alias tendsto_logb_nhdsWithin_zero_right := tendsto_logb_nhdsGT_zero

lemma tendsto_logb_nhdsGT_zero_of_base_lt_one (hb₀ : 0 < b) (hb : b < 1) :
    Tendsto (logb b) (𝓝[>] 0) atTop :=
  tendsto_log_nhdsGT_zero.atBot_mul_const_of_neg (inv_lt_zero.2 (log_neg hb₀ hb))

@[deprecated (since := "2025-03-18")]
alias tendsto_logb_nhdsWithin_zero_right_of_base_lt_one := tendsto_logb_nhdsGT_zero_of_base_lt_one

/--
The function `|logb b x|` tends to `+∞` as `x` tendsto `+∞`.
See also `tendsto_logb_atTop` and `tendsto_logb_atTop_of_base_lt_one`.
-/
lemma tendsto_abs_logb_atTop (hb : b ≠ -1 ∧ b ≠ 0 ∧ b ≠ 1) :
    Tendsto (|logb b ·|) atTop atTop := by
  wlog hb₀ : 0 < b generalizing b
  · exact (this (b := -b) (by simp [hb, neg_eq_iff_eq_neg]) (by linarith +splitNe)).congr (by simp)
  wlog hb₁ : 1 < b generalizing b
  · exact (this (b := b⁻¹) (by simp [hb, inv_eq_iff_eq_inv, inv_neg]) (by simpa)
      ((one_lt_inv₀ hb₀).2 (by linarith +splitNe))).congr (by simp)
  refine (tendsto_logb_atTop hb₁).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx₁
  rw [abs_of_nonneg]
  exact logb_nonneg hb₁ hx₁

theorem continuousOn_logb : ContinuousOn (logb b) {0}ᶜ := continuousOn_log.div_const _

/-- The real logarithm base b is continuous as a function from nonzero reals. -/
@[fun_prop]
theorem continuous_logb : Continuous fun x : { x : ℝ // x ≠ 0 } => logb b x :=
  continuous_log.div_const _

/-- The real logarithm base b is continuous as a function from positive reals. -/
@[fun_prop]
theorem continuous_logb' : Continuous fun x : { x : ℝ // 0 < x } => logb b x :=
  continuous_log'.div_const _

theorem continuousAt_logb (hx : x ≠ 0) : ContinuousAt (logb b) x :=
  (continuousAt_log hx).div_const _

@[simp]
theorem continuousAt_logb_iff (hb₀ : 0 < b) (hb : b ≠ 1) : ContinuousAt (logb b) x ↔ x ≠ 0 := by
  refine ⟨?_, continuousAt_logb⟩
  rintro h rfl
  cases lt_or_gt_of_ne hb with
  | inl hb₁ =>
      exact not_tendsto_nhds_of_tendsto_atTop (tendsto_logb_nhdsNE_zero_of_base_lt_one hb₀ hb₁)
        _ (h.tendsto.mono_left inf_le_left)
  | inr hb₁ =>
      exact not_tendsto_nhds_of_tendsto_atBot (tendsto_logb_nhdsNE_zero hb₁)
        _ (h.tendsto.mono_left inf_le_left)

theorem logb_prod {α : Type*} (s : Finset α) (f : α → ℝ) (hf : ∀ x ∈ s, f x ≠ 0) :
    logb b (∏ i ∈ s, f i) = ∑ i ∈ s, logb b (f i) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons => simp_all [logb_mul, Finset.prod_ne_zero_iff]

protected theorem _root_.Finsupp.logb_prod {α β : Type*} [Zero β] (f : α →₀ β) (g : α → β → ℝ)
    (hg : ∀ a, g a (f a) = 0 → f a = 0) : logb b (f.prod g) = f.sum fun a c ↦ logb b (g a c) :=
  logb_prod _ _ fun _x hx h₀ ↦ Finsupp.mem_support_iff.1 hx <| hg _ h₀

theorem logb_nat_eq_sum_factorization (n : ℕ) :
    logb b n = n.factorization.sum fun p t => t * logb b p := by
  simp only [logb, mul_div_assoc', log_nat_eq_sum_factorization n, Finsupp.sum, Finset.sum_div]

theorem tendsto_pow_logb_div_mul_add_atTop (a c : ℝ) (n : ℕ) (ha : a ≠ 0) :
    Tendsto (fun x => logb b x ^ n / (a * x + c)) atTop (𝓝 0) := by
  cases eq_or_ne (log b) 0 with
  | inl h => simpa [logb, h] using ((tendsto_mul_add_inv_atTop_nhds_zero _ _ ha).const_mul _)
  | inr h => apply (tendsto_pow_log_div_mul_add_atTop (a * (log b) ^ n) (c * (log b) ^ n) n
                (by positivity)).congr fun x ↦ by simp [field, div_pow, logb]

theorem isLittleO_pow_logb_id_atTop {n : ℕ} : (fun x => logb b x ^ n) =o[atTop] id := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · simpa using tendsto_pow_logb_div_mul_add_atTop 1 0 n one_ne_zero
  · filter_upwards [eventually_ne_atTop (0 : ℝ)] with x h₁ h₂ using (h₁ h₂).elim

theorem isLittleO_logb_id_atTop : logb b =o[atTop] id :=
  isLittleO_pow_logb_id_atTop.congr_left fun _ => pow_one _

theorem isLittleO_const_logb_atTop {c : ℝ} (hb : b ≠ -1 ∧ b ≠ 0 ∧ b ≠ 1) :
    (fun _ => c) =o[atTop] logb b := by
  rw [Asymptotics.isLittleO_const_left, or_iff_not_imp_left]
  intro hc
  exact tendsto_abs_logb_atTop hb

end Real

section Continuity

open Real

variable {α : Type*}
variable {b : ℝ}

theorem Filter.Tendsto.logb {f : α → ℝ} {l : Filter α} {x : ℝ}
    (h : Tendsto f l (𝓝 x)) (hx : x ≠ 0) :
    Tendsto (fun y => logb b (f y)) l (𝓝 (logb b x)) :=
  (continuousAt_logb hx).tendsto.comp h

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {a : α}

@[fun_prop]
theorem Continuous.logb (hf : Continuous f) (h₀ : ∀ x, f x ≠ 0) :
    Continuous fun x => logb b (f x) :=
  continuousOn_logb.comp_continuous hf h₀

@[fun_prop]
nonrec theorem ContinuousAt.logb (hf : ContinuousAt f a) (h₀ : f a ≠ 0) :
    ContinuousAt (fun x => logb b (f x)) a :=
  hf.logb h₀

nonrec theorem ContinuousWithinAt.logb (hf : ContinuousWithinAt f s a) (h₀ : f a ≠ 0) :
    ContinuousWithinAt (fun x => logb b (f x)) s a :=
  hf.logb h₀

@[fun_prop]
theorem ContinuousOn.logb (hf : ContinuousOn f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
    ContinuousOn (fun x => logb b (f x)) s := fun x hx => (hf x hx).logb (h₀ x hx)

end Continuity

section TendstoCompAddSub

open Filter

namespace Real

variable {b : ℝ}

theorem tendsto_logb_comp_add_sub_logb (y : ℝ) :
    Tendsto (fun x : ℝ => logb b (x + y) - logb b x) atTop (𝓝 0) := by
  simpa [sub_div] using (tendsto_log_comp_add_sub_log y).div_const (log b)

theorem tendsto_logb_nat_add_one_sub_logb :
    Tendsto (fun k : ℕ => logb b (k + 1) - logb b k) atTop (𝓝 0) :=
  (tendsto_logb_comp_add_sub_logb 1).comp tendsto_natCast_atTop_atTop

end Real

end TendstoCompAddSub

section Induction

/-- Induction principle for intervals of real numbers: if a proposition `P` is true
on `[x₀, r * x₀)` and if `P` for `[x₀, r^n * x₀)` implies `P` for `[r^n * x₀, r^(n+1) * x₀)`,
then `P` is true for all `x ≥ x₀`. -/
lemma Real.induction_Ico_mul {P : ℝ → Prop} (x₀ r : ℝ) (hr : 1 < r) (hx₀ : 0 < x₀)
    (base : ∀ x ∈ Set.Ico x₀ (r * x₀), P x)
    (step : ∀ n : ℕ, n ≥ 1 → (∀ z ∈ Set.Ico x₀ (r ^ n * x₀), P z) →
      (∀ z ∈ Set.Ico (r ^ n * x₀) (r ^ (n + 1) * x₀), P z)) :
    ∀ x ≥ x₀, P x := by
  suffices ∀ n : ℕ, ∀ x ∈ Set.Ico x₀ (r ^ (n + 1) * x₀), P x by
    intro x hx
    have hx' : 0 < x / x₀ := div_pos (hx₀.trans_le hx) hx₀
    refine this ⌊logb r (x / x₀)⌋₊ x ?_
    rw [mem_Ico, ← div_lt_iff₀ hx₀, ← rpow_natCast, ← logb_lt_iff_lt_rpow hr hx', Nat.cast_add,
      Nat.cast_one]
    exact ⟨hx, Nat.lt_floor_add_one _⟩
  intro n
  induction n with
  | zero => simpa using base
  | succ n ih =>
    exact fun x hx => (Ico_subset_Ico_union_Ico hx).elim (ih x) (step (n + 1) (by simp) ih _)

end Induction
