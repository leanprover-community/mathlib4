/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Log

#align_import analysis.special_functions.log.base from "leanprover-community/mathlib"@"f23a09ce6d3f367220dc3cecad6b7eb69eb01690"

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
be `logb b |x|` for `x < 0`, and `0` for `x = 0`.-/
-- @[pp_nodot] -- Porting note: removed
noncomputable def logb (b x : ℝ) : ℝ :=
  log x / log b
#align real.logb Real.logb

theorem log_div_log : log x / log b = logb b x :=
  rfl
#align real.log_div_log Real.log_div_log

@[simp]
theorem logb_zero : logb b 0 = 0 := by simp [logb]
                                       -- 🎉 no goals
#align real.logb_zero Real.logb_zero

@[simp]
theorem logb_one : logb b 1 = 0 := by simp [logb]
                                      -- 🎉 no goals
#align real.logb_one Real.logb_one

@[simp]
theorem logb_abs (x : ℝ) : logb b |x| = logb b x := by rw [logb, logb, log_abs]
                                                       -- 🎉 no goals
#align real.logb_abs Real.logb_abs

@[simp]
theorem logb_neg_eq_logb (x : ℝ) : logb b (-x) = logb b x := by
  rw [← logb_abs x, ← logb_abs (-x), abs_neg]
  -- 🎉 no goals
#align real.logb_neg_eq_logb Real.logb_neg_eq_logb

theorem logb_mul (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x * y) = logb b x + logb b y := by
  simp_rw [logb, log_mul hx hy, add_div]
  -- 🎉 no goals
#align real.logb_mul Real.logb_mul

theorem logb_div (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x / y) = logb b x - logb b y := by
  simp_rw [logb, log_div hx hy, sub_div]
  -- 🎉 no goals
#align real.logb_div Real.logb_div

@[simp]
theorem logb_inv (x : ℝ) : logb b x⁻¹ = -logb b x := by simp [logb, neg_div]
                                                        -- 🎉 no goals
#align real.logb_inv Real.logb_inv

theorem inv_logb (a b : ℝ) : (logb a b)⁻¹ = logb b a := by simp_rw [logb, inv_div]
                                                           -- 🎉 no goals
#align real.inv_logb Real.inv_logb

theorem inv_logb_mul_base {a b : ℝ} (h₁ : a ≠ 0) (h₂ : b ≠ 0) (c : ℝ) :
    (logb (a * b) c)⁻¹ = (logb a c)⁻¹ + (logb b c)⁻¹ := by
  simp_rw [inv_logb]; exact logb_mul h₁ h₂
  -- ⊢ logb c (a * b) = logb c a + logb c b
                      -- 🎉 no goals
#align real.inv_logb_mul_base Real.inv_logb_mul_base

theorem inv_logb_div_base {a b : ℝ} (h₁ : a ≠ 0) (h₂ : b ≠ 0) (c : ℝ) :
    (logb (a / b) c)⁻¹ = (logb a c)⁻¹ - (logb b c)⁻¹ := by
  simp_rw [inv_logb]; exact logb_div h₁ h₂
  -- ⊢ logb c (a / b) = logb c a - logb c b
                      -- 🎉 no goals
#align real.inv_logb_div_base Real.inv_logb_div_base

theorem logb_mul_base {a b : ℝ} (h₁ : a ≠ 0) (h₂ : b ≠ 0) (c : ℝ) :
    logb (a * b) c = ((logb a c)⁻¹ + (logb b c)⁻¹)⁻¹ := by rw [← inv_logb_mul_base h₁ h₂ c, inv_inv]
                                                           -- 🎉 no goals
#align real.logb_mul_base Real.logb_mul_base

theorem logb_div_base {a b : ℝ} (h₁ : a ≠ 0) (h₂ : b ≠ 0) (c : ℝ) :
    logb (a / b) c = ((logb a c)⁻¹ - (logb b c)⁻¹)⁻¹ := by rw [← inv_logb_div_base h₁ h₂ c, inv_inv]
                                                           -- 🎉 no goals
#align real.logb_div_base Real.logb_div_base

theorem mul_logb {a b c : ℝ} (h₁ : b ≠ 0) (h₂ : b ≠ 1) (h₃ : b ≠ -1) :
    logb a b * logb b c = logb a c := by
  unfold logb
  -- ⊢ log b / log a * (log c / log b) = log c / log a
  rw [mul_comm, div_mul_div_cancel _ (log_ne_zero.mpr ⟨h₁, h₂, h₃⟩)]
  -- 🎉 no goals
#align real.mul_logb Real.mul_logb

theorem div_logb {a b c : ℝ} (h₁ : c ≠ 0) (h₂ : c ≠ 1) (h₃ : c ≠ -1) :
    logb a c / logb b c = logb a b :=
  div_div_div_cancel_left' _ _ <| log_ne_zero.mpr ⟨h₁, h₂, h₃⟩
#align real.div_logb Real.div_logb

section BPosAndNeOne

variable (b_pos : 0 < b) (b_ne_one : b ≠ 1)

private theorem log_b_ne_zero : log b ≠ 0 := by
  have b_ne_zero : b ≠ 0; linarith
  -- ⊢ b ≠ 0
                          -- ⊢ log b ≠ 0
  have b_ne_minus_one : b ≠ -1; linarith
  -- ⊢ b ≠ -1
                                -- ⊢ log b ≠ 0
  simp [b_ne_one, b_ne_zero, b_ne_minus_one]
  -- 🎉 no goals

@[simp]
theorem logb_rpow : logb b (b ^ x) = x := by
  rw [logb, div_eq_iff, log_rpow b_pos]
  -- ⊢ log b ≠ 0
  exact log_b_ne_zero b_pos b_ne_one
  -- 🎉 no goals
#align real.logb_rpow Real.logb_rpow

theorem rpow_logb_eq_abs (hx : x ≠ 0) : b ^ logb b x = |x| := by
  apply log_injOn_pos
  simp only [Set.mem_Ioi]
  apply rpow_pos_of_pos b_pos
  -- ⊢ |x| ∈ Ioi 0
  simp only [abs_pos, mem_Ioi, Ne.def, hx, not_false_iff]
  -- ⊢ log (b ^ logb b x) = log |x|
  rw [log_rpow b_pos, logb, log_abs]
  -- ⊢ log x / log b * log b = log x
  field_simp [log_b_ne_zero b_pos b_ne_one]
  -- 🎉 no goals
#align real.rpow_logb_eq_abs Real.rpow_logb_eq_abs

@[simp]
theorem rpow_logb (hx : 0 < x) : b ^ logb b x = x := by
  rw [rpow_logb_eq_abs b_pos b_ne_one hx.ne']
  -- ⊢ |x| = x
  exact abs_of_pos hx
  -- 🎉 no goals
#align real.rpow_logb Real.rpow_logb

theorem rpow_logb_of_neg (hx : x < 0) : b ^ logb b x = -x := by
  rw [rpow_logb_eq_abs b_pos b_ne_one (ne_of_lt hx)]
  -- ⊢ |x| = -x
  exact abs_of_neg hx
  -- 🎉 no goals
#align real.rpow_logb_of_neg Real.rpow_logb_of_neg

theorem surjOn_logb : SurjOn (logb b) (Ioi 0) univ := fun x _ =>
  ⟨rpow b x, rpow_pos_of_pos b_pos x, logb_rpow b_pos b_ne_one⟩
#align real.surj_on_logb Real.surjOn_logb

theorem logb_surjective : Surjective (logb b) := fun x => ⟨b ^ x, logb_rpow b_pos b_ne_one⟩
#align real.logb_surjective Real.logb_surjective

@[simp]
theorem range_logb : range (logb b) = univ :=
  (logb_surjective b_pos b_ne_one).range_eq
#align real.range_logb Real.range_logb

theorem surjOn_logb' : SurjOn (logb b) (Iio 0) univ := by
  intro x _
  -- ⊢ x ∈ logb b '' Iio 0
  use -b ^ x
  -- ⊢ -b ^ x ∈ Iio 0 ∧ logb b (-b ^ x) = x
  constructor
  -- ⊢ -b ^ x ∈ Iio 0
  · simp only [Right.neg_neg_iff, Set.mem_Iio]
    -- ⊢ 0 < b ^ x
    apply rpow_pos_of_pos b_pos
    -- 🎉 no goals
  · rw [logb_neg_eq_logb, logb_rpow b_pos b_ne_one]
    -- 🎉 no goals
#align real.surj_on_logb' Real.surjOn_logb'

end BPosAndNeOne

section OneLtB

variable (hb : 1 < b)

private theorem b_pos : 0 < b := by linarith
                                    -- 🎉 no goals

-- Porting note: prime added to avoid clashing with `b_ne_one` further down the file
private theorem b_ne_one' : b ≠ 1 := by linarith
                                        -- 🎉 no goals

@[simp]
theorem logb_le_logb (h : 0 < x) (h₁ : 0 < y) : logb b x ≤ logb b y ↔ x ≤ y := by
  rw [logb, logb, div_le_div_right (log_pos hb), log_le_log h h₁]
  -- 🎉 no goals
#align real.logb_le_logb Real.logb_le_logb

theorem logb_lt_logb (hx : 0 < x) (hxy : x < y) : logb b x < logb b y := by
  rw [logb, logb, div_lt_div_right (log_pos hb)]
  -- ⊢ log x < log y
  exact log_lt_log hx hxy
  -- 🎉 no goals
#align real.logb_lt_logb Real.logb_lt_logb

@[simp]
theorem logb_lt_logb_iff (hx : 0 < x) (hy : 0 < y) : logb b x < logb b y ↔ x < y := by
  rw [logb, logb, div_lt_div_right (log_pos hb)]
  -- ⊢ log x < log y ↔ x < y
  exact log_lt_log_iff hx hy
  -- 🎉 no goals
#align real.logb_lt_logb_iff Real.logb_lt_logb_iff

theorem logb_le_iff_le_rpow (hx : 0 < x) : logb b x ≤ y ↔ x ≤ b ^ y := by
  rw [← rpow_le_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hx]
  -- 🎉 no goals
#align real.logb_le_iff_le_rpow Real.logb_le_iff_le_rpow

theorem logb_lt_iff_lt_rpow (hx : 0 < x) : logb b x < y ↔ x < b ^ y := by
  rw [← rpow_lt_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hx]
  -- 🎉 no goals
#align real.logb_lt_iff_lt_rpow Real.logb_lt_iff_lt_rpow

theorem le_logb_iff_rpow_le (hy : 0 < y) : x ≤ logb b y ↔ b ^ x ≤ y := by
  rw [← rpow_le_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hy]
  -- 🎉 no goals
#align real.le_logb_iff_rpow_le Real.le_logb_iff_rpow_le

theorem lt_logb_iff_rpow_lt (hy : 0 < y) : x < logb b y ↔ b ^ x < y := by
  rw [← rpow_lt_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hy]
  -- 🎉 no goals
#align real.lt_logb_iff_rpow_lt Real.lt_logb_iff_rpow_lt

theorem logb_pos_iff (hx : 0 < x) : 0 < logb b x ↔ 1 < x := by
  rw [← @logb_one b]
  -- ⊢ logb b 1 < logb b x ↔ 1 < x
  rw [logb_lt_logb_iff hb zero_lt_one hx]
  -- 🎉 no goals
#align real.logb_pos_iff Real.logb_pos_iff

theorem logb_pos (hx : 1 < x) : 0 < logb b x := by
  rw [logb_pos_iff hb (lt_trans zero_lt_one hx)]
  -- ⊢ 1 < x
  exact hx
  -- 🎉 no goals
#align real.logb_pos Real.logb_pos

theorem logb_neg_iff (h : 0 < x) : logb b x < 0 ↔ x < 1 := by
  rw [← logb_one]
  -- ⊢ logb b x < logb ?m.16248 1 ↔ x < 1
  exact logb_lt_logb_iff hb h zero_lt_one
  -- 🎉 no goals
#align real.logb_neg_iff Real.logb_neg_iff

theorem logb_neg (h0 : 0 < x) (h1 : x < 1) : logb b x < 0 :=
  (logb_neg_iff hb h0).2 h1
#align real.logb_neg Real.logb_neg

theorem logb_nonneg_iff (hx : 0 < x) : 0 ≤ logb b x ↔ 1 ≤ x := by
  rw [← not_lt, logb_neg_iff hb hx, not_lt]
  -- 🎉 no goals
#align real.logb_nonneg_iff Real.logb_nonneg_iff

theorem logb_nonneg (hx : 1 ≤ x) : 0 ≤ logb b x :=
  (logb_nonneg_iff hb (zero_lt_one.trans_le hx)).2 hx
#align real.logb_nonneg Real.logb_nonneg

theorem logb_nonpos_iff (hx : 0 < x) : logb b x ≤ 0 ↔ x ≤ 1 := by
  rw [← not_lt, logb_pos_iff hb hx, not_lt]
  -- 🎉 no goals
#align real.logb_nonpos_iff Real.logb_nonpos_iff

theorem logb_nonpos_iff' (hx : 0 ≤ x) : logb b x ≤ 0 ↔ x ≤ 1 := by
  rcases hx.eq_or_lt with (rfl | hx)
  -- ⊢ logb b 0 ≤ 0 ↔ 0 ≤ 1
  · simp [le_refl, zero_le_one]
    -- 🎉 no goals
  exact logb_nonpos_iff hb hx
  -- 🎉 no goals
#align real.logb_nonpos_iff' Real.logb_nonpos_iff'

theorem logb_nonpos (hx : 0 ≤ x) (h'x : x ≤ 1) : logb b x ≤ 0 :=
  (logb_nonpos_iff' hb hx).2 h'x
#align real.logb_nonpos Real.logb_nonpos

theorem strictMonoOn_logb : StrictMonoOn (logb b) (Set.Ioi 0) := fun _ hx _ _ hxy =>
  logb_lt_logb hb hx hxy
#align real.strict_mono_on_logb Real.strictMonoOn_logb

theorem strictAntiOn_logb : StrictAntiOn (logb b) (Set.Iio 0) := by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  -- ⊢ logb b y < logb b x
  rw [← logb_abs y, ← logb_abs x]
  -- ⊢ logb b |y| < logb b |x|
  refine' logb_lt_logb hb (abs_pos.2 hy.ne) _
  -- ⊢ |y| < |x|
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]
  -- 🎉 no goals
#align real.strict_anti_on_logb Real.strictAntiOn_logb

theorem logb_injOn_pos : Set.InjOn (logb b) (Set.Ioi 0) :=
  (strictMonoOn_logb hb).injOn
#align real.logb_inj_on_pos Real.logb_injOn_pos

theorem eq_one_of_pos_of_logb_eq_zero (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1 :=
  logb_injOn_pos hb (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.logb_one.symm)
#align real.eq_one_of_pos_of_logb_eq_zero Real.eq_one_of_pos_of_logb_eq_zero

theorem logb_ne_zero_of_pos_of_ne_one (hx_pos : 0 < x) (hx : x ≠ 1) : logb b x ≠ 0 :=
  mt (eq_one_of_pos_of_logb_eq_zero hb hx_pos) hx
#align real.logb_ne_zero_of_pos_of_ne_one Real.logb_ne_zero_of_pos_of_ne_one

theorem tendsto_logb_atTop : Tendsto (logb b) atTop atTop :=
  Tendsto.atTop_div_const (log_pos hb) tendsto_log_atTop
#align real.tendsto_logb_at_top Real.tendsto_logb_atTop

end OneLtB

section BPosAndBLtOne

variable (b_pos : 0 < b) (b_lt_one : b < 1)

private theorem b_ne_one : b ≠ 1 := by linarith
                                       -- 🎉 no goals

@[simp]
theorem logb_le_logb_of_base_lt_one (h : 0 < x) (h₁ : 0 < y) : logb b x ≤ logb b y ↔ y ≤ x := by
  rw [logb, logb, div_le_div_right_of_neg (log_neg b_pos b_lt_one), log_le_log h₁ h]
  -- 🎉 no goals
#align real.logb_le_logb_of_base_lt_one Real.logb_le_logb_of_base_lt_one

theorem logb_lt_logb_of_base_lt_one (hx : 0 < x) (hxy : x < y) : logb b y < logb b x := by
  rw [logb, logb, div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  -- ⊢ log x < log y
  exact log_lt_log hx hxy
  -- 🎉 no goals
#align real.logb_lt_logb_of_base_lt_one Real.logb_lt_logb_of_base_lt_one

@[simp]
theorem logb_lt_logb_iff_of_base_lt_one (hx : 0 < x) (hy : 0 < y) :
    logb b x < logb b y ↔ y < x := by
  rw [logb, logb, div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  -- ⊢ log y < log x ↔ y < x
  exact log_lt_log_iff hy hx
  -- 🎉 no goals
#align real.logb_lt_logb_iff_of_base_lt_one Real.logb_lt_logb_iff_of_base_lt_one

theorem logb_le_iff_le_rpow_of_base_lt_one (hx : 0 < x) : logb b x ≤ y ↔ b ^ y ≤ x := by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hx]
  -- 🎉 no goals
#align real.logb_le_iff_le_rpow_of_base_lt_one Real.logb_le_iff_le_rpow_of_base_lt_one

theorem logb_lt_iff_lt_rpow_of_base_lt_one (hx : 0 < x) : logb b x < y ↔ b ^ y < x := by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hx]
  -- 🎉 no goals
#align real.logb_lt_iff_lt_rpow_of_base_lt_one Real.logb_lt_iff_lt_rpow_of_base_lt_one

theorem le_logb_iff_rpow_le_of_base_lt_one (hy : 0 < y) : x ≤ logb b y ↔ y ≤ b ^ x := by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hy]
  -- 🎉 no goals
#align real.le_logb_iff_rpow_le_of_base_lt_one Real.le_logb_iff_rpow_le_of_base_lt_one

theorem lt_logb_iff_rpow_lt_of_base_lt_one (hy : 0 < y) : x < logb b y ↔ y < b ^ x := by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hy]
  -- 🎉 no goals
#align real.lt_logb_iff_rpow_lt_of_base_lt_one Real.lt_logb_iff_rpow_lt_of_base_lt_one

theorem logb_pos_iff_of_base_lt_one (hx : 0 < x) : 0 < logb b x ↔ x < 1 := by
  rw [← @logb_one b, logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one zero_lt_one hx]
  -- 🎉 no goals
#align real.logb_pos_iff_of_base_lt_one Real.logb_pos_iff_of_base_lt_one

theorem logb_pos_of_base_lt_one (hx : 0 < x) (hx' : x < 1) : 0 < logb b x := by
  rw [logb_pos_iff_of_base_lt_one b_pos b_lt_one hx]
  -- ⊢ x < 1
  exact hx'
  -- 🎉 no goals
#align real.logb_pos_of_base_lt_one Real.logb_pos_of_base_lt_one

theorem logb_neg_iff_of_base_lt_one (h : 0 < x) : logb b x < 0 ↔ 1 < x := by
  rw [← @logb_one b, logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one h zero_lt_one]
  -- 🎉 no goals
#align real.logb_neg_iff_of_base_lt_one Real.logb_neg_iff_of_base_lt_one

theorem logb_neg_of_base_lt_one (h1 : 1 < x) : logb b x < 0 :=
  (logb_neg_iff_of_base_lt_one b_pos b_lt_one (lt_trans zero_lt_one h1)).2 h1
#align real.logb_neg_of_base_lt_one Real.logb_neg_of_base_lt_one

theorem logb_nonneg_iff_of_base_lt_one (hx : 0 < x) : 0 ≤ logb b x ↔ x ≤ 1 := by
  rw [← not_lt, logb_neg_iff_of_base_lt_one b_pos b_lt_one hx, not_lt]
  -- 🎉 no goals
#align real.logb_nonneg_iff_of_base_lt_one Real.logb_nonneg_iff_of_base_lt_one

theorem logb_nonneg_of_base_lt_one (hx : 0 < x) (hx' : x ≤ 1) : 0 ≤ logb b x := by
  rw [logb_nonneg_iff_of_base_lt_one b_pos b_lt_one hx]
  -- ⊢ x ≤ 1
  exact hx'
  -- 🎉 no goals
#align real.logb_nonneg_of_base_lt_one Real.logb_nonneg_of_base_lt_one

theorem logb_nonpos_iff_of_base_lt_one (hx : 0 < x) : logb b x ≤ 0 ↔ 1 ≤ x := by
  rw [← not_lt, logb_pos_iff_of_base_lt_one b_pos b_lt_one hx, not_lt]
  -- 🎉 no goals
#align real.logb_nonpos_iff_of_base_lt_one Real.logb_nonpos_iff_of_base_lt_one

theorem strictAntiOn_logb_of_base_lt_one : StrictAntiOn (logb b) (Set.Ioi 0) := fun _ hx _ _ hxy =>
  logb_lt_logb_of_base_lt_one b_pos b_lt_one hx hxy
#align real.strict_anti_on_logb_of_base_lt_one Real.strictAntiOn_logb_of_base_lt_one

theorem strictMonoOn_logb_of_base_lt_one : StrictMonoOn (logb b) (Set.Iio 0) := by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  -- ⊢ logb b x < logb b y
  rw [← logb_abs y, ← logb_abs x]
  -- ⊢ logb b |x| < logb b |y|
  refine' logb_lt_logb_of_base_lt_one b_pos b_lt_one (abs_pos.2 hy.ne) _
  -- ⊢ |y| < |x|
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]
  -- 🎉 no goals
#align real.strict_mono_on_logb_of_base_lt_one Real.strictMonoOn_logb_of_base_lt_one

theorem logb_injOn_pos_of_base_lt_one : Set.InjOn (logb b) (Set.Ioi 0) :=
  (strictAntiOn_logb_of_base_lt_one b_pos b_lt_one).injOn
#align real.logb_inj_on_pos_of_base_lt_one Real.logb_injOn_pos_of_base_lt_one

theorem eq_one_of_pos_of_logb_eq_zero_of_base_lt_one (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1 :=
  logb_injOn_pos_of_base_lt_one b_pos b_lt_one (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one)
    (h₂.trans Real.logb_one.symm)
#align real.eq_one_of_pos_of_logb_eq_zero_of_base_lt_one Real.eq_one_of_pos_of_logb_eq_zero_of_base_lt_one

theorem logb_ne_zero_of_pos_of_ne_one_of_base_lt_one (hx_pos : 0 < x) (hx : x ≠ 1) : logb b x ≠ 0 :=
  mt (eq_one_of_pos_of_logb_eq_zero_of_base_lt_one b_pos b_lt_one hx_pos) hx
#align real.logb_ne_zero_of_pos_of_ne_one_of_base_lt_one Real.logb_ne_zero_of_pos_of_ne_one_of_base_lt_one

theorem tendsto_logb_atTop_of_base_lt_one : Tendsto (logb b) atTop atBot := by
  rw [tendsto_atTop_atBot]
  -- ⊢ ∀ (b_1 : ℝ), ∃ i, ∀ (a : ℝ), i ≤ a → logb b a ≤ b_1
  intro e
  -- ⊢ ∃ i, ∀ (a : ℝ), i ≤ a → logb b a ≤ e
  use 1 ⊔ b ^ e
  -- ⊢ ∀ (a : ℝ), 1 ⊔ b ^ e ≤ a → logb b a ≤ e
  intro a
  -- ⊢ 1 ⊔ b ^ e ≤ a → logb b a ≤ e
  simp only [and_imp, sup_le_iff]
  -- ⊢ 1 ≤ a → b ^ e ≤ a → logb b a ≤ e
  intro ha
  -- ⊢ b ^ e ≤ a → logb b a ≤ e
  rw [logb_le_iff_le_rpow_of_base_lt_one b_pos b_lt_one]
  -- ⊢ b ^ e ≤ a → b ^ e ≤ a
  tauto
  -- ⊢ 0 < a
  exact lt_of_lt_of_le zero_lt_one ha
  -- 🎉 no goals
#align real.tendsto_logb_at_top_of_base_lt_one Real.tendsto_logb_atTop_of_base_lt_one

end BPosAndBLtOne

theorem floor_logb_nat_cast {b : ℕ} {r : ℝ} (hb : 1 < b) (hr : 0 ≤ r) :
    ⌊logb b r⌋ = Int.log b r := by
  obtain rfl | hr := hr.eq_or_lt
  -- ⊢ ⌊logb (↑b) 0⌋ = Int.log b 0
  · rw [logb_zero, Int.log_zero_right, Int.floor_zero]
    -- 🎉 no goals
  have hb1' : 1 < (b : ℝ) := Nat.one_lt_cast.mpr hb
  -- ⊢ ⌊logb (↑b) r⌋ = Int.log b r
  apply le_antisymm
  -- ⊢ ⌊logb (↑b) r⌋ ≤ Int.log b r
  · rw [← Int.zpow_le_iff_le_log hb hr, ← rpow_int_cast b]
    -- ⊢ ↑b ^ ↑⌊logb (↑b) r⌋ ≤ r
    refine' le_of_le_of_eq _ (rpow_logb (zero_lt_one.trans hb1') hb1'.ne' hr)
    -- ⊢ ↑b ^ ↑⌊logb (↑b) r⌋ ≤ ↑b ^ logb (↑b) r
    exact rpow_le_rpow_of_exponent_le hb1'.le (Int.floor_le _)
    -- 🎉 no goals
  · rw [Int.le_floor, le_logb_iff_rpow_le hb1' hr, rpow_int_cast]
    -- ⊢ ↑b ^ Int.log b r ≤ r
    exact Int.zpow_log_le_self hb hr
    -- 🎉 no goals
#align real.floor_logb_nat_cast Real.floor_logb_nat_cast

theorem ceil_logb_nat_cast {b : ℕ} {r : ℝ} (hb : 1 < b) (hr : 0 ≤ r) :
    ⌈logb b r⌉ = Int.clog b r := by
  obtain rfl | hr := hr.eq_or_lt
  -- ⊢ ⌈logb (↑b) 0⌉ = Int.clog b 0
  · rw [logb_zero, Int.clog_zero_right, Int.ceil_zero]
    -- 🎉 no goals
  have hb1' : 1 < (b : ℝ) := Nat.one_lt_cast.mpr hb
  -- ⊢ ⌈logb (↑b) r⌉ = Int.clog b r
  apply le_antisymm
  -- ⊢ ⌈logb (↑b) r⌉ ≤ Int.clog b r
  · rw [Int.ceil_le, logb_le_iff_le_rpow hb1' hr, rpow_int_cast]
    -- ⊢ r ≤ ↑b ^ Int.clog b r
    refine' Int.self_le_zpow_clog hb r
    -- 🎉 no goals
  · rw [← Int.le_zpow_iff_clog_le hb hr, ← rpow_int_cast b]
    -- ⊢ r ≤ ↑b ^ ↑⌈logb (↑b) r⌉
    refine' (rpow_logb (zero_lt_one.trans hb1') hb1'.ne' hr).symm.trans_le _
    -- ⊢ ↑b ^ logb (↑b) r ≤ ↑b ^ ↑⌈logb (↑b) r⌉
    exact rpow_le_rpow_of_exponent_le hb1'.le (Int.le_ceil _)
    -- 🎉 no goals
#align real.ceil_logb_nat_cast Real.ceil_logb_nat_cast

@[simp]
theorem logb_eq_zero : logb b x = 0 ↔ b = 0 ∨ b = 1 ∨ b = -1 ∨ x = 0 ∨ x = 1 ∨ x = -1 := by
  simp_rw [logb, div_eq_zero_iff, log_eq_zero]
  -- ⊢ (x = 0 ∨ x = 1 ∨ x = -1) ∨ b = 0 ∨ b = 1 ∨ b = -1 ↔ b = 0 ∨ b = 1 ∨ b = -1 ∨ …
  tauto
  -- 🎉 no goals
#align real.logb_eq_zero Real.logb_eq_zero

-- TODO add other limits and continuous API lemmas analogous to those in Log.lean
open BigOperators

theorem logb_prod {α : Type*} (s : Finset α) (f : α → ℝ) (hf : ∀ x ∈ s, f x ≠ 0) :
    logb b (∏ i in s, f i) = ∑ i in s, logb b (f i) := by
  classical
    induction' s using Finset.induction_on with a s ha ih
    · simp
    simp only [Finset.mem_insert, forall_eq_or_imp] at hf
    simp [ha, ih hf.2, logb_mul hf.1 (Finset.prod_ne_zero_iff.2 hf.2)]
#align real.logb_prod Real.logb_prod

end Real
