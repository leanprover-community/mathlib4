/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Log.Basic

#align_import analysis.special_functions.complex.log from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# The complex `log` function

Basic properties, relationship with `exp`.
-/


noncomputable section

namespace Complex

open Set Filter

open Real Topology ComplexConjugate

/-- Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `(log x).im ≤ π`.
  `log 0 = 0`-/
-- Porting note: @[pp_nodot] does not exist in mathlib4
noncomputable def log (x : ℂ) : ℂ :=
  x.abs.log + arg x * I
#align complex.log Complex.log

theorem log_re (x : ℂ) : x.log.re = x.abs.log := by simp [log]
                                                    -- 🎉 no goals
#align complex.log_re Complex.log_re

theorem log_im (x : ℂ) : x.log.im = x.arg := by simp [log]
                                                -- 🎉 no goals
#align complex.log_im Complex.log_im

theorem neg_pi_lt_log_im (x : ℂ) : -π < (log x).im := by simp only [log_im, neg_pi_lt_arg]
                                                         -- 🎉 no goals
#align complex.neg_pi_lt_log_im Complex.neg_pi_lt_log_im

theorem log_im_le_pi (x : ℂ) : (log x).im ≤ π := by simp only [log_im, arg_le_pi]
                                                    -- 🎉 no goals
#align complex.log_im_le_pi Complex.log_im_le_pi

theorem exp_log {x : ℂ} (hx : x ≠ 0) : exp (log x) = x := by
  rw [log, exp_add_mul_I, ← ofReal_sin, sin_arg, ← ofReal_cos, cos_arg hx, ← ofReal_exp,
    Real.exp_log (abs.pos hx), mul_add, ofReal_div, ofReal_div,
    mul_div_cancel' _ (ofReal_ne_zero.2 <| abs.ne_zero hx), ← mul_assoc,
    mul_div_cancel' _ (ofReal_ne_zero.2 <| abs.ne_zero hx), re_add_im]
#align complex.exp_log Complex.exp_log

@[simp]
theorem range_exp : Set.range exp = {0}ᶜ :=
  Set.ext fun x =>
    ⟨by
      rintro ⟨x, rfl⟩
      -- ⊢ exp x ∈ {0}ᶜ
      exact exp_ne_zero x, fun hx => ⟨log x, exp_log hx⟩⟩
      -- 🎉 no goals
#align complex.range_exp Complex.range_exp

theorem log_exp {x : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π) : log (exp x) = x := by
  rw [log, abs_exp, Real.log_exp, exp_eq_exp_re_mul_sin_add_cos, ← ofReal_exp,
    arg_mul_cos_add_sin_mul_I (Real.exp_pos _) ⟨hx₁, hx₂⟩, re_add_im]
#align complex.log_exp Complex.log_exp

theorem exp_inj_of_neg_pi_lt_of_le_pi {x y : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π) (hy₁ : -π < y.im)
    (hy₂ : y.im ≤ π) (hxy : exp x = exp y) : x = y := by
  rw [← log_exp hx₁ hx₂, ← log_exp hy₁ hy₂, hxy]
  -- 🎉 no goals
#align complex.exp_inj_of_neg_pi_lt_of_le_pi Complex.exp_inj_of_neg_pi_lt_of_le_pi

theorem ofReal_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x :=
  Complex.ext (by rw [log_re, ofReal_re, abs_of_nonneg hx])
                  -- 🎉 no goals
    (by rw [ofReal_im, log_im, arg_ofReal_of_nonneg hx])
        -- 🎉 no goals
#align complex.of_real_log Complex.ofReal_log

theorem log_ofReal_re (x : ℝ) : (log (x : ℂ)).re = Real.log x := by simp [log_re]
                                                                    -- 🎉 no goals
#align complex.log_of_real_re Complex.log_ofReal_re

theorem log_ofReal_mul {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ≠ 0) :
    log (r * x) = Real.log r + log x := by
  replace hx := Complex.abs.ne_zero_iff.mpr hx
  -- ⊢ log (↑r * x) = ↑(Real.log r) + log x
  simp_rw [log, map_mul, abs_ofReal, arg_real_mul _ hr, abs_of_pos hr, Real.log_mul hr.ne' hx,
    ofReal_add, add_assoc]
#align complex.log_of_real_mul Complex.log_ofReal_mul

theorem log_mul_ofReal (r : ℝ) (hr : 0 < r) (x : ℂ) (hx : x ≠ 0) :
    log (x * r) = Real.log r + log x := by rw [mul_comm, log_ofReal_mul hr hx, add_comm]
                                           -- 🎉 no goals
#align complex.log_mul_of_real Complex.log_mul_ofReal

@[simp]
theorem log_zero : log 0 = 0 := by simp [log]
                                   -- 🎉 no goals
#align complex.log_zero Complex.log_zero

@[simp]
theorem log_one : log 1 = 0 := by simp [log]
                                  -- 🎉 no goals
#align complex.log_one Complex.log_one

theorem log_neg_one : log (-1) = π * I := by simp [log]
                                             -- 🎉 no goals
#align complex.log_neg_one Complex.log_neg_one

theorem log_I : log I = π / 2 * I := by simp [log]
                                        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.log_I Complex.log_I

theorem log_neg_I : log (-I) = -(π / 2) * I := by simp [log]
                                                  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.log_neg_I Complex.log_neg_I

theorem log_conj_eq_ite (x : ℂ) : log (conj x) = if x.arg = π then log x else conj (log x) := by
  simp_rw [log, abs_conj, arg_conj, map_add, map_mul, conj_ofReal]
  -- ⊢ ↑(Real.log (↑abs x)) + ↑(if arg x = π then π else -arg x) * I = if arg x = π …
  split_ifs with hx
  -- ⊢ ↑(Real.log (↑abs x)) + ↑π * I = ↑(Real.log (↑abs x)) + ↑(arg x) * I
  · rw [hx]
    -- 🎉 no goals
  simp_rw [ofReal_neg, conj_I, mul_neg, neg_mul]
  -- 🎉 no goals
#align complex.log_conj_eq_ite Complex.log_conj_eq_ite

theorem log_conj (x : ℂ) (h : x.arg ≠ π) : log (conj x) = conj (log x) := by
  rw [log_conj_eq_ite, if_neg h]
  -- 🎉 no goals
#align complex.log_conj Complex.log_conj

theorem log_inv_eq_ite (x : ℂ) : log x⁻¹ = if x.arg = π then -conj (log x) else -log x := by
  by_cases hx : x = 0
  -- ⊢ log x⁻¹ = if arg x = π then -↑(starRingEnd ℂ) (log x) else -log x
  · simp [hx]
    -- 🎉 no goals
  rw [inv_def, log_mul_ofReal, Real.log_inv, ofReal_neg, ← sub_eq_neg_add, log_conj_eq_ite]
  · simp_rw [log, map_add, map_mul, conj_ofReal, conj_I, normSq_eq_abs, Real.log_pow,
      Nat.cast_two, ofReal_mul, neg_add, mul_neg, neg_neg]
    norm_num; rw [two_mul] -- Porting note: added to simplify `↑2`
    -- ⊢ (if arg x = π then ↑(Real.log (↑abs x)) + ↑(arg x) * I else ↑(Real.log (↑abs …
              -- ⊢ (if arg x = π then ↑(Real.log (↑abs x)) + ↑(arg x) * I else ↑(Real.log (↑abs …
    split_ifs
    -- ⊢ ↑(Real.log (↑abs x)) + ↑(arg x) * I - (↑(Real.log (↑abs x)) + ↑(Real.log (↑a …
    · rw [add_sub_right_comm, sub_add_cancel']
      -- 🎉 no goals
    · rw [add_sub_right_comm, sub_add_cancel']
      -- 🎉 no goals
  · rwa [inv_pos, Complex.normSq_pos]
    -- 🎉 no goals
  · rwa [map_ne_zero]
    -- 🎉 no goals
#align complex.log_inv_eq_ite Complex.log_inv_eq_ite

theorem log_inv (x : ℂ) (hx : x.arg ≠ π) : log x⁻¹ = -log x := by rw [log_inv_eq_ite, if_neg hx]
                                                                  -- 🎉 no goals
#align complex.log_inv Complex.log_inv

theorem two_pi_I_ne_zero : (2 * π * I : ℂ) ≠ 0 := by norm_num [Real.pi_ne_zero, I_ne_zero]
                                                     -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.two_pi_I_ne_zero Complex.two_pi_I_ne_zero

theorem exp_eq_one_iff {x : ℂ} : exp x = 1 ↔ ∃ n : ℤ, x = n * (2 * π * I) := by
  constructor
  -- ⊢ exp x = 1 → ∃ n, x = ↑n * (2 * ↑π * I)
  · intro h
    -- ⊢ ∃ n, x = ↑n * (2 * ↑π * I)
    rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos x.im (-π) with ⟨n, hn, -⟩
    -- ⊢ ∃ n, x = ↑n * (2 * ↑π * I)
    use -n
    -- ⊢ x = ↑(-n) * (2 * ↑π * I)
    rw [Int.cast_neg, neg_mul, eq_neg_iff_add_eq_zero]
    -- ⊢ x + ↑n * (2 * ↑π * I) = 0
    have : (x + n * (2 * π * I)).im ∈ Set.Ioc (-π) π := by simpa [two_mul, mul_add] using hn
    -- ⊢ x + ↑n * (2 * ↑π * I) = 0
    rw [← log_exp this.1 this.2, exp_periodic.int_mul n, h, log_one]
    -- 🎉 no goals
  · rintro ⟨n, rfl⟩
    -- ⊢ exp (↑n * (2 * ↑π * I)) = 1
    exact (exp_periodic.int_mul n).eq.trans exp_zero
    -- 🎉 no goals
#align complex.exp_eq_one_iff Complex.exp_eq_one_iff

theorem exp_eq_exp_iff_exp_sub_eq_one {x y : ℂ} : exp x = exp y ↔ exp (x - y) = 1 := by
  rw [exp_sub, div_eq_one_iff_eq (exp_ne_zero _)]
  -- 🎉 no goals
#align complex.exp_eq_exp_iff_exp_sub_eq_one Complex.exp_eq_exp_iff_exp_sub_eq_one

theorem exp_eq_exp_iff_exists_int {x y : ℂ} : exp x = exp y ↔ ∃ n : ℤ, x = y + n * (2 * π * I) := by
  simp only [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add']
  -- 🎉 no goals
#align complex.exp_eq_exp_iff_exists_int Complex.exp_eq_exp_iff_exists_int

@[simp]
theorem countable_preimage_exp {s : Set ℂ} : (exp ⁻¹' s).Countable ↔ s.Countable := by
  refine' ⟨fun hs => _, fun hs => _⟩
  -- ⊢ Set.Countable s
  · refine' ((hs.image exp).insert 0).mono _
    -- ⊢ s ⊆ insert 0 (exp '' (exp ⁻¹' s))
    rw [Set.image_preimage_eq_inter_range, range_exp, ←Set.diff_eq, ←Set.union_singleton,
        Set.diff_union_self]
    exact Set.subset_union_left _ _
    -- 🎉 no goals
  · rw [← Set.biUnion_preimage_singleton]
    -- ⊢ Set.Countable (⋃ (y : ℂ) (_ : y ∈ s), exp ⁻¹' {y})
    refine' hs.biUnion fun z hz => _
    -- ⊢ Set.Countable (exp ⁻¹' {z})
    rcases em (∃ w, exp w = z) with (⟨w, rfl⟩ | hne)
    -- ⊢ Set.Countable (exp ⁻¹' {exp w})
    · simp only [Set.preimage, Set.mem_singleton_iff, exp_eq_exp_iff_exists_int, Set.setOf_exists]
      -- ⊢ Set.Countable (⋃ (i : ℤ), {x | x = w + ↑i * (2 * ↑π * I)})
      exact Set.countable_iUnion fun m => Set.countable_singleton _
      -- 🎉 no goals
    · push_neg at hne
      -- ⊢ Set.Countable (exp ⁻¹' {z})
      simp [Set.preimage, hne]
      -- 🎉 no goals
#align complex.countable_preimage_exp Complex.countable_preimage_exp

alias ⟨_, _root_.Set.Countable.preimage_cexp⟩ := countable_preimage_exp
#align set.countable.preimage_cexp Set.Countable.preimage_cexp

theorem tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto log (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 <| Real.log (abs z) - π * I) := by
  convert
    (continuous_ofReal.continuousAt.comp_continuousWithinAt
            (continuous_abs.continuousWithinAt.log _)).tendsto.add
      (((continuous_ofReal.tendsto _).comp <|
            tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhds) using 1
  · simp [sub_eq_add_neg]
    -- 🎉 no goals
  · lift z to ℝ using him
    -- ⊢ ↑abs ↑z ≠ 0
    simpa using hre.ne
    -- 🎉 no goals
#align complex.tendsto_log_nhds_within_im_neg_of_re_neg_of_im_zero Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero

theorem continuousWithinAt_log_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    ContinuousWithinAt log { z : ℂ | 0 ≤ z.im } z := by
  convert
    (continuous_ofReal.continuousAt.comp_continuousWithinAt
            (continuous_abs.continuousWithinAt.log _)).tendsto.add
      ((continuous_ofReal.continuousAt.comp_continuousWithinAt <|
            continuousWithinAt_arg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhds) using 1
  · lift z to ℝ using him
    -- ⊢ ↑abs ↑z ≠ 0
    simpa using hre.ne
    -- 🎉 no goals
#align complex.continuous_within_at_log_of_re_neg_of_im_zero
Complex.continuousWithinAt_log_of_re_neg_of_im_zero

theorem tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto log (𝓝[{ z : ℂ | 0 ≤ z.im }] z) (𝓝 <| Real.log (abs z) + π * I) := by
  simpa only [log, arg_eq_pi_iff.2 ⟨hre, him⟩] using
    (continuousWithinAt_log_of_re_neg_of_im_zero hre him).tendsto
#align complex.tendsto_log_nhds_within_im_nonneg_of_re_neg_of_im_zero Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero

@[simp]
theorem map_exp_comap_re_atBot : map exp (comap re atBot) = 𝓝[≠] 0 := by
  rw [← comap_exp_nhds_zero, map_comap, range_exp, nhdsWithin]
  -- 🎉 no goals
#align complex.map_exp_comap_re_at_bot Complex.map_exp_comap_re_atBot

@[simp]
theorem map_exp_comap_re_atTop : map exp (comap re atTop) = comap abs atTop := by
  rw [← comap_exp_comap_abs_atTop, map_comap, range_exp, inf_eq_left, le_principal_iff]
  -- ⊢ {0}ᶜ ∈ comap (↑abs) atTop
  exact eventually_ne_of_tendsto_norm_atTop tendsto_comap 0
  -- 🎉 no goals
#align complex.map_exp_comap_re_at_top Complex.map_exp_comap_re_atTop

end Complex

section LogDeriv

open Complex Filter

open Topology

variable {α : Type*}

theorem continuousAt_clog {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) : ContinuousAt log x := by
  refine' ContinuousAt.add _ _
  -- ⊢ ContinuousAt (fun x => ↑(Real.log (↑Complex.abs x))) x
  · refine' continuous_ofReal.continuousAt.comp _
    -- ⊢ ContinuousAt (fun x => Real.log (↑Complex.abs x)) x
    refine' (Real.continuousAt_log _).comp Complex.continuous_abs.continuousAt
    -- ⊢ ↑Complex.abs x ≠ 0
    rw [Complex.abs.ne_zero_iff]
    -- ⊢ x ≠ 0
    rintro rfl
    -- ⊢ False
    simp at h
    -- 🎉 no goals
  · have h_cont_mul : Continuous fun x : ℂ => x * I := continuous_id'.mul continuous_const
    -- ⊢ ContinuousAt (fun x => ↑(arg x) * I) x
    refine' h_cont_mul.continuousAt.comp (continuous_ofReal.continuousAt.comp _)
    -- ⊢ ContinuousAt (fun x => arg x) x
    exact continuousAt_arg h
    -- 🎉 no goals
#align continuous_at_clog continuousAt_clog

theorem _root_.Filter.Tendsto.clog {l : Filter α} {f : α → ℂ} {x : ℂ} (h : Tendsto f l (𝓝 x))
    (hx : 0 < x.re ∨ x.im ≠ 0) : Tendsto (fun t => log (f t)) l (𝓝 <| log x) :=
  (continuousAt_clog hx).tendsto.comp h
#align filter.tendsto.clog Filter.Tendsto.clog

variable [TopologicalSpace α]

nonrec
theorem _root_.ContinuousAt.clog {f : α → ℂ} {x : α} (h₁ : ContinuousAt f x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : ContinuousAt (fun t => log (f t)) x :=
  h₁.clog h₂
#align continuous_at.clog ContinuousAt.clog

nonrec
theorem _root_.ContinuousWithinAt.clog {f : α → ℂ} {s : Set α} {x : α}
    (h₁ : ContinuousWithinAt f s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
    ContinuousWithinAt (fun t => log (f t)) s x :=
  h₁.clog h₂
#align continuous_within_at.clog ContinuousWithinAt.clog

nonrec
theorem _root_.ContinuousOn.clog {f : α → ℂ} {s : Set α} (h₁ : ContinuousOn f s)
    (h₂ : ∀ x ∈ s, 0 < (f x).re ∨ (f x).im ≠ 0) : ContinuousOn (fun t => log (f t)) s := fun x hx =>
  (h₁ x hx).clog (h₂ x hx)
#align continuous_on.clog ContinuousOn.clog

nonrec
theorem _root_.Continuous.clog {f : α → ℂ} (h₁ : Continuous f)
    (h₂ : ∀ x, 0 < (f x).re ∨ (f x).im ≠ 0) : Continuous fun t => log (f t) :=
  continuous_iff_continuousAt.2 fun x => h₁.continuousAt.clog (h₂ x)
#align continuous.clog Continuous.clog

end LogDeriv
