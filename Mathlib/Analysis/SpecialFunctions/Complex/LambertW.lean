/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib

/-!
# The complex `LambertW` function

TODO: add doc, add local notation doc, add tag
-/

@[expose] public noncomputable section

section LambertWAux

namespace Real

open Filter Topology Set

variable {x : ℝ}

theorem tendsto_sin_nhdsGT_zero : Tendsto sin (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa using continuous_sin.tendsto 0 |>.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT pi_pos] with x hx using sin_pos_of_pos_of_lt_pi hx.1 hx.2

theorem tendsto_sin_nhdsLT_pi : Tendsto sin (𝓝[<] π) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa using continuous_sin.tendsto π |>.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT pi_pos] with x hx using sin_pos_of_pos_of_lt_pi hx.1 hx.2

theorem tendsto_cos_nhdsLT_pi : Tendsto cos (𝓝[<] π) (𝓝[>] (-1)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa using continuous_cos.tendsto π |>.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT pi_pos] with x hx using
      mem_Ioi.mpr <| cos_pi ▸ strictAntiOn_cos
        ⟨hx.left.le, hx.right.le⟩ ⟨pi_pos.le, le_rfl⟩ hx.right

private theorem existsUnique_mem_Ioc (x : ℝ) :
    ∃! k : ℤ, x ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π) := by
  simpa [mul_comm, mul_two, mul_sub, mul_add, add_comm, sub_lt_iff_lt_add] using
    existsUnique_sub_zsmul_mem_Ioc two_pi_pos x (-π)

theorem add_sin_mem_Ioo_of_mem_Ioo :
    ∀ ⦃x : ℝ⦄, x ∈ Ioo (-π) π -> x + x.sin ∈ Ioo (-π) π := by
  suffices ∀ x ∈ Ioo (-π) π, x + x.sin < π from fun x ⟨hxl, hxr⟩ =>
    ⟨by grind [this (-x) ⟨neg_lt_neg_iff.mpr hxr, neg_lt.mp hxl⟩, sin_neg x], this x ⟨hxl, hxr⟩⟩
  exact fun x hx => by grind [sin_lt <| sub_pos_of_lt hx.right, sin_pi_sub x]

private theorem existsUnique_mem_Ico_mul_exp_eq_of_mem_Ico (hx : x ∈ Ico (-(rexp 1)⁻¹) 0) :
    ∃! t ∈ Ico (-1) 0, t * rexp t = x := by
  obtain ⟨t, ht, hteq⟩ : ∃ t ∈ Icc (-1) 0, t * rexp t = x :=
    intermediate_value_Icc (by norm_num) (by fun_prop) ⟨by grind [exp_neg], by simpa using hx.2.le⟩
  exact ⟨t, ⟨⟨ht.left, by grind⟩, hteq⟩, fun y hy => exp_injective (mul_log_strictMonoOn.injOn
    (exp_le_exp.mpr hy.left.left) (exp_le_exp.mpr ht.left) (by grind [log_exp]))⟩

private theorem existsUnique_mem_Iic_mul_exp_eq_of_mem_Ico (hx : x ∈ Ico (-(rexp 1)⁻¹) 0) :
    ∃! t ∈ Iic (-1), t * rexp t = x := by
  obtain ⟨S, hS⟩ : ∃ S, ∀ b ≥ S, b ^ 1 * rexp (-b) < -x :=
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 |>.eventually <|
      eventually_lt_nhds <| neg_pos_of_neg hx.right).exists_forall_of_atTop
  obtain ⟨t, ht, hteq⟩ : ∃ t ∈ Icc (-(S ⊔ 1)) (-1), t * rexp t = x :=
    intermediate_value_Icc' (by simp) (by fun_prop)
      ⟨by grind [exp_neg], by grind [hS (S ⊔ 1), pow_one, exp_neg]⟩
  exact ⟨t, ⟨ht.2, hteq⟩, fun y hy => exp_injective <| mul_log_strictAntiOn.injOn
    ⟨exp_nonneg y, exp_le_exp.mpr hy.left⟩ ⟨exp_nonneg t, exp_le_exp.mpr ht.right⟩
      (by grind [log_exp])⟩

private theorem exists_add_log_eq (x : ℝ) : ∃ t > 0, t + log t = x :=
  continuousOn_id.add continuousOn_log |>.mono (by simp) |>.surjOn_of_tendsto
    nonempty_Ioi (tendsto_comp_coe_Ioi_atBot (Order.IsPredPrelimit.of_dense 0) |>.mpr <|
      tendsto_id.mono_left nhdsWithin_le_nhds |>.add_atBot tendsto_log_nhdsGT_zero)
        (tendsto_comp_val_Ioi_atTop.mpr <| tendsto_id.atTop_add_atTop tendsto_log_atTop) trivial

private theorem existsUnique_add_log_eq (x : ℝ) : ∃! t > 0, t + log t = x := by
  apply existsUnique_of_exists_of_unique (exists_add_log_eq x) fun t u ⟨ht, ht_eq⟩ ⟨hu, hu_eq⟩ => ?_
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h <;> [grind [log_lt_log ht h]; grind [log_lt_log hu h]]

theorem neg_exp_one_inv_le_mul_exp : -(rexp 1)⁻¹ ≤ x * rexp x := by
  grind [mul_exp_neg_le_exp_neg_one (-x), exp_neg]

end Real

namespace Complex

open Real Set

open scoped ComplexConjugate

variable {x y z w : ℂ} {i : ℤ}

private theorem arg_add_im_eq_pi_of_arg_eq_pi (h : x.arg = π) : x.arg + x.im = π := by
  simpa [(arg_eq_pi_iff.1 h).2]

-- theorem exists_arg_mul_eq_add_arg (hx : x ≠ 0) (hy : y ≠ 0) :
--     ∃ k : ℤ, (x * y).arg = x.arg + y.arg + k * (2 * π):= by
--   have h : ((x * y).arg : Real.Angle) = ((x.arg + y.arg : ℝ) : Real.Angle) := by
--     rw [arg_mul_coe_angle hx hy, Angle.coe_add]
--   obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h
--   exact ⟨k, by linarith⟩

private theorem arg_pos_of_arg_add_im_pos (h : 0 < w.arg + w.im) : 0 < w.arg := by
  rcases lt_trichotomy w.arg 0 with h | h | h
  · linarith [arg_neg_iff.mp h]
  · linarith [arg_eq_zero_iff.mp h |>.right]
  · exact h

private theorem arg_mem_Ioo_of_arg_add_im_pos (hw : w ≠ 0)
    (harg : w.arg ≠ π) (hA : 0 < w.arg + w.im) : w.arg ∈ Ioo 0 (min (w.arg + w.im) π) := by
  replace harg : w.arg < π := lt_of_le_of_ne (arg_le_pi w) harg
  have harg₀ : 0 < w.arg := arg_pos_of_arg_add_im_pos hA
  refine ⟨harg₀, lt_min ?_ harg⟩
  rw [← norm_mul_sin_arg]
  nlinarith [Real.sin_pos_of_pos_of_lt_pi harg₀ harg, norm_pos_iff.mpr hw]

private theorem sin_arg_ne_zero_of_arg_add_im_pos
    (hw : w ≠ 0) (harg : w.arg ≠ π) (hA : 0 < w.arg + w.im) : Real.sin w.arg ≠ 0 := by
  obtain ⟨h0, h1⟩ := arg_mem_Ioo_of_arg_add_im_pos hw harg hA
  exact (Real.sin_pos_of_pos_of_lt_pi h0 <| h1.trans_le <| min_le_right _ _).ne'

private theorem add_log_im : (x + x.log).im = x.arg + x.im := by
  simp [log, add_comm]

private theorem arg_mul_exp_eq_of_mem (hx : x ≠ 0)
    (h : x.arg + x.im ∈ Ioc ((2 * i - 1) * π) ((2 * i + 1) * π)) :
    (x * cexp x).arg = x.arg + x.im - i * (2 * π) := by
  rw [← exp_log hx, ← exp_add, mul_comm, arg_exp, add_im, log_im, toIocMod_eq_iff, exp_log hx]
  exact ⟨by grind [h.left, h.right, Real.pi_pos], i, by ring⟩

private theorem mul_exp_mem_of_arg_add_im_eq
    (hw : w.arg + w.im ∈ Ioc ((2 * i - 1) * π) ((2 * i + 1) * π))
    (hz : w * cexp w ∈ Iio 0 ×ℂ {0}) : w.arg + w.im = (2 * i + 1) * π := by
  grind [arg_mul_exp_eq_of_mem (fun nh => by simp [nh, mem_reProdIm] at hz) hw,
    arg_eq_pi_iff.mpr hz]

private theorem arg_add_im_eq_of_mul_exp_eq (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x * cexp x = y * cexp y) (hx' : x.arg + x.im ∈ Ioc ((2 * i - 1) * π) ((2 * i + 1) * π))
    (hy' : y.arg + y.im ∈ Ioc ((2 * i - 1) * π) ((2 * i + 1) * π)) :
    x.arg + x.im = y.arg + y.im := by
  grind [arg_mul_exp_eq_of_mem hx hx', arg_mul_exp_eq_of_mem hy hy']

private theorem mul_exp_eq_of_arg_add_im_eq (hx : x ≠ 0) (h : x.arg + x.im = (2 * i + 1) * π) :
    x * cexp x = -rexp (x + log x).re := by
  nth_rw 1 [← exp_log hx, ← exp_add, ← add_comm]
  apply Complex.ext
  · rw [exp_re, add_log_im, h, add_mul, one_mul, mul_comm (2 : ℝ), mul_assoc]
    rw_mod_cast [Real.cos_int_mul_two_pi_add_pi i]
    rw [mul_neg_one]
  · rw_mod_cast [exp_im, add_log_im, h, Real.sin_int_mul_pi (2 * i + 1), mul_zero]

--  this needs annotation
private theorem im_eq_zero_of_arg_add_im_eq_pi_of_mul_exp_mem {w : ℂ}
    (hw1 : w.arg + w.im = π) (hw2 : w * cexp w ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    w.im = 0 := by
  obtain ⟨hzge, hzlt⟩ := mem_Ico.mp <| mem_reProdIm.mp hw2 |>.left
  have hw₀ : w ≠ 0 := fun hw => by simp [hw] at hzlt
  by_contra nh
  obtain ⟨nh, harg⟩ : 0 < w.im ∧ w.arg = π - w.im := by grind [arg_le_pi w]
  have hnormsin : ‖w‖ * Real.sin w.im = w.im := by simpa [harg] using norm_mul_sin_arg w
  have hsin : 0 < Real.sin w.im := by nlinarith [hnormsin, norm_pos_iff.mpr hw₀]
  have hnorm : ‖w‖ = w.im / Real.sin w.im := by rwa [eq_div_iff hsin.ne']
  have hcos : ‖w‖ * -Real.cos w.im = w.re := by simpa [harg] using norm_mul_cos_arg w
  have himpi : w.im < π := by
    by_contra hc
    have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (x := w.im - 2 * π)
      (by linarith [neg_pi_lt_arg w]) (by linarith [not_lt.mp hc])
    grind [Real.sin_sub_two_pi]
  have hbc : w.im * Real.cos w.im < Real.sin w.im := by
    rcases lt_or_ge w.im (π / 2) with h | h
    · have hc : 0 < Real.cos w.im := Real.cos_pos_of_mem_Ioo ⟨by linarith [ pi_pos], h⟩
      simpa [Real.tan_eq_sin_div_cos, hc.ne'] using mul_lt_mul_of_pos_right (Real.lt_tan nh h) hc
    · nlinarith [Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith [himpi]), hsin]
  have hcore : -1 < (w + log w).re := by
    rw [add_re, log_re]
    grind [(div_lt_one hsin).mpr hbc,
      Real.log_pos (show 1 < ‖w‖ by simpa [hnorm, one_lt_div hsin] using Real.sin_lt nh)]
  rw [mul_exp_eq_of_arg_add_im_eq (i := 0) hw₀ (by grind), neg_re, ofReal_re,
    ← Real.exp_neg] at hzge
  linarith [Real.exp_le_exp.mp <| neg_le_neg_iff.mp hzge]

private theorem im_eq_zero_of_arg_add_im_eq_neg_pi_of_mul_exp_mem
    (hw1 : w.arg + w.im = -π) (hw2 : w * cexp w ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    w.im = 0 := by
  rw [← neg_eq_zero, ← conj_im]
  apply im_eq_zero_of_arg_add_im_eq_pi_of_mul_exp_mem ?_ ?_
  · rw [conj_im, arg_conj, ite_eq_right (by grind [pi_pos, arg_eq_pi_iff]), ← neg_add, hw1, neg_neg]
  · simp_all [mem_reProdIm, exp_conj, ← map_mul]

private theorem continuousOn_arg_add_im : ContinuousOn (fun w => w.arg + w.im) Complex.slitPlane :=
  continuousOn_arg.add continuous_im.continuousOn

end Complex

section Solve

open Real Complex ComplexConjugate Set Filter Topology

variable {ρ θ ϕ : ℝ}

namespace Real

theorem tendsto_const_sub_nhdsLT (θ : ℝ) :
    Tendsto (fun ϕ : ℝ => θ - ϕ) (𝓝[<] θ) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff, ← sub_self θ]
  refine ⟨tendsto_const_nhds.sub tendsto_id |>.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx using sub_lt_sub_left (mem_Iio.mp hx) θ

private theorem LambertW.tendsto_self_div_sin_nhdsGT_zero :
    Tendsto (fun u : ℝ => u / sin u) (𝓝[>] 0) (𝓝 1) := by
  have h1 : Tendsto (fun u : ℝ => sin u / u) (𝓝[>] 0) (𝓝 1) := by
    simpa [slope_fun_def_field, cos_zero] using
      (hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_sin 0)).mono_left (nhdsGT_le_nhdsNE 0)
  simpa [inv_div] using h1.inv₀ one_ne_zero

private theorem tendsto_mul_exp_neg_div_two_atTop :
    Tendsto (fun r ↦ r * rexp (-r / 2)) atTop (𝓝 0) := by
  convert! (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 |>.comp <|
    tendsto_id.atTop_div_const zero_lt_two).const_mul 2 using 2
  · simp [field]
  · rw [mul_zero]

private def LambertW.solutionArgAux (θ : ℝ) : ℝ -> ℝ := fun ϕ => (θ - ϕ) / sin ϕ

private def LambertW.solutionNormAux (θ : ℝ) : ℝ -> ℝ := fun ϕ =>
  solutionArgAux θ ϕ * rexp (solutionArgAux θ ϕ * cos ϕ)

private theorem LambertW.sin_pos_of_mem_Ioo_inf_pi (hϕ : ϕ ∈ Ioo 0 (θ ⊓ π)) : 0 < sin ϕ :=
  sin_pos_of_pos_of_lt_pi hϕ.1 <| hϕ.2.trans_le inf_le_right

private theorem LambertW.continuousOn_solutionArgAux {s : Set ℝ} (hs : ∀ x ∈ s, sin x ≠ 0) :
    ContinuousOn (solutionArgAux θ) s :=
  continuous_const.sub continuous_id |>.continuousOn |>.div continuous_sin.continuousOn hs

private theorem LambertW.continuousOn_solutionNormAux {s : Set ℝ} (hs : ∀ x ∈ s, sin x ≠ 0) :
    ContinuousOn (solutionNormAux θ) s :=
  letI h1 := continuousOn_solutionArgAux hs
  h1.mul (h1.mul continuous_cos.continuousOn).rexp

private theorem LambertW.hasDerivAt_solutionArgAux (θ : ℝ) (hs : sin ϕ ≠ 0) :
    HasDerivAt (solutionArgAux θ) (-(sin ϕ + (θ - ϕ) * cos ϕ) / sin ϕ ^ 2) ϕ := by
  refine hasDerivAt_id ϕ |>.const_sub θ |>.div (hasDerivAt_sin ϕ) hs |>.congr_deriv ?_
  simp only [id_eq, field, neg_add, SubNegMonoid.sub_eq_add_neg]

private theorem LambertW.deriv_solutionArgAux {ϕ : ℝ} (hs : sin ϕ ≠ 0) :
    deriv (solutionArgAux θ) ϕ = -(sin ϕ + (θ - ϕ) * cos ϕ) / sin ϕ ^ 2 :=
  hasDerivAt_solutionArgAux θ hs |>.deriv

private theorem LambertW.deriv_solutionNormAux_neg {ϕ : ℝ} (hϕ : ϕ ∈ Ioo 0 (θ ⊓ π)) :
    deriv (solutionNormAux θ) ϕ < 0 := by
  have hs₀ : 0 < sin ϕ := sin_pos_of_mem_Ioo_inf_pi hϕ
  have := (hasDerivAt_solutionArgAux θ hs₀.ne').differentiableAt
  calc deriv (solutionNormAux θ) ϕ = -rexp (solutionArgAux θ ϕ * cos ϕ) *
      ((sin ϕ + (θ - ϕ) * cos ϕ) ^ 2 / sin ϕ ^ 3 + (θ - ϕ) ^ 2 / sin ϕ) := by
        unfold solutionNormAux
        rw [deriv_fun_mul this (by fun_prop), _root_.deriv_exp (by fun_prop),
          deriv_fun_mul (by fun_prop) differentiableAt_cos, deriv_cos,
          deriv_solutionArgAux hs₀.ne',
          ← div_mul_cancel₀ (solutionArgAux θ ϕ) hs₀.ne', solutionArgAux]
        field_simp
        ring
      _ < 0 := by
        simp only [neg_mul, Left.neg_neg_iff]
        positivity [hϕ.right.trans_le inf_le_left]

private theorem LambertW.strictAntiOn_solutionNormAux :
    StrictAntiOn (solutionNormAux θ) (Ioo 0 (θ ⊓ π)) :=
  strictAntiOn_of_deriv_neg (convex_Ioo 0 (θ ⊓ π))
    (continuousOn_solutionNormAux fun _ hx => sin_pos_of_mem_Ioo_inf_pi hx |>.ne')
    fun _ hϕ => deriv_solutionNormAux_neg (by rwa [interior_Ioo] at hϕ)

private theorem LambertW.injOn_solutionNormAux : InjOn (solutionNormAux θ) (Ioo 0 (θ ⊓ π)) :=
  strictAntiOn_solutionNormAux.injOn

private theorem LambertW.tendsto_solutionArgAux_nhdsGT_zero (hθ : 0 < θ) :
    Tendsto (solutionArgAux θ) (𝓝[>] 0) atTop := by
  unfold solutionArgAux
  simpa [div_eq_mul_inv] using continuous_const.sub continuous_id |>.tendsto 0 |>.mono_left
    nhdsWithin_le_nhds |>.pos_mul_atTop (sub_pos.mpr hθ) <|
    tendsto_inv_nhdsGT_zero.comp tendsto_sin_nhdsGT_zero

-- private theorem LambertW.tendsto_solutionArgAux_nhdsLT_self (hθ1 : 0 < θ) (hθ2 : θ < π) :
--     Tendsto (solutionArgAux θ) (𝓝[<] θ) (𝓝 0) := by
--   change Tendsto ((fun ϕ : ℝ => θ - ϕ) / sin) (𝓝[<] θ) (𝓝 0)
--   simpa using ((tendsto_const_sub_nhdsLT θ).mono_right nhdsWithin_le_nhds).div
--     ((continuous_sin.tendsto θ).mono_left nhdsWithin_le_nhds)
--     (sin_pos_of_pos_of_lt_pi hθ1 hθ2).ne'

private theorem LambertW.tendsto_solutionArgAux_nhdsLT_pi (hθ : π < θ) :
    Tendsto (solutionArgAux θ) (𝓝[<] π) atTop :=
  continuous_const.sub continuous_id |>.tendsto π |>.mono_left
    nhdsWithin_le_nhds |>.pos_mul_atTop (sub_pos.mpr hθ) <|
      tendsto_inv_nhdsGT_zero.comp tendsto_sin_nhdsLT_pi

private theorem LambertW.tendsto_solutionArgAux_pi_nhdsLT_pi :
    Tendsto (solutionArgAux π) (𝓝[<] π) (𝓝 1) := by
  unfold solutionArgAux
  simpa [Function.comp_def] using tendsto_self_div_sin_nhdsGT_zero.comp (tendsto_const_sub_nhdsLT π)

private theorem LambertW.tendsto_solutionNormAux_nhdsGT_zero (hθ : 0 < θ) :
    Tendsto (solutionNormAux θ) (𝓝[>] 0) atTop := by
  refine tendsto_atTop_mono' (𝓝[>] 0) ?_ <| tendsto_solutionArgAux_nhdsGT_zero hθ
  filter_upwards [Ioo_mem_nhdsGT (a := θ ⊓ (π / 2)) (by grind [pi_pos])] with ϕ hϕ
  nth_rw 1 [← mul_one (solutionArgAux θ ϕ)]
  have hrϕ : 0 ≤ solutionArgAux θ ϕ := div_nonneg (by grind) (by grind [sin_pos_of_pos_of_lt_pi])
  apply mul_le_mul_of_nonneg_left (one_le_exp (mul_nonneg hrϕ ?_)) hrϕ
  grind [cos_pos_of_mem_Ioo]

private theorem LambertW.tendsto_solutionNormAux_nhdsLT_self (hθ1 : 0 < θ) (hθ2 : θ < π) :
    Tendsto (solutionNormAux θ) (𝓝[<] θ) (𝓝 0) := by
  have : ContinuousAt (solutionArgAux θ) θ :=
    ContinuousAt.div (by fun_prop) (by fun_prop) <| sin_pos_of_pos_of_lt_pi hθ1 hθ2 |>.ne'
  replace this : ContinuousAt (solutionNormAux θ) θ :=
    this.mul <| this.mul continuous_cos.continuousAt |>.rexp
  convert! this.tendsto.mono_left nhdsWithin_le_nhds using 2
  simp [solutionNormAux, solutionArgAux]

private theorem LambertW.tendsto_solutionNormAux_nhdsLT_pi (hθ : π < θ) :
    Tendsto (solutionNormAux θ) (𝓝[<] π) (𝓝 0) := by
  apply squeeze_zero' (g := fun ϕ => solutionArgAux θ ϕ * rexp (-(solutionArgAux θ ϕ) / 2))
  · filter_upwards [Ioo_mem_nhdsLT pi_pos] with x hx using
      mul_nonneg (div_nonneg (by grind) (by grind [sin_pos_of_pos_of_lt_pi])) (exp_nonneg _)
  · filter_upwards [Ioo_mem_nhdsLT (a := π - π / 3) (by grind [pi_pos])] with ϕ hϕ
    have hr : 0 ≤ solutionArgAux θ ϕ := div_nonneg (by grind [hϕ.right]) <| le_of_lt <|
      sin_pos_of_pos_of_lt_pi (by grind [pi_pos, hϕ.left]) hϕ.right
    have hcos : cos ϕ ≤ -(1 / 2) := by
      grw [cos_le_cos_of_nonneg_of_le_pi (by grind) hϕ.right.le hϕ.left.le,
        cos_pi_sub, cos_pi_div_three]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith)) hr
  · apply Filter.Tendsto.comp (g := fun r => r * rexp (-r / 2)) (y := atTop)
      tendsto_mul_exp_neg_div_two_atTop (tendsto_solutionArgAux_nhdsLT_pi hθ)

private theorem LambertW.tendsto_solutionNormAux_nhdsLT_inf_pi (hθ1 : θ ≠ π) (hθ2 : 0 < θ) :
    Tendsto (solutionNormAux θ) (𝓝[<] (θ ⊓ π)) (𝓝 0) := by
  rcases le_or_gt π θ with hθ' | hθ'
  · rw [min_eq_right hθ']
    exact tendsto_solutionNormAux_nhdsLT_pi <| lt_of_le_of_ne hθ' <| Ne.symm hθ1
  · rw [min_eq_left_of_lt hθ']
    exact tendsto_solutionNormAux_nhdsLT_self hθ2 hθ'

private theorem LambertW.tendsto_solutionNormAux_pi_nhdsLT_pi :
    Tendsto (solutionNormAux π) (𝓝[<] π) (𝓝 (rexp 1)⁻¹) := by
  unfold solutionNormAux
  simpa [exp_neg] using tendsto_solutionArgAux_pi_nhdsLT_pi.mul <|
    continuous_exp.tendsto (1 * -1) |>.comp <| tendsto_solutionArgAux_pi_nhdsLT_pi.mul <|
      tendsto_nhds_of_tendsto_nhdsWithin tendsto_cos_nhdsLT_pi

private theorem LambertW.existsUnique_solutionNormAux_pi (hρ : (rexp 1)⁻¹ < ρ) :
    ∃! ϕ ∈ Ioo 0 π, solutionNormAux π ϕ = ρ := by
  obtain ⟨φ, hφ, hφρ⟩ :=
    isPreconnected_Ioo.intermediate_value_Ioi
      (le_principal_iff.mpr (Ioo_mem_nhdsLT pi_pos))
        (le_principal_iff.mpr (Ioo_mem_nhdsGT pi_pos))
          (continuousOn_solutionNormAux fun x hx => sin_pos_of_mem_Ioo hx |>.ne')
            tendsto_solutionNormAux_pi_nhdsLT_pi
              (tendsto_solutionNormAux_nhdsGT_zero pi_pos) hρ
  exact ⟨φ, ⟨hφ, hφρ⟩, fun φ' hφ' => (min_self π ▸ injOn_solutionNormAux (θ := π))
    hφ'.1 hφ (hφ'.2.trans hφρ.symm)⟩

private theorem LambertW.existsUnique_solutionNormAux (hθ1 : θ ≠ π) (hθ2 : 0 < θ) (hρ : 0 < ρ) :
    ∃! ϕ ∈ Ioo 0 (θ ⊓ π), solutionNormAux θ ϕ = ρ := by
  obtain ⟨ϕ, hϕ⟩ : ∃ ϕ ∈ Ioo 0 (min θ π), solutionNormAux θ ϕ = ρ :=
    isPreconnected_Ioo.intermediate_value_Ioi
      (le_principal_iff.mpr <| Ioo_mem_nhdsLT <| lt_min hθ2 pi_pos)
        (le_principal_iff.mpr <| Ioo_mem_nhdsGT <| lt_min hθ2 pi_pos)
          (continuousOn_solutionNormAux fun x hx => sin_pos_of_mem_Ioo_inf_pi hx |>.ne')
            (tendsto_solutionNormAux_nhdsLT_inf_pi hθ1 hθ2)
              (tendsto_solutionNormAux_nhdsGT_zero hθ2) hρ
  exact ⟨ϕ, hϕ, fun _ hϕ' => Eq.symm <|
    injOn_solutionNormAux hϕ.left hϕ'.left <| hϕ.right ▸ hϕ'.right.symm⟩

private theorem LambertW.existsUnique_mem_Ioo_pi (hρ : (rexp 1)⁻¹ < ρ) :
    ∃! ϕ ∈ Ioo 0 π, (π - ϕ) / sin ϕ * rexp ((π - ϕ) / sin ϕ * cos ϕ) = ρ :=
  existsUnique_solutionNormAux_pi hρ

--  these need annotations
private theorem LambertW.existsUnique_mem_Ioo (hθ1 : θ ≠ π) (hθ2 : 0 < θ) (hρ : 0 < ρ) :
    ∃! ϕ ∈ Ioo 0 (θ ⊓ π),
      (θ - ϕ) / sin ϕ * rexp ((θ - ϕ) / sin ϕ * cos ϕ) = ρ :=
  existsUnique_solutionNormAux hθ1 hθ2 hρ

end Real

namespace Complex

--  these need annotations
private theorem LambertW.existsUnique_arg_add_im_eq_of_pos (hθ1 : θ ≠ π) (hθ2 : 0 < θ)
    (hρ : 0 < ρ) : ∃! w : ℂ, w.arg + w.im = θ ∧ w * cexp w = ρ * cexp (θ * I) := by
  set r : ℝ -> ℝ := fun ϕ => (θ - ϕ) / ϕ.sin
  obtain ⟨ϕ, ⟨hϕ, hrρ⟩, H⟩ := LambertW.existsUnique_mem_Ioo hθ1 hθ2 hρ
  change r ϕ * rexp (r ϕ * ϕ.cos) = ρ at hrρ
  have hsϕ : 0 < ϕ.sin :=
    sin_pos_of_pos_of_lt_pi hϕ.left <| hϕ.right.trans_le <| min_le_right θ π
  have hr : 0 < r ϕ := by
    unfold r
    refine div_pos_iff_of_pos_left ?_ |>.mpr hsϕ
    simpa using hϕ.right.trans_le <| min_le_left θ π
  refine ⟨r ϕ * cexp (ϕ * I), ⟨?_, ?_⟩, ?_⟩
  · rw [exp_ofReal_mul_I, ofReal_cos, ofReal_sin, arg_mul_cos_add_sin_mul_I hr (by grind)]
    simp [sin_ofReal_re]
    grind
  · calc
      _ = ↑(r ϕ * rexp (r ϕ * ϕ.cos)) * cexp (↑(ϕ + r ϕ * ϕ.sin) * I) := by
        nth_rw 2 [exp_mul_I]
        rw [mul_add, exp_add, ofReal_add, add_mul, exp_add]
        simp
        ring_nf
      _ = ρ * cexp (θ * I) := by grind
  · intro w' ⟨hw'ϕ, hw'ρ⟩
    have hw'ϕ_ne_pi : w'.arg ≠ π := by grind [arg_add_im_eq_pi_of_arg_eq_pi]
    have hw'₀ : w' ≠ 0 := fun nh =>
      mul_ne_zero (ofReal_ne_zero.mpr hρ.ne') (exp_ne_zero _) <| by rw [← hw'ρ, nh, zero_mul]
    have hθ'2 : 0 < w'.arg + w'.im := hw'ϕ ▸ hθ2
    have hw'r : ‖w'‖ = r (w'.arg) := by
      grind [eq_div_iff <| sin_arg_ne_zero_of_arg_add_im_pos hw'₀ hw'ϕ_ne_pi hθ'2, norm_mul_sin_arg]
    have hρ' : r (w'.arg) * rexp (r (w'.arg) * w'.arg.cos) = ρ := by
      have hc : ‖w' * cexp w'‖ = ‖ρ * cexp (θ * I)‖ := congrArg norm hw'ρ
      rw [norm_mul, norm_exp, ← norm_mul_cos_arg, hw'r] at hc
      simpa [norm_exp, norm_real, abs_of_pos hρ] using hc
    calc
      w' = ‖w'‖ * cexp (w'.arg * I) := norm_mul_exp_arg_mul_I w' |>.symm
      _ = (r (w'.arg)) * cexp (w'.arg * I) := by rw [hw'r]
      _ = (r ϕ) * cexp (ϕ * I) := by
        rw [H w'.arg ⟨hw'ϕ ▸ arg_mem_Ioo_of_arg_add_im_pos hw'₀ hw'ϕ_ne_pi hθ'2, hρ'⟩]

private theorem LambertW.existsUnique_arg_add_im_eq_pi (hρ : (rexp 1)⁻¹ < ρ) :
    ∃! w : ℂ, w.arg + w.im = π ∧ w * cexp w = ρ * cexp (π * I) ∧ w.im > 0 := by
  have hρ0 : 0 < ρ := (inv_pos.mpr (Real.exp_pos 1)).trans hρ
  set r : ℝ → ℝ := fun ϕ => (π - ϕ) / ϕ.sin with hrdef
  obtain ⟨ϕ, ⟨hϕ, hrρ⟩, H⟩ := Real.LambertW.existsUnique_mem_Ioo_pi hρ
  change r ϕ * rexp (r ϕ * ϕ.cos) = ρ at hrρ
  have hsϕ : 0 < ϕ.sin := sin_pos_of_pos_of_lt_pi hϕ.1 hϕ.2
  have hr : 0 < r ϕ := div_pos (sub_pos.mpr hϕ.2) hsϕ
  have hrsin : r ϕ * ϕ.sin = π - ϕ := by rw [hrdef]; exact div_mul_cancel₀ _ hsϕ.ne'
  have himr : ∀ ψ : ℝ, (r ψ * cexp (ψ * I)).im = r ψ * Real.sin ψ := fun ψ => by
    have h : (↑(r ψ) * (↑(Real.cos ψ) + ↑(Real.sin ψ) * I) : ℂ)
        = ↑(r ψ * Real.cos ψ) + ↑(r ψ * Real.sin ψ) * I := by push_cast; ring
    rw [exp_ofReal_mul_I, h, add_im, ofReal_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  refine ⟨r ϕ * cexp (ϕ * I), ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [himr, exp_ofReal_mul_I, ofReal_cos, ofReal_sin,
      arg_mul_cos_add_sin_mul_I hr ⟨by grind [Real.pi_pos, hϕ.left], hϕ.right.le⟩,
      hrsin, add_sub_cancel]
  · calc (r ϕ * cexp (ϕ * I)) * cexp (r ϕ * cexp (ϕ * I))
        = (r ϕ * cexp (ϕ * I)) * (cexp (↑(r ϕ * ϕ.cos)) * cexp (↑(r ϕ * ϕ.sin) * I)) := by
          nth_rw 2 [exp_ofReal_mul_I]
          rw [mul_add, exp_add]
          push_cast
          ring_nf
      _ = (r ϕ * rexp (r ϕ * ϕ.cos)) * (cexp (ϕ * I) * cexp (↑(r ϕ * ϕ.sin) * I)) := by
          rw [ofReal_exp]
          ring
      _ = (r ϕ * rexp (r ϕ * ϕ.cos)) * cexp ((ϕ * I) + (↑(r ϕ * ϕ.sin) * I)) := by rw [exp_add]
      _ = (r ϕ * rexp (r ϕ * ϕ.cos)) * cexp ((ϕ + r ϕ * ϕ.sin) * I) := by
          push_cast
          ring_nf
      _ = ρ * cexp (π * I) := by
          rw [← ofReal_mul, hrρ, ← ofReal_mul, ← ofReal_add, hrsin, add_sub_cancel]
  · rw [himr, hrsin, gt_iff_lt, sub_pos]
    exact hϕ.right
  · intro w' ⟨hw'ϕ, hw'ρ, hw'im⟩
    have hw'arg_ne : w'.arg ≠ π := fun h => by grind [arg_eq_pi_iff]
    have hθ'2 : 0 < w'.arg + w'.im := by grw [hw'ϕ, pi_pos]
    have hw'arg0 : 0 < w'.arg := arg_pos_of_arg_add_im_pos hθ'2
    have hw'argπ : w'.arg < π := by grind
    have hw'₀ : w' ≠ 0 := fun nh =>
      (mul_ne_zero (ofReal_ne_zero.mpr hρ0.ne') (exp_ne_zero _)) (by rw [← hw'ρ, nh]; simp)
    have hw'r : ‖w'‖ = r (w'.arg) := by
      have h : ‖w'‖ * Real.sin w'.arg = π - w'.arg := by
        rw [norm_mul_sin_arg, ← hw'ϕ, eq_sub_iff_add_eq']
      rw [hrdef, eq_div_iff (sin_arg_ne_zero_of_arg_add_im_pos hw'₀ hw'arg_ne hθ'2)]
      linarith
    have hρ' : r (w'.arg) * rexp (r (w'.arg) * Real.cos w'.arg) = ρ := by
      have hc : ‖w' * cexp w'‖ = ‖ρ * cexp (π * I)‖ := congrArg norm hw'ρ
      rw [norm_mul, norm_exp, norm_mul, norm_exp, ← norm_mul_cos_arg, hw'r] at hc
      simpa [abs_of_pos hρ0] using hc
    calc w' = ‖w'‖ * cexp (w'.arg * I) := (norm_mul_exp_arg_mul_I w').symm
      _ = r (w'.arg) * cexp (w'.arg * I) := by rw [hw'r]
      _ = r ϕ * cexp (ϕ * I) := by rw [H w'.arg ⟨⟨hw'arg0, hw'argπ⟩, hρ'⟩]

private theorem LambertW.existsUnique_arg_add_im_eq (hθ1 : θ ≠ π) (hθ2 : θ ≠ -π) (hρ : 0 < ρ) :
    ∃! w : ℂ, w.arg + w.im = θ ∧ w * cexp w = ρ * cexp (θ * I) := by
  rcases lt_trichotomy θ 0 with hθ' | rfl | hθ'
  · obtain ⟨w, ⟨hw1, hw2⟩, H⟩ : ∃! w : ℂ, w.arg + w.im = -θ ∧ w * cexp w = ρ * cexp (↑(-θ) * I) :=
      existsUnique_arg_add_im_eq_of_pos (θ := -θ) (by grind) (by linarith) hρ
    refine ⟨conj w, ⟨?_, ?_⟩, ?_⟩
    · simp [arg_conj, show w.arg ≠ π by grind [arg_eq_pi_iff], ← neg_add, hw1]
    · rw [exp_conj, ← map_mul, hw2, map_mul, conj_ofReal,
        ← exp_conj, map_mul, conj_I, conj_ofReal, ofReal_neg, neg_mul_neg]
    · intro w' ⟨hw'ϕ, hw'ρ⟩
      have hw'ϕ1 : w'.arg ≠ π := by grind [arg_add_im_eq_pi_of_arg_eq_pi]
      specialize H (conj w') ⟨?_, ?_⟩
      · simp [arg_conj, hw'ϕ1, ← hw'ϕ, add_comm]
      · simp [← map_mul, hw'ρ]
        simp [← exp_conj, conj_ofReal, conj_I]
      rw [← H, conj_conj]
  · rw [ofReal_zero, zero_mul, exp_zero, mul_one]
    obtain ⟨x, hx, H⟩ := existsUnique_add_log_eq (Real.log ρ)
    refine ⟨x, ⟨?_, ?_⟩, ?_⟩
    · simp [arg_eq_zero_iff, hx.left.le]
    · apply Complex.ext
      · simp only [mul_re, ofReal_re, ofReal_im, exp_ofReal_im, mul_zero, sub_zero, exp_ofReal_re]
        rw [← Real.exp_log hρ, ← hx.right, Real.exp_add, Real.exp_log hx.left, mul_comm]
      · simp
    · intro x' ⟨hx'1, hx'2⟩
      have him : x'.im = 0 := by grind [arg_neg_iff]
      rw [Complex.ext (z := x') (w := x'.re) rfl him] at hx'2 ⊢
      replace hx'2 := congrArg re hx'2
      simp only [mul_re, ofReal_re, exp_ofReal_re, ofReal_im, exp_ofReal_im, mul_zero,
        sub_zero] at hx'2
      have : 0 < x'.re := by grind [arg_eq_zero_iff]
      replace hx'2 := congrArg Real.log hx'2
      rw [Real.log_mul this.ne' (Real.exp_ne_zero x'.re), Real.log_exp, add_comm] at hx'2
      specialize H x'.re ⟨this, hx'2⟩
      rw [← H]
  · exact existsUnique_arg_add_im_eq_of_pos hθ1 hθ' hρ

end Complex

end Solve

end LambertWAux

namespace Complex

open Real Set Filter Topology

open scoped ComplexConjugate

variable {α : Type*} {k : ℤ} {z w : ℂ}

section LambertWRangeDomain

section Definition

/-- TODO doc -/
def LambertW.branchCut (k : ℤ) : Set ℂ :=
  Iic (if k = 0 then -(rexp 1)⁻¹ else 0) ×ℂ {0}

-- /-- TODO doc -/
-- def LambertW.openBranchCut (k : ℤ) : Set ℂ :=
--   Iio (if k = 0 then -(rexp 1)⁻¹ else 0) ×ℂ {0}

/-- TODO doc -/
def LambertW.slitPlane (k : ℤ) : Set ℂ :=
  (branchCut k)ᶜ

-- /-- TODO doc, ref this? https://en.wikipedia.org/wiki/Quadratrix_of_Hippias -/
-- def LambertW.boundaryAux (k : ℤ) : Set ℂ :=
--   { w | w.arg + w.im = (2 * k + 1) * π }
  -- (fun t => ⟨-t * Real.cot t, t⟩) '' Ioo (k * π) ((k + 1) * π)

-- /-- TODO doc -/
-- def LambertW.upperBoundary (k : ℤ) : Set ℂ := match k with
--   | Int.ofNat (_ + 1) => LambertW.boundaryAux (2 * k)
--   | 0 => LambertW.boundaryAux 0 ∪ {-1}
--   | -1 => LambertW.branchCut 0 ∪ LambertW.boundaryAux (-1)
--   | Int.negSucc (_ + 1) => LambertW.boundaryAux (2 * k + 1)

-- /-- TODO doc -/
-- def LambertW.lowerBoundary (k : ℤ) : Set ℂ := match k with
--   | Int.ofNat (_ + 2) => LambertW.boundaryAux (2 * k - 2)
--   | 1 => LambertW.boundaryAux 0 ∪ {-1}
--   | 0 => LambertW.boundaryAux (-1)
--   | Int.negSucc _ => LambertW.boundaryAux (2 * k + 1)

/-- TODO doc -/
def LambertW.domain (k : ℤ) : Set ℂ :=
  if k = 0 then univ else {0}ᶜ

@[simp]
theorem LambertW.domain_zero : domain 0 = univ :=
  rfl

theorem LambertW.domain_of_ne_zero (hk : k ≠ 0) : domain k = {0}ᶜ :=
  ite_eq_right hk

/-- TODO doc -/
def LambertW.range (k : ℤ) : Set ℂ := match k with
  | 0 => {w | w.arg + w.im ∈ Ioc (-π) π} \ Iio (-1) ×ℂ {0}
  | -1 => {w | w.arg + w.im ∈ Ioc (-3 * π) (-π)} ∪ Iic (-1) ×ℂ {0}
  | _ => {w | w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π)}

/-- TODO doc -/
def LambertW.openRange (k : ℤ) : Set ℂ :=
  if k = 0 then {w | w.arg + w.im ∈ Ioo (-π) π} ∪ Ioo (-1) 0 ×ℂ {0} else
    {w | w.arg + w.im ∈ Ioo ((2 * k - 1) * π) ((2 * k + 1) * π)}

@[simp]
theorem LambertW.openRange_zero :
    openRange 0 = {w | w.arg + w.im ∈ Ioo (-π) π} ∪ Ioo (-1) 0 ×ℂ {0} :=
  rfl

theorem LambertW.openRange_of_ne_zero (hk : k ≠ 0) :
    openRange k = {w | w.arg + w.im ∈ Ioo ((2 * k - 1) * π) ((2 * k + 1) * π)} :=
  ite_eq_right hk

end Definition

theorem LambertW.mem_domain_of_ne_zero (hz : z ≠ 0) : z ∈ domain k :=
  em (k = 0) |>.elim (fun hk => hk ▸ trivial) (fun hk => domain_of_ne_zero hk ▸ hz)

theorem LambertW.mem_range_zero_iff :
    w ∈ range 0 ↔ w.arg + w.im ∈ Ioc (-π) π ∧ ¬(w.re < -1 ∧ w.im = 0) := by
  simp [range, mem_reProdIm]

theorem LambertW.mem_range_neg_one_iff :
    w ∈ range (-1) ↔ w.arg + w.im ∈ Ioc (-3 * π) (-π) ∨ (w.re ≤ -1 ∧ w.im = 0) := by
  simp [range, mem_reProdIm]

theorem LambertW.mem_range_iff_of_ne (hk : k ≠ 0) (hk' : k ≠ -1) :
    w ∈ range k ↔ w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π) := by
  simp [range]

theorem LambertW.zero_mem_range_zero : 0 ∈ range 0 := by
  simp [mem_range_zero_iff, pi_pos, pi_nonneg]

theorem LambertW.zero_notMem_range_neg_one : 0 ∉ range (-1) := by
  simp [range, mem_reProdIm]

theorem LambertW.zero_notMem_range (hk : k ≠ 0) : 0 ∉ range k := by
  by_cases hk' : k = -1
  · exact hk' ▸ zero_notMem_range_neg_one
  rw [mem_range_iff_of_ne hk hk', arg_zero, zero_im, add_zero]
  rcases (show k < -1 ∨ k > 0 by omega) with hk | hk
  · simpa using fun _ => mul_neg_of_neg_of_pos (mod_cast by omega) pi_pos
  · simp [mul_pos (show (0 : ℝ) < 2 * k - 1 from mod_cast by omega) pi_pos |>.not_gt]

theorem LambertW.ne_zero_of_mem_range (hk : k ≠ 0) (hz : z ∈ range k) : z ≠ 0 := fun nh =>
  False.elim <| zero_notMem_range hk <| nh ▸ hz

@[simp]
theorem LambertW.zero_mem_range_iff : 0 ∈ range k ↔ k = 0 := by
  grind [zero_notMem_range, zero_mem_range_zero]

@[simp]
theorem LambertW.neg_one_mem_range_neg_one : -1 ∈ range (-1) := by
  simp [mem_range_neg_one_iff]

@[simp]
theorem LambertW.neg_one_mem_range_zero : -1 ∈ range 0 := by
  simp [mem_range_zero_iff, pi_pos]

theorem LambertW.arg_of_mem (hw : w ∈ Iic (-1) ×ℂ {0}) : w.arg = π :=
  arg_eq_pi_iff.mpr ⟨hw.left.trans_lt neg_one_lt_zero, hw.right⟩

theorem LambertW.arg_add_im_of_mem (hw : w ∈ Iic (-1) ×ℂ {0}) : w.arg + w.im = π :=
  arg_add_im_eq_pi_of_arg_eq_pi (arg_of_mem hw)

theorem LambertW.mem_range_iff_of_mem (hw : w ∈ Iic (-1) ×ℂ {0}) :
    w ∈ range k ↔ k = -1 ∨ (k = 0 ∧ w.re = -1) := by
  simp only [mem_reProdIm, mem_Iic, mem_singleton_iff] at hw
  constructor
  · intro h
    rcases (show k = 0 ∨ k = -1 ∨ (k ≠ 0 ∧ k ≠ -1) by tauto) with rfl | rfl | ⟨hk, hk'⟩
    · refine Or.inr ⟨rfl, le_antisymm hw.left ?_⟩
      by_contra! nh
      exact mem_range_zero_iff.mp h |>.right ⟨nh, hw.right⟩
    · exact Or.inl rfl
    · rw [mem_range_iff_of_ne hk hk', arg_add_im_of_mem hw] at h
      simp [field] at h
      norm_cast at h
      omega
  · rintro (rfl | ⟨rfl, hre⟩)
    · exact mem_range_neg_one_iff.mpr (Or.inr ⟨hw.1, hw.2⟩)
    · apply mem_range_zero_iff.mpr
      grind [arg_add_im_of_mem hw, pi_pos]

theorem LambertW.mem_range_iff_of_notMem (hw : w ∉ Iic (-1) ×ℂ {0}) :
    w ∈ range k ↔ w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π) := by
  rcases (show k = 0 ∨ k = -1 ∨ (k ≠ 0 ∧ k ≠ -1) by tauto) with rfl | rfl | ⟨hk, hk'⟩
  · rw [mem_range_zero_iff]
    have : ¬(w.re < -1 ∧ w.im = 0) := fun ⟨hre, him⟩ => hw ⟨hre.le, him⟩
    simp [this]
  · rw [mem_range_neg_one_iff]
    have : ¬(w.re ≤ -1 ∧ w.im = 0) := hw
    simp [this]
    grind
  · exact mem_range_iff_of_ne hk hk'

theorem LambertW.mem_openRange_zero_iff :
    w ∈ openRange 0 ↔ w.arg + w.im ∈ Ioo (-π) π ∨ (w.re ∈ Ioo (-1) 0 ∧ w.im = 0) := by
  simp [openRange_zero, mem_reProdIm]

theorem LambertW.mem_openRange_iff_of_ne (hk : k ≠ 0) :
    w ∈ openRange k ↔ w.arg + w.im ∈ Ioo ((2 * (k : ℝ) - 1) * π) ((2 * (k : ℝ) + 1) * π) := by
  simp [openRange_of_ne_zero hk]

private theorem LambertW.arg_add_im_mem_Ioo_of_mem_range_zero_of_mul_exp_mem
    (hw : w ∈ range 0) (hz : w * cexp w ∈ Complex.slitPlane) :
    w.arg + w.im ∈ Ioo (-π) π := by
  refine ⟨hw.left.left, lt_of_le_of_ne hw.left.right
    fun nh => mem_slitPlane_iff_arg.mp hz |>.left ?_⟩
  have := arg_mul_exp_eq_of_mem (x := w) (i := 0)
    (fun nh => by simp [nh] at hz) (by simpa using hw.left)
  rwa [nh, Int.cast_zero, zero_mul, sub_zero] at this

private theorem LambertW.arg_add_im_eq_pi_of_mem_range_zero
    (hw1 : w ∈ range 0) (hz : w * cexp w ∈ Iio 0 ×ℂ {0}) :
    w.arg + w.im = π := by
  grind [mul_exp_mem_of_arg_add_im_eq (w := w) (i := 0) (by simpa using hw1.left)]

private theorem LambertW.im_pos_of_arg_add_im_eq_pi_of_mul_exp_mem
    (hw2 : w.arg + w.im = π) (hz : w * cexp w ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0}) :
    0 < w.im := by
  apply lt_of_le_of_ne <| arg_nonneg_iff.mp <| (arg_pos_of_arg_add_im_pos <| hw2 ▸ pi_pos).le
  intro nh
  rw [← nh, add_zero, arg_eq_pi_iff] at hw2
  simp only [mem_reProdIm, mem_Iio, mem_singleton_iff] at hz
  apply hz.left.not_ge
  simpa [nh.symm, exp_re] using neg_exp_one_inv_le_mul_exp

private theorem LambertW.mem_of_mem_range_zero_of_mul_exp_mem
    (hw1 : w ∈ range 0) (hw2 : w.arg + w.im = π) (hz : w * cexp w ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    w ∈ Ico (-1) 0 ×ℂ {0} := by
  have := im_eq_zero_of_arg_add_im_eq_pi_of_mul_exp_mem hw2 hz
  rw [this, add_zero, arg_eq_pi_iff] at hw2
  refine ⟨⟨?_, hw2.left⟩, this⟩
  simpa [hw2, mem_reProdIm] using hw1.right

private theorem LambertW.arg_add_im_mem_Ioo_of_mem_range_neg_one_of_mul_exp_notMem
    (hw : w ∈ range (-1)) (hz : w * cexp w ∉ Iio 0 ×ℂ {0}) :
    w.arg + w.im ∈ Ioo (-3 * π) (-π) := by
  replace hw : w.arg + w.im ∈ Ioc (-3 * π) (-π) := by
    apply mem_range_neg_one_iff.mp hw |>.resolve_right fun nh => hz ?_
    simp [mem_reProdIm, exp_re, exp_im, nh.right, mul_neg_iff, Real.exp_pos w.re, LT.lt.not_gt]
    grind
  refine ⟨hw.left, lt_of_le_of_ne hw.right fun nh => ?_⟩
  have := arg_mul_exp_eq_of_mem (x := w) (i := -1)
    (fun nh => by simp [nh, pi_pos.not_ge] at hw) (by simp [nh, field]; norm_num)
  rw [nh] at this
  conv_rhs at this => ring_nf
  exact hz <| arg_eq_pi_iff.mp this

private theorem LambertW.arg_add_im_mem_Ioc_of_mem_range_neg_one_of_mul_exp_mem
    (hw : w ∈ range (-1)) (hz : w * cexp w ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0}) :
    w.arg + w.im ∈ Ioc (-3 * π) (-π) := mem_range_neg_one_iff.mp hw |>.resolve_right <| fun nh => by
  absurd hz.left
  simp [exp_im, exp_re, nh, neg_exp_one_inv_le_mul_exp]

private theorem LambertW.mem_Iic_of_mem_range_neg_one_of_mul_exp_mem
    (hw : w ∈ range (-1)) (hz : w * cexp w ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    w ∈ Iic (-1) ×ℂ {0} := mem_range_neg_one_iff.mp hw |>.resolve_left <| fun nh => by
  have := arg_mul_exp_eq_of_mem (x := w) (i := -1)
    (fun nh => by simp [mem_reProdIm, nh] at hz) (by grind)
  rw [arg_eq_pi_iff (z := w * cexp w) |>.mpr (by grind [mem_reProdIm.mp hz])] at this
  replace := im_eq_zero_of_arg_add_im_eq_neg_pi_of_mul_exp_mem (by grind) hz
  grind [arg_mem_Ioc]

private theorem LambertW.existsUnique_eq_pi_mul_exp_eq (hz : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0}) :
    ∃! w : ℂ, w.arg + w.im = π ∧ w * cexp w = z ∧ w.im > 0 := by
  set θ := π with hθ
  set ρ := ‖z‖
  have hρ : (rexp 1)⁻¹ < ‖z‖ := by
    rw [norm_eq_sqrt_sq_add_sq, hz.right, zero_pow (by omega), add_zero, sqrt_sq_eq_abs,
      abs_of_neg, lt_neg]
    · exact hz.left
    · apply hz.left.trans
      simp [exp_pos]
  have hz' : z = ρ * cexp (θ * I) := by
    rw [← norm_mul_exp_arg_mul_I z,
      arg_eq_pi_iff.mpr ⟨hz.left.trans (by simp [Real.exp_pos]), hz.right⟩]
  obtain ⟨w, ⟨hw, hwz⟩, H⟩ := existsUnique_arg_add_im_eq_pi hρ
  exact ⟨w, ⟨hw, hz' ▸ hwz⟩, fun w' ⟨hw', hw'z, hw'im⟩ =>
    H w' ⟨hw', by grind [norm_mul_exp_arg_mul_I], hw'im⟩⟩

private theorem LambertW.existsUnique_mem_Ico_exp_eq (hz : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    ∃! w : ℂ, w ∈ Ico (-1) 0 ×ℂ {0} ∧ w * cexp w = z := by
  obtain ⟨x, ⟨hx1, hx2⟩, H⟩ := existsUnique_mem_Ico_mul_exp_eq_of_mem_Ico hz.left
  refine ⟨x, ⟨by simpa [mem_reProdIm], ?_⟩, ?_⟩
  · simpa [Complex.ext_iff, exp_re, hx2] using hz.right.symm
  · intro w' ⟨hw'1, hw'2⟩
    apply Complex.ext (z := w') (w := x) (H w'.re ⟨hw'1.left, ?_⟩) hw'1.right
    simp [← hw'2, exp_re, mem_singleton_iff.mp <| mem_reProdIm.mp hw'1 |>.right]

private theorem LambertW.existsUnique_mem_Iic_exp_eq (hz : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    ∃! w : ℂ, w ∈ Iic (-1) ×ℂ {0} ∧ w * cexp w = z := by
  obtain ⟨x, ⟨hx1, hx2⟩, H⟩ := existsUnique_mem_Iic_mul_exp_eq_of_mem_Ico hz.left
  refine ⟨x, ⟨by simpa [mem_reProdIm], ?_⟩, ?_⟩
  · simpa [Complex.ext_iff, exp_re, hx2] using hz.right.symm
  · intro w' ⟨hw'1, hw'2⟩
    apply Complex.ext (z := w') (w := x) (H w'.re ⟨hw'1.left, ?_⟩) hw'1.right
    simp [← hw'2, exp_re, mem_singleton_iff.mp <| mem_reProdIm.mp hw'1 |>.right]

private theorem LambertW.existsUnique_eq_neg_pi_mul_exp_eq (hz : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0}) :
    ∃! w : ℂ, w.arg + w.im = -π ∧ w * cexp w = z := by
  obtain ⟨w, ⟨hw, hwz, hwim⟩, H⟩ := existsUnique_eq_pi_mul_exp_eq hz
  refine ⟨conj w, ⟨?_, ?_⟩, ?_⟩
  · rw [arg_conj, conj_im, ite_eq_right, ← hw, neg_add]
    grind
  · rw [exp_conj, ← map_mul, hwz, conj_eq_iff_im, hz.right]
  · intro w' ⟨hw', hw'z⟩
    rw [← H (conj w') ⟨?_, ?_, ?_⟩, conj_conj]
    · rw [arg_conj, conj_im, ite_eq_right, ← neg_add, hw', neg_neg]
      grind [pi_pos, arg_eq_pi_iff]
    · rw [exp_conj, ← map_mul, hw'z, conj_eq_iff_im, hz.right]
    · grind [arg_mem_Ioc w', pi_pos, conj_im]

private theorem LambertW.existsUnique_eq_mul_exp_eq
    (hk : k ≠ 0) (hk' : k ≠ -1) (hz : z ∈ Iio 0 ×ℂ {0}) :
    ∃! w : ℂ, w.arg + w.im = (2 * k + 1) * π ∧ w * cexp w = z := by
  set θ := (2 * k + 1) * π with hθ
  set ρ := ‖z‖
  have hz₀ : z ≠ 0 := fun nh => by simp [nh, mem_reProdIm] at hz
  have hargz : z.arg = π := arg_eq_pi_iff.mpr ⟨hz.left, hz.right⟩
  have hθz : cexp (θ * I) = cexp (z.arg * I) := by
    rw [hθ, hargz, ofReal_mul, ofReal_add, add_mul, add_mul, add_comm, ofReal_mul, ofReal_intCast,
      ofReal_ofNat, mul_comm 2, mul_assoc (k * 2 : ℂ), mul_assoc (k : ℂ), ← mul_assoc 2,
      exp_periodic.int_mul k, ofReal_one, one_mul]
  have hz' : z = ρ * cexp (θ * I) := by rw [← norm_mul_exp_arg_mul_I z, hθz]
  have hθ1 : θ ≠ π := by
    rcases (show k ≤ -2 ∨ k ≥ 1 by omega) with hk | hk <;> [apply ne_of_lt; apply ne_of_gt]
      <;> grw [hθ, hk] <;> grind [pi_pos]
  have hθ2 : θ ≠ -π := by
    rcases (show k ≤ -2 ∨ k ≥ 1 by omega) with hk | hk <;> [apply ne_of_lt; apply ne_of_gt]
      <;> grw [hθ, hk] <;> grind [pi_pos]
  obtain ⟨w, ⟨hw, hwz⟩, H⟩ := existsUnique_arg_add_im_eq hθ1 hθ2 <| norm_pos_iff.mpr hz₀
  exact ⟨w, ⟨hw, hz' ▸ hwz⟩, fun w' ⟨hw', hw'z⟩ => H w' ⟨hw', by grind [norm_mul_exp_arg_mul_I]⟩⟩

private theorem LambertW.existsUnique_mem_Ioo_mul_exp_eq (k : ℤ) (hz : z ∈ Complex.slitPlane) :
    ∃! w : ℂ, w.arg + w.im ∈ Ioo ((2 * k - 1) * π) ((2 * k + 1) * π) ∧ w * cexp w = z := by
  set θ := z.arg + k * (2 * π) with hθ
  set ρ := ‖z‖
  have hθz : cexp (θ * I) = cexp (z.arg * I) := by
    rw [hθ, ofReal_add, add_mul, ofReal_mul, ofReal_intCast, ofReal_mul, ofReal_ofNat,
      mul_assoc, exp_periodic.int_mul k]
  have hz' : z = ρ * cexp (θ * I) := by rw [← norm_mul_exp_arg_mul_I z, hθz]
  have hθ' : z.arg ∈ Ioo (-π) π :=
    ⟨arg_mem_Ioc z |>.left, lt_of_le_of_ne (arg_mem_Ioc z |>.right) <| slitPlane_arg_ne_pi hz⟩
  have hθ1 : θ ≠ π := by
    rcases (show k ≤ 0 ∨ k ≥ 1 by omega) with hk | hk <;> [apply ne_of_lt; apply ne_of_gt]
      <;> grw [hθ, hk] <;> grind
  have hθ2 : θ ≠ -π := by
    rcases (show k ≤ -1 ∨ k ≥ 0 by omega) with hk | hk <;> [apply ne_of_lt; apply ne_of_gt]
      <;> grw [hθ, hk] <;> grind
  obtain ⟨w, ⟨hw, hwz⟩, H⟩ := existsUnique_arg_add_im_eq hθ1 hθ2
    (norm_pos_iff.mpr <| slitPlane_ne_zero hz)
  refine ⟨w, by grind, fun w' ⟨hw', hw'z⟩ => H w' ⟨?_, ?_⟩⟩
  · grind [arg_mul_exp_eq_of_mem (by grind [slitPlane_ne_zero]) ⟨hw'.left, hw'.right.le⟩]
  · grind [norm_mul_exp_arg_mul_I]

theorem LambertW.image_mul_exp_range_zero : (fun w => w * cexp w) '' range 0 = univ := by
  refine eq_univ_iff_forall.mpr fun z => ?_
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  by_cases hz' : z ∈ Iio 0 ×ℂ {0}
  case neg =>
    replace hz : z ∈ Complex.slitPlane := by
      simp [Complex.ext_iff, mem_reProdIm, mem_slitPlane_iff] at hz hz' ⊢
      grind
    obtain ⟨w, ⟨⟨hwl, hwr⟩, hwz⟩, -⟩ := existsUnique_mem_Ioo_mul_exp_eq 0 hz
    simp only [Int.cast_zero, mul_zero, zero_sub, neg_mul, one_mul, zero_add,
      mem_image] at hwl hwr ⊢
    have hw' : w ∉ Iio (-1) ×ℂ {0} := by
      simp only [mem_reProdIm, mem_Iio, mem_singleton_iff, not_and]
      rintro hre him
      grind [arg_eq_pi_iff.mpr ⟨by linarith, him⟩]
    use w, ⟨⟨hwl, hwr.le⟩, hw'⟩, hwz
  rcases lt_or_ge z.re (-(rexp 1)⁻¹) with hz'' | hz''
  · replace hz'' : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, ⟨hwl, hwz, hwr⟩, -⟩ := existsUnique_eq_pi_mul_exp_eq hz''
    simp only [mem_image, mem_range_zero_iff, mem_Ioc, not_and]
    use w, ⟨⟨by rw [hwl]; linarith [pi_pos], hwl.le⟩, by simp [hwr.ne']⟩, hwz
  · replace hz'' : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, ⟨hw, hwz⟩, -⟩ := existsUnique_mem_Ico_exp_eq hz''
    simp [mem_reProdIm] at hw
    have hw' : w.arg + w.im = π :=
      arg_add_im_eq_pi_of_arg_eq_pi <| arg_eq_pi_iff.mpr ⟨hw.left.right, hw.right⟩
    simp only [mem_image, mem_range_zero_iff, mem_Ioc, not_and]
    use w, ⟨⟨by linarith [pi_pos], hw'.le⟩, by simp [hw.left.left.not_gt]⟩, hwz

theorem LambertW.image_mul_exp_range_neg_one : (fun w => w * cexp w) '' range (-1) = {0}ᶜ := by
  refine eq_of_subset_of_subset ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    simp only [mem_compl_iff, mem_singleton_iff, mul_eq_zero, exp_ne_zero, or_false]
    rintro rfl
    simp at hw
  intro z hz
  by_cases hz' : z ∈ Iio 0 ×ℂ {0}
  case neg =>
    replace hz : z ∈ Complex.slitPlane := by
      simp [Complex.ext_iff, mem_reProdIm, mem_slitPlane_iff] at hz hz' ⊢
      grind
    obtain ⟨w, ⟨⟨hwl, hwr⟩, hwz⟩, -⟩ := existsUnique_mem_Ioo_mul_exp_eq (-1) hz
    simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, mul_neg, mul_one, mem_image,
      mem_range_neg_one_iff, neg_mul, mem_Ioc] at hwl hwr ⊢
    use w, Or.inl ⟨by grind, by grind⟩, hwz
  rcases le_or_gt (-(rexp 1)⁻¹) z.re with hz'' | hz''
  · replace hz : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, ⟨hw, hwz⟩, -⟩ := existsUnique_mem_Iic_exp_eq hz
    simp only [Int.reduceNeg, mem_image, mem_range_neg_one_iff, neg_mul, mem_Ioc]
    simp only [mem_reProdIm, mem_singleton_iff] at hw
    use w, Or.inr hw, hwz
  · replace hz : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, ⟨hw, hwz⟩, -⟩ := existsUnique_eq_neg_pi_mul_exp_eq hz
    simp only [Int.reduceNeg, mem_image, mem_range_neg_one_iff, neg_mul, mem_Ioc]
    use w, Or.inl ⟨by grind [pi_pos], hw.le⟩, hwz

theorem LambertW.image_mul_exp_range_of_ne_zero (hk : k ≠ 0) (hk' : k ≠ -1) :
    (fun w => w * cexp w) '' range k = {0}ᶜ := by
  refine eq_of_subset_of_subset ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    simp only [mem_compl_iff, mem_singleton_iff, mul_eq_zero, exp_ne_zero, or_false]
    rintro rfl
    simp_all
  intro z hz
  suffices ∃ w : ℂ, w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π) ∧ w * cexp w = z by
    obtain ⟨w, hw, hwz⟩ := this
    simp only [mem_image, mem_range_iff_of_ne hk hk']
    use w
  by_cases hz' : z ∈ Iio 0 ×ℂ {0}
  · obtain ⟨w, ⟨hw, hwz⟩, -⟩ := existsUnique_eq_mul_exp_eq hk hk' hz'
    use w, ⟨by grind [pi_pos], hw.le⟩, hwz
  · replace hz : z ∈ Complex.slitPlane := by
      simp [Complex.ext_iff, mem_reProdIm, mem_slitPlane_iff] at hz hz' ⊢
      grind
    obtain ⟨w, ⟨⟨hwl, hwr⟩, hwz⟩, -⟩ := existsUnique_mem_Ioo_mul_exp_eq k hz
    use w, ⟨hwl, hwr.le⟩, hwz

theorem LambertW.image_mul_exp_range :
    (fun w => w * cexp w) '' range k = domain k := by
  by_cases hk : k = 0
  · rw [hk, image_mul_exp_range_zero, domain_zero]
  by_cases hk' : k = -1
  · rw [hk', image_mul_exp_range_neg_one, domain_of_ne_zero (by simp)]
  · rw [image_mul_exp_range_of_ne_zero hk hk', domain_of_ne_zero hk]

theorem LambertW.mapsTo_mul_exp_range :
    MapsTo (fun w => w * cexp w) (range k) (domain k) := by
  simpa only [← image_mul_exp_range] using mapsTo_image _ _

theorem LambertW.mapsTo_mul_exp_range_zero :
    MapsTo (fun w => w * cexp w) (range 0) univ := by
  simpa only [← domain_zero] using mapsTo_mul_exp_range

theorem LambertW.mapsTo_mul_exp_range_of_ne_zero (hk : k ≠ 0) :
    MapsTo (fun w => w * cexp w) (range k) {0}ᶜ := by
  simpa only [← domain_of_ne_zero hk] using mapsTo_mul_exp_range

private theorem LambertW.injOn_mul_exp_range_zero :
    InjOn (fun w => w * cexp w) (range 0) := by
  intro w₁ hw₁ w₂ hw₂ (h : w₁ * cexp w₁ = w₂ * cexp w₂)
  rw [mem_range_zero_iff] at hw₁ hw₂
  set z := w₁ * cexp w₁ with hz₁
  rename z = w₂ * cexp w₂ => hz₂
  by_cases hz : z = 0
  · simp_all
  by_cases hz' : z ∈ Iio 0 ×ℂ {0}
  case neg =>
    replace hz : z ∈ Complex.slitPlane := by
      simp [Complex.ext_iff, mem_reProdIm, mem_slitPlane_iff] at hz hz' ⊢
      grind
    obtain ⟨w, -, hw⟩ := existsUnique_mem_Ioo_mul_exp_eq 0 hz
    simp only [Int.cast_zero, mul_zero, zero_sub, neg_mul, one_mul, zero_add] at hw
    rw [hw w₁ ⟨arg_add_im_mem_Ioo_of_mem_range_zero_of_mul_exp_mem hw₁ hz, hz₁.symm⟩,
      hw w₂ ⟨arg_add_im_mem_Ioo_of_mem_range_zero_of_mul_exp_mem hw₂ (hz₂ ▸ hz), hz₂.symm⟩]
  have hw₁' : w₁.arg + w₁.im = π := arg_add_im_eq_pi_of_mem_range_zero hw₁ hz'
  have hw₂' : w₂.arg + w₂.im = π := by grind [mul_exp_mem_of_arg_add_im_eq (w := w₂) (i := 0)]
  rcases lt_or_ge z.re (-(rexp 1)⁻¹) with hz'' | hz''
  · replace hz : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, -, hw⟩ := existsUnique_eq_pi_mul_exp_eq hz
    rw [hw w₁ ⟨hw₁', hz₁.symm, im_pos_of_arg_add_im_eq_pi_of_mul_exp_mem hw₁' hz⟩,
      hw w₂ ⟨hw₂', hz₂.symm, im_pos_of_arg_add_im_eq_pi_of_mul_exp_mem hw₂' (hz₂ ▸ hz)⟩]
  · replace hz : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, -, hw⟩ := existsUnique_mem_Ico_exp_eq hz
    rw [hw w₁ ⟨mem_of_mem_range_zero_of_mul_exp_mem hw₁ hw₁' hz, hz₁.symm⟩,
      hw w₂ ⟨mem_of_mem_range_zero_of_mul_exp_mem hw₂ hw₂' (hz₂ ▸ hz), hz₂.symm⟩]

private theorem LambertW.injOn_mul_exp_range_neg_one :
    InjOn (fun w => w * cexp w) (range (-1)) := by
  intro w₁ hw₁ w₂ hw₂ (h : w₁ * cexp w₁ = w₂ * cexp w₂)
  set z := w₁ * cexp w₁ with hz₁
  rename z = w₂ * cexp w₂ => hz₂
  by_cases hz : z = 0
  · simp_all
  by_cases hz' : z ∈ Iio 0 ×ℂ {0}
  case neg =>
    replace hz : z ∈ Complex.slitPlane := by
      simp [Complex.ext_iff, mem_reProdIm, mem_slitPlane_iff] at hz hz' ⊢
      grind
    obtain ⟨w, -, hw⟩ := existsUnique_mem_Ioo_mul_exp_eq (-1) hz
    have := arg_add_im_mem_Ioo_of_mem_range_neg_one_of_mul_exp_notMem hw₁ hz'
    have := arg_add_im_mem_Ioo_of_mem_range_neg_one_of_mul_exp_notMem hw₂ (hz₂ ▸ hz')
    rw [hw w₁ ⟨by grind, hz₁.symm⟩, hw w₂ ⟨by grind, hz₂.symm⟩]
  rcases lt_or_ge z.re (-(rexp 1)⁻¹) with hz'' | hz''
  · replace hz : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, -, hw⟩ := existsUnique_eq_neg_pi_mul_exp_eq hz
    have := arg_add_im_mem_Ioc_of_mem_range_neg_one_of_mul_exp_mem hw₁ hz
    have := arg_add_im_mem_Ioc_of_mem_range_neg_one_of_mul_exp_mem hw₂ (hz₂ ▸ hz)
    rw [hw w₁ ⟨by grind [mul_exp_mem_of_arg_add_im_eq (w := w₁) (i := -1)], hz₁.symm⟩,
      hw w₂ ⟨by grind [mul_exp_mem_of_arg_add_im_eq (w := w₂) (i := -1)], hz₂.symm⟩]
  · replace hz : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0} := by
      simp only [mem_reProdIm, mem_Iio, mem_singleton_iff, mem_Ico] at hz' ⊢
      tauto
    obtain ⟨w, -, hw⟩ := existsUnique_mem_Iic_exp_eq hz
    rw [hw w₁ ⟨mem_Iic_of_mem_range_neg_one_of_mul_exp_mem hw₁ hz, hz₁.symm⟩,
      hw w₂ ⟨mem_Iic_of_mem_range_neg_one_of_mul_exp_mem hw₂ (hz₂ ▸ hz), hz₂.symm⟩]

private theorem LambertW.injOn_mul_exp_range_of_ne (hk : k ≠ 0) (hk' : k ≠ -1) :
    InjOn (fun w => w * cexp w) (range k) := by
  intro w₁ hw₁ w₂ hw₂ (h : w₁ * cexp w₁ = w₂ * cexp w₂)
  rw [mem_range_iff_of_ne hk hk'] at hw₁ hw₂
  have hw₁' : w₁ ≠ 0 := fun nh => by
    simp [nh, mul_neg_iff, pi_pos, pi_nonneg.not_gt] at hw₁
    norm_cast at hw₁
    omega
  have hw₂' : w₂ ≠ 0 := fun nh => by simp_all
  have hw₁w₂ : w₁.arg + w₁.im = w₂.arg + w₂.im := arg_add_im_eq_of_mul_exp_eq hw₁' hw₂' h hw₁ hw₂
  by_cases h_eq : w₁.arg + w₁.im = (2 * k + 1) * π
  · clear hw₁ hw₂
    have hz : w₁ * cexp w₁ ∈ Iio 0 ×ℂ {0} := arg_eq_pi_iff.mp <| by
      rw [mul_exp_eq_of_arg_add_im_eq hw₁' h_eq, ← ofReal_neg,
        arg_ofReal_of_neg <| neg_neg_iff_pos.mpr <| Real.exp_pos _]
    obtain ⟨w, -, hw⟩ := existsUnique_eq_mul_exp_eq hk hk' (z := w₁ * cexp w₁) hz
    rw [hw w₁ ⟨h_eq, rfl⟩, hw w₂ ⟨hw₁w₂ ▸ h_eq, h.symm⟩]
  · have hz : w₁ * cexp w₁ ∈ Complex.slitPlane := by
      apply mem_slitPlane_iff_arg.mpr ⟨?_, by simp [hw₁']⟩
      grind [arg_mul_exp_eq_of_mem hw₁' hw₁]
    obtain ⟨w, -, hw⟩ := existsUnique_mem_Ioo_mul_exp_eq k (z := w₁ * cexp w₁) hz
    rw [hw w₁ ⟨⟨hw₁.left, lt_of_le_of_ne hw₁.right h_eq⟩, rfl⟩,
      hw w₂ ⟨⟨hw₂.left, lt_of_le_of_ne hw₂.right (hw₁w₂ ▸ h_eq)⟩, h.symm⟩]

theorem LambertW.injOn_mul_exp_range :
    InjOn (fun w => w * cexp w) (range k) := by
  rcases (show k = 0 ∨ k = -1 ∨ (k ≠ 0 ∧ k ≠ -1) by tauto) with rfl | rfl | ⟨hk, hk'⟩
  · exact injOn_mul_exp_range_zero
  · exact injOn_mul_exp_range_neg_one
  · exact injOn_mul_exp_range_of_ne hk hk'

theorem LambertW.surjOn_mul_exp_range :
    SurjOn (fun w => w * cexp w) (range k) (domain k) := by
  simpa only [← image_mul_exp_range] using surjOn_image _ _

theorem LambertW.bijOn_mul_exp_range_domain :
    BijOn (fun w => w * cexp w) (range k) (domain k) :=
  ⟨mapsTo_mul_exp_range, injOn_mul_exp_range, surjOn_mul_exp_range⟩

theorem LambertW.iUnion_range : ⋃ k, range k = univ := by
  refine eq_univ_iff_forall.mpr fun w => mem_iUnion.mpr ?_
  by_cases hw : w ∈ Iic (-1) ×ℂ {0}
  · use -1, Or.inr hw
  · obtain ⟨k, hk, -⟩ : ∃! k : ℤ, w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π) :=
      Real.existsUnique_mem_Ioc (w.arg + w.im)
    use k, mem_range_iff_of_notMem hw |>.mpr hk

theorem LambertW.neg_one_notMem_range_of_ne (hk : k ≠ 0) (hk' : k ≠ -1) : -1 ∉ range k := by
  simp [mem_range_iff_of_ne hk hk', field]
  norm_cast
  omega

theorem LambertW.eq_of_mem_range_of_mem_range {i j : ℤ} (hi : w ∈ range i) (hj : w ∈ range j)
    (hw : w ≠ -1) : i = j := by
  by_cases hw' : w ∈ Iic (-1) ×ℂ {0}
  · have hre : w.re ≠ -1 := fun hre => hw (Complex.ext hre (by simpa using hw'.right))
    grind [mem_range_iff_of_mem hw']
  · obtain ⟨k, -, hk⟩ := Real.existsUnique_mem_Ioc (w.arg + w.im)
    grind [mem_range_iff_of_notMem hw' |>.mp hi, mem_range_iff_of_notMem hw' |>.mp hj]

theorem LambertW.existsUnique_mem_range_of_ne_neg_one (hw : w ≠ -1) :
    ∃! k : ℤ, w ∈ range k := by
  obtain ⟨k, hk⟩ := mem_iUnion.mp <| eq_univ_iff_forall.mp iUnion_range w
  exact ⟨k, hk, fun k' hk' => eq_of_mem_range_of_mem_range hk' hk hw⟩

--  TODO
-- theorem LambertW.openRange_subset_range : openRange k ⊆ range k := by
--   grind [belowBondary_of_strictBelowBondary, openRange, range]

-- theorem LambertW.slitPlane_subset_domain : slitPlane k ⊆ domain k := by
--   unfold slitPlane domain
--   split_ifs with hk <;> simp [branchCut, hk, mem_reProdIm]

-- theorem LambertW.interior_range : interior (range k) = openRange k := by
--   sorry

end LambertWRangeDomain

section LambertW

open LambertW

/-- TODO doc -/
@[pp_nodot]
def lambertW (k : ℤ) : ℂ -> ℂ :=
  Function.invFunOn (fun w => w * cexp w) (LambertW.range k)

@[inherit_doc] scoped[ComplexLambertW] notation "W_ " => Complex.lambertW
recommended_spelling "lambertW" for "W_" in [lambertW, ComplexLambertW.«termW_»]

open scoped ComplexLambertW

/-- TODO doc -/
scoped[ComplexLambertW] notation "W₀" => W_ 0
recommended_spelling "lambertW_zero" for "W₀" in [ComplexLambertW.«termW₀»]

/-- TODO doc -/
scoped[ComplexLambertW] notation "W₋₁" => W_ (-1)
recommended_spelling "lambertW_neg_one" for "W₋₁" in [ComplexLambertW.«termW₋₁»]

theorem lambertW_mem_range_of_mem_domain
    (hz : z ∈ domain k) : W_ k z ∈ range k := by
  refine Function.invFunOn_mem ?_
  rwa [← mem_image, bijOn_mul_exp_range_domain.image_eq]

theorem lambertW_mul_exp_of_mem_range (hw : w ∈ range k) : W_ k (w * exp w) = w :=
  LambertW.bijOn_mul_exp_range_domain.invOn_invFunOn.left hw

theorem lambertW_mul_exp_lambertW_of_mem_domain (hz : z ∈ domain k) :
    W_ k z * cexp (W_ k z) = z := by
  apply Function.invFunOn_eq (f := fun w => w * exp w)
  rwa [← mem_image, bijOn_mul_exp_range_domain.image_eq]

@[simp]
theorem lambertW_zero_mul_exp_lambertW_zero : W₀ z * cexp (W₀ z) = z :=
  lambertW_mul_exp_lambertW_of_mem_domain trivial

theorem exists_eq_lambertW_of_eq_mul_exp (hw : z = w * cexp w) :
    ∃ k : ℤ, w = W_ k z ∧ z ∈ domain k := by
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := eq_univ_iff_forall.mp iUnion_range w
  refine ⟨k, hw ▸ lambertW_mul_exp_of_mem_range hk |>.symm, ?_⟩
  by_cases hz : z = 0
  · rw [hz] at hw ⊢
    simp at hw
    simp [hw, zero_mem_range_iff] at hk
    simp [hk]
  by_cases hk : k = 0
  · simp [hk]
  · simpa [domain_of_ne_zero hk]

theorem eq_mul_exp_iff_exists_eq_lambertW :
    z = w * cexp w ↔ ∃ k : ℤ, w = W_ k z ∧ z ∈ domain k := by
  refine ⟨exists_eq_lambertW_of_eq_mul_exp, fun ⟨k, hk, hz⟩ => ?_⟩
  rw [hk, lambertW_mul_exp_lambertW_of_mem_domain hz]

theorem existsUnique_eq_lambertW_of_ne_neg_one
    (hw : z = w * cexp w) (hw' : w ≠ -1) : ∃! k : ℤ, w = W_ k z ∧ z ∈ domain k := by
  obtain ⟨k, hk, Hk⟩ := existsUnique_mem_range_of_ne_neg_one hw'
  refine ⟨k, ⟨hw ▸ lambertW_mul_exp_of_mem_range hk |>.symm, ?_⟩,
    fun k' hk' => Hk k' <| hk'.1 ▸ lambertW_mem_range_of_mem_domain hk'.2⟩
  by_cases hk₀ : k = 0
  · simp [hk₀]
  · apply mem_domain_of_ne_zero fun hz => ne_zero_of_mem_range hk₀ hk ?_
    simp_all

section TODO
-- /-- **TODO** doc -/
-- theorem conj_lambertW_eq_lambertW_neg_conj (hz : z ∈ LambertW.slitPlane k) :
--     conj (W_ k z) = W_ (-k) (conj z) := by
--   sorry

-- theorem LambertW.isOpen_domain : IsOpen (domain k) := by
--   change (if _ then _ else _ : Set ℂ) ∈ {y | IsOpen y}
--   simp [ite_mem]

-- theorem LambertW.isClosed_branchCut : IsClosed (branchCut k) :=
--   isClosed_Iic.reProdIm isClosed_singleton

-- theorem LambertW.isOpen_slitPlane : IsOpen (slitPlane k) :=
--   isClosed_branchCut.isOpen_compl

-- private theorem LambertW.isOpen_openRange_zero : IsOpen (openRange 0) := by
--   suffices openRange 0 =
--       Complex.slitPlane ∩ (fun w => w.arg + w.im) ⁻¹' Ioo (-π) π ∪ Metric.ball 0 1 by
--     simpa only [this] using
--       continuousOn_arg_add_im.isOpen_inter_preimage Complex.isOpen_slitPlane isOpen_Ioo |>.union
--         Metric.isOpen_ball
--   rw [openRange_zero]
--   ext w
--   constructor
--   · rintro (hidx | ⟨hre, him⟩)
--     · by_cases hs : w ∈ Complex.slitPlane
--       · exact Or.inl ⟨hs, hidx⟩
--       rw [Complex.mem_slitPlane_iff, not_or, not_not, not_lt] at hs
--       obtain ⟨hre, him⟩ := hs
--       rcases lt_or_eq_of_le hre with hre | hre
--       · exact False.elim <| lt_irrefl π <|
--           arg_add_im_eq_pi_of_arg_eq_pi (arg_eq_pi_iff.mpr ⟨hre, him⟩) ▸ hidx.right
--       · exact Or.inr <| (Complex.ext (w := 0) hre him) ▸ Metric.mem_ball_self zero_lt_one
--     · rw [mem_preimage, mem_singleton_iff] at him
--       refine Or.inr <| mem_ball_zero_iff.mpr ?_
--       rw [Complex.ext (z := w) (w := w.re) rfl him, norm_real, norm_eq_abs, abs_of_neg hre.right]
--       linarith [hre.left]
--   rintro (⟨-, hidx⟩ | hb)
--   · exact Or.inl hidx
--   rw [mem_ball_zero_iff] at hb
--   by_cases harg : w.arg = π
--   · obtain ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp harg
--     refine Or.inr ⟨⟨?_, hre⟩, him⟩
--     rw [Complex.ext (z := w) (w := w.re) rfl him, norm_real, norm_eq_abs, abs_of_neg hre] at hb
--     linarith
--   left
--   replace harg : w.arg ∈ Ioo (-π) π := ⟨neg_pi_lt_arg w, lt_of_le_of_ne (arg_le_pi w) harg⟩
--   rw [mem_ofPred, ← norm_mul_sin_arg]
--   generalize w.arg = x at *
--   rw [show x + ‖w‖ * x.sin = (1 - ‖w‖) * x + ‖w‖ * (x + x.sin) by ring]
--   exact (convex_Ioo (-π) π) harg (add_sin_mem_Ioo_of_mem_Ioo harg)
--     (sub_nonneg_of_le hb.le) (norm_nonneg w) (sub_add_cancel 1 ‖w‖)

-- private theorem LambertW.isOpen_openRange_of_ne (hk : k ≠ 0) : IsOpen (openRange k) := by
--   suffices openRange k = Complex.slitPlane ∩
--       (fun w => w.arg + w.im) ⁻¹' Ioo ((2 * k - 1) * π) ((2 * k + 1) * π) by
--     simpa only [this] using
--       continuousOn_arg_add_im.isOpen_inter_preimage Complex.isOpen_slitPlane isOpen_Ioo
--   rw [openRange_of_ne_zero hk]
--   ext w
--   refine ⟨fun hw => ⟨Classical.byContradiction fun nh => ?_, hw⟩, And.right⟩
--   rw [mem_slitPlane_iff_arg, not_and_or, not_not, not_not] at nh
--   rw [mem_ofPred] at hw
--   rcases nh with nh | nh
--   · rw [arg_eq_pi_iff.mp nh |>.right, add_zero] at hw
--     simp [nh, field, sub_lt_iff_lt_add, one_add_one_eq_two] at hw
--     norm_cast at hw
--     omega
--   · simp [nh, field, pi_pos, mul_neg_iff, pi_pos.not_gt] at hw
--     norm_cast at hw
--     omega

-- theorem LambertW.isOpen_openRange : IsOpen (openRange k) :=
--   em (k = 0) |>.elim (fun hk => hk ▸ isOpen_openRange_zero) isOpen_openRange_of_ne

-- theorem _root_.continuousAt_clambertW {z : ℂ} (h : z ∈ LambertW.slitPlane k) :
--     ContinuousAt (W_ k) z := by
--   sorry

-- theorem _root_.Filter.Tendsto.clambertW {l : Filter α} {f : α → ℂ} {x : ℂ} (h : Tendsto f l (𝓝 x))
--     (hx : x ∈ LambertW.slitPlane k) : Tendsto (fun t => W_ k (f t)) l (𝓝 <| W_ k x) :=
--   (continuousAt_clambertW hx).tendsto.comp h

-- variable [TopologicalSpace α]

-- nonrec theorem _root_.ContinuousAt.clambertW {f : α → ℂ} {x : α} (h₁ : ContinuousAt f x)
--     (h₂ : f x ∈ LambertW.slitPlane k) : ContinuousAt (fun t => W_ k (f t)) x :=
--   h₁.clambertW h₂

-- nonrec theorem _root_.ContinuousWithinAt.clambertW {f : α → ℂ} {s : Set α} {x : α}
--     (h₁ : ContinuousWithinAt f s x) (h₂ : f x ∈ LambertW.slitPlane k) :
--     ContinuousWithinAt (fun t => W_ k (f t)) s x :=
--   h₁.clambertW h₂

-- nonrec theorem _root_.ContinuousOn.clambertW {f : α → ℂ} {s : Set α} (h₁ : ContinuousOn f s)
--     (h₂ : ∀ x ∈ s, f x ∈ LambertW.slitPlane k) : ContinuousOn (fun t => W_ k (f t)) s :=
--   fun x hx => (h₁ x hx).clambertW (h₂ x hx)

-- nonrec theorem _root_.Continuous.clambertW {f : α → ℂ} (h₁ : Continuous f)
--     (h₂ : ∀ x, f x ∈ LambertW.slitPlane k) : Continuous fun t => W_ k (f t) :=
--   continuous_iff_continuousAt.mpr fun x => h₁.continuousAt.clambertW (h₂ x)

-- /-- TODO doc -/
-- def mulExpOpenPartialHomeomorph : OpenPartialHomeomorph ℂ ℂ where
--   toFun := fun w => w * cexp w
--   invFun := lambertW k
--   source := LambertW.openRange k
--   target := LambertW.slitPlane k
--   map_source' := by
--     sorry
--   map_target' z h := by
--     sorry
--   left_inv' _x hx := apply_mul_exp_of_mem_range <| openRange_subset_range hx
--   right_inv' _x hx := apply_mul_exp_apply_of_mem_domain <| slitPlane_subset_domain hx
--   open_source := isOpen_openRange
--   open_target := LambertW.isOpen_slitPlane
--   continuousOn_toFun := by fun_prop
--   continuousOn_invFun := continuousOn_id.clambertW fun _ => id
end TODO

end LambertW

end Complex

namespace Real

open Set

variable {x y : ℝ}

/-- TODO doc -/
def lambertWZero : ℝ -> ℝ := fun x => (Complex.lambertW 0 x).re

/-- TODO doc -/
def lambertWNegOne : ℝ -> ℝ := fun x => (Complex.lambertW (-1) x).re

@[inherit_doc] scoped[RealLambertW] notation "W₀" => Real.lambertWZero
recommended_spelling "lambertWZero" for "W₀" in [lambertWZero, RealLambertW.«termW₀»]

@[inherit_doc] scoped[RealLambertW] notation "W₋₁" => Real.lambertWNegOne
recommended_spelling "lambertWNegOne" for "W₋₁" in [lambertWNegOne, RealLambertW.«termW₋₁»]

open scoped RealLambertW

/-- TODO doc -/
scoped[OmegaConstant] notation "Ω" => W₀ 1
recommended_spelling "omegaConstant" for "Ω" in [OmegaConstant.«termΩ»]

open scoped OmegaConstant

theorem invOn_lambertWZero_mul_exp :
    InvOn W₀ (fun x => x * rexp x) (Ici (-1)) (Ici (-(rexp 1)⁻¹)) := by
  sorry

theorem invOn_mul_exp_lambertWZero :
    InvOn (fun x => x * rexp x) W₀ (Ici (-(rexp 1)⁻¹)) (Ici (-1)) := by
  sorry

theorem invOn_lambertWNegOne_mul_exp :
    InvOn W₋₁ (fun x => x * rexp x) (Iic (-1)) (Ico (-(rexp 1)⁻¹) 0) := by
  sorry

theorem invOn_mul_exp_lambertWNegOne :
    InvOn (fun x => x * rexp x) W₋₁ (Ico (-(rexp 1)⁻¹) 0) (Iic (-1)) := by
  sorry

theorem bijOn_lambertWZero : BijOn W₀ (Ici (-(rexp 1)⁻¹)) (Ici (-1)) := by
  sorry

theorem bijOn_lambertWNegOne : BijOn W₋₁ (Ico (-(rexp 1)⁻¹) 0) (Iic (-1)) := by
  sorry

theorem lambertWZero_mul_exp_of_le (hx : -1 ≤ x) : W₀ (x * rexp x) = x := by
  sorry

theorem lambertWZero_mul_exp_lambertWZero_of_le (hx : -(rexp 1)⁻¹ ≤ x) :
    W₀ x * rexp (W₀ x) = x := by
  sorry

theorem lambertWNegOne_mul_exp_of_le (hx : x ≤ -1) : W₋₁ (x * rexp x) = x := by
  sorry

theorem lambertWNegOne_mul_exp_lambertWNegOne_of_le (hx : x ∈ Ico (-(rexp 1)⁻¹) 0) :
    W₋₁ x * rexp (W₋₁ x) = x := by
  sorry

theorem strictMonoOn_lambertWZero : StrictMonoOn W₀ (Ici (-(rexp 1)⁻¹)) := by
  sorry

theorem strictAntiOn_lambetWNegOne : StrictAntiOn W₋₁ (Ico (-(rexp 1)⁻¹) 0) := by
  sorry

@[simp]
theorem lambertWZero_zero : W₀ 0 = 0 := by
  nth_rw 1 [show 0 = 0 * rexp 0 from zero_mul _ |>.symm, lambertWZero_mul_exp_of_le]
  norm_num

theorem lambertWZero_pos_of_pos (hx : 0 < x) : 0 < W₀ x := by
  have : -(rexp 1)⁻¹ ≤ 0 := by simpa using exp_nonneg 1
  exact lambertWZero_zero ▸ strictMonoOn_lambertWZero this (this.trans hx.le) hx

theorem lambertWZero_nonneg_of_nonneg (hx : 0 ≤ x) : 0 ≤ W₀ x := by
  have : -(rexp 1)⁻¹ ≤ 0 := by simpa using exp_nonneg 1
  exact lambertWZero_zero ▸ strictMonoOn_lambertWZero.monotoneOn this (this.trans hx) hx

theorem lambertWZero_neg_of_lt (hx : x < -(rexp 1)⁻¹) : W₀ x < 0 := by
  sorry

theorem lambertWZero_neg_of_neg (hx : x < 0) : W₀ x < 0 := by
  rcases lt_or_ge x (-(rexp 1)⁻¹) with hx' | hx'
  · exact lambertWZero_neg_of_lt hx'
  · exact lambertWZero_zero ▸ strictMonoOn_lambertWZero hx' (hx'.trans hx.le) hx

theorem lambertWZero_nonpos_of_nonpos (hx : x ≤ 0) : W₀ x ≤ 0 := by
  rcases lt_or_ge x (-(rexp 1)⁻¹) with hx' | hx'
  · exact lambertWZero_neg_of_lt hx' |>.le
  · exact lambertWZero_zero ▸ strictMonoOn_lambertWZero.monotoneOn hx' (hx'.trans hx) hx

theorem lambertWZero_ne_zero_of_ne_zero (hx : x ≠ 0) : W₀ x ≠ 0 := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · exact lambertWZero_neg_of_neg hx |>.ne
  · exact lambertWZero_pos_of_pos hx |>.ne'

theorem lambertWNegOne_neg_of_ne_zero (hx : x ≠ 0) : W₋₁ x < 0 := by
  sorry

open Qq Mathlib.Meta.Positivity in
/-- TODO doc -/
@[positivity Real.lambertWZero _]
meta def _root_.Mathlib.Meta.Positivity.evalLambertWZero :
    PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(W₀ $a) =>
    assertInstancesCommute
    match ← core zα pα a with
    | .positive pa => pure <| .positive q(lambertWZero_pos_of_pos $pa)
    | .nonnegative pa => pure <| .nonnegative q(lambertWZero_nonneg_of_nonneg $pa)
    | .nonzero pa => pure <| .nonzero q(lambertWZero_ne_zero_of_ne_zero $pa)
    | _ => pure .none
  | _, _, _ => throwError "not Real.lambertWZero"

theorem zero_lt_omegaConstant : 0 < Ω := by
  positivity

theorem omegaConstant_lt_one : Ω < 1 := by
  sorry

--  TODO
-- theorem lambertWZero_add_lambertWZero_of_pos (hx : 0 < x) (hy : 0 < y) :
--     W₀ x + W₀ y = W₀ (x * y / W₀ x + x * y / W₀ y) := by
--   sorry

end Real

#lint
