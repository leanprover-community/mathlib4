/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Limits and asymptotics of power functions at `+∞`

This file contains results about the limiting behaviour of power functions at `+∞`. For convenience
some results on asymptotics as `x → 0` (those which are not just continuity statements) are also
located here.
-/


noncomputable section

open Real Topology NNReal ENNReal Filter ComplexConjugate Finset Set

/-!
## Limits at `+∞`
-/


section Limits

open Real Filter

/-- The function `x ^ y` tends to `+∞` at `+∞` for any positive real `y`. -/
theorem tendsto_rpow_atTop {y : ℝ} (hy : 0 < y) : Tendsto (fun x : ℝ => x ^ y) atTop atTop := by
  rw [(atTop_basis' 0).tendsto_right_iff]
  intro b hb
  filter_upwards [eventually_ge_atTop 0, eventually_ge_atTop (b ^ (1 / y))] with x hx₀ hx
  simpa (disch := positivity) [Real.rpow_inv_le_iff_of_pos] using hx

/-- The function `x ^ (-y)` tends to `0` at `+∞` for any positive real `y`. -/
theorem tendsto_rpow_neg_atTop {y : ℝ} (hy : 0 < y) : Tendsto (fun x : ℝ => x ^ (-y)) atTop (𝓝 0) :=
  Tendsto.congr' (eventuallyEq_of_mem (Ioi_mem_atTop 0) fun _ hx => (rpow_neg (le_of_lt hx) y).symm)
    (tendsto_rpow_atTop hy).inv_tendsto_atTop

open Asymptotics in
lemma tendsto_rpow_atTop_of_base_lt_one (b : ℝ) (hb₀ : -1 < b) (hb₁ : b < 1) :
    Tendsto (b ^ · : ℝ → ℝ) atTop (𝓝 (0 : ℝ)) := by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  case inl => -- b < 0
    simp_rw [Real.rpow_def_of_nonpos hb.le, hb.ne, ite_false]
    rw [← isLittleO_const_iff (c := (1 : ℝ)) one_ne_zero, (one_mul (1 : ℝ)).symm]
    refine IsLittleO.mul_isBigO ?exp ?cos
    case exp =>
      rw [isLittleO_const_iff one_ne_zero]
      refine tendsto_exp_atBot.comp <| (tendsto_const_mul_atBot_of_neg ?_).mpr tendsto_id
      rw [← log_neg_eq_log, log_neg_iff (by linarith)]
      linarith
    case cos =>
      rw [isBigO_iff]
      exact ⟨1, Eventually.of_forall fun x => by simp [Real.abs_cos_le_one]⟩
  case inr.inl => -- b = 0
    refine Tendsto.mono_right ?_ (Iff.mpr pure_le_nhds_iff rfl)
    rw [tendsto_pure]
    filter_upwards [eventually_ne_atTop 0] with _ hx
    simp [hx]
  case inr.inr => -- b > 0
    simp_rw [Real.rpow_def_of_pos hb]
    refine tendsto_exp_atBot.comp <| (tendsto_const_mul_atBot_of_neg ?_).mpr tendsto_id
    exact (log_neg_iff hb).mpr hb₁

lemma tendsto_rpow_atBot_of_base_lt_one (b : ℝ) (hb₀ : 0 < b) (hb₁ : b < 1) :
    Tendsto (b ^ · : ℝ → ℝ) atBot atTop := by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
  refine tendsto_exp_atTop.comp <| (tendsto_const_mul_atTop_iff_neg <| tendsto_id (α := ℝ)).mpr ?_
  exact (log_neg_iff hb₀).mpr hb₁

lemma tendsto_rpow_atBot_of_base_gt_one (b : ℝ) (hb : 1 < b) :
    Tendsto (b ^ · : ℝ → ℝ) atBot (𝓝 0) := by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
  refine tendsto_exp_atBot.comp <| (tendsto_const_mul_atBot_of_pos ?_).mpr tendsto_id
  exact (log_pos_iff (by positivity)).mpr <| by aesop

@[deprecated (since := "2025-08-24")]
alias tendsto_rpow_atTop_of_base_gt_one := tendsto_rpow_atBot_of_base_gt_one

/-- The function `x ^ (a / (b * x + c))` tends to `1` at `+∞`, for any real numbers `a`, `b`, and
`c` such that `b` is nonzero. -/
theorem tendsto_rpow_div_mul_add (a b c : ℝ) (hb : 0 ≠ b) :
    Tendsto (fun x => x ^ (a / (b * x + c))) atTop (𝓝 1) := by
  refine
    Tendsto.congr' ?_
      ((tendsto_exp_nhds_zero_nhds_one.comp
            (by
              simpa only [mul_zero, pow_one] using
                (tendsto_const_nhds (x := a)).mul
                  (tendsto_div_pow_mul_exp_add_atTop b c 1 hb))).comp
        tendsto_log_atTop)
  apply eventuallyEq_of_mem (Ioi_mem_atTop (0 : ℝ))
  intro x hx
  simp only [Set.mem_Ioi, Function.comp_apply] at hx ⊢
  rw [exp_log hx, ← exp_log (rpow_pos_of_pos hx (a / (b * x + c))), log_rpow hx (a / (b * x + c))]
  field_simp

/-- The function `x ^ (1 / x)` tends to `1` at `+∞`. -/
theorem tendsto_rpow_div : Tendsto (fun x => x ^ ((1 : ℝ) / x)) atTop (𝓝 1) := by
  convert tendsto_rpow_div_mul_add (1 : ℝ) _ (0 : ℝ) zero_ne_one
  ring

/-- The function `x ^ (-1 / x)` tends to `1` at `+∞`. -/
theorem tendsto_rpow_neg_div : Tendsto (fun x => x ^ (-(1 : ℝ) / x)) atTop (𝓝 1) := by
  convert tendsto_rpow_div_mul_add (-(1 : ℝ)) _ (0 : ℝ) zero_ne_one
  ring

/-- The function `exp(x) / x ^ s` tends to `+∞` at `+∞`, for any real number `s`. -/
theorem tendsto_exp_div_rpow_atTop (s : ℝ) : Tendsto (fun x : ℝ => exp x / x ^ s) atTop atTop := by
  obtain ⟨n, hn⟩ := archimedean_iff_nat_lt.1 Real.instArchimedean s
  refine tendsto_atTop_mono' _ ?_ (tendsto_exp_div_pow_atTop n)
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 : ℝ)] with x hx₀ hx₁
  gcongr
  simpa using rpow_le_rpow_of_exponent_le hx₁ hn.le

/-- The function `exp (b * x) / x ^ s` tends to `+∞` at `+∞`, for any real `s` and `b > 0`. -/
theorem tendsto_exp_mul_div_rpow_atTop (s : ℝ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => exp (b * x) / x ^ s) atTop atTop := by
  refine ((tendsto_rpow_atTop hb).comp (tendsto_exp_div_rpow_atTop (s / b))).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx₀
  simp [Real.div_rpow, (exp_pos x).le, rpow_nonneg, ← Real.rpow_mul, ← exp_mul,
    mul_comm x, hb.ne', *]

/-- The function `x ^ s * exp (-b * x)` tends to `0` at `+∞`, for any real `s` and `b > 0`. -/
theorem tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s : ℝ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x ^ s * exp (-b * x)) atTop (𝓝 0) := by
  refine (tendsto_exp_mul_div_rpow_atTop s b hb).inv_tendsto_atTop.congr' ?_
  filter_upwards with x using by simp [exp_neg, inv_div, div_eq_mul_inv _ (exp _)]

nonrec theorem NNReal.tendsto_rpow_atTop {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ≥0 => x ^ y) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨c, hc⟩ := tendsto_atTop_atTop.mp (tendsto_rpow_atTop hy) b
  use c.toNNReal
  intro a ha
  exact mod_cast hc a (Real.toNNReal_le_iff_le_coe.mp ha)

theorem ENNReal.tendsto_rpow_at_top {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ≥0∞ => x ^ y) (𝓝 ⊤) (𝓝 ⊤) := by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro x
  obtain ⟨c, _, hc⟩ :=
    (atTop_basis_Ioi.tendsto_iff atTop_basis_Ioi).mp (NNReal.tendsto_rpow_atTop hy) x trivial
  have hc' : Set.Ioi ↑c ∈ 𝓝 (⊤ : ℝ≥0∞) := Ioi_mem_nhds ENNReal.coe_lt_top
  filter_upwards [hc'] with a ha
  by_cases ha' : a = ⊤
  · simp [ha', hy]
  lift a to ℝ≥0 using ha'
  simp only [Set.mem_Ioi, coe_lt_coe] at ha hc
  rw [← ENNReal.coe_rpow_of_nonneg _ hy.le]
  exact mod_cast hc a ha

end Limits

/-!
## Asymptotic results: `IsBigO`, `IsLittleO` and `IsTheta`
-/


namespace Complex

section

variable {α : Type*} {l : Filter α} {f g : α → ℂ}

open Asymptotics

theorem isTheta_exp_arg_mul_im (hl : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|) :
    (fun x => Real.exp (arg (f x) * im (g x))) =Θ[l] fun _ => (1 : ℝ) := by
  rcases hl with ⟨b, hb⟩
  refine Real.isTheta_exp_comp_one.2 ⟨π * b, ?_⟩
  rw [eventually_map] at hb ⊢
  refine hb.mono fun x hx => ?_
  rw [abs_mul]
  exact mul_le_mul (abs_arg_le_pi _) hx (abs_nonneg _) Real.pi_pos.le

theorem isBigO_cpow_rpow (hl : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|) :
    (fun x => f x ^ g x) =O[l] fun x => ‖f x‖ ^ (g x).re :=
  calc
    (fun x => f x ^ g x) =O[l]
        (show α → ℝ from fun x => ‖f x‖ ^ (g x).re / Real.exp (arg (f x) * im (g x))) :=
      isBigO_of_le _ fun _ => (norm_cpow_le _ _).trans (le_abs_self _)
    _ =Θ[l] (show α → ℝ from fun x => ‖f x‖ ^ (g x).re / (1 : ℝ)) :=
      ((isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl))
    _ =ᶠ[l] (show α → ℝ from fun x => ‖f x‖ ^ (g x).re) := by
      simp only [div_one, EventuallyEq.rfl]

theorem isTheta_cpow_rpow (hl_im : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|)
    (hl : ∀ᶠ x in l, f x = 0 → re (g x) = 0 → g x = 0) :
    (fun x => f x ^ g x) =Θ[l] fun x => ‖f x‖ ^ (g x).re :=
  calc
    (fun x => f x ^ g x) =Θ[l]
        (fun x => ‖f x‖ ^ (g x).re / Real.exp (arg (f x) * im (g x))) :=
      .of_norm_eventuallyEq <| hl.mono fun _ => norm_cpow_of_imp
    _ =Θ[l] fun x => ‖f x‖ ^ (g x).re / (1 : ℝ) :=
      (isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl_im)
    _ =ᶠ[l] (fun x => ‖f x‖ ^ (g x).re) := by
      simp only [div_one, EventuallyEq.rfl]

theorem isTheta_cpow_const_rpow {b : ℂ} (hl : b.re = 0 → b ≠ 0 → ∀ᶠ x in l, f x ≠ 0) :
    (fun x => f x ^ b) =Θ[l] fun x => ‖f x‖ ^ b.re :=
  isTheta_cpow_rpow isBoundedUnder_const <| by
    simpa only [eventually_imp_distrib_right, not_imp_not, Imp.swap (a := b.re = 0)] using hl

end

end Complex

open Real

namespace Asymptotics

variable {α : Type*} {r c : ℝ} {l : Filter α} {f g : α → ℝ}

theorem IsBigOWith.rpow (h : IsBigOWith c l f g) (hc : 0 ≤ c) (hr : 0 ≤ r) (hg : 0 ≤ᶠ[l] g) :
    IsBigOWith (c ^ r) l (fun x => f x ^ r) fun x => g x ^ r := by
  apply IsBigOWith.of_bound
  filter_upwards [hg, h.bound] with x hgx hx
  calc
    |f x ^ r| ≤ |f x| ^ r := abs_rpow_le_abs_rpow _ _
    _ ≤ (c * |g x|) ^ r := rpow_le_rpow (abs_nonneg _) hx hr
    _ = c ^ r * |g x ^ r| := by rw [mul_rpow hc (abs_nonneg _), abs_rpow_of_nonneg hgx]

theorem IsBigO.rpow (hr : 0 ≤ r) (hg : 0 ≤ᶠ[l] g) (h : f =O[l] g) :
    (fun x => f x ^ r) =O[l] fun x => g x ^ r :=
  let ⟨_, hc, h'⟩ := h.exists_nonneg
  (h'.rpow hc hr hg).isBigO

theorem IsTheta.rpow (hr : 0 ≤ r) (hf : 0 ≤ᶠ[l] f) (hg : 0 ≤ᶠ[l] g) (h : f =Θ[l] g) :
    (fun x => f x ^ r) =Θ[l] fun x => g x ^ r :=
  ⟨h.1.rpow hr hg, h.2.rpow hr hf⟩

theorem IsLittleO.rpow (hr : 0 < r) (hg : 0 ≤ᶠ[l] g) (h : f =o[l] g) :
    (fun x => f x ^ r) =o[l] fun x => g x ^ r := by
  refine .of_isBigOWith fun c hc ↦ ?_
  rw [← rpow_inv_rpow hc.le hr.ne']
  refine (h.forall_isBigOWith ?_).rpow ?_ ?_ hg <;> positivity

protected lemma IsBigO.sqrt (hfg : f =O[l] g) (hg : 0 ≤ᶠ[l] g) :
    (fun x ↦ √(f x)) =O[l] (fun x ↦ √(g x)) := by
  simpa [Real.sqrt_eq_rpow] using hfg.rpow one_half_pos.le hg

protected lemma IsLittleO.sqrt (hfg : f =o[l] g) (hg : 0 ≤ᶠ[l] g) :
    (fun x ↦ √(f x)) =o[l] (fun x ↦ √(g x)) := by
  simpa [Real.sqrt_eq_rpow] using hfg.rpow one_half_pos hg

protected lemma IsTheta.sqrt (hfg : f =Θ[l] g) (hf : 0 ≤ᶠ[l] f) (hg : 0 ≤ᶠ[l] g) :
    (Real.sqrt <| f ·) =Θ[l] (Real.sqrt <| g ·) :=
  ⟨hfg.1.sqrt hg, hfg.2.sqrt hf⟩

theorem isBigO_atTop_natCast_rpow_of_tendsto_div_rpow {𝕜 : Type*} [RCLike 𝕜] {g : ℕ → 𝕜}
    {a : 𝕜} {r : ℝ} (hlim : Tendsto (fun n ↦ g n / (n ^ r : ℝ)) atTop (𝓝 a)) :
    g =O[atTop] fun n ↦ (n : ℝ) ^ r := by
  refine (isBigO_of_div_tendsto_nhds ?_ ‖a‖ ?_).of_norm_left
  · filter_upwards [eventually_ne_atTop 0] with _ h
    simp [Real.rpow_eq_zero_iff_of_nonneg, h]
  · exact hlim.norm.congr fun n ↦ by simp [abs_of_nonneg, show 0 ≤ (n : ℝ) ^ r by positivity]

variable {E : Type*} [SeminormedRing E] (a b c : ℝ)

theorem IsBigO.mul_atTop_rpow_of_isBigO_rpow {f g : ℝ → E}
    (hf : f =O[atTop] fun t ↦ (t : ℝ) ^ a) (hg : g =O[atTop] fun t ↦ (t : ℝ) ^ b)
    (h : a + b ≤ c) :
    (f * g) =O[atTop] fun t ↦ (t : ℝ) ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

theorem IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow {f g : ℕ → E}
    (hf : f =O[atTop] fun n ↦ (n : ℝ) ^ a) (hg : g =O[atTop] fun n ↦ (n : ℝ) ^ b)
    (h : a + b ≤ c) :
    (f * g) =O[atTop] fun n ↦ (n : ℝ) ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  replace ht : 1 ≤ (t : ℝ) := Nat.one_le_cast.mpr ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

end Asymptotics

open Asymptotics

/-- `x ^ s = o(exp(b * x))` as `x → ∞` for any real `s` and positive `b`. -/
theorem isLittleO_rpow_exp_pos_mul_atTop (s : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => x ^ s) =o[atTop] fun x => exp (b * x) :=
  isLittleO_of_tendsto (fun _ h => absurd h (exp_pos _).ne') <| by
    simpa only [div_eq_mul_inv, exp_neg, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb

/-- `x ^ k = o(exp(b * x))` as `x → ∞` for any integer `k` and positive `b`. -/
theorem isLittleO_zpow_exp_pos_mul_atTop (k : ℤ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => x ^ k) =o[atTop] fun x => exp (b * x) := by
  simpa only [Real.rpow_intCast] using isLittleO_rpow_exp_pos_mul_atTop k hb

/-- `x ^ k = o(exp(b * x))` as `x → ∞` for any natural `k` and positive `b`. -/
theorem isLittleO_pow_exp_pos_mul_atTop (k : ℕ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => x ^ k) =o[atTop] fun x => exp (b * x) := by
  simpa using isLittleO_zpow_exp_pos_mul_atTop k hb

/-- `x ^ s = o(exp x)` as `x → ∞` for any real `s`. -/
theorem isLittleO_rpow_exp_atTop (s : ℝ) : (fun x : ℝ => x ^ s) =o[atTop] exp := by
  simpa only [one_mul] using isLittleO_rpow_exp_pos_mul_atTop s one_pos

/-- `exp (-a * x) = o(x ^ s)` as `x → ∞`, for any positive `a` and real `s`. -/
theorem isLittleO_exp_neg_mul_rpow_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IsLittleO atTop (fun x : ℝ => exp (-a * x)) fun x : ℝ => x ^ b := by
  apply isLittleO_of_tendsto'
  · refine (eventually_gt_atTop 0).mono fun t ht h => ?_
    rw [rpow_eq_zero_iff_of_nonneg ht.le] at h
    exact (ht.ne' h.1).elim
  · refine (tendsto_exp_mul_div_rpow_atTop (-b) a ha).inv_tendsto_atTop.congr' ?_
    refine (eventually_ge_atTop 0).mono fun t ht => ?_
    simp [field, Real.exp_neg, rpow_neg ht]

theorem isLittleO_log_rpow_atTop {r : ℝ} (hr : 0 < r) : log =o[atTop] fun x => x ^ r :=
  calc
    log =O[atTop] fun x => r * log x := isBigO_self_const_mul hr.ne' _ _
    _ =ᶠ[atTop] fun x => log (x ^ r) :=
      ((eventually_gt_atTop 0).mono fun _ hx => (log_rpow hx _).symm)
    _ =o[atTop] fun x => x ^ r := isLittleO_log_id_atTop.comp_tendsto (tendsto_rpow_atTop hr)

theorem isLittleO_log_rpow_rpow_atTop {s : ℝ} (r : ℝ) (hs : 0 < s) :
    (fun x => log x ^ r) =o[atTop] fun x => x ^ s :=
  let r' := max r 1
  have hr : 0 < r' := lt_max_iff.2 <| Or.inr one_pos
  have H : 0 < s / r' := div_pos hs hr
  calc
    (fun x => log x ^ r) =O[atTop] fun x => log x ^ r' :=
      .of_norm_eventuallyLE <| by
        filter_upwards [tendsto_log_atTop.eventually_ge_atTop 1] with x hx
        rw [Real.norm_of_nonneg (by positivity)]
        gcongr
        exacts [hx, le_max_left _ _]
    _ =o[atTop] fun x => (x ^ (s / r')) ^ r' :=
      ((isLittleO_log_rpow_atTop H).rpow hr <|
        (_root_.tendsto_rpow_atTop H).eventually <| eventually_ge_atTop 0)
    _ =ᶠ[atTop] fun x => x ^ s :=
      (eventually_ge_atTop 0).mono fun x hx ↦ by simp only [← rpow_mul hx, div_mul_cancel₀ _ hr.ne']

theorem isLittleO_abs_log_rpow_rpow_nhdsGT_zero {s : ℝ} (r : ℝ) (hs : s < 0) :
    (fun x => |log x| ^ r) =o[𝓝[>] 0] fun x => x ^ s :=
  ((isLittleO_log_rpow_rpow_atTop r (neg_pos.2 hs)).comp_tendsto tendsto_inv_nhdsGT_zero).congr'
    (mem_of_superset (Icc_mem_nhdsGT one_pos) fun x hx => by
      simp [abs_of_nonpos, log_nonpos hx.1 hx.2])
    (eventually_mem_nhdsWithin.mono fun x hx => by
      rw [Function.comp_apply, inv_rpow hx.out.le, rpow_neg hx.out.le, inv_inv])

@[deprecated (since := "2025-03-02")]
alias isLittleO_abs_log_rpow_rpow_nhds_zero := isLittleO_abs_log_rpow_rpow_nhdsGT_zero

theorem isLittleO_log_rpow_nhdsGT_zero {r : ℝ} (hr : r < 0) : log =o[𝓝[>] 0] fun x => x ^ r :=
  (isLittleO_abs_log_rpow_rpow_nhdsGT_zero 1 hr).neg_left.congr'
    (mem_of_superset (Icc_mem_nhdsGT one_pos) fun x hx => by
      simp [abs_of_nonpos (log_nonpos hx.1 hx.2)])
    .rfl

@[deprecated (since := "2025-03-02")]
alias isLittleO_log_rpow_nhds_zero := isLittleO_log_rpow_nhdsGT_zero

theorem tendsto_log_div_rpow_nhdsGT_zero {r : ℝ} (hr : r < 0) :
    Tendsto (fun x => log x / x ^ r) (𝓝[>] 0) (𝓝 0) :=
  (isLittleO_log_rpow_nhdsGT_zero hr).tendsto_div_nhds_zero

@[deprecated (since := "2025-03-02")]
alias tendsto_log_div_rpow_nhds_zero := tendsto_log_div_rpow_nhdsGT_zero

theorem tendsto_log_mul_rpow_nhdsGT_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x => log x * x ^ r) (𝓝[>] 0) (𝓝 0) :=
  (tendsto_log_div_rpow_nhdsGT_zero <| neg_lt_zero.2 hr).congr' <|
    eventually_mem_nhdsWithin.mono fun x hx => by rw [rpow_neg hx.out.le, div_inv_eq_mul]

@[deprecated (since := "2025-03-02")]
alias tendsto_log_mul_rpow_nhds_zero := tendsto_log_mul_rpow_nhdsGT_zero

lemma tendsto_log_mul_self_nhdsLT_zero : Filter.Tendsto (fun x ↦ log x * x) (𝓝[<] 0) (𝓝 0) := by
  have h := tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  simp only [Real.rpow_one] at h
  have h_eq : ∀ x ∈ Set.Iio 0, (-(fun x ↦ log x * x) ∘ (fun x ↦ |x|)) x = log x * x := by
    simp only [Set.mem_Iio, Pi.neg_apply, Function.comp_apply, log_abs]
    intro x hx
    simp only [abs_of_nonpos hx.le, mul_neg, neg_neg]
  refine tendsto_nhdsWithin_congr h_eq ?_
  nth_rewrite 3 [← neg_zero]
  refine (h.comp (tendsto_abs_nhdsNE_zero.mono_left ?_)).neg
  refine nhdsWithin_mono 0 (fun x hx ↦ ?_)
  simp only [Set.mem_Iio] at hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hx.ne, not_false_eq_true]

@[deprecated (since := "2025-03-02")]
alias tendsto_log_mul_self_nhds_zero_left := tendsto_log_mul_self_nhdsLT_zero
