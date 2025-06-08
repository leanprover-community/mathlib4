/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

/-!
# Periodic holomorphic functions

We show that if `f : ℂ → ℂ` satisfies `f (z + h) = f z`, for some nonzero real `h`, then there is a
function `F` such that `f z = F (exp (2 * π * I * z / h))` for all `z`; and if `f` is holomorphic
at some `z`, then `F` is holomorphic at `exp (2 * π * I * z / h)`.

We also show (using Riemann's removable singularity theorem) that if `f` is holomorphic and bounded
for all sufficiently large `im z`, then `F` extends to a holomorphic function on a neighbourhood of
`0`. As a consequence, if `f` tends to zero as `im z → ∞`, then in fact it decays *exponentially*
to zero. These results are important in the theory of modular forms.
-/

open Complex Filter Asymptotics

open scoped Real Topology

noncomputable section

local notation "I∞" => comap im atTop

variable (h : ℝ)

namespace Function.Periodic

/-- Parameter for q-expansions, `qParam h z = exp (2 * π * I * z / h)` -/
def qParam (z : ℂ) : ℂ := exp (2 * π * I * z / h)

/-- One-sided inverse of `qParam h`. -/
def invQParam (q : ℂ) : ℂ := h / (2 * π * I) * log q

local notation "𝕢" => qParam

section qParam

theorem norm_qParam (z : ℂ) : ‖𝕢 h z‖ = Real.exp (-2 * π * im z / h) := by
  simp only [qParam, norm_exp, div_ofReal_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
    mul_zero, sub_zero, I_re, mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, zero_sub,
    neg_mul]

@[deprecated (since := "2025-02-17")] alias abs_qParam := norm_qParam

theorem im_invQParam (q : ℂ) : im (invQParam h q) = -h / (2 * π) * Real.log ‖q‖ := by
  simp only [invQParam, ← div_div, div_I, neg_mul, neg_im, mul_im, mul_re, div_ofReal_re,
    div_ofNat_re, ofReal_re, I_re, mul_zero, div_ofReal_im, div_ofNat_im, ofReal_im, zero_div, I_im,
    mul_one, sub_self, zero_mul, add_zero, log_re, zero_add, neg_div]

variable {h} -- next few theorems all assume h ≠ 0 or 0 < h

theorem qParam_right_inv (hh : h ≠ 0) {q : ℂ} (hq : q ≠ 0) : 𝕢 h (invQParam h q) = q := by
  simp only [qParam, invQParam, ← mul_assoc, mul_div_cancel₀ _ two_pi_I_ne_zero,
    mul_div_cancel_left₀ _ (ofReal_ne_zero.mpr hh), exp_log hq]

theorem qParam_left_inv_mod_period (hh : h ≠ 0) (z : ℂ) :
    ∃ m : ℤ, invQParam h (𝕢 h z) = z + m * h := by
  dsimp only [qParam, invQParam]
  obtain ⟨m, hm⟩ := log_exp_exists (2 * ↑π * I * z / ↑h)
  refine ⟨m, by rw [hm, mul_div_assoc, mul_comm (m : ℂ), ← mul_add, ← mul_assoc,
    div_mul_cancel₀ _ two_pi_I_ne_zero, mul_add, mul_div_cancel₀ _ (mod_cast hh), mul_comm]⟩

theorem norm_qParam_lt_iff (hh : 0 < h) (A : ℝ) (z : ℂ) :
    ‖qParam h z‖ < Real.exp (-2 * π * A / h) ↔ A < im z := by
  rw [norm_qParam, Real.exp_lt_exp, div_lt_div_iff_of_pos_right hh, mul_lt_mul_left_of_neg]
  simpa using Real.pi_pos

@[deprecated (since := "2025-02-17")] alias abs_qParam_lt_iff := norm_qParam_lt_iff

theorem qParam_tendsto (hh : 0 < h) : Tendsto (qParam h) I∞ (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (.of_forall fun q ↦ exp_ne_zero _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_qParam]
  apply (tendsto_comap'_iff (m := fun y ↦ Real.exp (-2 * π * y / h)) (range_im ▸ univ_mem)).mpr
  refine Real.tendsto_exp_atBot.comp (.atBot_div_const hh (tendsto_id.const_mul_atTop_of_neg ?_))
  simpa using Real.pi_pos

theorem invQParam_tendsto (hh : 0 < h) : Tendsto (invQParam h) (𝓝[≠] 0) I∞ := by
  simp only [tendsto_comap_iff, comp_def, im_invQParam]
  apply Tendsto.const_mul_atBot_of_neg (div_neg_of_neg_of_pos (neg_lt_zero.mpr hh) (by positivity))
  exact Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero

end qParam

section PeriodicOnℂ

variable (h : ℝ) (f : ℂ → ℂ)

/-- The function `q ↦ f (invQParam h q)`, extended by a non-canonical choice of limit at 0. -/
def cuspFunction : ℂ → ℂ :=
  update (f ∘ invQParam h) 0 (limUnder (𝓝[≠] 0) (f ∘ invQParam h))

theorem cuspFunction_eq_of_nonzero {q : ℂ} (hq : q ≠ 0) :
    cuspFunction h f q = f (invQParam h q) :=
  update_of_ne hq ..

theorem cuspFunction_zero_eq_limUnder_nhds_ne :
    cuspFunction h f 0 = limUnder (𝓝[≠] 0) (cuspFunction h f) := by
  conv_lhs => simp only [cuspFunction, update_self]
  refine congr_arg lim (Filter.map_congr <| eventuallyEq_nhdsWithin_of_eqOn fun r hr ↦ ?_)
  rw [cuspFunction, update_of_ne hr]

variable {f h}

theorem eq_cuspFunction (hh : h ≠ 0) (hf : Periodic f h) (z : ℂ) :
    (cuspFunction h f) (𝕢 h z) = f z := by
  have : (cuspFunction h f) (𝕢 h z) = f (invQParam h (𝕢 h z)) := by
    rw [cuspFunction, update_of_ne, comp_apply]
    exact exp_ne_zero _
  obtain ⟨m, hm⟩ := qParam_left_inv_mod_period hh z
  simpa only [this, hm] using hf.int_mul m z

end PeriodicOnℂ

section HoloOnC

variable {h : ℝ} {f : ℂ → ℂ}

/--
Key technical lemma: the function `cuspFunction h f` is differentiable at the images of
differentiability points of `f` (even if `invQParam` is not differentiable there).
-/
theorem differentiableAt_cuspFunction (hh : h ≠ 0) (hf : Periodic f h)
    {z : ℂ} (hol_z : DifferentiableAt ℂ f z) :
    DifferentiableAt ℂ (cuspFunction h f) (𝕢 h z) := by
  let q := 𝕢 h z
  have qdiff : HasStrictDerivAt (𝕢 h) (q * (2 * π * I / h)) z := by
    simpa only [id_eq, mul_one] using (((hasStrictDerivAt_id z).const_mul _).div_const _).cexp
  -- Now show that the q-map has a differentiable local inverse at z, say L : ℂ → ℂ with L q = z.
  have diff_ne : q * (2 * π * I / h) ≠ 0 :=
    mul_ne_zero (exp_ne_zero _) (div_ne_zero two_pi_I_ne_zero <| mod_cast hh)
  let L := (qdiff.localInverse (𝕢 h) _ z) diff_ne
  have diff_L : DifferentiableAt ℂ L q := (qdiff.to_localInverse diff_ne).differentiableAt
  have hL : 𝕢 h ∘ L =ᶠ[𝓝 q] (id : ℂ → ℂ) :=
    (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_right_inverse
  -- Thus, if F = cuspFunction h f, we have F q' = f (L q') for q' near q.
  -- Since L is differentiable at q, and f is diff'ble at L q [ = z], we conclude
  -- that F is differentiable at q.
  have hF := hL.fun_comp (cuspFunction h f)
  have : cuspFunction h f ∘ 𝕢 h ∘ L = f ∘ L := funext fun z ↦ eq_cuspFunction hh hf (L z)
  rw [this] at hF
  rw [← EventuallyEq.eq_of_nhds (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_left_inverse]
    at hol_z
  exact (hol_z.comp q diff_L).congr_of_eventuallyEq hF.symm

theorem eventually_differentiableAt_cuspFunction_nhds_ne_zero (hh : 0 < h) (hf : Periodic f h)
    (h_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) :
    ∀ᶠ q in 𝓝[≠] 0, DifferentiableAt ℂ (cuspFunction h f) q := by
  refine ((invQParam_tendsto hh).eventually h_hol).mp ?_
  refine eventually_nhdsWithin_of_forall (fun q hq h_diff ↦ ?_)
  rw [← qParam_right_inv hh.ne' hq]
  exact differentiableAt_cuspFunction hh.ne' hf h_diff

end HoloOnC

section HoloAtInfC

variable {h : ℝ} {f : ℂ → ℂ}

theorem boundedAtFilter_cuspFunction (hh : 0 < h) (h_bd : BoundedAtFilter I∞ f) :
    BoundedAtFilter (𝓝[≠] 0) (cuspFunction h f) := by
  refine (h_bd.comp_tendsto <| invQParam_tendsto hh).congr' ?_ (by simp)
  refine eventually_nhdsWithin_of_forall fun q hq ↦ ?_
  rw [cuspFunction_eq_of_nonzero _ _ hq, comp_def]

theorem cuspFunction_zero_of_zero_at_inf (hh : 0 < h) (h_zer : ZeroAtFilter I∞ f) :
    cuspFunction h f 0 = 0 := by
  simpa only [cuspFunction, update_self] using (h_zer.comp (invQParam_tendsto hh)).limUnder_eq

theorem differentiableAt_cuspFunction_zero (hh : 0 < h) (hf : Periodic f h)
    (h_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) (h_bd : BoundedAtFilter I∞ f) :
    DifferentiableAt ℂ (cuspFunction h f) 0 := by
  obtain ⟨c, t⟩ := (boundedAtFilter_cuspFunction hh h_bd).bound
  replace t := (eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hf h_hol).and t
  simp only [norm_one, Pi.one_apply, mul_one] at t
  obtain ⟨S, hS1, hS2, hS3⟩ := eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp t)
  have h_diff : DifferentiableOn ℂ (cuspFunction h f) (S \ {0}) :=
    fun x hx ↦ (hS1 x hx.1 hx.2).1.differentiableWithinAt
  have hF_bd : BddAbove (norm ∘ cuspFunction h f '' (S \ {0})) := by
    use c
    simp only [mem_upperBounds, Set.mem_image, Set.mem_diff, forall_exists_index, and_imp]
    intro y q hq hq2 hy
    simpa only [← hy, norm_one, mul_one] using (hS1 q hq hq2).2
  have := differentiableOn_update_limUnder_of_bddAbove (IsOpen.mem_nhds hS2 hS3) h_diff hF_bd
  rw [← cuspFunction_zero_eq_limUnder_nhds_ne, update_eq_self] at this
  exact this.differentiableAt (IsOpen.mem_nhds hS2 hS3)

/--
If `f` is periodic, and holomorphic and bounded near `I∞`, then it tends to a limit at `I∞`,
and this limit is the value of its cusp function at 0.
-/
theorem tendsto_at_I_inf (hh : 0 < h) (hf : Periodic f h)
    (h_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) (h_bd : BoundedAtFilter I∞ f) :
    Tendsto f I∞ (𝓝 <| cuspFunction h f 0) := by
  suffices Tendsto (cuspFunction h f) (𝓝[≠] 0) (𝓝 <| cuspFunction h f 0) by
    simpa only [Function.comp_def, eq_cuspFunction hh.ne' hf] using this.comp (qParam_tendsto hh)
  exact tendsto_nhdsWithin_of_tendsto_nhds
    (differentiableAt_cuspFunction_zero hh hf h_hol h_bd).continuousAt.tendsto

/--
If `f` is periodic, holomorphic near `I∞`, and tends to zero at `I∞`, then in fact it tends to zero
exponentially fast.
-/
theorem exp_decay_of_zero_at_inf (hh : 0 < h) (hf : Periodic f h)
    (h_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) (h_zer : ZeroAtFilter I∞ f) :
    f =O[I∞] fun z ↦ Real.exp (-2 * π * im z / h) := by
  suffices cuspFunction h f =O[_] id by
    simpa only [comp_def, eq_cuspFunction hh.ne' hf, id_eq, norm_qParam]
      using (this.comp_tendsto (qParam_tendsto hh)).norm_right
  simpa only [cuspFunction_zero_of_zero_at_inf hh h_zer, sub_zero] using
    (differentiableAt_cuspFunction_zero hh hf h_hol h_zer.boundedAtFilter).isBigO_sub.mono
      nhdsWithin_le_nhds

end HoloAtInfC

end Function.Periodic
