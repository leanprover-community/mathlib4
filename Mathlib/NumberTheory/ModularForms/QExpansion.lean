/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# q-expansions of modular forms

We show that any modular form of level `Γ` can be written as `τ ↦ F (𝕢 h τ)` where `F` is
analytic on the open unit disc, and `𝕢 h` is the parameter `τ ↦ exp (2 * I * π * τ / h)`, for `h`
divisible by the cusp width of `Γ`. As an application, we show that cusp forms decay exponentially
to 0 as `im τ → ∞`.

We also define the `q`-expansion of a modular form, either as a power series or as a
`FormalMultilinearSeries`, and show that it converges to `f` on the upper half plane.

## Main definitions and results

* `SlashInvariantFormClass.cuspFunction`: for a slash-invariant form, this is the function
  `F` such that `f τ = F (exp (2 * π * I * τ / h))`, extended by a choice of limit at `0`.
* `ModularFormClass.differentiableAt_cuspFunction`: when `f` is a modular form, its `cuspFunction`
  is differentiable on the open unit disc (including at `0`).
* `ModularFormClass.qExpansion`: the `q`-expansion of a modular form (defined as the Taylor series
  of its `cuspFunction`), bundled as a `PowerSeries`.
* `ModularFormClass.hasSum_qExpansion`: the `q`-expansion evaluated at `𝕢 h τ` sums to `f τ`, for
  `τ` in the upper half plane.

## TO DO:

* define the `q`-expansion map on modular form spaces as a linear map (or even a ring hom from
  the graded ring of all modular forms?)
-/

open scoped Real NNReal MatrixGroups CongruenceSubgroup

noncomputable section

section Cauchy -- move this stuff into complex analysis hierarchy somewhere
open Complex Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {R : ℝ} {f : ℂ → E} {c : ℂ} {s : Set ℂ}

/-- Cauchy integral formula for higher derivatives at the central point, most general form
(assuming differentiability off a countable set). -/
lemma Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
    (h0 : 0 < R) (n : ℕ) (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R)) (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), (1 / (z - c) ^ (n + 1)) • f z)
      = (2 * π * I / n.factorial) • iteratedDeriv n f c := by
  have := hasFPowerSeriesOnBall_of_differentiable_off_countable (R := ⟨R, h0.le⟩) hs hc hd h0
      |>.factorial_smul 1 n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul] at this
  rw [← this, cauchyPowerSeries_apply, ← Nat.cast_smul_eq_nsmul ℂ, ← mul_smul, ← mul_smul,
    div_mul_cancel₀ _ (mod_cast n.factorial_ne_zero), mul_inv_cancel₀ two_pi_I_ne_zero, one_smul]
  simp [← mul_smul, pow_succ, mul_comm]

/-- Cauchy integral formula for higher derivatives at the central point, assuming differentiability
on the open ball and continuity on its closure. -/
lemma DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul
    (h0 : 0 < R) (n : ℕ) (hc : DiffContOnCl ℂ f (ball c R)) :
    (∮ z in C(c, R), (1 / (z - c) ^ (n + 1)) • f z)
      = (2 * π * I / n.factorial) • iteratedDeriv n f c :=
  c.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable h0 n
    Set.countable_empty hc.continuousOn_ball fun _ hx ↦ hc.differentiableAt isOpen_ball hx.1

/-- Cauchy integral formula for higher derivatives at the central point, assuming differentiability
on the closed ball. -/
lemma DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul (h0 : 0 < R) (n : ℕ)
    (hc : DifferentiableOn ℂ f (closedBall c R)) :
    (∮ z in C(c, R), (1 / (z - c) ^ (n + 1)) • f z)
      = (2 * π * I / n.factorial) • iteratedDeriv n f c :=
  (hc.mono closure_ball_subset_closedBall).diffContOnCl
    |>.circleIntegral_one_div_sub_center_pow_smul h0 n

end Cauchy

open ModularForm Complex Filter Function

open UpperHalfPlane hiding I

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} {h : ℕ} (f : F)
  (τ : ℍ) {z q : ℂ}

local notation "I∞" => comap Complex.im atTop
local notation "𝕢" => Periodic.qParam

namespace SlashInvariantFormClass

variable (h) in
/--
The analytic function `F` such that `f τ = F (exp (2 * π * I * τ / n))`, extended by a choice of
limit at `0`.
-/
def cuspFunction : ℂ → ℂ := Function.Periodic.cuspFunction h (f ∘ ofComplex)

variable [hF : SlashInvariantFormClass F Γ k]
include hF

theorem periodic_comp_ofComplex (hΓ : Γ.width ∣ h) : Periodic (f ∘ ofComplex) h := by
  intro w
  by_cases hw : 0 < im w
  · have : 0 < im (w + h) := by simp only [add_im, natCast_im, add_zero, hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw,
      ← vAdd_width_periodic f k (Nat.cast_dvd_cast hΓ) ⟨w, hw⟩]
    congr 1
    simp [UpperHalfPlane.ext_iff, add_comm]
  · have : im (w + h) ≤ 0 := by simpa only [add_im, natCast_im, add_zero, not_lt] using hw
    simp only [comp_apply, ofComplex_apply_of_im_nonpos this,
      ofComplex_apply_of_im_nonpos (not_lt.mp hw)]

theorem eq_cuspFunction {τ : ℍ} [NeZero h] (hΓ : Γ.width ∣ h) :
    cuspFunction h f (𝕢 h τ) = f τ := by
  simpa using (periodic_comp_ofComplex f hΓ).eq_cuspFunction (NeZero.ne _) τ

end SlashInvariantFormClass

open SlashInvariantFormClass

namespace ModularFormClass
-- These declarations don't logically need `f` to be a modular form (although they are pretty
-- useless without!)

variable (h) in
/-- The `q`-expansion of a level `n` modular form, bundled as a `PowerSeries`. -/
def qExpansion : PowerSeries ℂ :=
  .mk fun n ↦ (↑n.factorial)⁻¹ * iteratedDeriv n (cuspFunction h f) 0

lemma qExpansion_coeff (n : ℕ) :
    (qExpansion h f).coeff ℂ n = (↑n.factorial)⁻¹ * iteratedDeriv n (cuspFunction h f) 0 := by
  simp [qExpansion]

variable (h) in
/--
The `q`-expansion of a level `n` modular form, bundled as a `FormalMultilinearSeries`.

TODO: Maybe get rid of this and instead define a general API for converting `PowerSeries` to
`FormalMultilinearSeries`.
-/
def qExpansionFormalMultilinearSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  fun n ↦ (qExpansion h f).coeff ℂ n • ContinuousMultilinearMap.mkPiAlgebraFin ℂ n _

lemma qExpansionFormalMultilinearSeries_apply_norm (n : ℕ) :
    ‖qExpansionFormalMultilinearSeries h f n‖ = ‖(qExpansion h f).coeff ℂ n‖ := by
  rw [qExpansionFormalMultilinearSeries,
    ← (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin n) ℂ).symm.norm_map]
  simp

variable [hF : ModularFormClass F Γ k]
include hF

theorem differentiableAt_comp_ofComplex (hz : 0 < im z) :
    DifferentiableAt ℂ (f ∘ ofComplex) z :=
  mdifferentiableAt_iff_differentiableAt.mp ((holo f _).comp z (mdifferentiableAt_ofComplex hz))

theorem bounded_at_infty_comp_ofComplex :
    BoundedAtFilter I∞ (f ∘ ofComplex) := by
  simpa only [SlashAction.slash_one, ModularForm.toSlashInvariantForm_coe]
    using (ModularFormClass.bdd_at_infty f 1).comp_tendsto tendsto_comap_im_ofComplex

variable [NeZero h] (hΓ : Γ.width ∣ h)
include hΓ

theorem differentiableAt_cuspFunction (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (cuspFunction h f) q := by
  have npos : 0 < (h : ℝ) := mod_cast (Nat.pos_iff_ne_zero.mpr (NeZero.ne _))
  rcases eq_or_ne q 0 with rfl | hq'
  · exact (periodic_comp_ofComplex f hΓ).differentiableAt_cuspFunction_zero npos
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        (fun _ ↦ differentiableAt_comp_ofComplex f))
      (bounded_at_infty_comp_ofComplex f)
  · exact Periodic.qParam_right_inv npos.ne' hq' ▸
      (periodic_comp_ofComplex f hΓ).differentiableAt_cuspFunction npos.ne'
        <| differentiableAt_comp_ofComplex _ <| Periodic.im_invQParam_pos_of_norm_lt_one npos hq hq'

lemma analyticAt_cuspFunction_zero :
    AnalyticAt ℂ (cuspFunction h f) 0 :=
  DifferentiableOn.analyticAt
    (fun q hq ↦ (differentiableAt_cuspFunction _ hΓ hq).differentiableWithinAt)
    (by simpa only [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

lemma hasSum_qExpansion_of_abs_lt (hq : ‖q‖ < 1) :
    HasSum (fun m ↦ (qExpansion h f).coeff ℂ m • q ^ m) (cuspFunction h f q) := by
  simp only [qExpansion_coeff]
  have hdiff : DifferentiableOn ℂ (cuspFunction h f) (Metric.ball 0 1) := by
    refine fun z hz ↦ (differentiableAt_cuspFunction f hΓ ?_).differentiableWithinAt
    simpa using hz
  have qmem : q ∈ Metric.ball 0 1 := by simpa using hq
  convert hasSum_taylorSeries_on_ball hdiff qmem using 2 with m
  rw [sub_zero, smul_eq_mul, smul_eq_mul, mul_right_comm, smul_eq_mul, mul_assoc]

lemma hasSum_qExpansion :
    HasSum (fun m : ℕ ↦ (qExpansion h f).coeff ℂ m • 𝕢 h τ ^ m) (f τ) := by
  simpa only [eq_cuspFunction f hΓ] using
    hasSum_qExpansion_of_abs_lt f hΓ (τ.norm_qParam_lt_one h)

lemma qExpansionFormalMultilinearSeries_radius :
    1 ≤ (qExpansionFormalMultilinearSeries h f).radius := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
  lift r to NNReal using hr.ne_top
  apply FormalMultilinearSeries.le_radius_of_summable
  simp only [qExpansionFormalMultilinearSeries_apply_norm]
  rw [← r.abs_eq]
  simp_rw [← Real.norm_eq_abs, ← Complex.norm_real, ← norm_pow, ← norm_mul]
  exact (hasSum_qExpansion_of_abs_lt f hΓ (by simpa using hr)).summable.norm

/-- The `q`-expansion of `f` is an `FPowerSeries` representing `cuspFunction h f`. -/
lemma hasFPowerSeries_cuspFunction :
    HasFPowerSeriesOnBall (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 1 := by
  refine ⟨qExpansionFormalMultilinearSeries_radius f hΓ, zero_lt_one, fun {y} hy ↦ ?_⟩
  replace hy : ‖y‖ < 1 := by simpa [enorm_eq_nnnorm, ← NNReal.coe_lt_one] using hy
  simpa [qExpansionFormalMultilinearSeries] using hasSum_qExpansion_of_abs_lt f hΓ hy

/-- The `q`-expansion coefficient can be expressed as a `circleIntegral` for any radius `0 < R < 1`.
-/
lemma qExpansion_coeff_eq_circleIntegral (n : ℕ) {R : ℝ} (hR : 0 < R) (hR' : R < 1) :
    (qExpansion h f).coeff ℂ n =
      ((2 * π * I)⁻¹ * ∮ (z : ℂ) in C(0, R), cuspFunction h f z / z ^ (n + 1)) := by
  have : DifferentiableOn ℂ (cuspFunction h f) (Metric.closedBall 0 R) := fun z hz ↦
      (differentiableAt_cuspFunction f hΓ <| (mem_closedBall_zero_iff.mp hz).trans_lt hR')
        |>.differentiableWithinAt
  have := this.circleIntegral_one_div_sub_center_pow_smul hR n
  rw [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, ← div_eq_iff two_pi_I_ne_zero] at this
  simp_rw [qExpansion, PowerSeries.coeff_mk, ← this, sub_zero, smul_eq_mul, one_div_mul_eq_div,
    div_eq_inv_mul]

/-- The `q`-expansion coefficient can be expressed as an integral along a horizontal line
in the upper half-plane from `t * I` to `N + t * I`, for any `0 < t`.
-/
lemma qExpansion_coeff_eq_intervalIntegral (n : ℕ)
    {t : ℝ} (ht : 0 < t) : (qExpansion h f).coeff ℂ n =
    1 / h * ∫ u in (0)..h, 1 / 𝕢 h (u + t * I) ^ n * f (⟨u + t * I, by simpa using ht⟩) := by
  -- We use a circle integral in the `q`-domain of radius `R = exp (-2 * π * t / N)`.
  let R := Real.exp (-2 * π * t / h)
  have hR0 : 0 < R := Real.exp_pos _
  have hR1 : R < 1 := Real.exp_lt_one_iff.mpr <| by
    simp only [neg_mul, neg_div, neg_lt_zero]
    exact div_pos (by positivity) (mod_cast Nat.pos_of_neZero h)
  -- First apply `qExpansion_coeff_eq_circleIntegral` and rescale from `0 .. 2 * π` to `0 .. N`.
  rw [qExpansion_coeff_eq_circleIntegral f hΓ n hR0 hR1, circleIntegral,
    show 2 * π = h * (2 * π / h) by field_simp [NeZero.ne]]
  conv => enter [1, 2, 2]; rw [show 0 = 0 * (2 * π / h) by simp]
  simp_rw [← intervalIntegral.smul_integral_comp_mul_right, real_smul, ← mul_assoc,
    ← intervalIntegral.integral_const_mul]
  -- Compare the integrands
  congr 1 with u
  let τ : ℍ := ⟨u + t * I, by simpa using ht⟩
  have : circleMap 0 R (u * (2 * π / h)) = 𝕢 h τ := by
    simp only [circleMap, ofReal_exp, ← exp_add, zero_add, τ, UpperHalfPlane.coe_mk_subtype, R]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring_nf
  -- now just complex exponential arithmetic to finish
  simp_rw [deriv_circleMap, this, show u + t * I = τ by rfl, show ⟨↑τ, τ.2⟩ = τ by rfl,
    eq_cuspFunction _ hΓ, smul_eq_mul, pow_succ]
  ring_nf -- why do we need to do ring_nf twice here?
  field_simp [(show 𝕢 h τ ≠ 0 from Complex.exp_ne_zero _), Real.pi_ne_zero, NeZero.ne]
  ring_nf

end ModularFormClass

open ModularFormClass

namespace UpperHalfPlane.IsZeroAtImInfty

variable {f}

lemma zeroAtFilter_comp_ofComplex {α : Type*} [Zero α] [TopologicalSpace α] {f : ℍ → α}
    (hf : IsZeroAtImInfty f) : ZeroAtFilter I∞ (f ∘ ofComplex) := by
  simpa using hf.comp tendsto_comap_im_ofComplex

theorem cuspFunction_apply_zero [NeZero h] (hf : IsZeroAtImInfty f) :
    cuspFunction h f 0 = 0 :=
  Periodic.cuspFunction_zero_of_zero_at_inf (mod_cast (Nat.pos_iff_ne_zero.mpr (NeZero.ne _)))
    hf.zeroAtFilter_comp_ofComplex

/-- A modular form which vanishes at the cusp `∞` actually must decay at least as fast as
`Real.exp (-2 * π * τ.im / n)`, if `n` divides the cusp with.

(Note that `Γ` need not be finite index here). -/
theorem exp_decay_atImInfty_of_width_dvd [ModularFormClass F Γ k]
    (hf : IsZeroAtImInfty f) (hΓ : Γ.width ∣ h) :
    f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / h) := by
  -- If `n = 0` the statement is uninteresting, but true, so let's prove it.
  rcases eq_or_ne h 0 with rfl | hΓ'
  · simp only [Nat.cast_zero, div_zero, Real.exp_zero]
    exact hf.isBoundedAtImInfty
  -- Now the interesting case.
  · haveI : NeZero h := ⟨hΓ'⟩
    simpa [comp_def] using
      ((periodic_comp_ofComplex f hΓ).exp_decay_of_zero_at_inf
        (mod_cast (Nat.pos_iff_ne_zero.mpr (NeZero.ne _)))
        (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
          fun _ ↦ differentiableAt_comp_ofComplex f)
        (hf.zeroAtFilter_comp_ofComplex)).comp_tendsto tendsto_coe_atImInfty

/-- A modular form which vanishes at the cusp `∞` actually has exponentially rapid decay there. -/
theorem exp_decay_atImInfty [ModularFormClass F Γ k] (hf : IsZeroAtImInfty f) [Γ.FiniteIndex] :
    ∃ a, 0 < a ∧ f =O[atImInfty] fun τ ↦ Real.exp (-a * τ.im) := by
  haveI := Γ.width_ne_zero
  haveI := NeZero.mk this -- need both "bundled" and "unbundled" versions in context for next line
  refine ⟨2 * π / Γ.width, by positivity, ?_⟩
  convert hf.exp_decay_atImInfty_of_width_dvd dvd_rfl using 3
  ring

end UpperHalfPlane.IsZeroAtImInfty

namespace CuspFormClass

variable [hF : CuspFormClass F Γ k]
include hF

theorem exp_decay_atImInfty (hΓ : Γ.width ∣ h) :
    f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / h) :=
  IsZeroAtImInfty.exp_decay_atImInfty_of_width_dvd (by simpa using zero_at_infty f 1) hΓ

/-- If `f` is cuspidal, then it has exponentially rapid decay at every cusp. -/
theorem exp_decay_atImInfty_translate [Γ.FiniteIndex] (γ : SL(2, ℤ)) :
    ∃ a, 0 < a ∧ (f ∣[k] γ) =O[atImInfty] fun τ ↦ Real.exp (-a * τ.im) := by
  have hf : IsZeroAtImInfty (CuspForm.translate f γ) := CuspFormClass.zero_at_infty f γ
  suffices (Γ.map <| MulAut.conj γ⁻¹ : Subgroup SL(2, ℤ)).FiniteIndex from hf.exp_decay_atImInfty
  constructor
  rw [Γ.index_map_of_bijective (EquivLike.bijective _)]
  apply Subgroup.FiniteIndex.index_ne_zero

end CuspFormClass
