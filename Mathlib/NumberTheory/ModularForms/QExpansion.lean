/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.Identities
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# q-expansions of modular forms

We show that a modular form of level `Γ(n)` can be written as `τ ↦ F (𝕢 n τ)` where `F` is
analytic on the open unit disc, and `𝕢 n` is the parameter `τ ↦ exp (2 * I * π * τ / n)`. As an
application, we show that cusp forms decay exponentially to 0 as `im τ → ∞`.

We also define the `q`-expansion of a modular form, either as a power series or as a
`FormalMultilinearSeries`, and show that it converges to `f` on the upper half plane.

## Main definitions and results

* `SlashInvariantFormClass.cuspFunction`: for a level `n` slash-invariant form, this is the function
  `F` such that `f τ = F (exp (2 * π * I * τ / n))`, extended by a choice of limit at `0`.
* `ModularFormClass.differentiableAt_cuspFunction`: when `f` is a modular form, its `cuspFunction`
  is differentiable on the open unit disc (including at `0`).
* `ModularFormClass.qExpansion`: the `q`-expansion of a modular form (defined as the Taylor series
  of its `cuspFunction`), bundled as a `PowerSeries`.
* `ModularFormClass.hasSum_qExpansion`: the `q`-expansion evaluated at `𝕢 n τ` sums to `f τ`, for
  `τ` in the upper half plane.
* `qExpansionRingHom` defines the ring homomorphism from the graded ring of modular forms to power
  series given by taking `q`-expansions.
* `qExpansion_coeff_unique` shows that q-expansion coefficients are uniquely determined.

-/


@[expose] public noncomputable section

open ModularForm Complex Filter Function Matrix.SpecialLinearGroup Metric Set
open UpperHalfPlane hiding I

open scoped Real MatrixGroups CongruenceSubgroup Topology

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F)

local notation "I∞" => comap Complex.im atTop
local notation "𝕢" => Periodic.qParam

namespace UpperHalfPlane

/-- The value of `f` at the cusp `∞` (or an arbitrary choice of value if this limit is not
well-defined). -/
def valueAtInfty (f : ℍ → ℂ) : ℂ := limUnder atImInfty f

lemma IsZeroAtImInfty.valueAtInfty_eq_zero {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) :
    valueAtInfty f = 0 :=
  hf.limUnder_eq

lemma qParam_tendsto_atImInfty {h : ℝ} (hh : 0 < h) :
    Tendsto (fun τ : ℍ ↦ 𝕢 h τ) atImInfty (nhds 0) :=
  ((Periodic.qParam_tendsto hh).mono_right nhdsWithin_le_nhds).comp tendsto_coe_atImInfty

end UpperHalfPlane

namespace SlashInvariantFormClass

theorem periodic_comp_ofComplex [SlashInvariantFormClass F Γ k] (hΓ : h ∈ Γ.strictPeriods) :
    Periodic (f ∘ ofComplex) h := by
  intro w
  by_cases! hw : 0 < im w
  · have : 0 < im (w + h) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert SlashInvariantForm.vAdd_apply_of_mem_strictPeriods f ⟨w, hw⟩ hΓ using 2
    ext
    simp [add_comm]
  · have : im (w + h) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

variable (h) in
/--
The analytic function `F` such that `f τ = F (exp (2 * π * I * τ / h))`, extended by a choice of
limit at `0`.
-/
def cuspFunction (f : ℍ → ℂ) : ℂ → ℂ := Function.Periodic.cuspFunction h (f ∘ ofComplex)

theorem eq_cuspFunction [SlashInvariantFormClass F Γ k] (τ : ℍ) (hΓ : h ∈ Γ.strictPeriods)
    (hh : h ≠ 0) : cuspFunction h f (𝕢 h τ) = f τ := by
  simpa using (periodic_comp_ofComplex f hΓ).eq_cuspFunction hh τ

end SlashInvariantFormClass

open SlashInvariantFormClass

namespace ModularFormClass

theorem differentiableAt_comp_ofComplex [ModularFormClass F Γ k]
      {z : ℂ} (hz : 0 < im z) :
    DifferentiableAt ℂ (f ∘ ofComplex) z :=
  mdifferentiableAt_iff_differentiableAt.mp ((holo f _).comp z (mdifferentiableAt_ofComplex hz))

theorem bounded_at_infty_comp_ofComplex [ModularFormClass F Γ k] (hi : IsCusp OnePoint.infty Γ) :
    BoundedAtFilter I∞ (f ∘ ofComplex) :=
  (OnePoint.isBoundedAt_infty_iff.mp (bdd_at_cusps f hi)).comp_tendsto tendsto_comap_im_ofComplex

theorem differentiableAt_cuspFunction [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (cuspFunction h f) q := by
  rcases eq_or_ne q 0 with rfl | hq'
  · exact (periodic_comp_ofComplex f hΓ).differentiableAt_cuspFunction_zero hh
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        (fun _ ↦ differentiableAt_comp_ofComplex f))
      (bounded_at_infty_comp_ofComplex f <| Γ.isCusp_of_mem_strictPeriods hh hΓ)
  · exact Periodic.qParam_right_inv hh.ne' hq' ▸
      (periodic_comp_ofComplex f hΓ).differentiableAt_cuspFunction hh.ne'
        <| differentiableAt_comp_ofComplex _ <| Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq'

lemma differentiableOn_cuspFunction_ball [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    DifferentiableOn ℂ (cuspFunction h f) (Metric.ball 0 1) :=
  fun _ hz ↦ (differentiableAt_cuspFunction f hh hΓ <| mem_ball_zero_iff.mp hz)
    |>.differentiableWithinAt

set_option backward.isDefEq.respectTransparency false in
lemma analyticAt_cuspFunction_zero [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    AnalyticAt ℂ (cuspFunction h f) 0 :=
  DifferentiableOn.analyticAt
    (fun q hq ↦ (differentiableAt_cuspFunction _ hh hΓ hq).differentiableWithinAt)
    (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

lemma cuspFunction_apply_zero [ModularFormClass F Γ k] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    cuspFunction h f 0 = valueAtInfty f := by
  refine (Tendsto.limUnder_eq ?_).symm
  nth_rw 1 [← funext fun τ ↦ eq_cuspFunction f τ hΓ hh.ne']
  refine (analyticAt_cuspFunction_zero f hh hΓ).continuousAt.tendsto.comp ?_
  exact qParam_tendsto_atImInfty hh

variable (h) in
/-- The `q`-expansion of a level `n` modular form, bundled as a `PowerSeries`. -/
def qExpansion (f : ℍ → ℂ) : PowerSeries ℂ :=
  .mk fun m ↦ (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0

lemma qExpansion_coeff (f : ℍ → ℂ) (m : ℕ) :
    (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0 := by
  simp [qExpansion]

lemma qExpansion_coeff_zero [ModularFormClass F Γ k] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    (qExpansion h f).coeff 0 = valueAtInfty f := by
  simp [qExpansion_coeff, cuspFunction_apply_zero f hh hΓ]

set_option backward.isDefEq.respectTransparency false in
lemma hasSum_qExpansion_of_norm_lt [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ ↦ (qExpansion h f).coeff m • q ^ m) (cuspFunction h f q) := by
  convert hasSum_taylorSeries_on_ball (differentiableOn_cuspFunction_ball f hh hΓ)
    (by simpa using hq) using 2 with m
  grind [qExpansion_coeff, sub_zero, smul_eq_mul]

@[deprecated (since := "2025-12-04")] alias hasSum_qExpansion_of_abs_lt :=
  hasSum_qExpansion_of_norm_lt

lemma hasSum_qExpansion [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion h f).coeff m • 𝕢 h τ ^ m) (f τ) := by
  have : 0 < 2 * π * τ.im / h := by positivity
  have : ‖𝕢 h τ‖ < 1 := by simpa [Periodic.qParam, Complex.norm_exp, neg_div]
  simpa [eq_cuspFunction f _ hΓ hh.ne'] using hasSum_qExpansion_of_norm_lt f hh hΓ this

variable (h) in
/--
The `q`-expansion of a modular form, bundled as a `FormalMultilinearSeries`.

TODO: Maybe get rid of this and instead define a general API for converting `PowerSeries` to
`FormalMultilinearSeries`.
-/
def qExpansionFormalMultilinearSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ fun m ↦ (qExpansion h f).coeff m

@[simp]
lemma qExpansionFormalMultilinearSeries_coeff (m : ℕ) :
    (qExpansionFormalMultilinearSeries h f).coeff m = (qExpansion h f).coeff m := by
  simp [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.coeff_ofScalars]

lemma qExpansionFormalMultilinearSeries_apply_norm (m : ℕ) :
    ‖qExpansionFormalMultilinearSeries h f m‖ = ‖(qExpansion h f).coeff m‖ := by
  rw [qExpansionFormalMultilinearSeries,
    ← (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin m) ℂ).symm.norm_map]
  simp

set_option backward.isDefEq.respectTransparency false in
lemma qExpansionFormalMultilinearSeries_radius [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    1 ≤ (qExpansionFormalMultilinearSeries h f).radius := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
  lift r to NNReal using hr.ne_top
  apply FormalMultilinearSeries.le_radius_of_summable
  simp only [qExpansionFormalMultilinearSeries_apply_norm]
  rw [← r.abs_eq]
  simp_rw [← Real.norm_eq_abs, ← Complex.norm_real, ← norm_pow, ← norm_mul]
  exact (hasSum_qExpansion_of_norm_lt f hh hΓ (q := r) (by simpa using hr)).summable.norm

/-- The `q`-expansion of `f` is an `FPowerSeries` representing `cuspFunction n f`. -/
lemma hasFPowerSeries_cuspFunction [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    HasFPowerSeriesOnBall (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 1 := by
  refine ⟨qExpansionFormalMultilinearSeries_radius f hh hΓ, zero_lt_one, fun hy ↦ ?_⟩
  rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
    ← NNReal.coe_lt_one, coe_nnnorm] at hy
  simpa [qExpansionFormalMultilinearSeries, mul_comm] using hasSum_qExpansion_of_norm_lt f hh hΓ hy

set_option backward.isDefEq.respectTransparency false in
/-- The `q`-expansion coefficient can be expressed as a `circleIntegral` for any radius `0 < R < 1`.
-/
lemma qExpansion_coeff_eq_circleIntegral [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (n : ℕ) {R : ℝ} (hR : 0 < R) (hR' : R < 1) :
    (qExpansion h f).coeff n =
      ((2 * π * I)⁻¹ * ∮ (z : ℂ) in C(0, R), cuspFunction h f z / z ^ (n + 1)) := by
  have := ((differentiableOn_cuspFunction_ball f hh hΓ).mono
    (Metric.closedBall_subset_ball hR')).circleIntegral_one_div_sub_center_pow_smul hR n
  rw [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, ← div_eq_iff two_pi_I_ne_zero] at this
  simp_rw [qExpansion, PowerSeries.coeff_mk, ← this, sub_zero, smul_eq_mul, one_div_mul_eq_div,
    div_eq_inv_mul]

set_option backward.isDefEq.respectTransparency false in
/--
If `h` is a positive strict period of `f`, then the `q`-expansion coefficient can be expressed
as an integral along a horizontal line in the upper half-plane from `t * I` to `h + t * I`, for
any `0 < t`.
-/
lemma qExpansion_coeff_eq_intervalIntegral [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (qExpansion h f).coeff n =
      1 / h * ∫ u in 0..h, 1 / 𝕢 h (u + t * I) ^ n * f ⟨u + t * I, by simpa using ht⟩ := by
  -- We use a circle integral in the `q`-domain of radius `R = exp (-2 * π * t / h)`.
  let R := Real.exp (-2 * π * t / h)
  have hR0 : 0 < R := Real.exp_pos _
  have hR1 : R < 1 := Real.exp_lt_one_iff.2 <| by simpa [neg_div] using div_pos (by positivity) hh
  -- First apply `qExpansion_coeff_eq_circleIntegral` and rescale from `0 .. 2 * π` to `0 .. h`.
  rw [qExpansion_coeff_eq_circleIntegral f hh hΓ n hR0 hR1, circleIntegral,
    show 2 * π = h * (2 * π / h) by field_simp]
  conv => enter [1, 2, 2]; rw [show 0 = 0 * (2 * π / h) by simp]
  simp_rw [← intervalIntegral.smul_integral_comp_mul_right, real_smul, ← mul_assoc,
    ← intervalIntegral.integral_const_mul]
  -- Compare the integrands
  congr 1 with u
  let τ : ℍ := ⟨u + t * I, by simpa using ht⟩
  have : circleMap 0 R (u * (2 * π / h)) = 𝕢 h τ := by
    simp only [circleMap, ofReal_exp, ← exp_add, zero_add, τ, R]
    congr 1
    push_cast
    have := I_sq
    grind
  -- now just complex exponential arithmetic to finish
  simp_rw [deriv_circleMap, this, show u + t * I = τ by rfl, show ⟨↑τ, τ.2⟩ = τ by rfl,
    eq_cuspFunction f _ hΓ hh.ne', smul_eq_mul, pow_succ, push_cast]
  field_simp [(show 𝕢 h τ ≠ 0 from Complex.exp_ne_zero _), Real.pi_ne_zero, NeZero.ne]

theorem exp_decay_sub_atImInfty [ModularFormClass F Γ k] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    (fun τ ↦ f τ - valueAtInfty f) =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / h) := by
  have hi : IsCusp OnePoint.infty Γ := Γ.isCusp_of_mem_strictPeriods hh hΓ
  convert ((periodic_comp_ofComplex f hΓ).exp_decay_sub_of_bounded_at_inf hh
    (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        fun _ ↦ differentiableAt_comp_ofComplex f)
    (bounded_at_infty_comp_ofComplex f hi)).comp_tendsto tendsto_coe_atImInfty
  simp [← cuspFunction_apply_zero f hh hΓ, cuspFunction]

/-- Version of `exp_decay_sub_atImInfty` stating a less precise result but easier to apply in
practice (not specifying the growth rate precisely).

Note that the `Fact` hypothesis is automatically synthesized for arithmetic subgroups.
The discreteness hypothesis may be unnecessary, but it is satisfied in the cases of interest. -/
theorem exp_decay_sub_atImInfty' [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] [Fact (IsCusp OnePoint.infty Γ)] :
    ∃ c > 0, (fun τ ↦ f τ - valueAtInfty f) =O[atImInfty] (fun τ ↦ Real.exp (-c * τ.im)) := by
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have hΓ : Γ.strictWidthInfty ∈ Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  refine ⟨2 * π / Γ.strictWidthInfty, div_pos Real.two_pi_pos hh, ?_⟩
  convert exp_decay_sub_atImInfty f hh hΓ using 3 with τ
  ring_nf

end ModularFormClass

open ModularFormClass

namespace UpperHalfPlane.IsZeroAtImInfty

variable {f}

lemma zero_at_infty_comp_ofComplex {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) :
    ZeroAtFilter I∞ (f ∘ ofComplex) :=
  hf.comp tendsto_comap_im_ofComplex

theorem cuspFunction_apply_zero {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) (hh : 0 < h) :
    cuspFunction h f 0 = 0 :=
  Periodic.cuspFunction_zero_of_zero_at_inf hh hf.zero_at_infty_comp_ofComplex

theorem exp_decay_atImInfty [ModularFormClass F Γ k]
    (hf : IsZeroAtImInfty f) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / h) := by
  simpa [hf.valueAtInfty_eq_zero] using exp_decay_sub_atImInfty f hh hΓ

/-- Version of `exp_decay_atImInfty` stating a less precise result but easier to apply in practice
(not specifying the growth rate precisely). Note that the `Fact` hypothesis is automatically
synthesized for arithmetic subgroups. -/
theorem exp_decay_atImInfty' [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] [Fact (IsCusp OnePoint.infty Γ)] (hf : IsZeroAtImInfty f) :
    ∃ c > 0, f =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im) := by
  simpa [hf.valueAtInfty_eq_zero] using exp_decay_sub_atImInfty' f

end UpperHalfPlane.IsZeroAtImInfty

namespace CuspFormClass

include Γ k -- can't be inferred from statements but shouldn't be omitted
variable [CuspFormClass F Γ k]

theorem zero_at_infty_comp_ofComplex [Fact (IsCusp OnePoint.infty Γ)] :
    ZeroAtFilter I∞ (f ∘ ofComplex) :=
  (zero_at_infty f).comp tendsto_comap_im_ofComplex

theorem cuspFunction_apply_zero (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    cuspFunction h f 0 = 0 :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  (CuspFormClass.zero_at_infty f).cuspFunction_apply_zero hh

theorem exp_decay_atImInfty (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / h) :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  (CuspFormClass.zero_at_infty f).exp_decay_atImInfty hh hΓ

theorem exp_decay_atImInfty' [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    [Fact (IsCusp OnePoint.infty Γ)] :
    ∃ c > 0, f =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im) :=
  (CuspFormClass.zero_at_infty f).exp_decay_atImInfty'

end CuspFormClass

section ring

theorem cuspFunction_mul_zero {f g : ℂ → ℂ} (hfcts : ContinuousAt (Periodic.cuspFunction h f) 0)
    (hgcts : ContinuousAt (Periodic.cuspFunction h g) 0) : Periodic.cuspFunction h (f * g) 0 =
    Periodic.cuspFunction h f 0 * Periodic.cuspFunction h g 0 := by
  rw [Periodic.cuspFunction, update_self]
  exact (Periodic.tendsto_nhds_zero hfcts).mul (Periodic.tendsto_nhds_zero hgcts) |>.limUnder_eq

lemma qExpansion_mul_coeff_zero {f g : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    (qExpansion h (f * g)).coeff 0 = ((qExpansion h f).coeff 0) * (qExpansion h g).coeff 0 := by
  simpa [qExpansion_coeff] using cuspFunction_mul_zero hfcts hgcts

lemma cuspFunction_mul {f g : ℍ → ℂ}
    (hfcts : ContinuousAt (cuspFunction h f) 0) (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f * g) = cuspFunction h f * cuspFunction h g := by
  ext z
  by_cases H : z = 0
  · simpa [H] using cuspFunction_mul_zero hfcts hgcts
  · simp [cuspFunction, Periodic.cuspFunction, H]

protected lemma ModularForm.cuspFunction_mul [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {a b : ℤ} (f : ModularForm Γ a) (g : ModularForm Γ b) :
    cuspFunction h (f.mul g) = cuspFunction h f * cuspFunction h g :=
  cuspFunction_mul (analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (analyticAt_cuspFunction_zero g hh hΓ).continuousAt

lemma cuspFunction_smul {f : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0) (a : ℂ) :
    cuspFunction h (a • f) = a • cuspFunction h f := by
  apply Periodic.cuspFunction_smul hfcts

lemma cuspFunction_neg {f : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0) :
    cuspFunction h (-f) = -cuspFunction h f :=
  Periodic.cuspFunction_neg hfcts

lemma cuspFunction_add {f g : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f + g) = cuspFunction h f + cuspFunction h g :=
  Periodic.cuspFunction_add hfcts hgcts

lemma cuspFunction_sub {f g : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f - g) = cuspFunction h f - cuspFunction h g :=
  Periodic.cuspFunction_sub hfcts hgcts

lemma qExpansion_mul {f g : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    qExpansion h (f * g) = qExpansion h f * qExpansion h g := by
  ext
  simp only [qExpansion_coeff, cuspFunction_mul hf.continuousAt hg.continuousAt,
    iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.mul_sum, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Nat.cast_choose _ (by grind)]
  field_simp [Nat.factorial_ne_zero]

protected lemma ModularForm.qExpansion_mul [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {a b : ℤ} (f : ModularForm Γ a) (g : ModularForm Γ b) :
    qExpansion h (f.mul g) = qExpansion h f * qExpansion h g :=
  qExpansion_mul (analyticAt_cuspFunction_zero f hh hΓ) (analyticAt_cuspFunction_zero g hh hΓ)

lemma qExpansion_add {G : Type*} [FunLike G ℍ ℂ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    {a b : ℤ} (f : F) [ModularFormClass F Γ a] (g : G) [ModularFormClass G Γ b] :
    qExpansion h (f + g) = qExpansion h f + qExpansion h g := by
  ext
  grind [qExpansion, cuspFunction_add (analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (analyticAt_cuspFunction_zero g hh hΓ).continuousAt, PowerSeries.coeff_mk,
    iteratedDeriv_add (analyticAt_cuspFunction_zero f hh hΓ).contDiffAt
      (analyticAt_cuspFunction_zero g hh hΓ).contDiffAt]

lemma qExpansion_smul
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (a : ℂ) (f : F) [ModularFormClass F Γ k] :
    qExpansion h (a • f) = a • qExpansion h f := by
  ext
  grind [map_smul, smul_eq_mul, qExpansion, PowerSeries.coeff_mk, cuspFunction_smul
    (analyticAt_cuspFunction_zero f hh hΓ).continuousAt, iteratedDeriv_const_smul_field]

set_option backward.isDefEq.respectTransparency false in
lemma qExpansion_neg
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : F) [ModularFormClass F Γ k] :
    qExpansion h (-f) = -qExpansion h f := by
  simpa using qExpansion_smul hh hΓ (-1 : ℂ) f

set_option backward.isDefEq.respectTransparency false in
lemma qExpansion_sub (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {a b : ℤ}
    (f : ModularForm Γ a) (g : ModularForm Γ b) :
    qExpansion h (f - g) = qExpansion h f - qExpansion h g := by
  simpa [sub_eq_add_neg, ← qExpansion_neg hh hΓ g] using qExpansion_add hh hΓ f (-g)

lemma qExpansion_zero (h) : qExpansion h 0 = 0 := by
  suffices cuspFunction h 0 = 0 by ext; simp [qExpansion_coeff, this]
  simpa [cuspFunction, Periodic.cuspFunction]
    using (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).limUnder_eq

lemma qExpansion_eq_zero_iff (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {k : ℤ} (f : ModularForm Γ k) :
    qExpansion h f = 0 ↔ f = 0 := by
  refine ⟨fun H ↦ ?_, (· ▸ qExpansion_zero h)⟩
  ext z
  simp [← (hasSum_qExpansion f hh hΓ z).tsum_eq, H]

/-- The qExpansion map as an additive group hom. to power series over `ℂ`. -/
def qExpansionAddHom (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) :
    ModularForm Γ k →+ PowerSeries ℂ where
  toFun f := qExpansion h f
  map_zero' := qExpansion_zero h
  map_add' f g := qExpansion_add hh hΓ f g

lemma qExpansion_one [Γ.HasDetPlusMinusOne] : qExpansion h (1 : ModularForm Γ 0) = 1 := by
  ext m
  have h1 : cuspFunction h 1 = 1 := by
    ext q
    rcases eq_or_ne q 0 with rfl | hq
    · simpa [cuspFunction, Periodic.cuspFunction] using tendsto_const_nhds.limUnder_eq
    · simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero h _ hq]
  have h2 : iteratedDeriv m (1 : ℂ → ℂ) 0 = if m = 0 then 1 else 0 := by
    simpa [ite_apply] using iteratedDeriv_const
  simp +contextual [qExpansion_coeff, h1, h2]

open scoped DirectSum in
/-- The qExpansion map as a map from the graded ring of modular forms to power series over `ℂ`. -/
def qExpansionRingHom (h) [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) : (⨁ k, ModularForm Γ k) →+* PowerSeries ℂ :=
  DirectSum.toSemiring (qExpansionAddHom hh hΓ) qExpansion_one
    (ModularForm.qExpansion_mul hh hΓ)

@[simp]
lemma qExpansionRingHom_apply [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) (f : ModularForm Γ k) :
    qExpansionRingHom h hh hΓ (DirectSum.of _ k f) = qExpansion h f :=
  DirectSum.toSemiring_of ..

lemma qExpansion_of_mul [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (a b : ℤ) (f : ModularForm Γ a) (g : ModularForm Γ b) :
    qExpansion h ((DirectSum.of _ a f * DirectSum.of _ b g) (a + b)) =
    qExpansion h f * qExpansion h g := by
  simpa [DirectSum.of_mul_of] using ModularForm.qExpansion_mul hh hΓ f g

lemma qExpansion_of_pow [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (f : ModularForm Γ k) (n : ℕ) :
    qExpansion h ((((DirectSum.of _ k f)) ^ n) (n * k)) = (qExpansion h f) ^ n := by
  have := (qExpansionRingHom h hh hΓ).map_pow (DirectSum.of _ k f) n
  simpa [DirectSum.ofPow]

end ring

section uniqueness

private lemma hasSum_cuspFunction_of_hasSum_punctured
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {c : ℕ → ℂ} [ModularFormClass F Γ k] {f : F}
    (hf : ∀ (τ : ℍ), HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) {q : ℂ} (hq : ‖q‖ < 1)
    (hq1 : q ≠ 0) : HasSum (fun m ↦ c m • q ^ m) (cuspFunction h f q) := by
  grind [eq_cuspFunction f ⟨_, Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1⟩,
    Periodic.qParam_right_inv]

set_option backward.isDefEq.respectTransparency false in
private lemma hasFPowerSeriesOnBall_update (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {c : ℕ → ℂ} {f : F} [ModularFormClass F Γ k]
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (c m) • 𝕢 h τ ^ m) (f τ)) :
    HasFPowerSeriesOnBall (update (cuspFunction h f) 0 (c 0)) (.ofScalars ℂ c) 0 1 := by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
    rcases eq_or_ne r 0 with rfl | hr'
    · simp
    · lift r to NNReal using hr.ne_top
      apply FormalMultilinearSeries.le_radius_of_summable
      simpa [norm_smul] using (hasSum_cuspFunction_of_hasSum_punctured hh hΓ hf (q := r)
        (by simpa using hr) (mod_cast hr')).summable.norm
  · simp
  · intro y hy
    rw [zero_add]
    -- note the `simp`s below do not automatically apply this lemma to the argument of
    -- `Function.update`, because of limitations in `simp`'s support for dependent function types,
    -- see lean4 issue #12478.
    rw [← ENNReal.coe_one, eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hy
    rcases eq_or_ne y 0 with rfl | hy'
    · simpa +contextual [zero_pow_eq] using hasSum_ite_eq 0 (c 0)
    · simpa [update_of_ne hy', mul_comm]
        using hasSum_cuspFunction_of_hasSum_punctured hh hΓ hf hy hy'

lemma hasFPowerSeriesOnBall_cuspFunction {c : ℕ → ℂ} (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {f : F} [ModularFormClass F Γ k]
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) :
    HasFPowerSeriesOnBall (cuspFunction h f) (.ofScalars ℂ c) 0 1 := by
  -- previous lemma gives result after updating at 0
  have H1 : HasFPowerSeriesOnBall (update (cuspFunction h f) 0 (c 0)) (.ofScalars ℂ c) 0 1 :=
    hasFPowerSeriesOnBall_update hh hΓ hf
  -- now just need to check values at 0 match
  -- use continuity of both functions & we know it everywhere else
  have H2 : c 0 = cuspFunction h f 0 := by
    have L1 := H1.hasFPowerSeriesAt.continuousAt
    have L2 := (analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    have := (L1.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE L2).mp <|
      by filter_upwards [self_mem_nhdsWithin] with a ha using update_of_ne ha ..
    simpa [update_self] using this.eq_of_nhds
  rwa [update_eq_self_iff.mpr H2] at H1

lemma qExpansion_coeff_unique {c : ℕ → ℂ} (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {f : F} [ModularFormClass F Γ k]
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) (m : ℕ) :
    c m = (qExpansion h f).coeff m := by
  have h1 : HasFPowerSeriesAt (cuspFunction h f) (.ofScalars ℂ c) 0 :=
    (hasFPowerSeriesOnBall_cuspFunction hh hΓ hf).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 :=
    (hasFPowerSeries_cuspFunction f hh hΓ).hasFPowerSeriesAt
  simpa using congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)
