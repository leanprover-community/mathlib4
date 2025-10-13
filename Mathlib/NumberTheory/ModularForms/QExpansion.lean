/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.RingTheory.PowerSeries.Basic

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

## TO DO:

* generalise to handle arbitrary finite-index subgroups (not just `Γ(n)` for some `n`)
* define the `q`-expansion map on modular form spaces as a linear map (or even a ring hom from
  the graded ring of all modular forms?)
-/

open ModularForm Complex Filter UpperHalfPlane Function Matrix.SpecialLinearGroup

open scoped Real MatrixGroups CongruenceSubgroup

noncomputable section

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    {h : ℝ} (f : F)

local notation "I∞" => comap Complex.im atTop
local notation "𝕢" => Periodic.qParam

namespace SlashInvariantFormClass

theorem periodic_comp_ofComplex [SlashInvariantFormClass F Γ k] (hΓ : h ∈ Γ.strictPeriods) :
    Periodic (f ∘ ofComplex) h := by
  intro w
  by_cases hw : 0 < im w
  · have : 0 < im (w + h) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert SlashInvariantForm.vAdd_apply_of_mem_strictPeriods f ⟨w, hw⟩ hΓ using 2
    ext
    simp [add_comm]
  · have : im (w + h) ≤ 0 := by simpa using hw
    simp only [comp_apply, ofComplex_apply_of_im_nonpos this,
      ofComplex_apply_of_im_nonpos (not_lt.mp hw)]

variable (h) in
/--
The analytic function `F` such that `f τ = F (exp (2 * π * I * τ / n))`, extended by a choice of
limit at `0`.
-/
def cuspFunction : ℂ → ℂ := Function.Periodic.cuspFunction h (f ∘ ofComplex)

theorem eq_cuspFunction [SlashInvariantFormClass F Γ k] (τ : ℍ) (hΓ : h ∈ Γ.strictPeriods)
    (hh : h ≠ 0) : cuspFunction h f (𝕢 h τ) = f τ := by
  simpa only [comp_apply, ofComplex_apply]
    using (periodic_comp_ofComplex f hΓ).eq_cuspFunction hh τ

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

theorem differentiableAt_cuspFunction [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (cuspFunction h f) q := by
  have hi : IsCusp OnePoint.infty Γ := by
    rw [Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty] at hΓ
    refine Γ.strictWidthInfty_pos_iff.mp <| Γ.strictWidthInfty_nonneg.lt_of_ne' fun h0 ↦ hh.ne' ?_
    simpa only [h0, AddSubgroup.zmultiples_zero_eq_bot, AddSubgroup.mem_bot] using hΓ
  rcases eq_or_ne q 0 with rfl | hq'
  · exact (periodic_comp_ofComplex f hΓ).differentiableAt_cuspFunction_zero hh
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        (fun _ ↦ differentiableAt_comp_ofComplex f))
      (bounded_at_infty_comp_ofComplex f hi)
  · exact Periodic.qParam_right_inv hh.ne' hq' ▸
      (periodic_comp_ofComplex f hΓ).differentiableAt_cuspFunction hh.ne'
        <| differentiableAt_comp_ofComplex _ <| Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq'

lemma analyticAt_cuspFunction_zero [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    AnalyticAt ℂ (cuspFunction h f) 0 :=
  DifferentiableOn.analyticAt
    (fun q hq ↦ (differentiableAt_cuspFunction _ hh hΓ hq).differentiableWithinAt)
    (by simpa only [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

variable (h) in
/-- The `q`-expansion of a level `n` modular form, bundled as a `PowerSeries`. -/
def qExpansion : PowerSeries ℂ :=
  .mk fun m ↦ (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0

lemma qExpansion_coeff (m : ℕ) :
    (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0 := by
  simp [qExpansion]

lemma hasSum_qExpansion_of_abs_lt [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ ↦ (qExpansion h f).coeff m • q ^ m) (cuspFunction h f q) := by
  simp only [qExpansion_coeff]
  have hdiff : DifferentiableOn ℂ (cuspFunction h f) (Metric.ball 0 1) := by
    refine fun z hz ↦ (differentiableAt_cuspFunction f hh hΓ ?_).differentiableWithinAt
    simpa using hz
  have qmem : q ∈ Metric.ball 0 1 := by simpa using hq
  convert hasSum_taylorSeries_on_ball hdiff qmem using 2 with m
  rw [sub_zero, smul_eq_mul, smul_eq_mul, mul_right_comm, smul_eq_mul, mul_assoc]

lemma hasSum_qExpansion [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion h f).coeff m • 𝕢 h τ ^ m) (f τ) := by
  have : ‖𝕢 h τ‖ < 1 := by simp [Periodic.qParam, Complex.norm_exp, neg_div]; positivity
  simpa only [eq_cuspFunction f _ hΓ hh.ne'] using hasSum_qExpansion_of_abs_lt f hh hΓ this

variable (h) in
/--
The `q`-expansion of a level `n` modular form, bundled as a `FormalMultilinearSeries`.

TODO: Maybe get rid of this and instead define a general API for converting `PowerSeries` to
`FormalMultilinearSeries`.
-/
def qExpansionFormalMultilinearSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  fun m ↦ (qExpansion h f).coeff m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m _

lemma qExpansionFormalMultilinearSeries_apply_norm (m : ℕ) :
    ‖qExpansionFormalMultilinearSeries h f m‖ = ‖(qExpansion h f).coeff m‖ := by
  rw [qExpansionFormalMultilinearSeries,
    ← (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin m) ℂ).symm.norm_map]
  simp

lemma qExpansionFormalMultilinearSeries_radius [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    1 ≤ (qExpansionFormalMultilinearSeries h f).radius := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
  lift r to NNReal using hr.ne_top
  apply FormalMultilinearSeries.le_radius_of_summable
  simp only [qExpansionFormalMultilinearSeries_apply_norm]
  rw [← r.abs_eq]
  simp_rw [← Real.norm_eq_abs, ← Complex.norm_real, ← norm_pow, ← norm_mul]
  exact (hasSum_qExpansion_of_abs_lt f hh hΓ (q := r) (by simpa using hr)).summable.norm

/-- The `q`-expansion of `f` is an `FPowerSeries` representing `cuspFunction n f`. -/
lemma hasFPowerSeries_cuspFunction [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    HasFPowerSeriesOnBall (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 1 := by
  refine ⟨qExpansionFormalMultilinearSeries_radius f hh hΓ, zero_lt_one, fun hy ↦ ?_⟩
  rw [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
    ← NNReal.coe_lt_one, coe_nnnorm] at hy
  simpa [qExpansionFormalMultilinearSeries] using hasSum_qExpansion_of_abs_lt f hh hΓ hy

end ModularFormClass

open ModularFormClass

namespace CuspFormClass

theorem zero_at_infty_comp_ofComplex [CuspFormClass F Γ k] (hi : IsCusp OnePoint.infty Γ) :
    ZeroAtFilter I∞ (f ∘ ofComplex) :=
  (OnePoint.isZeroAt_infty_iff.mp (zero_at_cusps f hi)).comp tendsto_comap_im_ofComplex

theorem cuspFunction_apply_zero [CuspFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    cuspFunction h f 0 = 0 :=
  have hi : IsCusp OnePoint.infty Γ := by
    rw [Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty] at hΓ
    refine Γ.strictWidthInfty_pos_iff.mp <| Γ.strictWidthInfty_nonneg.lt_of_ne' fun h0 ↦ hh.ne' ?_
    simpa only [h0, AddSubgroup.zmultiples_zero_eq_bot, AddSubgroup.mem_bot] using hΓ
  Periodic.cuspFunction_zero_of_zero_at_inf hh (zero_at_infty_comp_ofComplex f hi)

theorem exp_decay_atImInfty [CuspFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / h) := by
  have hi : IsCusp OnePoint.infty Γ := by
    rw [Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty] at hΓ
    refine Γ.strictWidthInfty_pos_iff.mp <| Γ.strictWidthInfty_nonneg.lt_of_ne' fun h0 ↦ hh.ne' ?_
    simpa only [h0, AddSubgroup.zmultiples_zero_eq_bot, AddSubgroup.mem_bot] using hΓ
  simpa only [neg_mul, comp_def, ofComplex_apply, coe_im] using
    ((periodic_comp_ofComplex f hΓ).exp_decay_of_zero_at_inf hh
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        fun _ ↦ differentiableAt_comp_ofComplex f)
      (zero_at_infty_comp_ofComplex f hi)).comp_tendsto tendsto_coe_atImInfty

end CuspFormClass
