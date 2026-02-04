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
public import Mathlib.Analysis.Normed.Group.Tannery

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

open ModularForm Complex Filter Function Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I

open scoped Real MatrixGroups CongruenceSubgroup

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

theorem differentiableAt_cuspFunction [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (cuspFunction h f) q := by
  rcases eq_or_ne q 0 with rfl | hq'
  · exact (periodic_comp_ofComplex f hΓ).differentiableAt_cuspFunction_zero hh
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        (fun _ ↦ differentiableAt_comp_ofComplex f))
      (bounded_at_infty_comp_ofComplex f <| Γ.isCusp_of_mem_strictPeriods hh hΓ)
  · exact Periodic.qParam_right_inv hh.ne' hq' ▸
      (periodic_comp_ofComplex f hΓ).differentiableAt_cuspFunction hh.ne'
        <| differentiableAt_comp_ofComplex _ <| Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq'

lemma differentiableOn_cuspFunction_ball [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    DifferentiableOn ℂ (cuspFunction h f) (Metric.ball 0 1) :=
  fun _ hz ↦ (differentiableAt_cuspFunction f hh hΓ <| mem_ball_zero_iff.mp hz)
    |>.differentiableWithinAt

lemma analyticAt_cuspFunction_zero [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    AnalyticAt ℂ (cuspFunction h f) 0 :=
  DifferentiableOn.analyticAt
    (fun q hq ↦ (differentiableAt_cuspFunction _ hh hΓ hq).differentiableWithinAt)
    (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

lemma cuspFunction_apply_zero [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
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

lemma qExpansion_coeff_zero [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    (qExpansion h f).coeff 0 = valueAtInfty f := by
  simp [qExpansion_coeff, cuspFunction_apply_zero f hh hΓ]

lemma hasSum_qExpansion_of_norm_lt [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ ↦ (qExpansion h f).coeff m • q ^ m) (cuspFunction h f q) := by
  convert hasSum_taylorSeries_on_ball (differentiableOn_cuspFunction_ball f hh hΓ)
    (by simpa using hq) using 2 with m
  grind [qExpansion_coeff, sub_zero, smul_eq_mul]

@[deprecated (since := "2025-12-04")] alias hasSum_qExpansion_of_abs_lt :=
  hasSum_qExpansion_of_norm_lt

lemma hasSum_qExpansion [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (τ : ℍ) :
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
  exact (hasSum_qExpansion_of_norm_lt f hh hΓ (q := r) (by simpa using hr)).summable.norm

/-- The `q`-expansion of `f` is an `FPowerSeries` representing `cuspFunction n f`. -/
lemma hasFPowerSeries_cuspFunction [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    HasFPowerSeriesOnBall (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 1 := by
  refine ⟨qExpansionFormalMultilinearSeries_radius f hh hΓ, zero_lt_one, fun hy ↦ ?_⟩
  rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
    ← NNReal.coe_lt_one, coe_nnnorm] at hy
  simpa [qExpansionFormalMultilinearSeries] using hasSum_qExpansion_of_norm_lt f hh hΓ hy

/-- The `q`-expansion coefficient can be expressed as a `circleIntegral` for any radius `0 < R < 1`.
-/
lemma qExpansion_coeff_eq_circleIntegral [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (n : ℕ) {R : ℝ} (hR : 0 < R) (hR' : R < 1) :
    (qExpansion h f).coeff n =
      ((2 * π * I)⁻¹ * ∮ (z : ℂ) in C(0, R), cuspFunction h f z / z ^ (n + 1)) := by
  have := ((differentiableOn_cuspFunction_ball f hh hΓ).mono
    (Metric.closedBall_subset_ball hR')).circleIntegral_one_div_sub_center_pow_smul hR n
  rw [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, ← div_eq_iff two_pi_I_ne_zero] at this
  simp_rw [qExpansion, PowerSeries.coeff_mk, ← this, sub_zero, smul_eq_mul, one_div_mul_eq_div,
    div_eq_inv_mul]

/--
If `h` is a positive strict period of `f`, then the `q`-expansion coefficient can be expressed
as an integral along a horizontal line in the upper half-plane from `t * I` to `h + t * I`, for
any `0 < t`.
-/
lemma qExpansion_coeff_eq_intervalIntegral [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (n : ℕ)
    {t : ℝ} (ht : 0 < t) : (qExpansion h f).coeff n =
    1 / h * ∫ u in (0)..h, 1 / 𝕢 h (u + t * I) ^ n * f (⟨u + t * I, by simpa using ht⟩) := by
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

theorem exp_decay_sub_atImInfty [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    (fun τ ↦ f τ - valueAtInfty f) =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / h) := by
  have hi : IsCusp OnePoint.infty Γ := Γ.isCusp_of_mem_strictPeriods hh hΓ
  convert ((periodic_comp_ofComplex f hΓ).exp_decay_sub_of_bounded_at_inf hh
    (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        fun _ ↦ differentiableAt_comp_ofComplex f)
    (bounded_at_infty_comp_ofComplex f hi)).comp_tendsto tendsto_coe_atImInfty
  simp [← cuspFunction_apply_zero f hh hΓ, cuspFunction]

/-- Version of `exp_decay_sub_atImInfty` stating a less precise result but easier to apply in
practice (not specifying the growth rate precisely). Note that the `Fact` hypothesis is
automatically synthesized for arithmetic subgroups. -/
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

theorem exp_decay_atImInfty [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (hf : IsZeroAtImInfty f) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
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

variable [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]

theorem cuspFunction_apply_zero (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    cuspFunction h f 0 = 0 :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  (CuspFormClass.zero_at_infty f).cuspFunction_apply_zero hh

theorem exp_decay_atImInfty (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / h) :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  (CuspFormClass.zero_at_infty f).exp_decay_atImInfty hh hΓ

theorem exp_decay_atImInfty' [Fact (IsCusp OnePoint.infty Γ)] :
    ∃ c > 0, f =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im) :=
  (CuspFormClass.zero_at_infty f).exp_decay_atImInfty'

end CuspFormClass

section ring

open Metric Set

open scoped Topology

lemma periodic_tendsto_nhds_zero {f : ℂ → ℂ} (hcts : ContinuousAt (Periodic.cuspFunction h f) 0) :
    Tendsto (fun x ↦ f (Periodic.invQParam h x)) (𝓝[≠] 0) (𝓝 (Periodic.cuspFunction h f 0)) := by
  apply (tendsto_nhdsWithin_of_tendsto_nhds hcts.tendsto).congr'
  rw [eventuallyEq_nhdsWithin_iff, eventually_iff_exists_mem]
  refine ⟨ball 0 1, Metric.ball_mem_nhds _ Real.zero_lt_one , ?_⟩
  intro y hy hy0
  apply Function.Periodic.cuspFunction_eq_of_nonzero
  simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using hy0

theorem cuspFunction_mul_zero {f g : ℂ → ℂ} (hfcts : ContinuousAt (Periodic.cuspFunction h f) 0)
    (hgcts : ContinuousAt (Periodic.cuspFunction h g) 0) : Periodic.cuspFunction h (f * g) 0 =
    Periodic.cuspFunction h f 0 * Periodic.cuspFunction h g 0 := by
  rw [Periodic.cuspFunction, update_self]
  apply Filter.Tendsto.limUnder_eq
  exact Filter.Tendsto.mul (periodic_tendsto_nhds_zero hfcts)
    (periodic_tendsto_nhds_zero hgcts)

lemma qExpansion_mul_coeff_zero {f g : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    (qExpansion h (f * g)).coeff 0 = ((qExpansion h f).coeff 0) * (qExpansion h g).coeff 0 := by
  simpa [qExpansion_coeff] using cuspFunction_mul_zero hfcts hgcts

lemma cuspFunction_mul {f g : ℍ → ℂ}
    (hfcts : ContinuousAt (cuspFunction h f) 0) (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f * g) = cuspFunction h f * cuspFunction h g := by
  ext z
  by_cases H : z = 0
  · rw [H]
    simp only [Pi.mul_apply]
    apply cuspFunction_mul_zero hfcts hgcts
  · simp [cuspFunction, Periodic.cuspFunction, H]

lemma cuspFunction_modularForm_mul [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ] {a b : ℤ}
    (f : ModularForm Γ a) (g : ModularForm Γ b) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    cuspFunction h (f.mul g) = cuspFunction h f * cuspFunction h g := by
  exact cuspFunction_mul (analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (analyticAt_cuspFunction_zero g hh hΓ).continuousAt

lemma cuspFunction_smul {f : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0) (a : ℂ) :
    cuspFunction h (a • f) = a • cuspFunction h f := by
  simp only [cuspFunction, Periodic.cuspFunction] at *
  ext y
  obtain rfl | hy := eq_or_ne y 0; swap
  · simp [hy]
  · simpa using Filter.Tendsto.limUnder_eq (Filter.Tendsto.const_mul _ (by simpa using hfcts))

lemma cuspFunction_neg {f : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0) :
    cuspFunction h (-f) = - cuspFunction h f := by
  simpa using cuspFunction_smul hfcts (-1)

lemma cuspFunction_add {f g : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f + g) = cuspFunction h f + cuspFunction h g := by
  simp only [cuspFunction, Periodic.cuspFunction]
  ext y
  obtain rfl | hy := eq_or_ne y 0; swap
  · simp [hy]
  · have : ((f + g) ∘ ↑ofComplex) ∘ Periodic.invQParam h =
      (f ∘ ↑ofComplex) ∘ Periodic.invQParam h + (g ∘ ↑ofComplex) ∘ Periodic.invQParam h := by
      ext y
      simp
    simp only [Pi.add_apply, update_self] at *
    rw [this, Filter.Tendsto.limUnder_eq]
    exact Tendsto.add (tendsto_nhds_limUnder (Exists.intro _ (periodic_tendsto_nhds_zero hfcts)))
      (tendsto_nhds_limUnder (Exists.intro _ (periodic_tendsto_nhds_zero hgcts)))

lemma cuspFunction_sub {f g : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f - g) = cuspFunction h f - cuspFunction h g := by
  simp_rw [sub_eq_add_neg, ← (cuspFunction_neg hgcts)]
  apply cuspFunction_add hfcts (by simp [cuspFunction_neg hgcts, hgcts])

open Nat in
lemma qExpansion_mul {f g : ℍ → ℂ} {s : Set ℂ} (hsO : IsOpen s) (hs : 0 ∈ s)
    (hf : ContDiffOn ℂ ⊤ (cuspFunction h f) s) (hg : ContDiffOn ℂ ⊤ (cuspFunction h g) s) :
    qExpansion h (f * g) = qExpansion h f * qExpansion h g := by
  ext m
  induction m with
  | zero =>
    simpa using qExpansion_mul_coeff_zero
      (hf.continuousOn.continuousAt ((IsOpen.mem_nhds_iff hsO).mpr hs))
      (hg.continuousOn.continuousAt ((IsOpen.mem_nhds_iff hsO).mpr hs))
  | succ m hm =>
    have H := cuspFunction_mul (hf.continuousOn.continuousAt ((IsOpen.mem_nhds_iff hsO).mpr hs))
      (hg.continuousOn.continuousAt ((IsOpen.mem_nhds_iff hsO).mpr hs))
    have := iteratedDerivWithin_mul hs hsO.uniqueDiffOn (n := m + 1)
      (((hf.contDiffWithinAt hs).of_le le_top)) (((hg.contDiffWithinAt hs).of_le le_top))
    simp_rw [iteratedDerivWithin_of_isOpen (n := m + 1) hsO hs] at this
    conv at this =>
      enter [2,2,n]
      rw [iteratedDerivWithin_of_isOpen hsO hs, iteratedDerivWithin_of_isOpen hsO hs]
    simp only [qExpansion_coeff, H, PowerSeries.coeff_mul, this]
    have h0 : ((m + 1)! : ℂ) ≠ 0 := by
      simp [Nat.factorial_ne_zero (m + 1)]
    rw [inv_mul_eq_iff_eq_mul₀ h0, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.mul_sum, Nat.succ_eq_add_one]
    have ht (x : ℕ) : ↑(m + 1)! *
      ((↑x !)⁻¹ * iteratedDeriv x (cuspFunction h f) 0 *
        ((↑(m + 1 - x)!)⁻¹ * iteratedDeriv (m + 1 - x) (cuspFunction h g) 0)) =
        (↑(m + 1)! *
      ((↑x !)⁻¹ * ((↑(m + 1 - x)!)⁻¹) * iteratedDeriv x (cuspFunction h f) 0 *
        iteratedDeriv (m + 1 - x) (cuspFunction h g) 0)) := by ring
    simp_rw [ht]
    apply Finset.sum_congr rfl (fun x hx ↦ ?_)
    grind [Nat.cast_choose ℂ (b := m + 1) (a := x) (by grind)]

lemma qExpansion_modularForm_mul [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ] (a b : ℤ)
    (f : ModularForm Γ a) (g : ModularForm Γ b) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    qExpansion h (f.mul g) = qExpansion h f * qExpansion h g := by
  apply qExpansion_mul (s := Metric.ball 0 1) (isOpen_ball) (by simp)
  · refine DifferentiableOn.contDiffOn (fun y hy ↦ ?_) (isOpen_ball)
    exact (differentiableAt_cuspFunction f hh hΓ (by simpa using hy)).differentiableWithinAt
  · refine DifferentiableOn.contDiffOn (fun y hy ↦ ?_) (isOpen_ball)
    exact (differentiableAt_cuspFunction g hh hΓ (by simpa using hy)).differentiableWithinAt

lemma qExpansion_add {G : Type*} [FunLike G ℍ ℂ] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    {a b : ℤ} (f : F) [ModularFormClass F Γ a] (g : G) [ModularFormClass G Γ b] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) : qExpansion h (f + g) = qExpansion h f + qExpansion h g := by
  ext m
  have := cuspFunction_add (f := f) (g := g) (h := h)
   (analyticAt_cuspFunction_zero f hh hΓ).continuousAt
   (analyticAt_cuspFunction_zero g hh hΓ).continuousAt
  · simp only [qExpansion, this, PowerSeries.coeff_mk, map_add]
    rw [iteratedDeriv_add]
    · ring
    · apply ContDiffOn.contDiffAt  (s := Metric.ball 0 1) ?_ (ball_mem_nhds 0 (by simp))
      refine DifferentiableOn.contDiffOn (fun y hy ↦ ?_) (isOpen_ball)
      exact (differentiableAt_cuspFunction f hh hΓ (by simpa using hy)).differentiableWithinAt
    · apply ContDiffOn.contDiffAt  (s := Metric.ball 0 1) ?_ (ball_mem_nhds 0 (by simp))
      refine DifferentiableOn.contDiffOn (fun y hy ↦ ?_) (isOpen_ball)
      exact (differentiableAt_cuspFunction g hh hΓ (by simpa using hy)).differentiableWithinAt

lemma qExpansion_smul [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (a : ℂ) (f : F) [ModularFormClass F Γ k] :
    (qExpansion h (a • f)) = (a • qExpansion h f) := by
  ext m
  simp_rw [_root_.map_smul, smul_eq_mul, qExpansion, PowerSeries.coeff_mk, cuspFunction_smul
    (analyticAt_cuspFunction_zero f hh hΓ).continuousAt, iteratedDeriv_fun_const_smul]
  grind [Pi.smul_apply, smul_eq_mul]

lemma qExpansion_neg [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : F) [ModularFormClass F Γ k] :
    qExpansion h (-f) = - (qExpansion h f) := by
  simpa using (qExpansion_smul hh hΓ (-1 : ℂ) f)

lemma qExpansion_zero (hh : 0 < h) : qExpansion h 0 = 0 := by
  ext m
  have := cuspFunction_smul (f := 0) (h := h) ?_ 0
  · simp only [smul_zero, zero_smul, qExpansion, PowerSeries.coeff_mk, map_zero, mul_eq_zero,
      inv_eq_zero, Nat.cast_eq_zero] at *
    rw [this]
    by_cases hm : m = 0
    · simp only [hm, Nat.factorial_zero, one_ne_zero, iteratedDeriv_zero, Pi.zero_apply, or_true]
    · right
      simpa [hm] using iteratedDeriv_const (𝕜 := ℂ) (F := ℂ) (x := 0) (c := 0) (n := m)
  apply (Function.Periodic.differentiableAt_cuspFunction_zero hh (by simp) (by simp) _).continuousAt
  simpa using ZeroAtFilter.boundedAtFilter (zero_zeroAtFilter I∞)

lemma qExpansion_injective [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (i : ℤ) (f : ModularForm Γ i) :
    qExpansion h f = 0 ↔ f = 0 := by
  refine ⟨fun H ↦ ?_, fun H ↦ (by simp [H, qExpansion_zero hh])⟩
  ext z
  simp [← (hasSum_qExpansion f hh hΓ z).tsum_eq, H]

/-- The qExpansion map as an additive group hom. to power series over `ℂ`. -/
def qExpansionAddHom [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (i : ℤ) : ModularForm Γ i →+ PowerSeries ℂ where
  toFun f := qExpansion h f
  map_zero' := by rw [qExpansion_injective hh hΓ]
  map_add' f g := qExpansion_add f g hh hΓ

lemma qExpansion_one [Γ.HasDetPlusMinusOne] : qExpansion h (1 : ModularForm Γ 0) = 1 := by
  ext m
  rw [qExpansion_coeff]
  by_cases hm : m = 0
  · simpa [hm, cuspFunction, Periodic.cuspFunction] using
      Filter.Tendsto.limUnder_eq tendsto_const_nhds
  · simp only [cuspFunction, Periodic.cuspFunction, one_coe_eq_one, Pi.one_comp,
    PowerSeries.coeff_one, hm, ↓reduceIte, mul_eq_zero, inv_eq_zero, Nat.cast_eq_zero,
    Nat.factorial_ne_zero, false_or]
    have := iteratedDeriv_const (𝕜 := ℂ) (F := ℂ) (x := 0) (c := 1) (n := m)
    simp only [hm] at this
    convert this
    next z =>
      by_cases hz : z = 0
      · rw [hz]
        simpa [update_self] using Filter.Tendsto.limUnder_eq tendsto_const_nhds
      · simp [hz]

open scoped DirectSum in
/-- The qExpansion map as a map from the graded ring of modular forms to power series over `ℂ`. -/
def qExpansionRingHom [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) : (⨁ i, ModularForm Γ i) →+* (PowerSeries ℂ) := by
  apply DirectSum.toSemiring (qExpansionAddHom hh hΓ)
  · simpa [qExpansionAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using qExpansion_one
  · intro a b f g
    simpa [qExpansionAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      using qExpansion_modularForm_mul a b f g hh hΓ

@[simp]
lemma qExpansionRingHom_apply [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (i : ℤ) (f : ModularForm Γ i) :
    qExpansionRingHom hh hΓ (DirectSum.of _ i f) = qExpansion h f := by
  simp [qExpansionRingHom, qExpansionAddHom]

lemma qExpansion_of_mul [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (a b : ℤ) (f : ModularForm Γ a) (g : ModularForm Γ b) :
    qExpansion h ((((DirectSum.of _ a f)) * (DirectSum.of _ b g)) (a + b)) =
    (qExpansion h f) * (qExpansion h g) := by
  have := (qExpansionRingHom hh hΓ).map_mul (DirectSum.of _ a f) (DirectSum.of _ b g)
  simpa [DirectSum.of_mul_of]

lemma qExpansion_of_pow [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (f : ModularForm Γ k) (n : ℕ) :
    qExpansion h ((((DirectSum.of _ k f)) ^ n) (n * k)) = (qExpansion h f) ^ n := by
  have := (qExpansionRingHom hh hΓ).map_pow (DirectSum.of _ k f) n
  simpa [ DirectSum.ofPow]

lemma qExpansion_sub [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ] (a b : ℤ)
    (f : ModularForm Γ a) (g : ModularForm Γ b) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    qExpansion h (f - g) = qExpansion h f - qExpansion h g := by
  simp_rw [sub_eq_add_neg, ← (qExpansion_neg hh hΓ g)]
  exact (qExpansion_add f ( -g) hh hΓ)

end ring

section uniqueness

open Metric Topology

private lemma hasSum_cuspFunction_of_hasSum_annulus [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    {F : Type*} [FunLike F ℍ ℂ] {k : ℤ} [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (c : ℕ → ℂ) (f : F)
    (hf : ∀ (τ : ℍ), HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) {q : ℂ} (hq : ‖q‖ < 1)
    (hq1 : q ≠ 0) : HasSum (fun m ↦ c m • q ^ m) (cuspFunction h f q) := by
  have h1 := Function.Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
  have h2 := hf ⟨(Periodic.invQParam h q), h1⟩
  have := eq_cuspFunction (h := h) f ⟨(Periodic.invQParam h q), h1⟩ hΓ (by grind)
  simp only [smul_eq_mul, ne_eq, coe_mk_subtype] at *
  rw [Function.Periodic.qParam_right_inv (by grind) hq1] at this h2
  simpa [← this] using h2

-- This is a bit ugly, is there a nicer way to prove this?
lemma cuspFunction_zero_eq_const_coeff {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
     {h : ℝ} [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
     (c : ℕ → ℂ) (f : F) [ModularFormClass F Γ k]
     (hf : ∀ (τ : ℍ), HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) : cuspFunction h f 0 = c 0 := by
  rw [cuspFunction, Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
  apply Filter.Tendsto.limUnder_eq
  have (q : ℂ) := hasSum_cuspFunction_of_hasSum_annulus hh hΓ c f hf (q := q)
  have htt : Tendsto (fun q ↦ ∑' m, c m * q ^ m) (𝓝[≠] 0) (𝓝 (c 0)) := by
    have hD := tendsto_tsum_of_dominated_convergence (𝓕 := (𝓝[≠] (0 : ℂ)))
      (f := fun q : ℂ ↦ fun m : ℕ ↦ c m * q ^ m) (g := fun m ↦ c m * 0 ^ m)
      (bound := fun m ↦ ‖c m‖ * (1 / 2 ) ^ m ) ?_ ?_ ?_
    · convert hD
      rw [Summable.tsum_eq_zero_add (by simpa [← summable_nat_add_iff 1] using summable_zero)]
      simp
    · simpa using (this (1/2) (by norm_num)
        (by apply one_div_ne_zero; exact Ne.symm (NeZero.ne' 2))).summable.norm
    · exact fun k ↦ Tendsto.const_mul (c k)
        (Tendsto.mono_left (Continuous.tendsto (continuous_pow k) 0) nhdsWithin_le_nhds)
    · rw [eventually_iff_exists_mem]
      use {z | (z : ℂ) ≠ 0 ∧ ‖z‖ < 1 / 2}
      constructor
      · rw [@mem_nhdsWithin_iff]
        refine ⟨1 / 2, by norm_num, fun y hy ↦ by aesop⟩
      · intro y hy k
        simp only [norm_mul, norm_pow]
        gcongr
        grind
  apply htt.congr'
  rw [@eventuallyEq_nhdsWithin_iff, eventually_nhds_iff_ball]
  refine ⟨1, by simpa using fun y hy hy0 ↦ (this y hy hy0).tsum_eq⟩

lemma hasSum_cuspFunction_of_hasSum [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (c : ℕ → ℂ) (f : F) [ModularFormClass F Γ k]
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (c m) • 𝕢 h τ ^ m) (f τ)) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ ↦ c m • q ^ m) (cuspFunction h f q) := by
  by_cases hq1 : q = 0
  · simp_rw [hq1, cuspFunction_zero_eq_const_coeff hh hΓ c f hf, smul_eq_mul]
    rw [Summable.hasSum_iff (by simpa [← summable_nat_add_iff 1] using summable_zero),
      Summable.tsum_eq_zero_add (by simpa [← summable_nat_add_iff 1] using summable_zero)]
    simp
  · exact hasSum_cuspFunction_of_hasSum_annulus hh hΓ c f hf hq hq1

private lemma qParam_onto_annulus (r h : ℝ) (hr : 0 < r) (hr2 : r < 1) (hh : 0 < h) :
    ∃ (z : ℍ), ‖𝕢 h z‖ = r := by
  use ⟨Periodic.invQParam h r, ?_⟩
  · have hq := Function.Periodic.qParam_right_inv (h := h) (q := r) (by grind) (by aesop)
    simp [UpperHalfPlane.coe, hq, hr.le]
  · rw [Function.Periodic.im_invQParam, norm_real, Real.norm_eq_abs, Real.log_abs, mul_pos_iff]
    right
    refine ⟨div_neg_of_neg_of_pos (by simp [hh]) (Real.two_pi_pos), (Real.log_neg_iff hr).mpr hr2⟩

lemma qExpansion_coeff_unique [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ] (c : ℕ → ℂ) (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (f : F) [ModularFormClass F Γ k]
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (c m) • 𝕢 h τ ^ m) (f τ)) :
    c = (fun m ↦ (qExpansion h f).coeff m) := by
  -- idea: use uniqueness of formal multilinear series representing a function.
  ext m
  have h0 := hasFPowerSeries_cuspFunction (h := h) f hh hΓ
  let qExpansion2 : PowerSeries ℂ := .mk fun m ↦ c m
  let qq : FormalMultilinearSeries ℂ ℂ ℂ :=
    fun m ↦ (qExpansion2).coeff m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m _
  have hqq2 (m : ℕ) : ‖qq m‖ = ‖qExpansion2.coeff m‖ := by
    unfold qq
    rw [← (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin m) ℂ).symm.norm_map]
    simp only [_root_.map_smul, smul_eq_mul, norm_mul,
      LinearIsometryEquiv.norm_map, ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one]
  have H2 : HasFPowerSeriesOnBall (cuspFunction h f) qq 0 1 := by
    have H21 : 1 ≤ qq.radius := by
        refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
        lift r to NNReal using hr.ne_top
        apply FormalMultilinearSeries.le_radius_of_summable
        simp only [hqq2, PowerSeries.coeff_mk, qExpansion2]
        by_cases hr0 : r = 0
        · simpa [hr0, ← summable_nat_add_iff 1] using summable_zero
        · obtain ⟨z, hz⟩ := qParam_onto_annulus r h ((by simp [pos_iff_ne_zero.mpr hr0] ))
            (by simpa using hr) hh
          simpa [NNReal.coe_pow, ← hz] using (summable_norm_iff.mpr (hf z).summable)
    refine ⟨H21 , zero_lt_one, ?_⟩
    intro y hy
    simp only [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
      ← NNReal.coe_lt_one, coe_nnnorm, zero_add] at hy ⊢
    apply (hasSum_cuspFunction_of_hasSum hh hΓ c f hf hy).congr
    simp [smul_eq_mul, PowerSeries.coeff_mk, qq, qExpansion2]
  have h3 : HasFPowerSeriesAt (cuspFunction h f) qq 0 := by
    use 1
  have h4 : HasFPowerSeriesAt (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 := by
    use 1
  have := FormalMultilinearSeries.ext_iff.mp (HasFPowerSeriesAt.eq_formalMultilinearSeries h3 h4) m
  simp only [PowerSeries.coeff_mk, qExpansionFormalMultilinearSeries, qq, qExpansion2] at this
  have htv : (c m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ).toFun = ((PowerSeries.coeff m)
    (qExpansion h f) • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ).toFun := by
    rw [this]
  simpa [Pi.natCast_def, qExpansion2, qq] using (congrFun htv m)


end uniqueness
