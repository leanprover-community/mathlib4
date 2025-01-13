/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# q-expansions of modular forms

We show that a modular form of level `Γ(n)` can be written as `τ ↦ F (𝕢 n τ)` where `F` is
analytic on the open unit disc, and `𝕢 n` is the parameter `τ ↦ exp (2 * I * π * τ / n)`. As an
application, we show that cusp forms decay exponentially to 0 as `im τ → ∞`.

## TO DO:

* generalise to handle arbitrary finite-index subgroups (not just `Γ(n)` for some `n`)
* define the `q`-expansion as a formal power series
-/

open ModularForm Complex Filter UpperHalfPlane Function

open scoped Real MatrixGroups CongruenceSubgroup

noncomputable section

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

local notation "I∞" => comap Complex.im atTop
local notation "𝕢" => Periodic.qParam

theorem Function.Periodic.im_invQParam_pos_of_abs_lt_one
    {h : ℝ} (hh : 0 < h) {q : ℂ} (hq : q.abs < 1) (hq_ne : q ≠ 0) :
    0 < im (Periodic.invQParam h q) :=
  im_invQParam .. ▸ mul_pos_of_neg_of_neg
    (div_neg_of_neg_of_pos (neg_lt_zero.mpr hh) Real.two_pi_pos)
    ((Real.log_neg_iff (abs.pos hq_ne)).mpr hq)

lemma Function.Periodic.abs_qParam_le_of_one_half_le_im {ξ : ℂ} (hξ : 1 / 2 ≤ ξ.im) :
    ‖𝕢 1 ξ‖ ≤ rexp (-π) := by
  rwa [Periodic.qParam, ofReal_one, div_one, norm_eq_abs, abs_exp, Real.exp_le_exp,
    mul_right_comm, mul_I_re, neg_le_neg_iff, ← ofReal_ofNat, ← ofReal_mul, im_ofReal_mul,
    mul_comm _ π, mul_assoc, le_mul_iff_one_le_right Real.pi_pos, ← div_le_iff₀' two_pos]

theorem UpperHalfPlane.abs_qParam_lt_one (n : ℕ) [NeZero n] (τ : ℍ) : (𝕢 n τ).abs < 1 := by
  rw [Periodic.abs_qParam, Real.exp_lt_one_iff, neg_mul, coe_im, neg_mul, neg_div, neg_lt_zero,
    div_pos_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero <| NeZero.ne _)]
  positivity

namespace SlashInvariantFormClass

theorem periodic_comp_ofComplex [SlashInvariantFormClass F Γ(n) k] :
    Periodic (f ∘ ofComplex) n := by
  intro w
  by_cases hw : 0 < im w
  · have : 0 < im (w + n) := by simp only [add_im, natCast_im, add_zero, hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert SlashInvariantForm.vAdd_width_periodic n k 1 f ⟨w, hw⟩ using 2
    simp only [Int.cast_one, mul_one, UpperHalfPlane.ext_iff, coe_mk_subtype, coe_vadd,
      ofReal_natCast, add_comm]
  · have : im (w + n) ≤ 0 := by simpa only [add_im, natCast_im, add_zero, not_lt] using hw
    simp only [comp_apply, ofComplex_apply_of_im_nonpos this,
      ofComplex_apply_of_im_nonpos (not_lt.mp hw)]

/--
The analytic function `F` such that `f τ = F (exp (2 * π * I * τ / n))`, extended by a choice of
limit at `0`.
-/
def cuspFunction : ℂ → ℂ := Function.Periodic.cuspFunction n (f ∘ ofComplex)

theorem eq_cuspFunction [NeZero n] [SlashInvariantFormClass F Γ(n) k] (τ : ℍ) :
    cuspFunction n f (𝕢 n τ) = f τ := by
  simpa only [comp_apply, ofComplex_apply]
    using (periodic_comp_ofComplex n f).eq_cuspFunction (NeZero.ne _) τ

end SlashInvariantFormClass

open SlashInvariantFormClass

namespace ModularFormClass

theorem differentiableAt_comp_ofComplex [ModularFormClass F Γ k] {z : ℂ} (hz : 0 < im z) :
    DifferentiableAt ℂ (f ∘ ofComplex) z :=
  mdifferentiableAt_iff_differentiableAt.mp ((holo f _).comp z (mdifferentiableAt_ofComplex hz))

theorem bounded_at_infty_comp_ofComplex [ModularFormClass F Γ k] :
    BoundedAtFilter I∞ (f ∘ ofComplex) := by
  simpa only [SlashAction.slash_one, ModularForm.toSlashInvariantForm_coe]
    using (ModularFormClass.bdd_at_infty f 1).comp_tendsto tendsto_comap_im_ofComplex

theorem differentiableAt_cuspFunction [NeZero n] [ModularFormClass F Γ(n) k]
    {q : ℂ} (hq : q.abs < 1) :
    DifferentiableAt ℂ (cuspFunction n f) q := by
  have npos : 0 < (n : ℝ) := mod_cast (Nat.pos_iff_ne_zero.mpr (NeZero.ne _))
  rcases eq_or_ne q 0 with rfl | hq'
  · exact (periodic_comp_ofComplex n f).differentiableAt_cuspFunction_zero npos
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        (fun _ ↦ differentiableAt_comp_ofComplex f))
      (bounded_at_infty_comp_ofComplex f)
  · exact Periodic.qParam_right_inv npos.ne' hq' ▸
      (periodic_comp_ofComplex n f).differentiableAt_cuspFunction npos.ne'
        <| differentiableAt_comp_ofComplex _ <| Periodic.im_invQParam_pos_of_abs_lt_one npos hq hq'

lemma analyticAt_cuspFunction_zero [NeZero n] [ModularFormClass F Γ(n) k] :
    AnalyticAt ℂ (cuspFunction n f) 0 :=
  DifferentiableOn.analyticAt
    (fun q hq ↦ (differentiableAt_cuspFunction _ _ hq).differentiableWithinAt)
    (by simpa only [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

/-- The `q`-expansion of a level `n` modular form, bundled as a `PowerSeries`. -/
def qExpansion : PowerSeries ℂ :=
  .mk fun m ↦ (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction n f) 0

lemma qExpansion_coeff (m : ℕ) :
    (qExpansion n f).coeff ℂ m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction n f) 0 := by
  simp [qExpansion]

lemma hasSum_qExpansion_of_abs_lt [NeZero n] [ModularFormClass F Γ(n) k]
    {q : ℂ} (hq : q.abs < 1) :
    HasSum (fun m : ℕ ↦ (qExpansion n f).coeff ℂ m • q ^ m) (cuspFunction n f q) := by
  simp only [qExpansion_coeff, ← eq_cuspFunction n f]
  have hdiff : DifferentiableOn ℂ (cuspFunction n f) (Metric.ball 0 1) := by
    refine fun z hz ↦ (differentiableAt_cuspFunction n f ?_).differentiableWithinAt
    simpa using hz
  have qmem : q ∈ Metric.ball 0 1 := by simpa using hq
  convert hasSum_taylorSeries_on_ball hdiff qmem using 2 with m
  rw [sub_zero, smul_eq_mul, smul_eq_mul, mul_right_comm, smul_eq_mul, mul_assoc]

lemma hasSum_qExpansion [NeZero n] [ModularFormClass F Γ(n) k] (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion n f).coeff ℂ m • 𝕢 n τ ^ m) (f τ) := by
  simpa only [eq_cuspFunction n f] using
    hasSum_qExpansion_of_abs_lt n f (τ.abs_qParam_lt_one n)

/-- The `q`-expansion of a level `n` modular form, bundled as a `FormalMultilinearSeries`. -/
def qExpansion_formalMultilinearSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  fun m ↦ (qExpansion n f).coeff ℂ m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m _

lemma qExpansion_formalMultilinearSeries_apply_norm (m : ℕ) :
    ‖qExpansion_formalMultilinearSeries n f m‖ = ‖(qExpansion n f).coeff ℂ m‖ := by
  rw [qExpansion_formalMultilinearSeries,
    ← (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin m) ℂ).symm.norm_map]
  simp

lemma qExpansion_formalMultilinearSeries_radius [NeZero n] [ModularFormClass F Γ(n) k] :
    1 ≤ (qExpansion_formalMultilinearSeries n f).radius := by
  refine le_of_forall_ge_of_dense fun r hr ↦ ?_
  lift r to NNReal using hr.ne_top
  apply FormalMultilinearSeries.le_radius_of_summable
  simp only [qExpansion_formalMultilinearSeries_apply_norm]
  rw [← r.abs_eq]
  simp_rw [pow_abs, ← Complex.abs_ofReal, ofReal_pow, ← Complex.norm_eq_abs, ← norm_mul]
  exact (hasSum_qExpansion_of_abs_lt n f (q := r) (by simpa using hr)).summable.norm

/-- The `q`-expansion of `f` is an `FPowerSeries` representing `cuspFunction n f`. -/
lemma hasFPowerSeries_cuspFunction [NeZero n] [ModularFormClass F Γ(n) k] :
    HasFPowerSeriesOnBall (cuspFunction n f) (qExpansion_formalMultilinearSeries n f) 0 1 := by
  refine ⟨qExpansion_formalMultilinearSeries_radius n f, zero_lt_one, fun hy ↦ ?_⟩
  rw [EMetric.mem_ball, edist_zero_right, ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_one,
    coe_nnnorm, norm_eq_abs] at hy
  simpa [qExpansion_formalMultilinearSeries] using hasSum_qExpansion_of_abs_lt n f hy

end ModularFormClass

open ModularFormClass

namespace CuspFormClass

theorem zero_at_infty_comp_ofComplex [CuspFormClass F Γ k] : ZeroAtFilter I∞ (f ∘ ofComplex) := by
  simpa only [SlashAction.slash_one, toSlashInvariantForm_coe]
    using (zero_at_infty f 1).comp tendsto_comap_im_ofComplex

theorem cuspFunction_apply_zero [NeZero n] [CuspFormClass F Γ(n) k] :
    cuspFunction n f 0 = 0 :=
  Periodic.cuspFunction_zero_of_zero_at_inf (mod_cast (Nat.pos_iff_ne_zero.mpr (NeZero.ne _)))
    (zero_at_infty_comp_ofComplex f)

theorem exp_decay_atImInfty [NeZero n] [CuspFormClass F Γ(n) k] :
    f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / n) := by
  simpa only [neg_mul, comp_def, ofComplex_apply, coe_im] using
    ((periodic_comp_ofComplex n f).exp_decay_of_zero_at_inf
      (mod_cast (Nat.pos_iff_ne_zero.mpr (NeZero.ne _)))
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        fun _ ↦ differentiableAt_comp_ofComplex f)
      (zero_at_infty_comp_ofComplex f)).comp_tendsto tendsto_coe_atImInfty

end CuspFormClass
