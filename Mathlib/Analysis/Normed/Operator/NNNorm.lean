/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Operator norm as an `NNNorm`

Operator norm as an `NNNorm`, i.e. taking values in non-negative reals.

-/

public section

suppress_compilation

open Bornology
open Filter hiding map_smul
open scoped NNReal Topology Uniformity
open Metric ContinuousLinearMap
open Set Real

variable {𝕜 𝕜₂ 𝕜₃ E F G : Type*}

section NontriviallySemiNormed

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]

namespace ContinuousLinearMap

theorem nnnorm_def (f : E →SL[σ₁₂] F) : ‖f‖₊ = sInf { c | ∀ x, ‖f x‖₊ ≤ c * ‖x‖₊ } := by
  ext
  rw [NNReal.coe_sInf, coe_nnnorm, norm_def, NNReal.coe_image]
  simp_rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, mem_setOf_eq, NNReal.coe_mk,
    exists_prop]

@[simp, nontriviality]
theorem opNNNorm_subsingleton [Subsingleton E] (f : E →SL[σ₁₂] F) : ‖f‖₊ = 0 :=
  NNReal.eq <| f.opNorm_subsingleton

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem opNNNorm_le_bound (f : E →SL[σ₁₂] F) (M : ℝ≥0) (hM : ∀ x, ‖f x‖₊ ≤ M * ‖x‖₊) : ‖f‖₊ ≤ M :=
  opNorm_le_bound f (zero_le (a := M)) hM

/-- If one controls the norm of every `A x`, `‖x‖₊ ≠ 0`, then one controls the norm of `A`. -/
theorem opNNNorm_le_bound' (f : E →SL[σ₁₂] F) (M : ℝ≥0) (hM : ∀ x, ‖x‖₊ ≠ 0 → ‖f x‖₊ ≤ M * ‖x‖₊) :
    ‖f‖₊ ≤ M :=
  opNorm_le_bound' f (zero_le (a := M)) fun x hx => hM x <| by rwa [← NNReal.coe_ne_zero]

/-- For a continuous real linear map `f`, if one controls the norm of every `f x`, `‖x‖₊ = 1`, then
one controls the norm of `f`. -/
theorem opNNNorm_le_of_unit_nnnorm [NormedAlgebra ℝ 𝕜] {f : E →SL[σ₁₂] F} {C : ℝ≥0}
    (hf : ∀ x, ‖x‖₊ = 1 → ‖f x‖₊ ≤ C) : ‖f‖₊ ≤ C :=
  opNorm_le_of_unit_norm C.coe_nonneg fun x hx => hf x <| by rwa [← NNReal.coe_eq_one]

theorem opNNNorm_le_of_lipschitz {f : E →SL[σ₁₂] F} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ‖f‖₊ ≤ K :=
  opNorm_le_of_lipschitz hf

theorem opNNNorm_eq_of_bounds {φ : E →SL[σ₁₂] F} (M : ℝ≥0) (h_above : ∀ x, ‖φ x‖₊ ≤ M * ‖x‖₊)
    (h_below : ∀ N, (∀ x, ‖φ x‖₊ ≤ N * ‖x‖₊) → M ≤ N) : ‖φ‖₊ = M :=
  Subtype.ext <| opNorm_eq_of_bounds (zero_le (a := M)) h_above <| Subtype.forall'.mpr h_below

theorem opNNNorm_le_iff {f : E →SL[σ₁₂] F} {C : ℝ≥0} : ‖f‖₊ ≤ C ↔ ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊ :=
  opNorm_le_iff C.2

theorem isLeast_opNNNorm (f : E →SL[σ₁₂] F) : IsLeast {C : ℝ≥0 | ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊} ‖f‖₊ := by
  simpa only [← opNNNorm_le_iff] using isLeast_Ici

theorem opNNNorm_comp_le (h : F →SL[σ₂₃] G) (f : E →SL[σ₁₂] F) : ‖h.comp f‖₊ ≤ ‖h‖₊ * ‖f‖₊ :=
  opNorm_comp_le h f

lemma opENorm_comp_le (h : F →SL[σ₂₃] G) (f : E →SL[σ₁₂] F) : ‖h.comp f‖ₑ ≤ ‖h‖ₑ * ‖f‖ₑ := by
  simpa [enorm, ← ENNReal.coe_mul] using opNNNorm_comp_le h f

theorem le_opNNNorm (f : E →SL[σ₁₂] F) (x : E) : ‖f x‖₊ ≤ ‖f‖₊ * ‖x‖₊ :=
  f.le_opNorm x

lemma le_opENorm (f : E →SL[σ₁₂] F) (x : E) : ‖f x‖ₑ ≤ ‖f‖ₑ * ‖x‖ₑ := by
  dsimp [enorm]; exact mod_cast le_opNNNorm ..

theorem nndist_le_opNNNorm (f : E →SL[σ₁₂] F) (x y : E) : nndist (f x) (f y) ≤ ‖f‖₊ * nndist x y :=
  dist_le_opNorm f x y

/-- continuous linear maps are Lipschitz continuous. -/
theorem lipschitz (f : E →SL[σ₁₂] F) : LipschitzWith ‖f‖₊ f :=
  AddMonoidHomClass.lipschitz_of_bound_nnnorm f _ f.le_opNNNorm

/-- Evaluation of a continuous linear map `f` at a point is Lipschitz continuous in `f`. -/
theorem lipschitz_apply (x : E) : LipschitzWith ‖x‖₊ fun f : E →SL[σ₁₂] F => f x :=
  lipschitzWith_iff_norm_sub_le.2 fun f g => ((f - g).le_opNorm x).trans_eq (mul_comm _ _)

theorem exists_mul_lt_apply_of_lt_opNNNorm (f : E →SL[σ₁₂] F) {r : ℝ≥0} (hr : r < ‖f‖₊) :
    ∃ x, r * ‖x‖₊ < ‖f x‖₊ := by
  simpa only [not_forall, not_le, Set.mem_setOf] using
    notMem_of_lt_csInf (nnnorm_def f ▸ hr : r < sInf { c : ℝ≥0 | ∀ x, ‖f x‖₊ ≤ c * ‖x‖₊ })
      (OrderBot.bddBelow _)

theorem exists_mul_lt_of_lt_opNorm (f : E →SL[σ₁₂] F) {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < ‖f‖) :
    ∃ x, r * ‖x‖ < ‖f x‖ := by
  lift r to ℝ≥0 using hr₀
  exact f.exists_mul_lt_apply_of_lt_opNNNorm hr

end ContinuousLinearMap

namespace ContinuousLinearEquiv
variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

protected theorem lipschitz (e : E ≃SL[σ₁₂] F) : LipschitzWith ‖(e : E →SL[σ₁₂] F)‖₊ e :=
  (e : E →SL[σ₁₂] F).lipschitz

end ContinuousLinearEquiv

end NontriviallySemiNormed

section DenselyNormedDomain
variable [NormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

namespace ContinuousLinearMap

theorem exists_lt_apply_of_lt_opNNNorm (f : E →SL[σ₁₂] F) {r : ℝ≥0}
    (hr : r < ‖f‖₊) : ∃ x : E, ‖x‖₊ < 1 ∧ r < ‖f x‖₊ := by
  obtain ⟨y, hy⟩ := f.exists_mul_lt_apply_of_lt_opNNNorm hr
  have hy' : ‖y‖₊ ≠ 0 :=
    nnnorm_ne_zero_iff.2 fun heq => by
      simp [heq, nnnorm_zero, map_zero] at hy
  have hfy : ‖f y‖₊ ≠ 0 := hy.ne_zero
  rw [← inv_inv ‖f y‖₊, NNReal.lt_inv_iff_mul_lt (inv_ne_zero hfy), mul_assoc, mul_comm ‖y‖₊, ←
    mul_assoc, ← NNReal.lt_inv_iff_mul_lt hy'] at hy
  obtain ⟨k, hk₁, hk₂⟩ := NormedField.exists_lt_nnnorm_lt 𝕜 hy
  refine ⟨k • y, (nnnorm_smul k y).symm ▸ (NNReal.lt_inv_iff_mul_lt hy').1 hk₂, ?_⟩
  rwa [map_smulₛₗ f, nnnorm_smul, ← div_lt_iff₀ hfy.bot_lt, div_eq_mul_inv,
    RingHomIsometric.nnnorm_map]

theorem exists_lt_apply_of_lt_opNorm (f : E →SL[σ₁₂] F) {r : ℝ}
    (hr : r < ‖f‖) : ∃ x : E, ‖x‖ < 1 ∧ r < ‖f x‖ := by
  by_cases hr₀ : r < 0
  · exact ⟨0, by simpa using hr₀⟩
  · lift r to ℝ≥0 using not_lt.1 hr₀
    exact f.exists_lt_apply_of_lt_opNNNorm hr

theorem sSup_unit_ball_eq_nnnorm (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' ball 0 1) = ‖f‖₊ := by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ((nonempty_ball.mpr zero_lt_one).image _) ?_
    fun ub hub => ?_
  · rintro - ⟨x, hx, rfl⟩
    simpa only [mul_one] using f.le_opNorm_of_le (mem_ball_zero_iff.1 hx).le
  · obtain ⟨x, hx, hxf⟩ := f.exists_lt_apply_of_lt_opNNNorm hub
    exact ⟨_, ⟨x, mem_ball_zero_iff.2 hx, rfl⟩, hxf⟩

theorem sSup_unit_ball_eq_norm (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' ball 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using NNReal.coe_inj.2 f.sSup_unit_ball_eq_nnnorm

theorem sSup_unitClosedBall_eq_nnnorm (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' closedBall 0 1) = ‖f‖₊ := by
  have hbdd : ∀ y ∈ (fun x => ‖f x‖₊) '' closedBall 0 1, y ≤ ‖f‖₊ := by
    rintro - ⟨x, hx, rfl⟩
    exact f.unit_le_opNorm x (mem_closedBall_zero_iff.1 hx)
  refine le_antisymm (csSup_le ((nonempty_closedBall.mpr zero_le_one).image _) hbdd) ?_
  rw [← sSup_unit_ball_eq_nnnorm]
  gcongr
  exacts [⟨‖f‖₊, hbdd⟩, ball_subset_closedBall]

theorem sSup_unitClosedBall_eq_norm (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' closedBall 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using
    NNReal.coe_inj.2 f.sSup_unitClosedBall_eq_nnnorm

theorem exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm [NormedAlgebra ℝ 𝕜]
    (f : E →SL[σ₁₂] F) {r : ℝ≥0} (hr : r < ‖f‖₊) :
    ∃ x : E, ‖x‖₊ = 1 ∧ r < ‖f x‖₊ := by
  obtain ⟨x, hlt, hr⟩ := exists_lt_apply_of_lt_opNNNorm f hr
  obtain rfl | hx0 := eq_zero_or_nnnorm_pos x
  · simp at hr
  use algebraMap ℝ 𝕜 ‖x‖⁻¹ • x
  suffices r < ‖x‖₊⁻¹ * ‖f x‖₊ by simpa [nnnorm_smul, inv_mul_cancel₀ hx0.ne'] using this
  calc
    r < 1⁻¹ * ‖f x‖₊ := by simpa
    _ < ‖x‖₊⁻¹ * ‖f x‖₊ := by gcongr; exact hr.pos

/-- When the domain is a real normed space, `ContinuousLinearMap.sSup_unitClosedBall_eq_nnnorm` can
be tightened to take the supremum over only the `Metric.sphere`. -/
theorem sSup_sphere_eq_nnnorm [NormedAlgebra ℝ 𝕜] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' Metric.sphere 0 1) = ‖f‖₊ := by
  cases subsingleton_or_nontrivial E
  · simp [sphere_eq_empty_of_subsingleton one_ne_zero]
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
      ((NormedSpace.sphere_nonempty.mpr zero_le_one).image _) ?_ fun ub hub => ?_
  · rintro - ⟨x, hx, rfl⟩
    simpa only [mul_one] using f.le_opNorm_of_le (mem_sphere_zero_iff_norm.1 hx).le
  · obtain ⟨x, hx, hxf⟩ := f.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm hub
    exact ⟨_, ⟨x, by simpa using congrArg NNReal.toReal hx, rfl⟩, hxf⟩

/-- When the domain is a real normed space, `ContinuousLinearMap.sSup_unitClosedBall_eq_norm` can be
tightened to take the supremum over only the `Metric.sphere`. -/
theorem sSup_sphere_eq_norm [NormedAlgebra ℝ 𝕜] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' Metric.sphere 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using NNReal.coe_inj.2 f.sSup_sphere_eq_nnnorm

end ContinuousLinearMap

end DenselyNormedDomain
