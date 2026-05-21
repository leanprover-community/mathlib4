/-
Copyright (c) 2024 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Properties about the powers of the norm

In this file we prove that `x ↦ ‖x‖ ^ p` is continuously differentiable for
an inner product space and for a real number `p > 1`.

## TODO
* `x ↦ ‖x‖ ^ p` should be `C^n` for `p > n`.

-/

public section

section ContDiffNormPow

open Asymptotics Real Topology
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_norm_rpow (x : E) {p : ℝ} (hp : 1 < p) :
    HasFDerivAt (fun x : E ↦ ‖x‖ ^ p) ((p * ‖x‖ ^ (p - 2)) • innerSL ℝ x) x := by
  by_cases hx : x = 0
  · simp only [hx, norm_zero, map_zero, smul_zero]
    have h2p : 0 < p - 1 := sub_pos.mpr hp
    refine .of_isLittleO ?_
    calc (fun x : E ↦ ‖x‖ ^ p - ‖(0 : E)‖ ^ p - 0)
        = (fun x : E ↦ ‖x‖ ^ p) := by simp [zero_lt_one.trans hp |>.ne']
      _ = (fun x : E ↦ ‖x‖ * ‖x‖ ^ (p - 1)) := by
          ext x
          rw [← rpow_one_add' (norm_nonneg x) (by positivity)]
          ring_nf
      _ =o[𝓝 0] (fun x : E ↦ ‖x‖ * 1) := by
        refine (isBigO_refl _ _).mul_isLittleO <| (isLittleO_const_iff <| by simp).mpr ?_
        convert continuousAt_id.norm.rpow_const (.inr h2p.le) |>.tendsto
        simp [h2p.ne']
      _ =O[𝓝 0] (fun (x : E) ↦ x - 0) := by
        simp_rw [mul_one, isBigO_norm_left (f' := fun x ↦ x), sub_zero, isBigO_refl]
  · apply HasStrictFDerivAt.hasFDerivAt
    convert (hasStrictFDerivAt_norm_sq x).rpow_const (p := p / 2) (by simp [hx]) using 0
    simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    ring_nf

theorem differentiable_norm_rpow {p : ℝ} (hp : 1 < p) :
    Differentiable ℝ (fun x : E ↦ ‖x‖ ^ p) :=
  fun x ↦ hasFDerivAt_norm_rpow x hp |>.differentiableAt

theorem hasDerivAt_norm_rpow (x : ℝ) {p : ℝ} (hp : 1 < p) :
    HasDerivAt (fun x : ℝ ↦ ‖x‖ ^ p) (p * ‖x‖ ^ (p - 2) * x) x := by
  convert hasFDerivAt_norm_rpow x hp |>.hasDerivAt using 1; simp

theorem hasDerivAt_abs_rpow (x : ℝ) {p : ℝ} (hp : 1 < p) :
    HasDerivAt (fun x : ℝ ↦ |x| ^ p) (p * |x| ^ (p - 2) * x) x := by
  simpa using hasDerivAt_norm_rpow x hp

theorem fderiv_norm_rpow (x : E) {p : ℝ} (hp : 1 < p) :
    fderiv ℝ (fun x ↦ ‖x‖ ^ p) x = (p * ‖x‖ ^ (p - 2)) • innerSL ℝ x :=
  hasFDerivAt_norm_rpow x hp |>.fderiv

theorem Differentiable.fderiv_norm_rpow {f : F → E} (hf : Differentiable ℝ f)
    {x : F} {p : ℝ} (hp : 1 < p) :
    fderiv ℝ (fun x ↦ ‖f x‖ ^ p) x =
    (p * ‖f x‖ ^ (p - 2)) • (innerSL ℝ (f x)).comp (fderiv ℝ f x) :=
  hasFDerivAt_norm_rpow (f x) hp |>.comp x (hf x).hasFDerivAt |>.fderiv

theorem norm_fderiv_norm_rpow_le {f : F → E} (hf : Differentiable ℝ f) {x : F}
    {p : ℝ} (hp : 1 < p) :
    ‖fderiv ℝ (fun x ↦ ‖f x‖ ^ p) x‖ ≤ p * ‖f x‖ ^ (p - 1) * ‖fderiv ℝ f x‖ := by
  rw [hf.fderiv_norm_rpow hp, norm_smul, norm_mul]
  simp_rw [norm_rpow_of_nonneg (norm_nonneg _), norm_norm, norm_eq_abs,
    abs_eq_self.mpr <| zero_le_one.trans hp.le, mul_assoc]
  gcongr _ * ?_
  refine mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le ..) (by positivity)
    |>.trans_eq ?_
  rw [innerSL_apply_norm, ← mul_assoc, ← Real.rpow_add_one' (by positivity) (by linarith)]
  ring_nf

theorem norm_fderiv_norm_id_rpow (x : E) {p : ℝ} (hp : 1 < p) :
    ‖fderiv ℝ (fun x ↦ ‖x‖ ^ p) x‖ = p * ‖x‖ ^ (p - 1) := by
  rw [fderiv_norm_rpow x hp, norm_smul, norm_mul]
  simp_rw [norm_rpow_of_nonneg (norm_nonneg _), norm_norm, norm_eq_abs,
    abs_eq_self.mpr <| zero_le_one.trans hp.le, mul_assoc, innerSL_apply_norm]
  rw [← Real.rpow_add_one' (by positivity) (by linarith)]
  ring_nf

theorem nnnorm_fderiv_norm_rpow_le {f : F → E} (hf : Differentiable ℝ f)
    {x : F} {p : ℝ≥0} (hp : 1 < p) :
    ‖fderiv ℝ (fun x ↦ ‖f x‖ ^ (p : ℝ)) x‖₊ ≤ p * ‖f x‖₊ ^ ((p : ℝ) - 1) * ‖fderiv ℝ f x‖₊ :=
  norm_fderiv_norm_rpow_le hf hp

lemma enorm_fderiv_norm_rpow_le {f : F → E} (hf : Differentiable ℝ f)
    {x : F} {p : ℝ≥0} (hp : 1 < p) :
    ‖fderiv ℝ (fun x ↦ ‖f x‖ ^ (p : ℝ)) x‖ₑ ≤ p * ‖f x‖ₑ ^ ((p : ℝ) - 1) * ‖fderiv ℝ f x‖ₑ := by
  simpa [enorm, ← ENNReal.coe_rpow_of_nonneg _ (sub_nonneg.2 <| NNReal.one_le_coe.2 hp.le),
    ← ENNReal.coe_mul] using nnnorm_fderiv_norm_rpow_le hf hp

theorem contDiff_norm_rpow {p : ℝ} (hp : 1 < p) : ContDiff ℝ 1 (fun x : E ↦ ‖x‖ ^ p) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x ↦ hasFDerivAt_norm_rpow x hp |>.differentiableAt, ?_⟩
  simp_rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · simp_rw [hx, ContinuousAt, fderiv_norm_rpow (0 : E) hp, norm_zero, map_zero, smul_zero]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds) ?_
      (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_fderiv_norm_id_rpow _ hp |>.le)
    suffices ContinuousAt (fun x : E ↦ p * ‖x‖ ^ (p - 1)) 0 by
      simpa [ContinuousAt, sub_ne_zero_of_ne hp.ne'] using this
    fun_prop (discharger := simp [hp.le])
  · simp_rw [funext fun x ↦ fderiv_norm_rpow (E := E) (x := x) hp]
    fun_prop (discharger := simp [hx])

theorem ContDiff.norm_rpow {f : F → E} (hf : ContDiff ℝ 1 f) {p : ℝ} (hp : 1 < p) :
    ContDiff ℝ 1 (fun x ↦ ‖f x‖ ^ p) :=
  contDiff_norm_rpow hp |>.comp hf

theorem Differentiable.norm_rpow {f : F → E} (hf : Differentiable ℝ f) {p : ℝ} (hp : 1 < p) :
    Differentiable ℝ (fun x ↦ ‖f x‖ ^ p) :=
  contDiff_norm_rpow hp |>.differentiable one_ne_zero |>.comp hf

end ContDiffNormPow
