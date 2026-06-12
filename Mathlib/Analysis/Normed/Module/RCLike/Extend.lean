/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Extend

/-!
# Norm properties of the extension of continuous `ℝ`-linear functionals to `𝕜`-linear functionals

This file shows that `StrongDual.extendRCLike` preserves the norm of the functional.
-/

public section

open RCLike ContinuousLinearMap Module
open scoped ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]

/-- If a real-linear functional is bounded by a `𝕜`-seminorm, then its `𝕜`-linear extension
is bounded by the same seminorm. -/
theorem Module.Dual.norm_extendRCLike_le_seminorm [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
    [IsScalarTower ℝ 𝕜 E] (fr : Dual ℝ E) {p : Seminorm 𝕜 E} (hp : ∀ x, |fr x| ≤ p x) (x : E) :
    ‖(fr.extendRCLike x : 𝕜)‖ ≤ p x := by
  by_cases hx : fr.extendRCLike (𝕜 := 𝕜) x = 0
  · simp [hx]
  have hsq : ‖fr.extendRCLike (𝕜 := 𝕜) x‖ ^ 2 ≤ ‖fr.extendRCLike (𝕜 := 𝕜) x‖ * p x := calc
    _ = fr (conj (fr.extendRCLike x) • x) := fr.norm_extendRCLike_apply_sq x
    _ ≤ |fr (conj (fr.extendRCLike x) • x)| := le_abs_self _
    _ ≤ p (conj (fr.extendRCLike x) • x) := hp _
    _ = ‖conj (fr.extendRCLike x)‖ * p x := map_smul_eq_mul _ _ _
    _ = ‖(fr.extendRCLike x)‖ * p x := by rw [norm_conj]
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.2 hx)).1 <| by simpa [pow_two, mul_comm] using hsq

namespace StrongDual

/-- If a continuous real-linear functional is bounded by a `𝕜`-seminorm, then its `𝕜`-linear
extension is bounded by the same seminorm. -/
theorem norm_extendRCLike_le_seminorm [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
    [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] (fr : StrongDual ℝ E)
    {p : Seminorm 𝕜 E} (hp : ∀ x, |fr x| ≤ p x) (x : E) :
    ‖(fr.extendRCLike x : 𝕜)‖ ≤ p x :=
  Dual.norm_extendRCLike_le_seminorm fr hp x

variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- The norm of the extension is bounded by `‖fr‖`. -/
theorem norm_extendRCLike_bound (fr : StrongDual ℝ F) (x : F) :
    ‖(fr.extendRCLike x : 𝕜)‖ ≤ ‖fr‖ * ‖x‖ := by
  refine Module.Dual.norm_extendRCLike_le_seminorm (p := ‖fr‖₊ • normSeminorm 𝕜 F)
    fr.toLinearMap ?_ x
  simp [← Real.norm_eq_abs, NNReal.smul_def, le_opNorm]

@[simp]
theorem norm_extendRCLike (fr : StrongDual ℝ F) : ‖(fr.extendRCLike : StrongDual 𝕜 F)‖ = ‖fr‖ :=
  le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fr.norm_extendRCLike_bound) <|
    opNorm_le_bound _ (norm_nonneg _) fun x =>
      calc
        ‖fr x‖ = ‖re (fr.extendRCLike x : 𝕜)‖ := by simp
        _ ≤ ‖(fr.extendRCLike x : 𝕜)‖ := abs_re_le_norm _
        _ ≤ ‖(fr.extendRCLike : StrongDual 𝕜 F)‖ * ‖x‖ := le_opNorm _ _

/-- `StrongDual.extendRCLike` bundled into a linear isometry equivalence. -/
@[expose, simps! -isSimp apply symm_apply]
noncomputable def extendRCLikeₗᵢ : StrongDual ℝ F ≃ₗᵢ[ℝ] StrongDual 𝕜 F where
  toLinearEquiv := StrongDual.extendRCLikeₗ
  norm_map' := norm_extendRCLike

end StrongDual

namespace ContinuousLinearMap
open StrongDual

@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜'_bound := norm_extendRCLike_bound
@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜' := norm_extendRCLike
@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜 := norm_extendRCLike

end ContinuousLinearMap
