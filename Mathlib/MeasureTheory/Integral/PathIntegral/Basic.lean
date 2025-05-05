/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift

open MeasureTheory unitInterval Topology Set Interval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b c d : E}

noncomputable def pathIntegralFun (ω : E → E →L[ℝ] F) (γ : Path a b) (t : ℝ) : F :=
  ω (γ.extend t) (derivWithin γ.extend I t)

noncomputable def pathIntegral (ω : E → E →L[ℝ] F) (γ : Path a b) : F :=
  ∫ t in (0)..1, pathIntegralFun ω γ t

def PathIntegrable (ω : E → E →L[ℝ] F) (γ : Path a b) : Prop :=
  IntervalIntegrable (pathIntegralFun ω γ) volume 0 1

theorem pathIntegral_of_not_completeSpace (h : ¬CompleteSpace F) (ω : E → E →L[ℝ] F)
    (γ : Path a b) : pathIntegral ω γ = 0 := by
  simp [pathIntegral, intervalIntegral, integral, h]

@[simp]
theorem pathIntegralFun_refl (ω : E → E →L[ℝ] F) (a : E) : pathIntegralFun ω (.refl a) = 0 := by
  ext
  simp [pathIntegralFun]

@[simp]
theorem pathIntegralFun_cast (ω : E → E →L[ℝ] F) (γ : Path a b) (hc : c = a) (hd : d = b) :
    pathIntegralFun ω (γ.cast hc hd) = pathIntegralFun ω γ :=
  rfl

@[simp]
theorem pathIntegral_cast (ω : E → E →L[ℝ] F) (γ : Path a b) (hc : c = a) (hd : d = b) :
    pathIntegral ω (γ.cast hc hd) = pathIntegral ω γ :=
  rfl

@[simp]
theorem PathIntegrable.cast_iff {ω : E → E →L[ℝ] F} {γ : Path a b} (hc : c = a) (hd : d = b) :
    PathIntegrable ω (γ.cast hc hd) ↔ PathIntegrable ω γ := .rfl

protected alias ⟨_, PathIntegrable.cast⟩ := PathIntegrable.cast_iff

@[simp]
theorem pathIntegral_refl (ω : E → E →L[ℝ] F) (a : E) : pathIntegral ω (.refl a) = 0 := by
  simp [pathIntegral]

@[simp]
theorem PathIntegrable.refl (ω : E → E →L[ℝ] F) (a : E) : PathIntegrable ω (.refl a) := by
  simp [PathIntegrable, Pi.zero_def]

theorem pathIntegralFun_symm_apply (ω : E → E →L[ℝ] F) (γ : Path a b) (t : ℝ) :
    pathIntegralFun ω γ.symm t = -pathIntegralFun ω γ (1 - t) := by
  simp [pathIntegralFun, γ.extend_symm, derivWithin_comp_sub_left]

@[simp]
theorem pathIntegralFun_symm (ω : E → E →L[ℝ] F) (γ : Path a b):
    pathIntegralFun ω γ.symm = (-pathIntegralFun ω γ <| 1 - ·) :=
  funext <| pathIntegralFun_symm_apply ω γ

protected theorem PathIntegrable.symm {ω : E → E →L[ℝ] F} {γ : Path a b} (h : PathIntegrable ω γ) :
    PathIntegrable ω γ.symm := by
  simpa [PathIntegrable] using (h.comp_sub_left 1).neg.symm

@[simp]
theorem pathIntegrable_symm {ω : E → E →L[ℝ] F} {γ : Path a b} :
    PathIntegrable ω γ.symm ↔ PathIntegrable ω γ :=
  ⟨fun h ↦ by simpa using h.symm, .symm⟩

@[simp]
theorem pathIntegral_symm (ω : E → E →L[ℝ] F) (γ : Path a b) :
    pathIntegral ω γ.symm = -pathIntegral ω γ := by
  simp [pathIntegral, pathIntegralFun_symm]

theorem pathIntegralFun_trans_of_lt_half (ω : E → E →L[ℝ] F) (γ₁ : Path a b) (γ₂ : Path b c)
    {t : ℝ} (ht₀ : 0 < t) (ht : t < 1 / 2) :
    pathIntegralFun ω (γ₁.trans γ₂) t = (2 : ℝ) • pathIntegralFun ω γ₁ (2 * t) := by
  have : (γ₁.trans γ₂).extend =ᶠ[𝓝 t] (fun s ↦ γ₁.extend (2 * s)) :=
    (eventually_le_nhds ht).mono fun _ ↦ Path.extend_trans_of_le_half _ _
  rw [pathIntegralFun, this.self_of_nhds, derivWithin_of_mem_nhds, this.deriv_eq, pathIntegralFun,
    derivWithin_of_mem_nhds, deriv_comp_mul_left, map_smul] <;>
    apply Icc_mem_nhds <;> linarith

theorem pathIntegralFun_trans_aeEq_left (ω : E → E →L[ℝ] F) (γ₁ : Path a b) (γ₂ : Path b c) :
    pathIntegralFun ω (γ₁.trans γ₂) =ᵐ[volume.restrict (Ι (0 : ℝ) (1 / 2))]
      fun t ↦ (2 : ℝ) • pathIntegralFun ω γ₁ (2 * t) := by
  rw [uIoc_of_le (by positivity), ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₀, ht⟩
  exact pathIntegralFun_trans_of_lt_half ω γ₁ γ₂ ht₀ ht

theorem pathIntegralFun_trans_of_half_lt (ω : E → E →L[ℝ] F) (γ₁ : Path a b) (γ₂ : Path b c)
    {t : ℝ} (ht₀ : 1 / 2 < t) (ht : t < 1) :
    pathIntegralFun ω (γ₁.trans γ₂) t = (2 : ℝ) • pathIntegralFun ω γ₂ (2 * t - 1) := by
  have : (γ₁.trans γ₂).extend =ᶠ[𝓝 t] (fun s ↦ γ₂.extend (2 * s - 1)) :=
    (eventually_ge_nhds ht₀).mono fun _ ↦ Path.extend_trans_of_half_le _ _
  rw [pathIntegralFun, this.self_of_nhds, derivWithin_of_mem_nhds, this.deriv_eq, pathIntegralFun,
    derivWithin_of_mem_nhds, deriv_comp_mul_left (γ₂.extend <| · - 1), deriv_comp_sub_const,
    map_smul] <;> apply Icc_mem_nhds <;> linarith

theorem pathIntegralFun_trans_aeEq_right (ω : E → E →L[ℝ] F) (γ₁ : Path a b) (γ₂ : Path b c) :
    pathIntegralFun ω (γ₁.trans γ₂) =ᵐ[volume.restrict (Ι (1 / 2 : ℝ) 1)]
      fun t ↦ (2 : ℝ) • pathIntegralFun ω γ₂ (2 * t - 1) := by
  rw [uIoc_of_le (by linarith), ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₁, ht₂⟩
  exact pathIntegralFun_trans_of_half_lt ω γ₁ γ₂ ht₁ ht₂

theorem PathIntegrable.intervalIntegrable_pathIntegralFun_trans_left {ω : E → E →L[ℝ] F}
    {γ₁ : Path a b} (h : PathIntegrable ω γ₁) (γ₂ : Path b c) :
    IntervalIntegrable (pathIntegralFun ω (γ₁.trans γ₂)) volume 0 (1 / 2) :=
  .congr (by simpa using (h.comp_mul_left 2).smul (2 : ℝ))
    (pathIntegralFun_trans_aeEq_left _ _ _).symm

theorem PathIntegrable.intervalIntegrable_pathIntegralFun_trans_right {ω : E → E →L[ℝ] F}
    (γ₁ : Path a b) {γ₂ : Path b c} (h : PathIntegrable ω γ₂) :
    IntervalIntegrable (pathIntegralFun ω (γ₁.trans γ₂)) volume (1 / 2) 1 :=
  .congr (by simpa using ((h.comp_sub_right 1).comp_mul_left 2).smul (2 : ℝ))
    (pathIntegralFun_trans_aeEq_right _ _ _).symm

protected theorem PathIntegrable.trans {ω : E → E →L[ℝ] F} {γ₁ : Path a b} {γ₂ : Path b c}
    (h₁ : PathIntegrable ω γ₁) (h₂ : PathIntegrable ω γ₂) : PathIntegrable ω (γ₁.trans γ₂) :=
  (h₁.intervalIntegrable_pathIntegralFun_trans_left γ₂).trans
    (h₂.intervalIntegrable_pathIntegralFun_trans_right γ₁)

theorem pathIntegral_trans {ω : E → E →L[ℝ] F} {γ₁ : Path a b} {γ₂ : Path b c}
    (h₁ : PathIntegrable ω γ₁) (h₂ : PathIntegrable ω γ₂) :
    pathIntegral ω (γ₁.trans γ₂) = pathIntegral ω γ₁ + pathIntegral ω γ₂ := by
  rw [pathIntegral, ← intervalIntegral.integral_add_adjacent_intervals
    (h₁.intervalIntegrable_pathIntegralFun_trans_left γ₂)
    (h₂.intervalIntegrable_pathIntegralFun_trans_right γ₁),
    intervalIntegral.integral_congr_ae_restrict (pathIntegralFun_trans_aeEq_left _ _ _),
    intervalIntegral.integral_congr_ae_restrict (pathIntegralFun_trans_aeEq_right _ _ _),
    intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left,
    intervalIntegral.integral_smul,
    intervalIntegral.smul_integral_comp_mul_left (f := (pathIntegralFun ω γ₂ <| · - 1)),
    intervalIntegral.integral_comp_sub_right]
  norm_num [pathIntegral]

-- ω (γ.extend t) (derivWithin γ.extend I t)

/-- If a 1-form `ω` is continuous on a set `s`,
then it is path integrable along any $C^1$ path in this set. -/
theorem ContinuousOn.pathIntegrable_of_contDiffOn {ω : E → E →L[ℝ] F} {γ : Path a b}
    {s : Set E} (hω : ContinuousOn ω s) (hγ : ContDiffOn ℝ 1 γ.extend I) (hγs : ∀ t, γ t ∈ s) :
    PathIntegrable ω γ := by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  unfold pathIntegralFun
  apply ContinuousOn.clm_apply
  · exact hω.comp (by fun_prop) fun _ _ ↦ hγs _
  · exact hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl

