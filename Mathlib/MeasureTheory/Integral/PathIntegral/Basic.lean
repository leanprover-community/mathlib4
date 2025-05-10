/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Integral of a 1-form along a path

In this file we define integral of a 1-form along a path
and prove basic properties of this operation.
-/

open MeasureTheory unitInterval Topology Set Interval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : E}

/-- The function `t ↦ ω (γ t) (γ' t)` which appears in the definition of a path integral.

This definition is used to factor out common parts of lemmas about `Pa -/
noncomputable def pathIntegralFun (ω : E → E →L[ℝ] F) (γ : Path a b) (t : ℝ) : F :=
  ω (γ.extend t) (derivWithin γ.extend I t)

/-- A 1-form `ω` is *path integrable* along a path `γ`,
if the function `pathIntegralFun ω γ t = ω (γ t) (γ' t)` is integrable on `[0, 1]`.

The actual definition uses `Path.extend γ`,
because both interval integrals and derivatives expect globally defined functions.
-/
def PathIntegrable (ω : E → E →L[ℝ] F) (γ : Path a b) : Prop :=
  IntervalIntegrable (pathIntegralFun ω γ) volume 0 1

/-- Integral of a 1-form `ω : E → E →L[ℝ] F` along a path `γ`,
defined as $\int_0^1 \omega(\gamma(t))(\gamma'(t))$.

The actual definition uses `pathIntegralFun` which uses `Path.extend γ`
and `derivWithin (Path.extend γ) (Set.Icc 0 1) t`,
because calculus-related definitions in Mathlib expect globally defined functions as arguments. -/
noncomputable def pathIntegral (ω : E → E →L[ℝ] F) (γ : Path a b) : F :=
  ∫ t in (0)..1, pathIntegralFun ω γ t

-- TODO: use `∈`
-- TODO: fix priorities
@[inherit_doc pathIntegral]
notation3 "∫ᵖ "(...)" in " γ ", "r:60:(scoped ω => pathIntegral ω γ) => r

/-- Path integral is defined using Bochner integral,
thus it is defined as zero whenever the codomain is not a complete space. -/
theorem pathIntegral_of_not_completeSpace (h : ¬CompleteSpace F) (ω : E → E →L[ℝ] F)
    (γ : Path a b) : ∫ᵖ x in γ, ω x = 0 := by
  simp [pathIntegral, intervalIntegral, integral, h]

/-!
### Operations on paths
-/

section PathOperations

variable {c d : E} {ω : E → E →L[ℝ] F} {γ γab : Path a b} {γbc : Path b c} {t : ℝ}

@[simp]
theorem pathIntegralFun_refl (ω : E → E →L[ℝ] F) (a : E) : pathIntegralFun ω (.refl a) = 0 := by
  ext
  simp [pathIntegralFun]

@[simp]
theorem pathIntegral_refl (ω : E → E →L[ℝ] F) (a : E) : ∫ᵖ x in .refl a, ω x = 0 := by
  simp [pathIntegral]

@[simp]
theorem PathIntegrable.refl (ω : E → E →L[ℝ] F) (a : E) : PathIntegrable ω (.refl a) := by
  simp [PathIntegrable, Pi.zero_def]

@[simp]
theorem pathIntegralFun_cast (ω : E → E →L[ℝ] F) (γ : Path a b) (hc : c = a) (hd : d = b) :
    pathIntegralFun ω (γ.cast hc hd) = pathIntegralFun ω γ :=
  rfl

@[simp]
theorem pathIntegral_cast (ω : E → E →L[ℝ] F) (γ : Path a b) (hc : c = a) (hd : d = b) :
    ∫ᵖ x in γ.cast hc hd, ω x = ∫ᵖ x in γ, ω x :=
  rfl

@[simp]
theorem PathIntegrable.cast_iff (hc : c = a) (hd : d = b) :
    PathIntegrable ω (γ.cast hc hd) ↔ PathIntegrable ω γ := .rfl

protected alias ⟨_, PathIntegrable.cast⟩ := PathIntegrable.cast_iff

theorem pathIntegralFun_symm_apply (ω : E → E →L[ℝ] F) (γ : Path a b) (t : ℝ) :
    pathIntegralFun ω γ.symm t = -pathIntegralFun ω γ (1 - t) := by
  simp [pathIntegralFun, γ.extend_symm, derivWithin_comp_const_sub]

@[simp]
theorem pathIntegralFun_symm (ω : E → E →L[ℝ] F) (γ : Path a b):
    pathIntegralFun ω γ.symm = (-pathIntegralFun ω γ <| 1 - ·) :=
  funext <| pathIntegralFun_symm_apply ω γ

protected theorem PathIntegrable.symm (h : PathIntegrable ω γ) : PathIntegrable ω γ.symm := by
  simpa [PathIntegrable] using (h.comp_sub_left 1).neg.symm

@[simp]
theorem pathIntegrable_symm : PathIntegrable ω γ.symm ↔ PathIntegrable ω γ :=
  ⟨fun h ↦ by simpa using h.symm, .symm⟩

@[simp]
theorem pathIntegral_symm (ω : E → E →L[ℝ] F) (γ : Path a b) :
    ∫ᵖ x in γ.symm, ω x = -∫ᵖ x in γ, ω x := by
  simp [pathIntegral, pathIntegralFun_symm]

theorem pathIntegralFun_trans_of_lt_half (ω : E → E →L[ℝ] F) (γab : Path a b) (γbc : Path b c)
    (ht₀ : 0 < t) (ht : t < 1 / 2) :
    pathIntegralFun ω (γab.trans γbc) t = (2 : ℝ) • pathIntegralFun ω γab (2 * t) := by
  have : (γab.trans γbc).extend =ᶠ[𝓝 t] (fun s ↦ γab.extend (2 * s)) :=
    (eventually_le_nhds ht).mono fun _ ↦ Path.extend_trans_of_le_half _ _
  rw [pathIntegralFun, this.self_of_nhds, derivWithin_of_mem_nhds, this.deriv_eq, pathIntegralFun,
    derivWithin_of_mem_nhds, deriv_comp_mul_left, map_smul] <;>
    apply Icc_mem_nhds <;> linarith

theorem pathIntegralFun_trans_aeeq_left (ω : E → E →L[ℝ] F) (γab : Path a b) (γbc : Path b c) :
    pathIntegralFun ω (γab.trans γbc) =ᵐ[volume.restrict (Ι (0 : ℝ) (1 / 2))]
      fun t ↦ (2 : ℝ) • pathIntegralFun ω γab (2 * t) := by
  rw [uIoc_of_le (by positivity), ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₀, ht⟩
  exact pathIntegralFun_trans_of_lt_half ω γab γbc ht₀ ht

theorem pathIntegralFun_trans_of_half_lt (ω : E → E →L[ℝ] F) (γab : Path a b) (γbc : Path b c)
    (ht₀ : 1 / 2 < t) (ht : t < 1) :
    pathIntegralFun ω (γab.trans γbc) t = (2 : ℝ) • pathIntegralFun ω γbc (2 * t - 1) := by
  have : (γab.trans γbc).extend =ᶠ[𝓝 t] (fun s ↦ γbc.extend (2 * s - 1)) :=
    (eventually_ge_nhds ht₀).mono fun _ ↦ Path.extend_trans_of_half_le _ _
  rw [pathIntegralFun, this.self_of_nhds, derivWithin_of_mem_nhds, this.deriv_eq, pathIntegralFun,
    derivWithin_of_mem_nhds, deriv_comp_mul_left _ (γbc.extend <| · - 1), deriv_comp_sub_const,
    map_smul] <;> apply Icc_mem_nhds <;> linarith

theorem pathIntegralFun_trans_aeeq_right (ω : E → E →L[ℝ] F) (γab : Path a b) (γbc : Path b c) :
    pathIntegralFun ω (γab.trans γbc) =ᵐ[volume.restrict (Ι (1 / 2 : ℝ) 1)]
      fun t ↦ (2 : ℝ) • pathIntegralFun ω γbc (2 * t - 1) := by
  rw [uIoc_of_le (by linarith), ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht₁, ht₂⟩
  exact pathIntegralFun_trans_of_half_lt ω γab γbc ht₁ ht₂

theorem PathIntegrable.intervalIntegrable_pathIntegralFun_trans_left
    (h : PathIntegrable ω γab) (γbc : Path b c) :
    IntervalIntegrable (pathIntegralFun ω (γab.trans γbc)) volume 0 (1 / 2) :=
  .congr (by simpa using (h.comp_mul_left 2).smul (2 : ℝ))
    (pathIntegralFun_trans_aeeq_left _ _ _).symm

theorem PathIntegrable.intervalIntegrable_pathIntegralFun_trans_right
    (γab : Path a b) (h : PathIntegrable ω γbc) :
    IntervalIntegrable (pathIntegralFun ω (γab.trans γbc)) volume (1 / 2) 1 :=
  .congr (by simpa using ((h.comp_sub_right 1).comp_mul_left 2).smul (2 : ℝ))
    (pathIntegralFun_trans_aeeq_right _ _ _).symm

protected theorem PathIntegrable.trans (h₁ : PathIntegrable ω γab) (h₂ : PathIntegrable ω γbc) :
    PathIntegrable ω (γab.trans γbc) :=
  (h₁.intervalIntegrable_pathIntegralFun_trans_left γbc).trans
    (h₂.intervalIntegrable_pathIntegralFun_trans_right γab)

theorem pathIntegral_trans (h₁ : PathIntegrable ω γab) (h₂ : PathIntegrable ω γbc) :
    ∫ᵖ x in γab.trans γbc, ω x = pathIntegral ω γab + pathIntegral ω γbc := by
  rw [pathIntegral, ← intervalIntegral.integral_add_adjacent_intervals
    (h₁.intervalIntegrable_pathIntegralFun_trans_left γbc)
    (h₂.intervalIntegrable_pathIntegralFun_trans_right γab),
    intervalIntegral.integral_congr_ae_restrict (pathIntegralFun_trans_aeeq_left _ _ _),
    intervalIntegral.integral_congr_ae_restrict (pathIntegralFun_trans_aeeq_right _ _ _),
    intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left,
    intervalIntegral.integral_smul,
    intervalIntegral.smul_integral_comp_mul_left (f := (pathIntegralFun ω γbc <| · - 1)),
    intervalIntegral.integral_comp_sub_right]
  norm_num [pathIntegral]

/-- If a 1-form `ω` is continuous on a set `s`,
then it is path integrable along any $C^1$ path in this set. -/
theorem ContinuousOn.pathIntegrable_of_contDiffOn {s : Set E} (hω : ContinuousOn ω s)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγs : ∀ t, γ t ∈ s) : PathIntegrable ω γ := by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  unfold pathIntegralFun
  apply ContinuousOn.clm_apply
  · exact hω.comp (by fun_prop) fun _ _ ↦ hγs _
  · exact hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl

end PathOperations

/-!
### Algebraic operations on the 1-form
-/

variable {ω ω₁ ω₂ : E → E →L[ℝ] F} {γ : Path a b} {t : ℝ}

@[simp]
theorem pathIntegralFun_add :
    pathIntegralFun (ω₁ + ω₂) γ = pathIntegralFun ω₁ γ + pathIntegralFun ω₂ γ :=
  rfl

protected nonrec theorem PathIntegrable.add (h₁ : PathIntegrable ω₁ γ) (h₂ : PathIntegrable ω₂ γ) :
    PathIntegrable (ω₁ + ω₂) γ :=
  h₁.add h₂

theorem pathIntegral_add (h₁ : PathIntegrable ω₁ γ) (h₂ : PathIntegrable ω₂ γ) :
    pathIntegral (ω₁ + ω₂) γ = (∫ᵖ x in γ, ω₁ x) + ∫ᵖ x in γ, ω₂ x :=
  intervalIntegral.integral_add h₁ h₂

theorem pathIntegral_fun_add (h₁ : PathIntegrable ω₁ γ) (h₂ : PathIntegrable ω₂ γ) :
    ∫ᵖ x in γ, ω₁ x + ω₂ x = (∫ᵖ x in γ, ω₁ x) + ∫ᵖ x in γ, ω₂ x :=
  pathIntegral_add h₁ h₂

@[simp]
theorem pathIntegralFun_zero : pathIntegralFun (0 : E → E →L[ℝ] F) γ = 0 := rfl

@[simp]
theorem pathIntegralFun_fun_zero : pathIntegralFun (fun _ ↦ 0 : E → E →L[ℝ] F) γ = 0 := rfl

-- TODO: add `intervalIntegrable_zero`
theorem PathIntegrable.zero : PathIntegrable (0 : E → E →L[ℝ] F) γ := by
  simp [PathIntegrable, intervalIntegrable_const, Pi.zero_def]

theorem PathIntegrable.fun_zero : PathIntegrable (fun _ ↦ 0 : E → E →L[ℝ] F) γ := .zero

@[simp]
theorem pathIntegral_zero : pathIntegral (0 : E → E →L[ℝ] F) γ = 0 := by simp [pathIntegral]

@[simp]
theorem pathIntegral_fun_zero : ∫ᵖ _ in γ, (0 : E →L[ℝ] F) = 0 := pathIntegral_zero

@[simp]
theorem pathIntegralFun_neg : pathIntegralFun (-ω) γ = -pathIntegralFun ω γ := rfl

nonrec theorem PathIntegrable.neg (h : PathIntegrable ω γ) : PathIntegrable (-ω) γ :=
  h.neg

theorem PathIntegrable.fun_neg (h : PathIntegrable ω γ) : PathIntegrable (-ω ·) γ :=
  h.neg

@[simp]
theorem PathIntegrable.neg_iff : PathIntegrable (-ω) γ ↔ PathIntegrable ω γ :=
  ⟨fun h ↦ by simpa using h.neg, .neg⟩

@[simp]
theorem PathIntegrable.fun_neg_iff : PathIntegrable (-ω ·) γ ↔ PathIntegrable ω γ :=
  PathIntegrable.neg_iff

@[simp]
theorem pathIntegral_neg : pathIntegral (-ω) γ = -∫ᵖ x in γ, ω x := by
  simp [pathIntegral]

@[simp]
theorem pathIntegral_fun_neg : ∫ᵖ x in γ, -ω x = -∫ᵖ x in γ, ω x := pathIntegral_neg

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] {c : 𝕜}

@[simp]
theorem pathIntegralFun_smul : pathIntegralFun (c • ω) γ = c • pathIntegralFun ω γ := rfl

nonrec theorem PathIntegrable.smul (h : PathIntegrable ω γ) : PathIntegrable (c • ω) γ :=
  h.smul c

@[simp]
theorem PathIntegrable.smul_iff : PathIntegrable (c • ω) γ ↔ c = 0 ∨ PathIntegrable ω γ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [PathIntegrable.zero]
  · simp only [hc, false_or]
    refine ⟨fun h ↦ ?_, .smul⟩
    simpa [hc] using h.smul (c := c⁻¹)

@[simp]
theorem pathIntegral_smul : pathIntegral (c • ω) γ = c • pathIntegral ω γ :=
  intervalIntegral.integral_smul _ _

@[simp]
theorem pathIntegral_fun_smul : ∫ᵖ x in γ, c • ω x = c • ∫ᵖ x in γ, ω x := pathIntegral_smul
