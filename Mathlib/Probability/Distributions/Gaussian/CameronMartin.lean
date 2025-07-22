/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Cameron-Martin space

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open MeasureTheory NormedSpace UniformSpace
open scoped ENNReal InnerProductSpace

noncomputable
def UniformSpace.Completion.continuousLinearMapExtension {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E →L[ℝ] F) :
    Completion E →L[ℝ] F where
  toFun x := Completion.extension f x
  map_add' x₁ x₂ := by
    refine Completion.induction_on₂ x₁ x₂ ?_ fun x₁' x₂' ↦ ?_
    · have : Continuous (Completion.extension f) := Completion.continuous_extension
      exact isClosed_eq (by fun_prop) (by fun_prop)
    · rw [Completion.extension_coe, Completion.extension_coe, ← map_add,
        ← Completion.extension_coe (f := f)]
      · congr
        norm_cast
      all_goals exact ContinuousLinearMap.uniformContinuous _
  map_smul' r x := by
    simp only [RingHom.id_apply]
    induction x using Completion.induction_on with
    | hp =>
      have h_cont : Continuous ( Completion.extension f) := Completion.continuous_extension
      refine isClosed_eq ?_ (by fun_prop)
      -- fun_prop fails here (it also fails in the `have` below)
      have : Continuous fun (a : Completion E) ↦ r • a := continuous_const_smul _
      exact h_cont.comp this
    | ih x =>
      rw [Completion.extension_coe, ← map_smul,
        ← Completion.extension_coe (f := f)]
      · congr
        norm_cast
      all_goals exact ContinuousLinearMap.uniformContinuous _
  cont := Completion.continuous_extension

lemma norm_eval_le_norm_mul_ciSup {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [Module ℝ G] [NormSMulClass ℝ G]
    (f : Dual ℝ E →L[ℝ] G) {y : E} (hy : ∃ M, ∀ L : Dual ℝ E, ‖f L‖ ≤ 1 → L y ≤ M) (L : Dual ℝ E) :
    ‖L y‖ ≤ ‖f L‖ * ⨆ (L' : Dual ℝ E) (_ : ‖f L'‖ ≤ 1), L' y := by
  have h_bdd : BddAbove (Set.range fun L' ↦ ⨆ (_ : ‖f L'‖ ≤ 1), L' y) := by
    obtain ⟨M, hM⟩ := hy
    refine ⟨M, ?_⟩
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    intro L
    by_cases hL : ‖f L‖ ≤ 1
    · simpa [hL] using hM L hL
    · simp only [hL, Real.iSup_of_isEmpty]
      simpa using hM 0 (by simp)
  have h L (hL : ‖f L‖ = 1) : ‖L y‖ ≤ ‖f L‖ * ⨆ L', ⨆ (_ : ‖f L'‖ ≤ 1), L' y := by
    rw [hL, one_mul]
    rcases le_total 0 (L y) with hLy | hLy
    · exact le_ciSup_of_le h_bdd L (by simp [hL, abs_of_nonneg hLy])
    · exact le_ciSup_of_le h_bdd (-L) (by simp [hL, abs_of_nonpos hLy])
  have hL_zero_of_L2 (hL : f L = 0) : L y = 0 := by
    have h_smul (r : ℝ) : f (r • L) = 0 := by simp [hL]
    contrapose! hy with hL_zero
    refine fun M ↦ ⟨((M + 1) / L y) • L, by simp [h_smul], ?_⟩
    simp [div_mul_cancel₀ _ hL_zero]
  by_cases hL_zero : L y = 0
  · simp only [hL_zero, norm_zero]
    refine mul_nonneg (by positivity) ?_
    exact le_ciSup_of_le h_bdd 0 (by simp)
  specialize h (‖f L‖⁻¹ • L) ?_
  · simp only [map_smul, norm_smul, norm_inv, norm_norm]
    rw [inv_mul_cancel₀]
    simp only [ne_eq, norm_eq_zero]
    contrapose! hL_zero
    exact hL_zero_of_L2 hL_zero
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv,
    norm_norm, map_smul, norm_smul] at h
  rwa [mul_assoc, mul_le_mul_iff_of_pos_left] at h
  simp only [inv_pos, norm_pos_iff, ne_eq]
  contrapose! hL_zero
  exact hL_zero_of_L2 hL_zero

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [SecondCountableTopology E] in
lemma covarianceBilin_apply' [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    covarianceBilin μ L₁ L₂ = ∫ x, L₁ (x - μ[id]) * L₂ (x - μ[id]) ∂μ := by
  rw [covarianceBilin_apply h]
  have hL (L : Dual ℝ E) : μ[L] = L (∫ x, x ∂μ) := L.integral_comp_comm (h.integrable (by simp))
  simp [← hL]

section centeredToLp

noncomputable
def integralDualCLM (μ : Measure E) : Dual ℝ E →L[ℝ] ℝ := L1.integralCLM.comp (Dual.toLp μ 1)

noncomputable
def integralDualCLM' (μ : Measure E) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Dual ℝ E →L[ℝ] Lp ℝ p μ :=
  (Lp.constL p μ ℝ).comp (integralDualCLM μ)

noncomputable
def Dual.centeredToLp (μ : Measure E) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Dual ℝ E →L[ℝ] Lp ℝ p μ :=
  Dual.toLp μ p - integralDualCLM' μ p

lemma centeredToLp_apply (μ : Measure E) [IsGaussian μ] (hp : p ≠ ∞) (L : Dual ℝ E) :
    Dual.centeredToLp μ p L =ᵐ[μ] fun x ↦ L (x - ∫ z, z ∂μ) := by
  simp only [Dual.centeredToLp, ContinuousLinearMap.coe_sub', Pi.sub_apply,
    AddSubgroupClass.coe_sub, map_sub]
  filter_upwards [Dual.toLp_apply_ae (IsGaussian.memLp_id μ p hp) L,
    Lp.coeFn_sub (Dual.toLp μ p L) (integralDualCLM' μ p L)] with x hx₁ hx₂
  simp only [AddSubgroupClass.coe_sub, Pi.sub_apply] at hx₂
  rw [← hx₁, hx₂]
  congr
  simp only [integralDualCLM', integralDualCLM, ContinuousLinearMap.coe_comp', Function.comp_apply,
    Lp.constL_apply, Lp.const_val, AEEqFun.coeFn_const_eq]
  rw [← L1.integral_eq, L1.integral_eq_integral, ← IsGaussian.integral_dual]
  refine integral_congr_ae ?_
  exact Dual.toLp_apply_ae (IsGaussian.memLp_id μ 1 (by simp)) L

lemma norm_centeredToLp [IsGaussian μ] (L : Dual ℝ E) :
    ‖Dual.centeredToLp μ 2 L‖ = √(covarianceBilin μ L L) := by
  simp only [covarianceBilin_apply' (IsGaussian.memLp_id μ 2 (by simp)), id_eq]
  rw [norm_eq_sqrt_real_inner]
  congr
  refine integral_congr_ae ?_
  filter_upwards [centeredToLp_apply μ (by simp : 2 ≠ ∞) L] with x hx
  simp [hx]

lemma sq_norm_centeredToLp [IsGaussian μ] (L : Dual ℝ E) :
    ‖Dual.centeredToLp μ 2 L‖ ^ 2 = covarianceBilin μ L L := by
  rw [norm_centeredToLp, Real.sq_sqrt]
  rw [covarianceBilin_same_eq_variance (IsGaussian.memLp_id μ 2 (by simp))]
  exact variance_nonneg _ _

end centeredToLp

variable [IsGaussian μ]

section CameronMartinSpace

noncomputable
abbrev CameronMartin (μ : Measure E) [IsFiniteMeasure μ] :=
  Completion (Submodule.map (Dual.centeredToLp μ 2) ⊤)

noncomputable
instance [IsFiniteMeasure μ] : NormedAddCommGroup (CameronMartin μ) := by
  unfold CameronMartin; infer_instance

noncomputable
instance [IsFiniteMeasure μ] : InnerProductSpace ℝ (CameronMartin μ) := by
  unfold CameronMartin; infer_instance

instance [IsFiniteMeasure μ] : CompleteSpace (CameronMartin μ) := by
  unfold CameronMartin; infer_instance

noncomputable
def pureCameronMartin (μ : Measure E) [IsFiniteMeasure μ] (L : Dual ℝ E) : CameronMartin μ :=
  (⟨Dual.centeredToLp μ 2 L, Submodule.mem_map.mpr ⟨L, by simp, rfl⟩⟩ :
    Submodule.map (Dual.centeredToLp μ 2) ⊤)

lemma norm_pureCameronMartin (L : Dual ℝ E) :
    ‖pureCameronMartin μ L‖ = √(covarianceBilin μ L L) := by
  rw [pureCameronMartin, Completion.norm_coe]
  simp only [AddSubgroupClass.coe_norm]
  exact norm_centeredToLp _

lemma sq_norm_pureCameronMartin (L : Dual ℝ E) :
    ‖pureCameronMartin μ L‖ ^ 2 = covarianceBilin μ L L := by
  rw [norm_pureCameronMartin, Real.sq_sqrt]
  rw [covarianceBilin_same_eq_variance (IsGaussian.memLp_id μ 2 (by simp))]
  exact variance_nonneg _ _

end CameronMartinSpace

section EvaluationMap

variable {y : E}

noncomputable
def evalL2 (μ : Measure E) [IsGaussian μ]
    (y : E) (x : Submodule.map (Dual.centeredToLp μ 2) ⊤) : ℝ :=
  (Submodule.mem_map.mp x.2).choose y

lemma norm_eval_le_norm_centeredToLp_mul
    (hy : ∃ M, ∀ L : Dual ℝ E, covarianceBilin μ L L ≤ 1 → L y ≤ M) (L : Dual ℝ E) :
    ‖L y‖ ≤ ‖Dual.centeredToLp μ 2 L‖
      * ⨆ (L' : Dual ℝ E) (_ : covarianceBilin μ L' L' ≤ 1), L' y := by
  simp_rw [← sq_norm_centeredToLp, sq_le_one_iff_abs_le_one, abs_norm] at hy ⊢
  exact norm_eval_le_norm_mul_ciSup (Dual.centeredToLp μ 2) hy L

lemma norm_evalL2_le (hy : ∃ M, ∀ L : Dual ℝ E, covarianceBilin μ L L ≤ 1 → L y ≤ M)
    (x : Submodule.map (Dual.centeredToLp μ 2) ⊤) :
    ‖evalL2 μ y x‖ ≤ ‖x‖ * ⨆ (L : Dual ℝ E) (_ : covarianceBilin μ L L ≤ 1), L y := by
  simp only [AddSubgroupClass.coe_norm]
  conv_rhs => rw [← (Submodule.mem_map.mp x.2).choose_spec.2]
  exact norm_eval_le_norm_centeredToLp_mul hy (Submodule.mem_map.mp x.2).choose

lemma eval_eq_of_centeredToLp_eq (hy : ∃ M, ∀ L : Dual ℝ E, covarianceBilin μ L L ≤ 1 → L y ≤ M)
    (L L' : Dual ℝ E) (hL : Dual.centeredToLp μ 2 L = Dual.centeredToLp μ 2 L') :
    L y = L' y := by
  rw [← sub_eq_zero, ← Pi.sub_apply, ← norm_eq_zero]
  suffices ‖⇑(L - L') y‖ = 0 by simpa
  refine le_antisymm ?_ (by positivity)
  refine (norm_eval_le_norm_centeredToLp_mul hy _ (μ := μ)).trans ?_
  simp [hL]

lemma evalL2_eq (hy : ∃ M, ∀ L : Dual ℝ E, covarianceBilin μ L L ≤ 1 → L y ≤ M)
    (x : Submodule.map (Dual.centeredToLp μ 2) ⊤)
    {L : Dual ℝ E} (hL : Dual.centeredToLp μ 2 L = x) :
    evalL2 μ y x = L y := by
  rw [evalL2]
  refine eval_eq_of_centeredToLp_eq hy (Submodule.mem_map.mp x.2).choose L ?_
  rw [hL, (Submodule.mem_map.mp x.2).choose_spec.2]

lemma evalL2_centeredToLp_eq (hy : ∃ M, ∀ L : Dual ℝ E, covarianceBilin μ L L ≤ 1 → L y ≤ M)
    (L : Dual ℝ E) :
    evalL2 μ y ⟨Dual.centeredToLp μ 2 L, Submodule.mem_map.mpr ⟨L, by simp, rfl⟩⟩ = L y :=
  evalL2_eq hy _ (by simp)

noncomputable
def evalL2CLM (μ : Measure E) [IsGaussian μ] (y : E)
    (hy : ∃ M, ∀ L : Dual ℝ E, covarianceBilin μ L L ≤ 1 → L y ≤ M) :
    Submodule.map (Dual.centeredToLp μ 2) ⊤ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun x := evalL2 μ y x
      map_add' x₁ x₂ := by
        obtain ⟨L₁, -, hL₁⟩ := Submodule.mem_map.mp x₁.2
        obtain ⟨L₂, -, hL₂⟩ := Submodule.mem_map.mp x₂.2
        rw [evalL2_eq hy x₁ hL₁, evalL2_eq hy x₂ hL₂, evalL2_eq hy (x₁ + x₂) (L := L₁ + L₂)]
        · simp
        · simp [hL₁, hL₂]
      map_smul' r x := by
        obtain ⟨L, -, hL⟩ := Submodule.mem_map.mp x.2
        rw [evalL2_eq hy x hL, evalL2_eq hy (r • x) (L := r • L)]
        · simp
        · simp [hL] }
    (⨆ (L' : Dual ℝ E) (_ : covarianceBilin μ L' L' ≤ 1), L' y) fun x ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, AddSubgroupClass.coe_norm]
    rw [mul_comm]
    exact norm_evalL2_le hy x

noncomputable
def evalMapCLM (μ : Measure E) [IsGaussian μ] (y : E)
    (hy : ∃ M, ∀ L : Dual ℝ E, covarianceBilin μ L L ≤ 1 → L y ≤ M) :
    Dual ℝ (CameronMartin μ) :=
  Completion.continuousLinearMapExtension (evalL2CLM μ y hy)

lemma evalMapCLM_pureCameronMartin (hy : ∃ M, ∀ L : Dual ℝ E, covarianceBilin μ L L ≤ 1 → L y ≤ M)
    (L : Dual ℝ E) :
    evalMapCLM μ y hy (pureCameronMartin μ L) = L y := by
  simp only [evalMapCLM, Completion.continuousLinearMapExtension, ContinuousLinearMap.coe_mk',
    LinearMap.coe_mk, AddHom.coe_mk] -- extract lemma
  rw [pureCameronMartin, Completion.extension_coe (ContinuousLinearMap.uniformContinuous _)]
  simp only [evalL2CLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [evalL2_centeredToLp_eq hy]

noncomputable
def toCameronMartin (μ : Measure E) [IsGaussian μ] (y : E)
    (hy : ∃ M, ∀ L : Dual ℝ E, covarianceBilin μ L L ≤ 1 → L y ≤ M) :
    CameronMartin μ :=
  (InnerProductSpace.toDual ℝ (CameronMartin μ)).symm (evalMapCLM μ y hy)

lemma evalMapCLM_apply (μ : Measure E) [IsGaussian μ]
    (hy : ∃ M, ∀ L : Dual ℝ E, covarianceBilin μ L L ≤ 1 → L y ≤ M)
    (x : CameronMartin μ) :
    evalMapCLM μ y hy x = ⟪x, toCameronMartin μ y hy⟫_ℝ := by
  rw [toCameronMartin, real_inner_comm, InnerProductSpace.toDual_symm_apply]

end EvaluationMap

section ToInitialSpace

noncomputable
def toInit (μ : Measure E) [IsFiniteMeasure μ] (x : Submodule.map (Dual.centeredToLp μ 2) ⊤) : E :=
  ∫ y, (Submodule.mem_map.mp x.2).choose (y - ∫ z, z ∂μ) • (y - ∫ z, z ∂μ) ∂μ

lemma toInit_eq (x : Submodule.map (Dual.centeredToLp μ 2) ⊤) {L : Dual ℝ E}
    (hL : Dual.centeredToLp μ 2 L = x) :
    toInit μ x = ∫ y, L (y - ∫ z, z ∂μ) • (y - ∫ z, z ∂μ) ∂μ :=
  calc toInit μ x
  _ = ∫ y, x.1 y • (y - ∫ z, z ∂μ) ∂μ := by
    rw [toInit]
    conv_rhs => rw [← (Submodule.mem_map.mp x.2).choose_spec.2]
    refine integral_congr_ae ?_
    filter_upwards [centeredToLp_apply μ (by simp : 2 ≠ ∞) (Submodule.mem_map.mp x.2).choose]
      with y hy
    rw [hy]
  _ = ∫ y, Dual.centeredToLp μ 2 L y • (y - ∫ z, z ∂μ) ∂μ := by rw [hL]
  _ = ∫ y, L (y - ∫ z, z ∂μ) • (y - ∫ z, z ∂μ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [centeredToLp_apply μ (by simp : 2 ≠ ∞) L] with y hy
    rw [hy]

lemma apply_toInit (x : Submodule.map (Dual.centeredToLp μ 2) ⊤) (L : Dual ℝ E) :
    L (toInit μ x)
      = ∫ y, (Submodule.mem_map.mp x.2).choose (y - ∫ z, z ∂μ) * L (y - ∫ z, z ∂μ) ∂μ := by
  rw [toInit, ← L.integral_comp_comm]
  · simp
  rw [← integrable_norm_iff]
  swap; · fun_prop
  simp only [Submodule.mem_top, true_and, map_sub, norm_smul]
  refine MemLp.integrable_mul (p := 2) (q := 2) ?_ ?_
  · rw [memLp_norm_iff]
    swap; · fun_prop
    exact MemLp.sub (IsGaussian.memLp_dual μ _ 2 (by simp)) (memLp_const _)
  · rw [memLp_norm_iff]
    swap; · fun_prop
    exact MemLp.sub (IsGaussian.memLp_id μ 2 (by simp)) (memLp_const _)

lemma apply_toInit_eq_inner (x : Submodule.map (Dual.centeredToLp μ 2) ⊤) (L : Dual ℝ E) :
    L (toInit μ x) = ⟪Dual.centeredToLp μ 2 L, x⟫_ℝ := by
  rw [← (Submodule.mem_map.mp x.2).choose_spec.2]
  rw [L2.inner_def, apply_toInit]
  simp only [RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [centeredToLp_apply μ (by simp : 2 ≠ ∞) L,
    centeredToLp_apply μ (by simp : 2 ≠ ∞) (Submodule.mem_map.mp x.2).choose] with y hy₁ hy₂
  rw [hy₁, hy₂]

lemma norm_toInit_le (x : Submodule.map (Dual.centeredToLp μ 2) ⊤) :
    ‖toInit μ x‖ ≤ ‖Dual.centeredToLp μ 2‖ * ‖x‖ := by
  refine norm_le_dual_bound ℝ _ (by positivity) fun L ↦ ?_
  calc ‖L (toInit μ x)‖
  _ = ‖⟪Dual.centeredToLp μ 2 L, x⟫_ℝ‖ := by rw [apply_toInit_eq_inner]
  _ ≤ ‖Dual.centeredToLp μ 2 L‖ * ‖x‖ := norm_inner_le_norm ((Dual.centeredToLp μ 2) L) x
  _ ≤ ‖Dual.centeredToLp μ 2‖ * ‖L‖ * ‖x‖ := by
    gcongr
    exact (Dual.centeredToLp μ 2).le_opNorm L
  _ = ‖Dual.centeredToLp μ 2‖ * ‖x‖ * ‖L‖ := by ring

noncomputable
def toInitialSpaceₗ' (μ : Measure E) [IsGaussian μ] :
    Submodule.map (Dual.centeredToLp μ 2) ⊤ →ₗ[ℝ] E where
  toFun x := toInit μ x
  map_add' x y := by
    rw [eq_iff_forall_dual_eq (𝕜 := ℝ)]
    intro L
    simp_rw [map_add, apply_toInit_eq_inner, Submodule.coe_add, inner_add_right]
  map_smul' r x := by
    rw [eq_iff_forall_dual_eq (𝕜 := ℝ)]
    intro L
    simp_rw [map_smul, apply_toInit_eq_inner, Submodule.coe_smul, inner_smul_right]
    simp

noncomputable
def toInitialSpace' (μ : Measure E) [IsGaussian μ] :
    Submodule.map (Dual.centeredToLp μ 2) ⊤ →L[ℝ] E :=
  (toInitialSpaceₗ' μ).mkContinuous ‖Dual.centeredToLp μ 2‖ norm_toInit_le

lemma apply_toInitialSpace'_eq_inner (x : Submodule.map (Dual.centeredToLp μ 2) ⊤) (L : Dual ℝ E) :
    L (toInitialSpace' μ x) = ⟪Dual.centeredToLp μ 2 L, x⟫_ℝ := by
  simp [toInitialSpace', toInitialSpaceₗ', apply_toInit_eq_inner]

noncomputable
def toInitialSpace (μ : Measure E) [IsGaussian μ] (x : CameronMartin μ) : E :=
  Completion.extension (toInitialSpace' μ) x

@[fun_prop]
lemma continuous_toInitialSpace :
    Continuous (toInitialSpace μ : CameronMartin μ → E) := Completion.continuous_extension

lemma apply_toInitialSpace_eq_inner (x : CameronMartin μ) (L : Dual ℝ E) :
    L (toInitialSpace μ x) = ⟪pureCameronMartin μ L, x⟫_ℝ := by
  revert x
  rw [← funext_iff]
  refine Completion.ext (by fun_prop) (by fun_prop) fun x ↦ ?_
  rw [toInitialSpace, Completion.extension_coe, apply_toInitialSpace'_eq_inner]
  · rw [pureCameronMartin, Completion.inner_coe]
    rfl
  · exact ContinuousLinearMap.uniformContinuous _

noncomputable
def toInitialSpaceCLM (μ : Measure E) [IsGaussian μ] : CameronMartin μ →L[ℝ] E where
  toFun x := toInitialSpace μ x
  map_add' x y := by
    rw [eq_iff_forall_dual_eq (𝕜 := ℝ)]
    intro L
    simp_rw [map_add, apply_toInitialSpace_eq_inner, inner_add_right]
  map_smul' r x := by
    rw [eq_iff_forall_dual_eq (𝕜 := ℝ)]
    intro L
    simp_rw [map_smul, apply_toInitialSpace_eq_inner, inner_smul_right]
    simp
  cont := Completion.continuous_extension

lemma apply_toInitialSpaceCLM_eq_inner (x : CameronMartin μ) (L : Dual ℝ E) :
    L (toInitialSpaceCLM μ x) = ⟪pureCameronMartin μ L, x⟫_ℝ := by
  simp [toInitialSpaceCLM, apply_toInitialSpace_eq_inner]

lemma eq_zero_of_toInitialSpaceCLM_eq_zero {x : CameronMartin μ} (h : toInitialSpaceCLM μ x = 0) :
    x = 0 := by
  suffices ∀ y : CameronMartin μ, ⟪y, x⟫_ℝ = 0 by
    rw [← inner_self_eq_zero (𝕜 := ℝ) (x := x)]
    exact this x
  rw [← funext_iff]
  refine Completion.ext (by fun_prop) (by fun_prop) fun L ↦ ?_
  obtain ⟨L', -, hL'⟩ := Submodule.mem_map.mp L.2
  have : pureCameronMartin μ L' = ((↑) : Submodule.map (Dual.centeredToLp μ 2) ⊤
      → Completion (Submodule.map (Dual.centeredToLp μ 2) ⊤)) L := by
    unfold pureCameronMartin
    congr
  rw [← this, ← apply_toInitialSpaceCLM_eq_inner, h]
  simp

lemma toInitialSpaceCLM_injective : Function.Injective (toInitialSpaceCLM μ) := by
  intro x y h
  rw [← sub_eq_zero, ← map_sub] at h
  rw [← sub_eq_zero, eq_zero_of_toInitialSpaceCLM_eq_zero h]

lemma todooo (x : CameronMartin μ) {L : Dual ℝ E} (hL : covarianceBilin μ L L ≤ 1) :
    L (toInitialSpace μ x) ≤ ‖x‖ := by
  calc L (toInitialSpace μ x)
  _ = ⟪pureCameronMartin μ L, x⟫_ℝ := apply_toInitialSpace_eq_inner x L
  _ ≤ ‖⟪pureCameronMartin μ L, x⟫_ℝ‖ := Real.le_norm_self _
  _ ≤ ‖pureCameronMartin μ L‖ * ‖x‖ := norm_inner_le_norm (pureCameronMartin μ L) x
  _ = √(covarianceBilin μ L L) * ‖x‖ := by rw [norm_pureCameronMartin]
  _ ≤ 1 * ‖x‖ := by gcongr; exact Real.sqrt_le_one.mpr hL
  _ = ‖x‖ := by rw [one_mul]

end ToInitialSpace

lemma toInitialSpaceCLM_toCameronMartin {y : E}
    (hy : ∃ M, ∀ L : Dual ℝ E, covarianceBilin μ L L ≤ 1 → L y ≤ M) :
    toInitialSpaceCLM μ (toCameronMartin μ y hy) = y := by
  rw [eq_iff_forall_dual_eq (𝕜 := ℝ)]
  intro L
  rw [← evalMapCLM_pureCameronMartin hy, apply_toInitialSpaceCLM_eq_inner, evalMapCLM_apply]

end ProbabilityTheory
