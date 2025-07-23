/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.MeasureTheory.Measure.SeparableMeasure
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

lemma InnerProductSpace.norm_le_dual_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ y : E, ⟪x, y⟫_ℝ ≤ M * ‖y‖) :
    ‖x‖ ≤ M := by
  refine NormedSpace.norm_le_dual_bound ℝ _ hMp fun f ↦ ?_
  let y := (InnerProductSpace.toDual ℝ E).symm f
  obtain hy : f x = ⟪x, y⟫_ℝ := by
    unfold y
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  rw [hy]
  simp only [Real.norm_eq_abs, abs_le]
  constructor
  · specialize hM (-y)
    simp only [inner_neg_right, norm_neg] at hM
    rw [← neg_le]
    convert hM
    simp [y]
  · convert hM y
    simp [y]

lemma InnerProductSpace.norm_le_dual_bound_of_norm_le_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ y : E, ‖y‖ ≤ 1 → ⟪x, y⟫_ℝ ≤ M) :
    ‖x‖ ≤ M := by
  refine InnerProductSpace.norm_le_dual_bound x hMp fun y ↦ ?_
  by_cases h_zero : ‖y‖ = 0
  · simp only [h_zero, mul_zero]
    rw [inner_eq_zero_of_right _ h_zero]
  specialize hM (‖y‖⁻¹ • y) ?_
  · simp only [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm]
    exact inv_mul_le_one
  · simp only [inner_smul_right] at hM
    rwa [inv_mul_le_iff₀ (by positivity), mul_comm] at hM

lemma InnerProductSpace.norm_eq_ciSup_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (x : E) :
    ‖x‖ = ⨆ (y : E) (_ : ‖y‖ ≤ 1), ⟪x, y⟫_ℝ := by
  have h_ciSup_le y : ⨆ (_ : ‖y‖ ≤ 1), ⟪x, y⟫_ℝ ≤ ‖x‖ := by
    by_cases hy : ‖y‖ ≤ 1
    · simp only [hy, ciSup_unique]
      calc ⟪x, y⟫_ℝ
      _ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * 1 := by gcongr
      _ = ‖x‖ := by rw [mul_one]
    · simp [hy]
  have h_bdd : BddAbove (Set.range fun y ↦ ⨆ (_ : ‖y‖ ≤ 1), ⟪x, y⟫_ℝ) := by
    refine ⟨‖x‖, ?_⟩
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    intro y
    exact h_ciSup_le y
  refine le_antisymm ?_ (ciSup_le h_ciSup_le)
  · refine InnerProductSpace.norm_le_dual_bound_of_norm_le_one x ?_ fun y hy ↦ ?_
    · exact le_ciSup_of_le h_bdd 0 (by simp)
    · exact le_ciSup_of_le h_bdd y (by simp [hy])

namespace UniformSpace.Completion

/-- Extension of a continuous linear map `E →L[R] F` into a complete space to the completion of `E`,
giving a continuous linear map `Completion E →L[R] F`. -/
noncomputable
def continuousLinearMapExtension (R : Type*) {E F : Type*} [Semiring R]
    [UniformSpace E] [AddCommGroup E] [IsUniformAddGroup E]
    [Module R E] [UniformContinuousConstSMul R E]
    [UniformSpace F] [AddCommGroup F] [IsUniformAddGroup F]
    [Module R F] [UniformContinuousConstSMul R F] [T2Space F] [CompleteSpace F]
    (f : E →L[R] F) :
    Completion E →L[R] F where
  toFun x := Completion.extension f x
  map_add' x₁ x₂ := by
    refine Completion.induction_on₂ x₁ x₂ ?_ fun x₁' x₂' ↦ ?_
    · have : Continuous (Completion.extension f) := continuous_extension
      exact isClosed_eq (by fun_prop) (by fun_prop)
    · rw [extension_coe, extension_coe, ← map_add, ← extension_coe (f := f)]
      · congr
        norm_cast
      all_goals exact ContinuousLinearMap.uniformContinuous _
  map_smul' r x := by
    simp only [RingHom.id_apply]
    induction x using Completion.induction_on with
    | hp =>
      have h_cont : Continuous (Completion.extension f) := continuous_extension
      refine isClosed_eq ?_ (by fun_prop)
      -- fun_prop fails here (it also fails in the `have` below)
      have : Continuous fun (a : Completion E) ↦ r • a := continuous_const_smul _
      exact h_cont.comp this
    | ih x =>
      rw [extension_coe, ← map_smul, ← extension_coe (f := f)]
      · congr
        norm_cast
      all_goals exact ContinuousLinearMap.uniformContinuous _
  cont := continuous_extension

lemma continuousLinearMapExtension_apply {R E F : Type*} [Semiring R]
    [UniformSpace E] [AddCommGroup E] [IsUniformAddGroup E]
    [Module R E] [UniformContinuousConstSMul R E]
    [UniformSpace F] [AddCommGroup F] [IsUniformAddGroup F]
    [Module R F] [UniformContinuousConstSMul R F] [T2Space F] [CompleteSpace F]
    (f : E →L[R] F) (x : Completion E) :
    Completion.continuousLinearMapExtension R f x = Completion.extension f x := by
  simp [continuousLinearMapExtension]

@[simp]
lemma continuousLinearMapExtension_coe {R E F : Type*} [Semiring R]
    [UniformSpace E] [AddCommGroup E] [IsUniformAddGroup E]
    [Module R E] [UniformContinuousConstSMul R E]
    [UniformSpace F] [AddCommGroup F] [IsUniformAddGroup F]
    [Module R F] [UniformContinuousConstSMul R F] [T2Space F] [CompleteSpace F]
    (f : E →L[R] F) (x : E) :
    Completion.continuousLinearMapExtension R f x = f x := by
  simp [continuousLinearMapExtension, extension_coe f.uniformContinuous]

end UniformSpace.Completion

lemma norm_eval_le_norm_mul_ciSup {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [Module ℝ G] [NormSMulClass ℝ G]
    (f : Dual ℝ E →ₗ[ℝ] G) {y : E} (hy : ∃ M, ∀ L, ‖f L‖ ≤ 1 → L y ≤ M) (L : Dual ℝ E) :
    ‖L y‖ ≤ ‖f L‖ * ⨆ (L') (_ : ‖f L'‖ ≤ 1), L' y := by
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

-- added in another PR
omit [SecondCountableTopology E] in
lemma covarianceBilin_apply' [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    covarianceBilin μ L₁ L₂ = ∫ x, L₁ (x - μ[id]) * L₂ (x - μ[id]) ∂μ := by
  rw [covarianceBilin_apply h]
  have hL (L : Dual ℝ E) : μ[L] = L (∫ x, x ∂μ) := L.integral_comp_comm (h.integrable (by simp))
  simp [← hL]

section centeredToLp

/-- The Bochner integral as a continuous linear map from the dual to `ℝ`.
This is well defined if the measure has a first moment. If not, it is uniformly zero (since
`Dual.toLp` is zero in that case). -/
noncomputable
def integralDualCLM (μ : Measure E) : Dual ℝ E →L[ℝ] ℝ := L1.integralCLM.comp (Dual.toLp μ 1)

/-- The function `L ↦ L (x - μ[id])` as a continuous linear map from the dual to `Lp ℝ p μ`.
This definition takes meaningful values only if the measure has a first moment and a moment of
order `p` (`MemLp id 1 μ` and `MemLp id p μ`). -/
noncomputable
def Dual.centeredToLp (μ : Measure E) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Dual ℝ E →L[ℝ] Lp ℝ p μ :=
  Dual.toLp μ p - (Lp.constL p μ ℝ).comp (integralDualCLM μ)

lemma centeredToLp_apply (μ : Measure E) [IsGaussian μ] (hp : p ≠ ∞) (L : Dual ℝ E) :
    Dual.centeredToLp μ p L =ᵐ[μ] fun x ↦ L (x - ∫ z, z ∂μ) := by
  simp only [Dual.centeredToLp, ContinuousLinearMap.coe_sub', Pi.sub_apply,
    AddSubgroupClass.coe_sub, map_sub]
  filter_upwards [Dual.toLp_apply_ae (IsGaussian.memLp_id μ p hp) L,
    Lp.coeFn_sub (Dual.toLp μ p L) ((Lp.constL p μ ℝ).comp (integralDualCLM μ) L)] with x hx₁ hx₂
  simp only [AddSubgroupClass.coe_sub, Pi.sub_apply] at hx₂
  rw [← hx₁, hx₂]
  congr
  simp only [integralDualCLM, ContinuousLinearMap.coe_comp', Function.comp_apply,
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

/-- The Cameron-Martin space of a Gaussian measure.
This is a separable Hilbert space. -/
noncomputable
abbrev CameronMartin (μ : Measure E) [IsFiniteMeasure μ] :=
  Completion (Submodule.map (Dual.centeredToLp μ 2) ⊤)

-- Uncomment the following lines to check that we can synthesize instances for `CameronMartin μ`:
-- #synth NormedAddCommGroup (CameronMartin μ)
-- #synth InnerProductSpace ℝ (CameronMartin μ)
-- #synth CompleteSpace (CameronMartin μ)

instance (μ : Measure E) [IsFiniteMeasure μ] : SecondCountableTopology (CameronMartin μ) := by
  suffices SecondCountableTopology (Submodule.map (Dual.centeredToLp μ 2) ⊤) by infer_instance
  have : Fact (2 ≠ ∞) := ⟨by simp⟩
  exact TopologicalSpace.Subtype.secondCountableTopology _

namespace CameronMartin

/-- Inclusion from the dual into the Cameron-Martin space, as a linear map. -/
noncomputable
def ofDual (μ : Measure E) [IsFiniteMeasure μ] : Dual ℝ E →ₗ[ℝ] CameronMartin μ :=
  Completion.toComplL.toLinearMap.comp (((Dual.centeredToLp μ 2).submoduleMap ⊤).comp
    (Submodule.topEquiv (R := ℝ) (M := Dual ℝ E)).symm.toLinearMap)

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma ofDual_apply (L : Dual ℝ E) :
    ofDual μ L
      = (⟨Dual.centeredToLp μ 2 L, Submodule.mem_map.mpr ⟨L, by simp, rfl⟩⟩ :
        Submodule.map (Dual.centeredToLp μ 2) ⊤) := rfl

lemma norm_ofDual (L : Dual ℝ E) : ‖ofDual μ L‖ = √(covarianceBilin μ L L) := by
  rw [ofDual_apply]
  simp only [Completion.norm_coe, AddSubgroupClass.coe_norm]
  exact norm_centeredToLp _

lemma sq_norm_ofDual (L : Dual ℝ E) : ‖ofDual μ L‖ ^ 2 = covarianceBilin μ L L := by
  rw [norm_ofDual, Real.sq_sqrt]
  rw [covarianceBilin_same_eq_variance (IsGaussian.memLp_id μ 2 (by simp))]
  exact variance_nonneg _ _

end CameronMartin

end CameronMartinSpace

section EvaluationMap

variable {y : E}

namespace CameronMartinAux -- namespace for auxiliary definitions and lemmas

/-- For an L2 function `x` in the image of `Dual ℝ E` by `Dual.centeredToLp μ 2`, we can evaluate
`x` at `y : E` by taking `L y` for an arbitrary `L : Dual ℝ E` that is sent to `x`.
This is an auxiliary definition for `CameronMartin.eval`. -/
noncomputable
def evalL2 (μ : Measure E) [IsGaussian μ] (y : E) (x : Submodule.map (Dual.centeredToLp μ 2) ⊤) :
    ℝ :=
  (Submodule.mem_map.mp x.2).choose y

lemma norm_eval_le_norm_centeredToLp_mul (hy : ∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M)
    (L : Dual ℝ E) :
    ‖L y‖ ≤ ‖Dual.centeredToLp μ 2 L‖ * ⨆ (L') (_ : covarianceBilin μ L' L' ≤ 1), L' y := by
  simp_rw [← sq_norm_centeredToLp, sq_le_one_iff_abs_le_one, abs_norm] at hy ⊢
  exact norm_eval_le_norm_mul_ciSup (Dual.centeredToLp μ 2).toLinearMap hy L

lemma norm_evalL2_le (hy : ∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M)
    (x : Submodule.map (Dual.centeredToLp μ 2) ⊤) :
    ‖evalL2 μ y x‖ ≤ ‖x‖ * ⨆ (L : Dual ℝ E) (_ : covarianceBilin μ L L ≤ 1), L y := by
  simp only [AddSubgroupClass.coe_norm]
  conv_rhs => rw [← (Submodule.mem_map.mp x.2).choose_spec.2]
  exact norm_eval_le_norm_centeredToLp_mul hy (Submodule.mem_map.mp x.2).choose

lemma eval_eq_of_centeredToLp_eq (hy : ∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M)
    (L L' : Dual ℝ E) (hL : Dual.centeredToLp μ 2 L = Dual.centeredToLp μ 2 L') :
    L y = L' y := by
  rw [← sub_eq_zero, ← Pi.sub_apply, ← norm_eq_zero]
  suffices ‖⇑(L - L') y‖ = 0 by simpa
  refine le_antisymm ?_ (by positivity)
  refine (norm_eval_le_norm_centeredToLp_mul hy _ (μ := μ)).trans ?_
  simp [hL]

lemma evalL2_eq (hy : ∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M)
    (x : Submodule.map (Dual.centeredToLp μ 2) ⊤)
    {L : Dual ℝ E} (hL : Dual.centeredToLp μ 2 L = x) :
    evalL2 μ y x = L y := by
  rw [evalL2]
  refine eval_eq_of_centeredToLp_eq hy (Submodule.mem_map.mp x.2).choose L ?_
  rw [hL, (Submodule.mem_map.mp x.2).choose_spec.2]

lemma evalL2_centeredToLp_eq (hy : ∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M)
    (L : Dual ℝ E) :
    evalL2 μ y ⟨Dual.centeredToLp μ 2 L, Submodule.mem_map.mpr ⟨L, by simp, rfl⟩⟩ = L y :=
  evalL2_eq hy _ (by simp)

end CameronMartinAux

namespace CameronMartin
open CameronMartinAux

/-- Evaluation map on the Cameron-Martin space. `CameronMartin.eval μ y hy x` is the evaluation of
`x` at `y`, where `x` is an element of the Cameron-Martin space of the Gaussian measure `μ`.
This map is defined for `y` with bounded Cameron-Martin norm, i.e., such that there exists `M` with
`∀ L : Dual ℝ E, covarianceBilin μ L L ≤ 1 → L y ≤ M`.
It satisfies `eval μ y hy (ofDual μ L) = L y`. -/
noncomputable
def eval (μ : Measure E) [IsGaussian μ] (y : E)
    (hy : ∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M) :
    Dual ℝ (CameronMartin μ) :=
  Completion.continuousLinearMapExtension ℝ <|
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
    (⨆ (L') (_ : covarianceBilin μ L' L' ≤ 1), L' y) fun x ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, AddSubgroupClass.coe_norm]
    rw [mul_comm]
    exact norm_evalL2_le hy x

lemma eval_ofDual (hy : ∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M) (L : Dual ℝ E) :
    eval μ y hy (ofDual μ L) = L y := by
  rw [ofDual_apply]
  simp only [eval, Completion.continuousLinearMapExtension_coe, LinearMap.mkContinuous_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [evalL2_centeredToLp_eq hy]

/-- Map from the space on which a Gaussian measure `μ` is defined to the Cameron-Martin space
of `μ`. This takes a meaningful value only if the argument has bounded Cameron-Martin norm,
and takes the default value zero otherwise. -/
noncomputable
def ofBounded (μ : Measure E) [IsGaussian μ] (y : E)
    [Decidable (∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M)] :
    CameronMartin μ :=
  if hy : ∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M
    then (InnerProductSpace.toDual ℝ (CameronMartin μ)).symm (eval μ y hy)
    else 0

variable [Decidable (∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M)]

lemma ofBounded_def (hy : ∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M) :
    ofBounded μ y = (InnerProductSpace.toDual ℝ (CameronMartin μ)).symm (eval μ y hy) := by
  simp [ofBounded, hy]

lemma eval_apply (hy : ∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M) (x : CameronMartin μ) :
    eval μ y hy x = ⟪x, ofBounded μ y⟫_ℝ := by
  rw [ofBounded_def hy, real_inner_comm, InnerProductSpace.toDual_symm_apply]

end CameronMartin

end EvaluationMap

section ToInitialSpace

namespace CameronMartinAux -- namespace for auxiliary definitions and lemmas

/-- From `x` in the image of `Dual ℝ E` by `Dual.centeredToLp μ 2`, we define a point of `E` by
`∫ y, L (y - ∫ z, z ∂μ) • (y - ∫ z, z ∂μ) ∂μ` for an arbitrary `L : Dual ℝ E` with
`Dual.centeredToLp μ 2 L = x`.
This is an auxiliary definition for `CameronMartin.toInitialSpace`. -/
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
    filter_upwards [centeredToLp_apply μ (by simp : 2 ≠ ∞) L] with y hy using by rw [hy]

lemma apply_toInit (x : Submodule.map (Dual.centeredToLp μ 2) ⊤) (L : Dual ℝ E) :
    L (toInit μ x)
      = ∫ y, (Submodule.mem_map.mp x.2).choose (y - ∫ z, z ∂μ) * L (y - ∫ z, z ∂μ) ∂μ := by
  rw [toInit, ← L.integral_comp_comm]
  · simp
  rw [← integrable_norm_iff (by fun_prop)]
  simp only [Submodule.mem_top, true_and, map_sub, norm_smul]
  refine MemLp.integrable_mul (p := 2) (q := 2) ?_ ?_
  · rw [memLp_norm_iff (by fun_prop)]
    exact MemLp.sub (IsGaussian.memLp_dual μ _ 2 (by simp)) (memLp_const _)
  · rw [memLp_norm_iff (by fun_prop)]
    exact MemLp.sub (IsGaussian.memLp_id μ 2 (by simp)) (memLp_const _)

lemma apply_toInit_eq_inner (x : Submodule.map (Dual.centeredToLp μ 2) ⊤) (L : Dual ℝ E) :
    L (toInit μ x) = ⟪Dual.centeredToLp μ 2 L, x⟫_ℝ := by
  rw [← (Submodule.mem_map.mp x.2).choose_spec.2, L2.inner_def, apply_toInit]
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

end CameronMartinAux

namespace CameronMartin
open CameronMartinAux

/-- Continuous linear map from the Cameron-Martin space of a Gaussian measure to the space on
which that measure is defined. This map is injective: see `toInitialSpace_injective`.
Therefore, we can see the Cameron-Martin space as a subspace of the initial space, with a different
norm. -/
noncomputable
def toInitialSpace (μ : Measure E) [IsGaussian μ] : CameronMartin μ →L[ℝ] E :=
  Completion.continuousLinearMapExtension ℝ <|
  LinearMap.mkContinuous
    { toFun x := toInit μ x
      map_add' x y := by
        refine (eq_iff_forall_dual_eq (𝕜 := ℝ)).mpr fun L ↦ ?_
        simp_rw [map_add, apply_toInit_eq_inner, Submodule.coe_add, inner_add_right]
      map_smul' r x := by
        refine (eq_iff_forall_dual_eq (𝕜 := ℝ)).mpr fun L ↦ ?_
        simp_rw [map_smul, apply_toInit_eq_inner, Submodule.coe_smul, inner_smul_right]
        simp }
    ‖Dual.centeredToLp μ 2‖ norm_toInit_le

lemma apply_toInitialSpace_eq_inner (x : CameronMartin μ) (L : Dual ℝ E) :
    L (toInitialSpace μ x) = ⟪CameronMartin.ofDual μ L, x⟫_ℝ := by
  simp only [toInitialSpace, Completion.continuousLinearMapExtension_apply]
  revert x
  rw [← funext_iff]
  refine Completion.ext (by fun_prop) (by fun_prop) fun x ↦ ?_
  rw [Completion.extension_coe (ContinuousLinearMap.uniformContinuous _)]
  simp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [apply_toInit_eq_inner, CameronMartin.ofDual_apply, Completion.inner_coe]
  rfl

lemma eq_zero_of_toInitialSpace_eq_zero {x : CameronMartin μ}
    (h : toInitialSpace μ x = 0) :
    x = 0 := by
  suffices ∀ y : CameronMartin μ, ⟪y, x⟫_ℝ = 0 by
    rw [← inner_self_eq_zero (𝕜 := ℝ) (x := x)]
    exact this x
  rw [← funext_iff]
  refine Completion.ext (by fun_prop) (by fun_prop) fun L ↦ ?_
  obtain ⟨L', -, hL'⟩ := Submodule.mem_map.mp L.2
  have : CameronMartin.ofDual μ L' = L := by rw [CameronMartin.ofDual_apply]; congr
  rw [← this, ← apply_toInitialSpace_eq_inner, h]
  simp

lemma toInitialSpace_injective : Function.Injective (toInitialSpace μ) := by
  intro x y h
  rw [← sub_eq_zero, ← map_sub] at h
  rw [← sub_eq_zero, eq_zero_of_toInitialSpace_eq_zero h]

/-- Any point of the Cameron-Martin space has finite Cameron-Martin norm
`⨆ L (_ : covarianceBilin L L ≤ 1), L x` (when seen as a point of the initial space). -/
lemma apply_toInitialSpace_le_norm (x : CameronMartin μ)
    {L : Dual ℝ E} (hL : covarianceBilin μ L L ≤ 1) :
    L (toInitialSpace μ x) ≤ ‖x‖ := by
  calc L (toInitialSpace μ x)
  _ = ⟪ofDual μ L, x⟫_ℝ := apply_toInitialSpace_eq_inner x L
  _ ≤ ‖ofDual μ L‖ * ‖x‖ := real_inner_le_norm (ofDual μ L) x
  _ = √(covarianceBilin μ L L) * ‖x‖ := by rw [norm_ofDual]
  _ ≤ 1 * ‖x‖ := by gcongr; exact Real.sqrt_le_one.mpr hL
  _ = ‖x‖ := by rw [one_mul]

end CameronMartin

end ToInitialSpace

namespace CameronMartin

variable {y : E} [Decidable (∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M)]

@[simp]
lemma toInitialSpace_ofBounded (hy : ∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M) :
    toInitialSpace μ (ofBounded μ y) = y := by
  refine (eq_iff_forall_dual_eq (𝕜 := ℝ)).mpr fun L ↦ ?_
  rw [← eval_ofDual hy, apply_toInitialSpace_eq_inner, eval_apply]

@[simp]
lemma ofBounded_toInitialSpace (x : CameronMartin μ)
    [Decidable (∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L (toInitialSpace μ x) ≤ M)] :
    ofBounded μ (toInitialSpace μ x) = x := by
  refine toInitialSpace_injective ?_
  rw [toInitialSpace_ofBounded ⟨‖x‖, fun _ hL ↦ apply_toInitialSpace_le_norm x hL⟩]

lemma ofDual_inner_le_of_norm_ofDual_le (x : CameronMartin μ) {L : Dual ℝ E}
    (hL : ‖ofDual μ L‖ ≤ 1) :
    ⟪ofDual μ L, x⟫_ℝ ≤ ⨆ (L) (_ : covarianceBilin μ L L ≤ 1), L (toInitialSpace μ x) := by
  refine le_ciSup_of_le ?_ L ?_
  · refine ⟨‖x‖, ?_⟩
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    intro L
    by_cases hL : covarianceBilin μ L L ≤ 1
    · simpa [hL] using apply_toInitialSpace_le_norm x hL
    · simp [hL]
  have hL' : covarianceBilin μ L L ≤ 1 := by rwa [CameronMartin.norm_ofDual, Real.sqrt_le_one] at hL
  simp only [hL', ciSup_unique]
  rw [← apply_toInitialSpace_eq_inner]

lemma ofDual_inner_le_mul (x : CameronMartin μ) (L : Dual ℝ E) :
    ⟪ofDual μ L, x⟫_ℝ
      ≤ ‖ofDual μ L‖ * ⨆ (L) (_ : covarianceBilin μ L L ≤ 1), L (toInitialSpace μ x) := by
  by_cases h_zero : ‖ofDual μ L‖ = 0
  · simp only [h_zero, zero_mul]
    rw [inner_eq_zero_of_left _ h_zero]
  have h := ofDual_inner_le_of_norm_ofDual_le x (L := ‖ofDual μ L‖⁻¹ • L) ?_
  · simp only [map_smul, inner_smul_left, map_inv₀, conj_trivial] at h
    rwa [inv_mul_le_iff₀ (by positivity)] at h
  · simp only [map_smul, norm_smul, norm_inv, norm_norm]
    exact inv_mul_le_one

lemma inner_le_mul_ciSup (x y : CameronMartin μ) :
    ⟪y, x⟫_ℝ ≤ ‖y‖ * ⨆ (L) (_ : covarianceBilin μ L L ≤ 1), L (toInitialSpace μ x) := by
  induction y using Completion.induction_on with
  | hp =>
    exact isClosed_le (by fun_prop) (by fun_prop)
  | ih a =>
    obtain ⟨L, -, hL⟩ := Submodule.mem_map.mp a.2
    have : (a : CameronMartin μ) = CameronMartin.ofDual μ L := by
      simp_rw [CameronMartin.ofDual_apply, hL]
    rw [this]
    exact ofDual_inner_le_mul x L

lemma norm_eq_ciSup (x : CameronMartin μ) :
    ‖x‖ = ⨆ (L) (_ : covarianceBilin μ L L ≤ 1), L (toInitialSpace μ x) := by
  refine le_antisymm ?_ ?_
  · refine InnerProductSpace.norm_le_dual_bound x ?_ fun y ↦ ?_
    · by_cases h_bdd :
          BddAbove (Set.range fun L ↦ ⨆ (_ : covarianceBilin μ L L ≤ 1), L (toInitialSpace μ x))
      · exact le_ciSup_of_le h_bdd 0 (by simp)
      · simp [h_bdd]
    rw [real_inner_comm, mul_comm]
    exact inner_le_mul_ciSup x y
  · refine ciSup_le fun L ↦ ?_
    by_cases hL : covarianceBilin μ L L ≤ 1
    · simpa [hL] using apply_toInitialSpace_le_norm x hL
    · simp [hL]

lemma norm_ofBounded {y : E} [Decidable (∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M)]
    (hy : ∃ M, ∀ L, covarianceBilin μ L L ≤ 1 → L y ≤ M) :
    ‖ofBounded μ y‖ = ⨆ (L) (_ : covarianceBilin μ L L ≤ 1), L y := by
  simp [norm_eq_ciSup, toInitialSpace_ofBounded hy]

end CameronMartin

end ProbabilityTheory
