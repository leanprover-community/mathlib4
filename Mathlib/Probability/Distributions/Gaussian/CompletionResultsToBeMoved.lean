/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.GDelta.MetrizableSpace
/-!
# Completion Results To Be Moved

-/

@[expose] public section

open NormedSpace UniformSpace
open scoped InnerProductSpace

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

lemma norm_eval_le_norm_mul_ciSup {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [Module ℝ G] [NormSMulClass ℝ G]
    (f : StrongDual ℝ E →ₗ[ℝ] G) {y : E} (hy : ∃ M, ∀ L, ‖f L‖ ≤ 1 → L y ≤ M) (L : StrongDual ℝ E) :
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

/-- Coercion from a submodule to its topological closure as a continuous linear map. -/
def toClosureCLM {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul R M] (s : Submodule R M) :
    s →L[R] s.topologicalClosure where
  toFun := coeClosure
  map_add' := coeClosure_add
  map_smul' := coeClosure_smul

section Extension

variable {M R F : Type*} [Ring R] [NormedAddCommGroup M] [Module R M]
  [CompleteSpace M] [UniformContinuousConstSMul R M]
  [UniformSpace F] [AddCommGroup F] [Module R F] [T2Space F] [CompleteSpace F]
  [IsUniformAddGroup F] [UniformContinuousConstSMul R F]
  {s : Submodule R M}

/-- Extension of a linear map `s →L[R] F` on a submodule to a linear map on the topological
closure of the submodule. -/
noncomputable
def closureExtensionCLM (s : Submodule R M) (f : s →L[R] F) : s.topologicalClosure →L[R] F :=
  ContinuousLinearMap.extend f (toClosureCLM s)

lemma denseRange_coeClosure (s : Submodule R M) :
    DenseRange (coeClosure : s → s.topologicalClosure) := by
  sorry

lemma IsUniformInducing_toClosureCLM (s : Submodule R M) :
    IsUniformInducing (toClosureCLM s) := by
  sorry

@[simp]
lemma closureExtensionCLM_coe (s : Submodule R M) (f : s →L[R] F) (x : s) :
    closureExtensionCLM s f x = f x :=
  ContinuousLinearMap.extend_eq f (denseRange_coeClosure s) (IsUniformInducing_toClosureCLM s) _

end Extension
