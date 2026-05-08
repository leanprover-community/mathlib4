/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Maps.Strict.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Strict linear maps with closed range are closed under finite-rank perturbation
-/

@[expose] public section

open Topology Set Submodule Function

variable {𝕜 𝕜₁ 𝕜₂}
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NontriviallyNormedField 𝕜₁] [CompleteSpace 𝕜₁]
  [NontriviallyNormedField 𝕜₂] [CompleteSpace 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂} [RingHomSurjective σ]

variable {E F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [Module 𝕜₁ E] [AddCommGroup F] [Module 𝕜 F] [Module 𝕜₂ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜₁ E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [ContinuousSMul 𝕜₂ F]

section FiniteCodimSubspace

theorem step1_foward (A : Submodule 𝕜₁ E) (K : Submodule 𝕜₁ E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜₁ (E ⧸ A)] (K_disj_A : Disjoint K A) :
    IsClosedEmbedding (restrict A K.mkQ) := by
  constructor
  · rcases K_disj_A.exists_isCompl with ⟨S, K_le_S, S_compl_A⟩
    replace S_compl_A : IsTopCompl S A :=
      S_compl_A.symm.isTopCompl_of_quotient_finiteDimensional A_closed |>.symm
    -- TODO: `Submodule.liftQL`
    let s : E ⧸ K →L[𝕜₁] A :=
      ⟨K.liftQ (A.projectionOntoL S S_compl_A.symm) (by simpa),
        continuous_quot_lift _ (A.projectionOntoL S S_compl_A.symm).continuous⟩
    have leftInv : LeftInverse s (restrict A K.mkQ) := fun x ↦ by simp [s]
    refine .of_leftInverse leftInv s.continuous (by fun_prop)
  · rw [← K.isQuotientMap_mkQ.isClosed_preimage, range_restrict, ← Submodule.map_coe,
      ← Submodule.comap_coe K.mkQ]
    exact isClosed_mono_of_finiteDimensional_quotient A_closed (le_comap_map _ A)

theorem step2_forward (u : E →SL[σ] F) (A : Submodule 𝕜₁ E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜₁ (E ⧸ A)] (h_ker : Disjoint u.ker A) (h_strict : IsStrictMap u)
    (h_closed : IsClosed (range u)) : IsClosedEmbedding (restrict A u) := by
  -- TODO: `Submodule.liftQL` ?
  let u' : E ⧸ u.ker →ₛₗ[σ] F := u.ker.liftQ u le_rfl
  have u'_clemb : IsClosedEmbedding u' := by
    constructor
    · rw [isStrictMap_iff_isEmbedding_kerLift] at h_strict
      -- exact h_strict
      sorry -- should be fixed with more API on strict homs
    · simpa [u', ← LinearMap.coe_range, Submodule.range_liftQ]
  let π : E →L[𝕜₁] E ⧸ u.ker := u.ker.mkQL
  have π_restr_clemb : IsClosedEmbedding (restrict A π) :=
    step1_foward A u.ker A_closed h_ker
  have eq : restrict A u = u' ∘ restrict A π := by ext x; simp [π, u']
  rw [eq]
  exact u'_clemb.comp π_restr_clemb

theorem foo (u : E →SL[σ] F) (A : Submodule 𝕜₁ E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜₁ (E ⧸ A)] :
    (IsStrictMap u ∧ IsClosed (range u)) ↔
      (IsStrictMap (restrict A u) ∧ IsClosed (u '' A)) := by
  sorry

end FiniteCodimSubspace

section FiniteRank

theorem bar [T1Space F] (u v : E →L[𝕜] F) (h_finite_rank : FiniteDimensional 𝕜 (u - v).range) :
    (IsStrictMap u ∧ IsClosed (range u)) ↔ (IsStrictMap v ∧ IsClosed (range v)) := by
  let A := (u - v).ker
  have hA : IsClosed (A : Set E) := (u - v).isClosed_ker
  have : FiniteDimensional 𝕜 (E ⧸ A) := (u - v).toLinearMap.quotKerEquivRange.symm.finiteDimensional
  have eqOn_A : EqOn u v A := fun _ ↦ by simp [A, sub_eq_zero]
  simp_rw [foo u A hA, foo v A hA, ← range_restrict, restrict_eq_restrict_iff.mpr eqOn_A]

end FiniteRank
