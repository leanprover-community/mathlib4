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

variable {𝕜₁ 𝕜₂}
  [NontriviallyNormedField 𝕜₁] [CompleteSpace 𝕜₁]
  [NontriviallyNormedField 𝕜₂] [CompleteSpace 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂}

variable {E F : Type*}
  [AddCommGroup E] [Module 𝕜₁ E] [AddCommGroup F] [Module 𝕜₂ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜₁ E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₂ F]

section FiniteCodimSubspace

variable (A : Submodule 𝕜₁ E) (u : E →SL[σ] F)

theorem step1 [RingHomSurjective σ] (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜₁ (E ⧸ A)] (h_ker : Disjoint u.ker A) (h_strict : IsStrictMap u)
    (h_closed : IsClosed (u.range : Set F)) : IsClosedEmbedding (restrict A u) := by
  -- TODO: `Submodule.liftQL` ?
  let u' : E ⧸ u.ker →ₛₗ[σ] F := u.ker.liftQ u le_rfl
  have u'_clemb : IsClosedEmbedding u' := by
    constructor
    · rw [isStrictMap_iff_isEmbedding_kerLift] at h_strict
      -- exact h_strict
      sorry -- should be fixed with more API on strict homs
    · simpa [u', ← LinearMap.coe_range, Submodule.range_liftQ]
  let π : E →L[𝕜₁] E ⧸ u.ker := u.ker.mkQL
  have π_restr_clemb : IsClosedEmbedding (restrict A π) := by
    constructor
    · rcases h_ker.exists_isCompl with ⟨S, ker_le_S, S_compl_A⟩
      replace S_compl_A : IsTopCompl S A :=
        S_compl_A.symm.isTopCompl_of_quotient_finiteDimensional A_closed |>.symm
      -- TODO: `Submodule.liftQL`
      let s : E ⧸ u.ker →L[𝕜₁] A :=
        ⟨u.ker.liftQ (A.projectionOntoL S S_compl_A.symm) (by simpa),
          continuous_quot_lift _ (A.projectionOntoL S S_compl_A.symm).continuous⟩
      have leftInv : LeftInverse s (restrict A π) := fun x ↦ by simp [π, s]
      refine .of_leftInverse leftInv s.continuous (by fun_prop)
    · rw [← u.ker.isQuotientMap_mkQL.isClosed_preimage, range_restrict]
      change IsClosed (comap π.toLinearMap (map π.toLinearMap A) : Set E)
      exact isClosed_mono_of_finiteDimensional_quotient A_closed (le_comap_map _ A)
  have eq : restrict A u = u' ∘ restrict A π := by ext x; simp [π, u']
  rw [eq]
  exact u'_clemb.comp π_restr_clemb

end FiniteCodimSubspace
