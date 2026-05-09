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

/-!
## Proof of `ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict`

Let `u : E →L[𝕜] F` be a continuous linear map, and `A` a finite codimension closed
subspace of `E`. We want to show that `u` is strict with closed range if and only if
`Set.restrict A u` is strict with closed range.

We do the proof in three steps.
-/

/-!
### Step 1

We prove the theorem under the assumptions that
- `u` is surjective
- `u.ker` is disjoint from `A` (i.e. `u` is injective on `A`)

The statement becomes: `u` is a quotient map if and only if `Set.restrict A u` is
a closed embedding.
-/

/-- The forward direction of step 1 in the proof of
`ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict`, which you should use instead.

Note that we only prove it for `u = K.mkQ`, because it is easier and precisely what we will need
in step 2. -/
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

/-- The backward direction of step 1 in the proof of
`ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict`, which you should use instead.

Note the hypothesis `h_ker` is implied `h_clemb`, but since this is a private theorem
we just write the most convenient statement to prove and use. -/
theorem step1_backward (A : Submodule 𝕜₁ E) (u : E →SL[σ] F) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜₁ (E ⧸ A)] (h_ker : Disjoint u.ker A) (h_range : u.range = ⊤)
    (h_clemb : IsClosedEmbedding (restrict A u)) :
    IsQuotientMap u := by
  sorry

/-!
### Step 2

We prove the theorem under the assumption that `u.ker` is disjoint from `A`
(i.e. `u` is injective on `A`).

The statement becomes: `u` is strict with closed range if and only if `Set.restrict A u` is
a closed embedding.
-/

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

theorem step2 (u : E →SL[σ] F) (A : Submodule 𝕜₁ E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜₁ (E ⧸ A)] (h_ker : Disjoint u.ker A) :
    (IsStrictMap u ∧ IsClosed (range u)) ↔ IsClosedEmbedding (restrict A u) := by
  sorry

/-!
### Step 3

We now deduce from the two previous step the full strength of the theorem.
-/

public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict (u : E →SL[σ] F)
    (A : Submodule 𝕜₁ E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜₁ (E ⧸ A)] :
    (IsStrictMap u ∧ IsClosed (range u)) ↔
      (IsStrictMap (restrict A u) ∧ IsClosed (u '' A)) := by
  sorry

end FiniteCodimSubspace

section FiniteRank

-- TODO: state in terms of "equality modulo finite rank" relation
public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_finiteDimensional [T1Space F]
    (u v : E →L[𝕜] F) (h_finite_rank : FiniteDimensional 𝕜 (u - v).range) :
    (IsStrictMap u ∧ IsClosed (range u)) ↔ (IsStrictMap v ∧ IsClosed (range v)) := by
  let A := (u - v).ker
  have hA : IsClosed (A : Set E) := (u - v).isClosed_ker
  have : FiniteDimensional 𝕜 (E ⧸ A) := (u - v).toLinearMap.quotKerEquivRange.symm.finiteDimensional
  have eqOn_A : EqOn u v A := fun _ ↦ by simp [A, sub_eq_zero]
  simp_rw [u.isStrictMap_isClosed_range_iff_restrict A hA,
    v.isStrictMap_isClosed_range_iff_restrict A hA,
    ← range_restrict, restrict_eq_restrict_iff.mpr eqOn_A]

end FiniteRank
