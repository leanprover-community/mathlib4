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

variable {𝕜}
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {E F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]

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
theorem step1_foward (A : Submodule 𝕜 E) (K : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] (K_disj_A : Disjoint K A) :
    IsClosedEmbedding (restrict A K.mkQ) := by
  constructor
  · rcases K_disj_A.exists_isCompl with ⟨S, K_le_S, S_compl_A⟩
    replace S_compl_A : IsTopCompl S A :=
      S_compl_A.symm.isTopCompl_of_quotient_finiteDimensional A_closed |>.symm
    -- TODO: `Submodule.liftQL`
    let s : E ⧸ K →L[𝕜] A :=
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
theorem step1_backward (A : Submodule 𝕜 E) (u : E →L[𝕜] F) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] (h_ker : Disjoint u.ker A) (h_range : u.range = ⊤)
    (h_clemb : IsClosedEmbedding (restrict A u)) :
    IsQuotientMap u := by
  rcases h_ker.exists_isCompl with ⟨S, ker_le_S, S_compl_A⟩
  replace S_compl_A : IsTopCompl S A :=
      S_compl_A.symm.isTopCompl_of_quotient_finiteDimensional A_closed |>.symm
  have : FiniteDimensional 𝕜 S :=
    quotientEquivOfIsCompl A S S_compl_A.isCompl.symm |>.finiteDimensional
  have uA_closed : IsClosed (map u.toLinearMap A : Set F) := by
    simpa [← range_restrict] using h_clemb.isClosed_range
  have uS_compl_uA : IsCompl (map u.toLinearMap S) (map u.toLinearMap A) := by
    constructor
    · rw [disjoint_iff, inf_comm, map_inf_eq_map_inf_comap, comap_map_eq, sup_eq_left.mpr ker_le_S,
        S_compl_A.isCompl.symm.inf_eq_bot, Submodule.map_bot]
    · rw [codisjoint_iff, ← Submodule.map_sup, S_compl_A.isCompl.sup_eq_top, Submodule.map_top,
        h_range]
  replace uS_compl_uA : IsTopCompl (map u.toLinearMap S) (map u.toLinearMap A) :=
      uS_compl_uA.symm.isTopCompl_of_isClosed_of_finiteDimensional uA_closed |>.symm
  sorry

/-!
### Step 2

We prove the theorem under the assumption that `u.ker` is disjoint from `A`
(i.e. `u` is injective on `A`).

The statement becomes: `u` is strict with closed range if and only if `Set.restrict A u` is
a closed embedding.
-/

theorem step2_forward (u : E →L[𝕜] F) (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] (h_ker : Disjoint u.ker A) (h_strict : IsStrictMap u)
    (h_closed : IsClosed (range u)) : IsClosedEmbedding (restrict A u) := by
  -- TODO: `Submodule.liftQL` ?
  let u' : E ⧸ u.ker →ₗ[𝕜] F := u.ker.liftQ u le_rfl
  have u'_clemb : IsClosedEmbedding u' := by
    constructor
    · sorry -- should be fixed with more API on strict homs
    · simpa [u', ← LinearMap.coe_range, Submodule.range_liftQ]
  let π : E →L[𝕜] E ⧸ u.ker := u.ker.mkQL
  have π_restr_clemb : IsClosedEmbedding (restrict A π) :=
    step1_foward A u.ker A_closed h_ker
  have eq : restrict A u = u' ∘ restrict A π := by ext x; simp [π, u']
  exact eq ▸ u'_clemb.comp π_restr_clemb

theorem step2_backward (u : E →L[𝕜] F) (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] (h_ker : Disjoint u.ker A)
    (h_clemb : IsClosedEmbedding (restrict A u)) :
    IsStrictMap u ∧ IsClosed (range u) := by
  rcases A.exists_isCompl with ⟨S, A_compl_S⟩
  have : FiniteDimensional 𝕜 S :=
    quotientEquivOfIsCompl A S A_compl_S |>.finiteDimensional
  rw [isClosedEmbedding_iff, range_restrict] at h_clemb
  have : range u = (map u.toLinearMap A ⊔ map u.toLinearMap S) := by
    rw [← Submodule.map_sup, A_compl_S.sup_eq_top, Submodule.map_top,
      LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  refine ⟨?_, this ▸ Submodule.isClosed_sup_finiteDimensional _ _ h_clemb.2⟩
  sorry

theorem step2 (u : E →L[𝕜] F) (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] (h_ker : Disjoint u.ker A) :
    (IsStrictMap u ∧ IsClosed (range u)) ↔ IsClosedEmbedding (restrict A u) := by
  sorry

/-!
### Step 3

We now deduce from the two previous step the full strength of the theorem.
-/

#check IsOpenQuotientMap

public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict (u : E →L[𝕜] F)
    (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] :
    (IsStrictMap u ∧ IsClosed (range u)) ↔
      (IsStrictMap (restrict A u) ∧ IsClosed (u '' A)) := by
  set N : Submodule 𝕜 E := A ⊓ u.ker
  set v : E ⧸ N →L[𝕜] F := ⟨N.liftQ u inf_le_right, continuous_quot_lift _ u.continuous⟩
  have v_eq_u : v ∘L N.mkQL = u := rfl
  set B : Submodule 𝕜 (E ⧸ N) := map N.mkQ A
  have comap_B : comap N.mkQ B = A := by simp [B, N]
  have B_closed : IsClosed (B : Set <| E ⧸ N) := by
    rwa [← N.isQuotientMap_mkQ.isClosed_preimage, ← comap_coe, comap_B]
  have codim_B : FiniteDimensional 𝕜 ((E ⧸ N) ⧸ B) :=
    quotientQuotientEquivQuotient N A inf_le_left |>.symm.finiteDimensional
  have range_eq : range v = range u := range_quot_lift _
  have image_eq : v '' B = u '' A := by simp [B, ← v_eq_u, ← image_comp]
  rw [← range_eq, ← image_eq]
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

section FiniteDimQuotient

-- TODO: better name
-- TODO: use ∘ or ∘L ? The simp NF is ∘
public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_quotient
    (u : E →L[𝕜] F) (A : Submodule 𝕜 F) [dim_A : FiniteDimensional 𝕜 A]
    (A_compl : ClosedComplemented A) :
    (IsStrictMap u ∧ IsClosed (range u)) ↔
      (IsStrictMap (A.mkQ ∘ u) ∧ IsClosed (range (A.mkQ ∘ u))) := by
  obtain ⟨S, A_compl_S⟩ := A_compl.exists_isTopCompl
  sorry

end FiniteDimQuotient
