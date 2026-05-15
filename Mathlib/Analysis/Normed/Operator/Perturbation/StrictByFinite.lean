/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Maps.Strict.Basic
public import Mathlib.Topology.LocalAtTarget
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
  · -- We show that `restrict A K.mkQ` is an embedding by exhibiting a continuous left inverse.
    -- Fix `S` an algebraic complement of `A` containing `K`.
    rcases K_disj_A.exists_isCompl with ⟨S, K_le_S, S_compl_A⟩
    -- Because `A` is closed with finite codimension, `S` is in fact a topological complement
    -- of `A`.
    replace S_compl_A : IsTopCompl S A :=
      S_compl_A.symm.isTopCompl_of_finiteDimensional_quotient A_closed |>.symm
    -- Thus the projection onto `A` along `S` is continuous, and it vanishes on `K`.
    -- Hence it defines a map `E ⧸ K →L[𝕜] A`, which is our left inverse.
    let s : E ⧸ K →L[𝕜] A := K.liftQL (A.projectionOntoL S S_compl_A.symm) (by simpa)
    have leftInv : LeftInverse s (restrict A K.mkQ) := fun x ↦ by simp [s]
    refine .of_leftInverse leftInv s.continuous (by fun_prop)
  · -- The subspace `K.mkQ ⁻¹' K.mkQ '' A` contains the closed and finite codimension subspace `A`,
    -- hence it is closed. By definition of the quotient topology, this shows that
    -- `restrict A K.mkQ` has closed range.
    rw [← K.isQuotientMap_mkQ.isClosed_preimage, range_restrict, ← Submodule.map_coe,
      ← Submodule.comap_coe K.mkQ]
    exact isClosed_mono_of_finiteDimensional_quotient A_closed (le_comap_map _ A)

/-- The backward direction of step 1 in the proof of
`ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict`, which you should use instead.

Note the hypothesis `h_ker` is implied `h_clemb`, but since this is a private theorem
we just write the most convenient statement to prove and use. -/
theorem step1_backward (u : E →L[𝕜] F) (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] (h_ker : Disjoint u.ker A) (h_range : u.range = ⊤)
    (h_clemb : IsClosedEmbedding (restrict A u)) :
    IsQuotientMap u := by
  rcases h_ker.exists_isCompl with ⟨S, ker_le_S, S_compl_A⟩
  replace S_compl_A : IsTopCompl S A :=
      S_compl_A.symm.isTopCompl_of_finiteDimensional_quotient A_closed |>.symm
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

omit [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] in
theorem step2_forward (u : E →L[𝕜] F) (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] (h_ker : Disjoint u.ker A) (h_strict : IsStrictMap u)
    (h_closed : IsClosed (range u)) : IsClosedEmbedding (restrict A u) := by
  -- Denote by `π : E → E ⧸ u.ker` the quotient map. Since `u.ker` is disjoint from `A`, we know
  -- from step 1 that `restrict A π` is a closed embedding.
  let π : E →L[𝕜] E ⧸ u.ker := u.ker.mkQL
  have π_restr_clemb : IsClosedEmbedding (restrict A π) :=
    step1_foward A u.ker A_closed h_ker
  -- But we can factor `restrict A u` as `u' ∘ restrict A π`, where `u' : E ⧸ u.ker → F`
  -- is the injection induced by `u`. Thus, it remains to show that `u'` is also a closed embedding.
  let u' : E ⧸ u.ker →L[𝕜] F := u.ker.liftQL u le_rfl
  have eq : restrict A u = u' ∘ restrict A π := by ext x; simp [π, u']
  have u'_clemb : IsClosedEmbedding u' := by
  -- By assumption, `range u' = range u` is closed.
  -- We also assumed that `u` is strict, which precisely means that `u'` is an embedding.
  -- Hence, we are done.
    constructor
    · -- Note: this should be simpler with more API on strict group homs;
      -- the issue is that the quotients associated to `LinearMap.ker` and `Setoid.ker`
      -- are not defeq...
      have : Injective u' := by simp [u', ← LinearMap.ker_eq_bot, ker_liftQ_eq_bot]
      simpa [isEmbedding_iff_isStrictMap_injective, this, and_true,
        u.ker.isQuotientMap_mkQL.isStrictMap_iff]
    · simpa [u', ← LinearMap.coe_range, Submodule.range_liftQ]
  exact eq ▸ u'_clemb.comp π_restr_clemb

theorem step2_backward (u : E →L[𝕜] F) (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] (h_ker : Disjoint u.ker A)
    (h_clemb : IsClosedEmbedding (restrict A u)) :
    IsStrictMap u ∧ IsClosed (range u) := by
  -- Fix `S` an algebraic complement of `A` containing `K`. Note that `S` has finite
  -- dimension.
  rcases A.exists_isCompl with ⟨S, A_compl_S⟩
  have : FiniteDimensional 𝕜 S :=
    quotientEquivOfIsCompl A S A_compl_S |>.finiteDimensional
  -- Because `map u A` is closed by assumption, it follows that `u.range = map u A ⊔ map u S`
  -- is closed.
  have range_u_closed : IsClosed (u.range : Set F) := by
    rw [isClosedEmbedding_iff, range_restrict] at h_clemb
    have : u.range = (map u.toLinearMap A ⊔ map u.toLinearMap S) := by
      rw [← Submodule.map_sup, A_compl_S.sup_eq_top, Submodule.map_top]
    exact this ▸ Submodule.isClosed_sup_finiteDimensional _ _ h_clemb.2
  -- It remains to show that `u` is strict, which means precisely that the co-restriction
  -- `u' : E → u.range` is a quotient map. By step 1, it is enough to show that
  -- `restrict A u'` is a closed embedding. This follows from the fact that
  -- `restrict A u = u.range.subtype ∘ restrict A u'`, since both
  -- `restrict A u` and `u.range.subtype` are closed embeddings.
  refine ⟨?_, range_u_closed⟩
  set u' : E →L[𝕜] u.range := u.rangeRestrict
  have h_clemb' : IsClosedEmbedding (restrict A u') := by
    rw [← range_u_closed.isClosedEmbedding_subtypeVal.of_comp_iff]
    exact h_clemb
  exact step1_backward u' A A_closed (by simpa [u']) (by simp [u']) h_clemb'

theorem step2 (u : E →L[𝕜] F) (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] (h_ker : Disjoint u.ker A) :
    (IsStrictMap u ∧ IsClosed (range u)) ↔ IsClosedEmbedding (restrict A u) :=
  ⟨fun H ↦ step2_forward u A A_closed h_ker H.1 H.2, step2_backward u A A_closed h_ker⟩

/-!
### Step 3

We now deduce from the two previous step the full strength of the theorem.
-/

public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict (u : E →L[𝕜] F)
    (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] :
    (IsStrictMap u ∧ IsClosed (range u)) ↔
      (IsStrictMap (restrict A u) ∧ IsClosed (u '' A)) := by
  set N : Submodule 𝕜 E := A ⊓ u.ker
  set π : E →L[𝕜] E ⧸ N := N.mkQL
  set v : E ⧸ N →L[𝕜] F := N.liftQL u inf_le_right
  have π_quot : IsOpenQuotientMap π := N.isOpenQuotientMap_mkQL
  have v_comp_π_eq_u : v ∘ π = u := rfl
  set B : Submodule 𝕜 (E ⧸ N) := map N.mkQ A
  have comap_B : comap π.toLinearMap B = A := by simp [B, N, π]
  have A_mapsTo_B : MapsTo π A B := fun _ ↦ by simp [← comap_B]
  have B_closed : IsClosed (B : Set <| E ⧸ N) := by
    rwa [← π_quot.isQuotientMap.isClosed_preimage, ← π.coe_coe, ← comap_coe, comap_B]
  have codim_B : FiniteDimensional 𝕜 ((E ⧸ N) ⧸ B) :=
    quotientQuotientEquivQuotient N A inf_le_left |>.symm.finiteDimensional
  set π' : A →L[𝕜] B :=
    ⟨π.restrict A_mapsTo_B, π.continuous.restrict A_mapsTo_B⟩
  have π'_quot : IsOpenQuotientMap π' := by
    let φ : (N.mkQL ⁻¹' B) ≃ₜ A := .setCongr congr(SetLike.coe $comap_B)
    exact N.isOpenQuotientMap_mkQL.restrictPreimage B |>.comp
      φ.symm.isOpenQuotientMap
  have v_comp_π'_eq_u : restrict B v ∘ π' = restrict A u := rfl
  have v_ker : Disjoint v.ker B := by
    simp [disjoint_iff, v, B, toLinearMap_liftQL, ker_liftQ,
      map_inf_eq_map_inf_comap, comap_map_mkQ, N, inf_comm]
  have v_restr_inj : Injective (restrict B v) :=
    injOn_iff_injective.mp <| LinearMap.injOn_of_disjoint_ker subset_rfl v_ker.symm
  have range_eq : range v = range u := range_quot_lift _
  have image_eq : v '' B = u '' A := by simp [B, ← v_comp_π_eq_u, π, ← image_comp]
  rw [← range_eq, ← image_eq, ← v_comp_π'_eq_u, ← v_comp_π_eq_u,
    ← π_quot.isQuotientMap.isStrictMap_iff, ← π'_quot.isQuotientMap.isStrictMap_iff]
  simp [step2 v B B_closed v_ker, isClosedEmbedding_iff, range_restrict v,
    isEmbedding_iff_isStrictMap_injective, v_restr_inj]

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
public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_quotient [T1Space F]
    (u : E →L[𝕜] F) (A : Submodule 𝕜 F) [dim_A : FiniteDimensional 𝕜 A]
    (A_compl : ClosedComplemented A) :
    (IsStrictMap u ∧ IsClosed (range u)) ↔
      (IsStrictMap (A.mkQ ∘ u) ∧ IsClosed (range (A.mkQ ∘ u))) := by
  obtain ⟨S, A_compl_S⟩ := A_compl.exists_isTopCompl
  let Φ : (F ⧸ A) ≃L[𝕜] S := A.quotientEquivOfIsTopCompl S A_compl_S
  let i : S →L[𝕜] F := S.subtypeL
  have i_clemb : IsClosedEmbedding i := S.isClosedEmbedding_subtypeL A_compl_S.symm.isClosed
  let p : F →L[𝕜] F := S.projectionL A A_compl_S.symm
  have eq : i ∘ Φ ∘ A.mkQ = p := rfl
  simp_rw [Φ.toHomeomorph.isEmbedding.isStrictMap_iff, ← Φ.toHomeomorph.isClosed_image,
    i_clemb.isStrictMap_iff, i_clemb.isClosed_iff_image_isClosed, ← range_comp, Φ.coe_toHomeomorph]
  -- simp_rw [Φ.toHomeomorph.isEmbedding.isStrictMap_iff, ← Φ.toHomeomorph.isClosed_image,
  --   ← range_comp, ← Function.comp_assoc, Φ.coe_toHomeomorph, eq,
  --   S.isEmbedding_subtypeL.isStrictMap_iff,
  --   S.isClosedEmbedding_subtypeL A_compl_S.symm.isClosed |>.isClosed_iff_image_isClosed,
  --   ← range_comp, ← ContinuousLinearMap.coe_comp']
  -- simp
  sorry

end FiniteDimQuotient
