/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.Topology.Maps.Strict.Basic
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Strict linear maps with closed range are closed under finite-rank perturbation

Fix `𝕜` a complete nontrivially normed field, and `E`, `F` two topological vector spaces
over `𝕜`. This file contains various results expressing that the set of continuous
linear maps `u : E →L[𝕜] F` which are **strict** and have **closed range** is
"stable under finite-rank perturbations".

More precisely, we prove the following statements:
* `ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict`: given a closed
  subspace `A` of `E` of finite codimension, we have that `u` is strict with closed range
  if and only if `u.domRestrict A` is strict with closed range.
* `ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict`: if `u, v : E →L[𝕜] F`
  differ by a finite rank continuous linear map, then `u` is strict with closed range if and only
  if `v` is strict with closed range.
* `ContinuousLinearMap.isStrictMap_isClosed_range_iff_quotient`: given a *complemented*
  finite dimensional subspace `B` of `F`, we have that `u` is strict with closed range
  if and only if `B.mkQL ∘L u` is strict with closed range.

These three results show up crucially when developping the theory of Fredholm operators
between topological vector spaces. Note that none of the results here use the Hahn-Banach
theorem, so there is no significant restriction on the field.

## References

* [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 1][bourbaki2023]
-/

open Topology Set Submodule Function ContinuousLinearMap

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
`u.domRestrict A` is strict with closed range.

We do the proof in four steps.
-/

/-!
### Step 1

We prove the theorem under the assumptions that
- `u` is surjective
- `u.ker` is disjoint from `A` (i.e. `u` is injective on `A`)

The statement becomes: `u` is a quotient map if and only if `u.domRestrict A` is
a closed embedding.
-/

/-- The forward direction of step 1 in the proof of
`ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict`, which you should use instead.

We prove it first for `u = K.mkQL`, because we have no analog of `Submodule.liftQL` for arbitrary
linear quotient maps; when this is solved, this should be merged with `step1_forward` below. -/
theorem step1_foward' (A : Submodule 𝕜 E) (K : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] (K_disj_A : Disjoint K A) :
    IsClosedEmbedding (K.mkQL.domRestrict A) := by
  constructor
  · -- We show that `K.mkQL.domRestrict A` is an embedding by exhibiting a continuous left inverse.
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
  · -- The subspace `K.mkQL ⁻¹' K.mkQL '' A` contains the closed and finite codimension subspace
    -- `A`, hence it is closed. By definition of the quotient topology, this shows that
    -- `K.mkQL.domRestrict A` has closed range.
    rw [← K.isQuotientMap_mkQ.isClosed_preimage, ContinuousLinearMap.coe_domRestrict,
      range_restrict, ← ContinuousLinearMap.coe_coe, ← map_coe, ← comap_coe K.mkQ]
    exact isClosed_mono_of_finiteDimensional_quotient A_closed (le_comap_map _ A)

omit [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] in
/-- The forward direction of step 1 in the proof of
`ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict`, which you should use instead. -/
theorem step1_foward (u : E →L[𝕜] F) (A : Submodule 𝕜 E)
    (A_closed : IsClosed (A : Set E)) [codim_A : FiniteDimensional 𝕜 (E ⧸ A)]
    (h_ker : Disjoint u.ker A) (h_quot : IsQuotientMap u) :
    IsClosedEmbedding (u.domRestrict A) := by
  -- Because `u` is a quotient linear map, we can identify it with "the" quotient map
  -- `E → E ⧸ u.ker`, for which we have proven the result above.
  -- TODO: there should be API
  set Φ : (E ⧸ u.ker) ≃L[𝕜] F :=
  { toLinearEquiv := u.toLinearMap.quotKerEquivOfSurjective h_quot.surjective
    continuous_toFun := continuous_quot_lift _ h_quot.continuous
    continuous_invFun := h_quot.continuous_iff.mpr <| u.ker.continuous_mkQ.congr fun x ↦ by
      simp [← ContinuousLinearMap.coe_coe] }
  -- TODO: there should be API
  have Φ_clemb : IsClosedEmbedding Φ := Φ.toHomeomorph.isClosedEmbedding
  have eq : u.domRestrict A = Φ ∘L u.ker.mkQL.domRestrict A := rfl
  simpa [eq, Φ_clemb.of_comp_iff] using step1_foward' A u.ker A_closed h_ker

/-- The backward direction of step 1 in the proof of
`ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict`, which you should use instead.

Note the hypothesis `h_ker` is implied `h_clemb`, but since this is a private theorem
we just write the most convenient statement to prove and use. -/
theorem step1_backward [T2Space F] (u : E →L[𝕜] F) (A : Submodule 𝕜 E)
    (A_closed : IsClosed (A : Set E)) [codim_A : FiniteDimensional 𝕜 (E ⧸ A)]
    (h_ker : Disjoint u.ker A) (h_range : u.range = ⊤)
    (h_clemb : IsClosedEmbedding (u.domRestrict A)) :
    IsQuotientMap u := by
  -- Fix `S` an algebraic complement of `A` containing `u.ker`. It has finite dimension.
  rcases h_ker.exists_isCompl with ⟨S, ker_le_S, S_compl_A⟩
  have : FiniteDimensional 𝕜 S :=
    quotientEquivOfIsCompl A S S_compl_A.symm |>.finiteDimensional
  -- Because `A` is closed with finite codimension, `S` is in fact a topological complement of `A`.
  replace S_compl_A : IsTopCompl S A :=
      S_compl_A.symm.isTopCompl_of_finiteDimensional_quotient A_closed |>.symm
  -- By assumption, `map u A` is closed.
  have uA_closed : IsClosed (map u.toLinearMap A : Set F) := by
    simpa [← range_restrict] using h_clemb.isClosed_range
  -- Because `u` is assumed surjective and `S ⊔ A = ⊤`, we have `map u S ⊔ map u A = ⊤`.
  -- Furthermore, because the kernel of `u` is fully contained in `S`, we can show that
  -- `map u S ⊓ map u A = ⊥`, so that `map u S` and `map u A` are in fact algebraic complements
  -- of each other.
  have uS_compl_uA : IsCompl (map u.toLinearMap S) (map u.toLinearMap A) := by
    constructor
    · rw [disjoint_iff, inf_comm, map_inf_eq_map_inf_comap, comap_map_eq, sup_eq_left.mpr ker_le_S,
        S_compl_A.isCompl.symm.inf_eq_bot, Submodule.map_bot]
    · rw [codisjoint_iff, ← Submodule.map_sup, S_compl_A.isCompl.sup_eq_top, Submodule.map_top,
        h_range]
  -- Since `map u S` has finite dimension, `map u A` has finite codimension. But we also know that
  -- `map u A` is closed so, once again, `map u S` and `map u A` are in fact *topological*
  -- complements of each other.
  replace uS_compl_uA : IsTopCompl (map u.toLinearMap S) (map u.toLinearMap A) :=
      uS_compl_uA.symm.isTopCompl_of_isClosed_of_finiteDimensional uA_closed |>.symm
  -- Thus, we have decomposed both the comain and the codomain into topopological complements.
  -- Using the corresponding isomorphisms `(S × A) ≃L[𝕜] E` and `(map u S × map u A) ≃L[𝕜] F`,
  -- we have to show that the map `u₁.prodMap u₂ : S × A → map u S × map u A` is a quotient map.
  set Φ : (S × A) ≃L[𝕜] E := prodEquivOfIsTopCompl S A S_compl_A
  set Ψ : (map u.toLinearMap S × map u.toLinearMap A) ≃L[𝕜] F :=
    prodEquivOfIsTopCompl _ _ uS_compl_uA
  set u₁ : S →L[𝕜] map u.toLinearMap S := u.restrict (fun _ ↦ mem_map_of_mem)
  set u₂ : A →L[𝕜] map u.toLinearMap A := u.restrict (fun _ ↦ mem_map_of_mem)
  have u₁_surj : Surjective u₁ := surjective_mapsTo_image_restrict _ _
  have u₂_surj : Surjective u₂ := surjective_mapsTo_image_restrict _ _
  have eq : u = Ψ ∘ (u₁.prodMap u₂) ∘ Φ.symm := by
    ext x
    simp [Φ, Ψ, u₁, u₂, ← map_add, projectionL_add_projectionL_eq_self]
  suffices IsQuotientMap (Prod.map u₁ u₂) from eq ▸
    (Ψ.toHomeomorph.isQuotientMap.comp this |>.comp Φ.symm.toHomeomorph.isQuotientMap)
  -- Since linear quotient maps are automatically open, and since the product of two open quotient
  -- maps is a quotient map, this reduces to showing that both `u₁` and `u₂` are quotient maps.
  refine IsOpenQuotientMap.prodMap ?_ ?_ |>.isQuotientMap <;>
  apply AddMonoidHom.isOpenQuotientMap_of_isQuotientMap ?_
  -- `u₁` is a quotient map because it is a surjective linear map between finite dimensional spaces.
  · refine ContinuousLinearMap.isQuotientMap_of_finiteDimensional u₁
      (u₁.range_eq_top_of_surjective u₁_surj)
  -- `u₂` is strict because `(map u A).subtype ∘ u₂ = u.restrict A` is an embedding (hence strict)
  -- by assumptions. Since `u₂` is surjective, it is a quotient map, and we are done.
  · simp_rw [isQuotientMap_iff_isStrictMap_surjective, u₂_surj, and_true,
      (map u.toLinearMap A).isEmbedding_subtype.isStrictMap_iff]
    exact h_clemb.isStrictMap

theorem step1 [T2Space F] (u : E →L[𝕜] F) (A : Submodule 𝕜 E)
    (A_closed : IsClosed (A : Set E)) [codim_A : FiniteDimensional 𝕜 (E ⧸ A)]
    (h_ker : Disjoint u.ker A) (h_range : u.range = ⊤) :
    IsQuotientMap u ↔ IsClosedEmbedding (u.domRestrict A) :=
  ⟨step1_foward u A A_closed h_ker, step1_backward u A A_closed h_ker h_range⟩

/-!
### Step 2

We prove the theorem under the assumptions that
- `u` has closed range
- `u.ker` is disjoint from `A` (i.e. `u` is injective on `A`)

The statement becomes: `u` is strict if and only if `Set.restrict A u` is a closed embedding.
-/

theorem step2 [T2Space F] (u : E →L[𝕜] F) (A : Submodule 𝕜 E)
    (A_closed : IsClosed (A : Set E)) [codim_A : FiniteDimensional 𝕜 (E ⧸ A)]
    (h_ker : Disjoint u.ker A) (h_range : IsClosed (u.range : Set F)) :
    IsStrictMap u ↔ IsClosedEmbedding (u.domRestrict A) := by
  -- Let `F' := u.range` and `i : F' →L[𝕜] F` be the inclusion map. By assumption,
  -- `i` is a closed embedding.
  set F' : Submodule 𝕜 F := u.range
  set i : F' →L[𝕜] F := F'.subtypeL
  have i_clemb : IsClosedEmbedding i := F'.isClosedEmbedding_subtypeL h_range
  -- Furthermore, `u` factors as `i ∘ u'` with `u' : E →L[𝕜] F'` surjective,
  -- and we clearly have `u.domRestrict A = i ∘ u'.domRestrict A` as well.
  set u' : E →L[𝕜] F' := u.rangeRestrict
  have range_u' : u'.range = ⊤ := u.range_rangeRestrict
  have u'_surj : Surjective u' := u.surjective_rangeRestrict
  have eq1 : u = i ∘L u' := rfl
  have eq2 : u.domRestrict A = i ∘L (u'.domRestrict A) := rfl
  -- Note that we still have that `u'.ker = u.ker` is disjoint from `A`.
  have ker_u' : u'.ker = u.ker := u.ker_rangeRestrict
  -- Thus we can apply step 1 to `u'`, and we get that `u'` is strict if and only if
  -- `u'.domRestrict A` is a closed embedding.
  have step1_output : IsQuotientMap u' ↔ IsClosedEmbedding (u'.domRestrict A) :=
    step1 u' A A_closed (ker_u' ▸ h_ker) range_u'
  -- On the other hand:
  -- * since `i` is an embedding, `u = i ∘ u'` is strict if and only if `u'` is strict
  --   (i.e a quotient map, by surjectivity);
  -- * since `i` is a closed embedding, `u.domRestrict A = i ∘ u'.domRestrict A` is a closed
  --   embedding if and only if `u'.domRestrict A` is a closed embedding.
  -- Hence, we have proven our statement.
  simp_rw [eq2, eq1, ContinuousLinearMap.coe_comp', i_clemb.of_comp_iff, ← i_clemb.isStrictMap_iff,
    ← step1_output, isQuotientMap_iff_isStrictMap_surjective, u'_surj, and_true]

/-!
### Step 3

We prove the theorem under the assumption that `u.ker` is disjoint from `A`
(i.e. `u` is injective on `A`).

The statement becomes: `u` is strict with closed range if and only if `Set.restrict A u` is
a closed embedding.
-/

theorem step3 [T2Space F] (u : E →L[𝕜] F) (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] (h_ker : Disjoint u.ker A) :
    (IsStrictMap u ∧ IsClosed (u.range : Set F)) ↔ IsClosedEmbedding (u.domRestrict A) := by
  -- It suffices to show that, if `u.domRestrict A` is a closed embedding, then the range of `u`
  -- is closed. Indeed, if this is the case, both sides of the equivalence imply that `u` has
  -- closed range, so we can invoke step 2 to prove each direction.
  suffices IsClosedEmbedding (u.domRestrict A) → IsClosed (u.range : Set F) by
    rw [← iff_self_and] at this
    rw [this, and_congr_left_iff]
    exact step2 u A A_closed h_ker
  -- Thus, assume that `u.domRestrict A` is a closed embedding. In particular, `map u A` is closed.
  intro h_clemb
  rw [isClosedEmbedding_iff, ← ContinuousLinearMap.coe_coe, ← LinearMap.coe_range,
    ContinuousLinearMap.toLinearMap_domRestrict, LinearMap.range_domRestrict] at h_clemb
  -- Fix `S` an algebraic complement of `A` containing `u.ker`. Note that `S` has finite
  -- dimension.
  rcases A.exists_isCompl with ⟨S, A_compl_S⟩
  have : FiniteDimensional 𝕜 S :=
    quotientEquivOfIsCompl A S A_compl_S |>.finiteDimensional
  -- Because `map u A` is closed and `map u S` is finite dimensional, we get that
  -- `u.range = map u A ⊔ map u S` is closed.
  have : u.range = (map u.toLinearMap A ⊔ map u.toLinearMap S) := by
    rw [← Submodule.map_sup, A_compl_S.sup_eq_top, Submodule.map_top]
  exact this ▸ Submodule.isClosed_sup_finiteDimensional _ _ h_clemb.2

/-!
### Step 4

We now deduce from the two previous step the full strength of the theorem.
-/

/-- Consider `u : E →L[𝕜] F` and `A` a closed subspace of `E` of finite codimension.
We have that `u` is strict with closed range if and only if `u.domRestrict A` is strict with
closed range.

This is [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 1, Prop. 1][bourbaki2023]. -/
public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict [T2Space F]
    (u : E →L[𝕜] F) (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] :
    (IsStrictMap u ∧ IsClosed (u.range : Set F)) ↔
      (IsStrictMap (u.domRestrict A) ∧ IsClosed (map u.toLinearMap A : Set F)) := by
  -- To reduce to step 2, we quotient by `N := A ⊓ u.ker`. Denoting by `π : E → E ⧸ N`
  -- the (automatically open) quotient map, `u` factors as `v ∘ π` with `v : E ⧸ N → F`.
  set N : Submodule 𝕜 E := A ⊓ u.ker
  set π : E →L[𝕜] E ⧸ N := N.mkQL
  set v : E ⧸ N →L[𝕜] F := N.liftQL u inf_le_right
  have π_quot : IsOpenQuotientMap π := N.isOpenQuotientMap_mkQL
  have v_comp_π_eq_u : v ∘L π = u := rfl
  -- We also consider the submodule `B := map π A` of `E ⧸ N`. It has finite codimension and,
  -- by construction, it is disjoint from the kernel of `v`.
  set B : Submodule 𝕜 (E ⧸ N) := map N.mkQ A
  have codim_B : FiniteDimensional 𝕜 ((E ⧸ N) ⧸ B) :=
    quotientQuotientEquivQuotient N A inf_le_left |>.symm.finiteDimensional
  have v_ker : Disjoint v.ker B := by
    simp [disjoint_iff, v, B, toLinearMap_liftQL, ker_liftQ,
      map_inf_eq_map_inf_comap, comap_map_mkQ, N, inf_comm]
  have v_restr_inj : Injective (Set.restrict B v) :=
    injOn_iff_injective.mp <| LinearMap.injOn_of_disjoint_ker subset_rfl v_ker.symm
  -- Because `A` contains `N`, we have `A = comap π B`. In particular, `B` is closed.
  have comap_B : comap π.toLinearMap B = A := by simp [B, N, π]
  have A_mapsTo_B : MapsTo π A B := fun _ ↦ by simp [← comap_B]
  have B_closed : IsClosed (B : Set <| E ⧸ N) := by
    rwa [← π_quot.isQuotientMap.isClosed_preimage, ← π.coe_coe, ← comap_coe, comap_B]
  -- Thus, we can apply step 3 to `v`: we get that `v` is strict with closed range if
  -- and only if `v.domRestrict B` is strict with closed range.
  have step3_output : (IsStrictMap v ∧ IsClosed (v.range : Set F)) ↔
      (IsStrictMap (v.domRestrict B) ∧ IsClosed (map v.toLinearMap B : Set F)) := by
    simp [step3 v B B_closed v_ker, isClosedEmbedding_iff, ContinuousLinearMap.coe_domRestrict,
      ← range_restrict, isEmbedding_iff_isStrictMap_injective, v_restr_inj]
  -- Now, we wish to reduce our statement about `u` and `u.domRestrict A`
  -- to what we know about `v` and `v.domRestrict B`.
  -- First, it is clear that `range u = range v` and `map u A = map v B`.
  have range_eq : v.range = u.range := range_liftQ _ _ _
  have image_eq : map v.toLinearMap B = map u.toLinearMap A := by
    simp [B, ← v_comp_π_eq_u, π, ← map_comp]
  -- Furthermore, since `π` is a quotient map and `u = v ∘ π`, we have that `u` is strict
  -- if and only if `v` is strict.
  have strict_iff : IsStrictMap u ↔ IsStrictMap v := by
    rw [← v_comp_π_eq_u, ContinuousLinearMap.coe_comp', ← π_quot.isQuotientMap.isStrictMap_iff]
  -- Now, recall the equality `A = comap π B`; it ensures that the restriction
  -- `π' : A → B` of the open quotient map `π` is *still* an (open quotient map).
  set π' : A →L[𝕜] B := π.restrict A_mapsTo_B
  have π'_quot : IsOpenQuotientMap π' := by
    let φ : (N.mkQL ⁻¹' B) ≃ₜ A := .setCongr congr(SetLike.coe $comap_B)
    exact N.isOpenQuotientMap_mkQL.restrictPreimage B |>.comp
      φ.symm.isOpenQuotientMap
  have v_comp_π'_eq_u : v.domRestrict B ∘L π' = u.domRestrict A := rfl
  -- Because `v.domRestrict B ∘ π' = u.domRestrict A`, it follows that `u.domRestrict A`
  -- is strict if and only if `v.domRestrict B` is strict.
  have strict_iff_restrict : IsStrictMap (u.domRestrict A) ↔ IsStrictMap (v.domRestrict B) := by
    rw [← v_comp_π'_eq_u, ContinuousLinearMap.coe_comp', ← π'_quot.isQuotientMap.isStrictMap_iff]
  -- Thus, we are done!
  rw [strict_iff, strict_iff_restrict, ← range_eq, ← image_eq]
  exact step3_output

-- TODO: state in terms of "equality modulo finite rank" relation
/-- If `u, v : E →L[𝕜] F` agree on a closed subspace `A` of `E` with finite codimension,
then `u` is strict with closed range if and only if `v` is strict with closed range. -/
public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_eqOn [T1Space F]
    (u v : E →L[𝕜] F) (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] (h_eqOn : EqOn u v A) :
    (IsStrictMap u ∧ IsClosed (u.range : Set F)) ↔
      (IsStrictMap v ∧ IsClosed (v.range : Set F)) := by
  simp_rw [u.isStrictMap_isClosed_range_iff_restrict A,
    v.isStrictMap_isClosed_range_iff_restrict A, ← LinearMap.range_domRestrict,
    LinearMap.coe_range, LinearMap.coe_domRestrict, ContinuousLinearMap.coe_domRestrict,
    ContinuousLinearMap.coe_coe, restrict_eq_restrict_iff.mpr h_eqOn]

end FiniteCodimSubspace

/-!
## Consequences
-/

section FiniteRank

-- TODO: state in terms of "equality modulo finite rank" relation
-- TODO: unify with statement above
/-- If `u, v : E →L[𝕜] F` differ by a finite rank continuous linear map, then `u` is strict with
closed range if and only if `v` is strict with closed range.

This is [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 1, Cor. 1][bourbaki2023]. -/
public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_finiteDimensional [T1Space F]
    (u v : E →L[𝕜] F) (h_finite_rank : FiniteDimensional 𝕜 (u - v).range) :
    (IsStrictMap u ∧ IsClosed (u.range : Set F)) ↔
      (IsStrictMap v ∧ IsClosed (v.range : Set F)) := by
  let A := (u - v).ker
  have A_closed : IsClosed (A : Set E) := (u - v).isClosed_ker
  have : FiniteDimensional 𝕜 (E ⧸ A) := (u - v).toLinearMap.quotKerEquivRange.symm.finiteDimensional
  have eqOn_A : EqOn u v A := fun _ ↦ by simp [A, sub_eq_zero]
  exact ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_eqOn u v A A_closed eqOn_A

end FiniteRank

section FiniteDimQuotient

/-- Consider `u : E →L[𝕜] F` and `B` a *complemented* finite dimensional subspace `F`. We have
that `u` is strict with closed range if and only if `B.mkQL ∘L u` is strict with closed range.

This is [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 1, Cor. 2][bourbaki2023]. -/
public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_quotient [T1Space F]
    (u : E →L[𝕜] F) (A : Submodule 𝕜 F) [dim_A : FiniteDimensional 𝕜 A]
    (A_compl : ClosedComplemented A) :
    (IsStrictMap u ∧ IsClosed (u.range : Set F)) ↔
      (IsStrictMap (A.mkQL ∘L u) ∧ IsClosed ((A.mkQL ∘L u).range : Set (F ⧸ A))) := by
  obtain ⟨S, A_compl_S⟩ := A_compl.exists_isTopCompl
  let Φ : (F ⧸ A) ≃L[𝕜] S := A.quotientEquivOfIsTopCompl S A_compl_S
  let i : S →L[𝕜] F := S.subtypeL
  have i_clemb : IsClosedEmbedding i := S.isClosedEmbedding_subtypeL A_compl_S.symm.isClosed
  let p : F →L[𝕜] F := S.projectionL A A_compl_S.symm
  have eq : i ∘ Φ ∘ A.mkQ = p := rfl
  have : FiniteDimensional 𝕜 (u - p ∘L u).range := by
    suffices (u - p ∘L u).range ≤ A from finiteDimensional_of_le this
    rintro - ⟨x, rfl⟩
    exact sub_projection_mem _ (u x)
  calc  IsStrictMap u ∧ IsClosed (range u)
    _ ↔ (IsStrictMap (p ∘ u) ∧ IsClosed (range (p ∘ u))) :=
          ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_finiteDimensional _ _ this
    _ ↔ (IsStrictMap (i ∘ Φ ∘ A.mkQ ∘ u) ∧ IsClosed (range (i ∘ Φ ∘ A.mkQ ∘ u))) := by
          simp_rw [← eq, Function.comp_assoc]
    _ ↔ (IsStrictMap (Φ ∘ A.mkQ ∘ u) ∧ IsClosed (range (Φ ∘ A.mkQ ∘ u))) := by
          rw [i_clemb.isStrictMap_iff, i_clemb.isClosed_iff_image_isClosed, ← range_comp]
    _ ↔ (IsStrictMap (A.mkQ ∘ u) ∧ IsClosed (range (A.mkQ ∘ u))) := by
          rw [Φ.toHomeomorph.isEmbedding.isStrictMap_iff, ← Φ.toHomeomorph.isClosed_image,
              ← range_comp, Φ.coe_toHomeomorph]

end FiniteDimQuotient
