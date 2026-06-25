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
public import Mathlib.Algebra.Module.LinearMap.FiniteRange

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

We do the proof in five steps.
-/

/-!
### Step 1

We prove the theorem under the assumptions that
- `u` is surjective
- `u.ker` is disjoint from `A` (i.e. `u` is injective on `A`)
- `map u A` is closed

The strategy of proof is to decompose both spaces into complementary subspace,
with one of the spaces being finite dimensional and `u` preserving this decomposition.

The result then follows from `AddMonoidHom.isStrictMap_prodMap_iff` and
`ContinuousLinearMap.isStrictMap_of_finiteDimensional`.
-/

theorem step1 [T2Space F] (u : E →L[𝕜] F) (A : Submodule 𝕜 E)
    (A_closed : IsClosed (A : Set E)) [codim_A : FiniteDimensional 𝕜 (E ⧸ A)]
    (h_ker : Disjoint u.ker A) (h_range : u.range = ⊤)
    (uA_closed : IsClosed (map u.toLinearMap A : Set F)) :
    IsStrictMap u ↔ IsStrictMap (u.domRestrict A) := by
  -- Fix `S` an algebraic complement of `A` containing `u.ker`. It has finite dimension.
  rcases h_ker.exists_isCompl with ⟨S, ker_le_S, S_compl_A⟩
  have : FiniteDimensional 𝕜 S :=
    quotientEquivOfIsCompl A S S_compl_A.symm |>.finiteDimensional
  -- Because `u` is assumed surjective and `S ⊔ A = ⊤`, we have `map u S ⊔ map u A = ⊤`.
  -- Furthermore, because the kernel of `u` is fully contained in `S`, we can show that
  -- `map u S ⊓ map u A = ⊥`, so that `map u S` and `map u A` are in fact algebraic complements
  -- of each other.
  have uS_compl_uA : IsCompl (map u.toLinearMap S) (map u.toLinearMap A) := by
    constructor
    · rw [disjoint_iff, inf_comm, map_inf_eq_map_inf_comap, comap_map_eq, sup_eq_left.mpr ker_le_S,
        S_compl_A.symm.inf_eq_bot, Submodule.map_bot]
    · rw [codisjoint_iff, ← Submodule.map_sup, S_compl_A.sup_eq_top, Submodule.map_top,
        h_range]
  -- Because `A` (resp. `map u A`) is closed and `S` (resp `map u S`) has finite dimension,
  -- `A` and `S` (resp `map u A` and `map u S`) are in fact *topological* complements of each other.
  replace S_compl_A : IsTopCompl S A :=
    S_compl_A.symm.isTopCompl_of_finiteDimensional_quotient A_closed |>.symm
  replace uS_compl_uA : IsTopCompl (map u.toLinearMap S) (map u.toLinearMap A) :=
      uS_compl_uA.symm.isTopCompl_of_isClosed_of_finiteDimensional uA_closed |>.symm
  -- Thus, we have decomposed both the domain and the codomain into topopological complements,
  -- and `u` preserves this decomposition, inducing maps `uₛ : S → map u S` and `uₐ : A → map u A`.
  set uₛ : S →L[𝕜] map u.toLinearMap S := u.restrict (fun _ ↦ mem_map_of_mem)
  set uₐ : A →L[𝕜] map u.toLinearMap A := u.restrict (fun _ ↦ mem_map_of_mem)
  -- Using the corresponding isomorphisms `(S × A) ≃L[𝕜] E` and `(map u S × map u A) ≃L[𝕜] F`,
  -- we have to show that the map `uₛ.prodMap uₐ : S × A → map u S × map u A` is strict
  -- if and only if `uₐ : A → map u A` is strict.
  -- This follows from `AddMonoidHom.isStrictMap_prodMap_iff`, and the fact that `uₛ` is a
  -- continuous linear map between finite dimensional spaces, hence a strict map.
  set Φ : (S × A) ≃L[𝕜] E := prodEquivOfIsTopCompl S A S_compl_A
  set Ψ : (map u.toLinearMap S × map u.toLinearMap A) ≃L[𝕜] F :=
    prodEquivOfIsTopCompl _ _ uS_compl_uA
  have u_eq : u = Ψ ∘ (uₛ.prodMap uₐ) ∘ Φ.symm := by
    ext x
    simp [Φ, Ψ, uₛ, uₐ, ← map_add, projection_add_projection_eq_self]
  have u_restr_eq : u.domRestrict A = (map u.toLinearMap A).subtypeL ∘ uₐ := rfl
  suffices IsStrictMap (uₛ.prodMap uₐ) ↔ IsStrictMap uₐ by
    rwa [u_restr_eq, u_eq, ← (isEmbedding_subtypeL _).isStrictMap_iff,
      ← Ψ.isHomeomorph.isEmbedding.isStrictMap_iff,
      ← Φ.symm.isHomeomorph.isQuotientMap.isStrictMap_iff]
  -- TODO: we should think of a way to avoid this
  change IsStrictMap (uₛ.toAddMonoidHom.prodMap uₐ.toAddMonoidHom) ↔ IsStrictMap uₐ
  simp_rw [AddMonoidHom.isStrictMap_prodMap_iff, LinearMap.toAddMonoidHom_coe, coe_coe,
    uₛ.isStrictMap_of_finiteDimensional, true_and]

/-!
### Step 2

We prove the theorem under the assumptions that
- `u` is surjective
- `u.ker` is disjoint from `A` (i.e. `u` is injective on `A`)
-/

theorem step2 [T2Space F] (u : E →L[𝕜] F) (A : Submodule 𝕜 E)
    (A_closed : IsClosed (A : Set E)) [codim_A : FiniteDimensional 𝕜 (E ⧸ A)]
    (h_ker : Disjoint u.ker A) (h_range : u.range = ⊤) :
    IsStrictMap u ↔ IsStrictMap (u.domRestrict A) ∧ IsClosed (map u.toLinearMap A : Set F) := by
  -- To reduce to step 1, it suffices to show that `IsStrictMap u → IsClosed (map u A)`.
  suffices IsStrictMap u → IsClosed (map u.toLinearMap A : Set F) by grind only [step1]
  -- So, we assume that `u` is strict. Because it is surjective, it is a quotient map.
  intro u_strict
  have u_quot : IsQuotientMap u := by
    rw [LinearMap.range_eq_top, coe_coe] at h_range
    simp [isQuotientMap_iff_isStrictMap_surjective, h_range, u_strict]
  -- Hence, we have to check that `comap u (map u A)` is closed. This follows from
  -- `A ≤ comap u (map u A)` and the fact that `A` is closed with finite codimension.
  rw [← u_quot.isClosed_preimage, ← coe_coe, ← Submodule.comap_coe]
  exact Submodule.isClosed_mono_of_finiteDimensional_quotient A_closed (le_comap_map _ _)

/-!
### Step 3

We prove the theorem under the assumptions that
- `u` has closed range
- `u.ker` is disjoint from `A` (i.e. `u` is injective on `A`)
-/

theorem step3 [T2Space F] (u : E →L[𝕜] F) (A : Submodule 𝕜 E)
    (A_closed : IsClosed (A : Set E)) [codim_A : FiniteDimensional 𝕜 (E ⧸ A)]
    (h_ker : Disjoint u.ker A) (h_range : IsClosed (u.range : Set F)) :
    IsStrictMap u ↔ IsStrictMap (u.domRestrict A) ∧ IsClosed (map u.toLinearMap A : Set F) := by
  -- Let `F' := u.range` and `i : F' →L[𝕜] F` be the inclusion map. By assumption,
  -- `i` is a closed embedding.
  set F' : Submodule 𝕜 F := u.range
  set i : F' →L[𝕜] F := F'.subtypeL
  have i_clemb : IsClosedEmbedding i := F'.isClosedEmbedding_subtypeL h_range
  -- Furthermore, `u` factors as `i ∘ u'` with `u' : E →L[𝕜] F'` surjective,
  -- and we clearly have `u.domRestrict A = i ∘ u'.domRestrict A` as well.
  set u' : E →L[𝕜] F' := u.rangeRestrict
  have range_u' : u'.range = ⊤ := u.range_rangeRestrict
  have eq1 : u = i ∘L u' := rfl
  have eq2 : u.domRestrict A = i ∘L (u'.domRestrict A) := rfl
  -- We can rewrite our goal in terms of `u'`.
  simp_rw [eq2, eq1, coe_comp, ← i_clemb.isEmbedding.isStrictMap_iff, toLinearMap_comp, map_comp,
    map_coe i.toLinearMap, coe_coe, ← i_clemb.isClosed_iff_image_isClosed]
  -- We finish by applying step 2 (using that `u.ker = u'.ker`).
  exact step2 u' A A_closed (u.ker_rangeRestrict ▸ h_ker) range_u'

/-!
### Step 4

We prove the theorem under the assumption that `u.ker` is disjoint from `A`
(i.e. `u` is injective on `A`).
-/

theorem step4 [T2Space F] (u : E →L[𝕜] F) (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] (h_ker : Disjoint u.ker A) :
    (IsStrictMap u ∧ IsClosed (u.range : Set F)) ↔
      IsStrictMap (u.domRestrict A) ∧ IsClosed (map u.toLinearMap A : Set F) := by
  -- To reduce to step 3, it suffices to show that, if `map u A` is closed, then so is `u.range`.
  suffices IsClosed (map u.toLinearMap A : Set F) → IsClosed (u.range : Set F) by
    grind only [step3]
  -- So, we assume that `map u A` is closed.
  intro uA_closed
  -- Fix `S` an algebraic complement of `A` containing `u.ker`. It has finite dimension.
  rcases h_ker.exists_isCompl with ⟨S, ker_le_S, S_compl_A⟩
  have : FiniteDimensional 𝕜 S :=
    quotientEquivOfIsCompl A S S_compl_A.symm |>.finiteDimensional
  -- It follows that `u.range = map u A ⊔ map u S` is closed.
  rw [← Submodule.map_top, ← S_compl_A.symm.sup_eq_top, Submodule.map_sup]
  exact isClosed_sup_finiteDimensional _ _ uA_closed


/-!
### Step 5

We now deduce from the previous steps the full strength of the theorem.
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
  -- To reduce to step 4, we quotient by `N := A ⊓ u.ker`. Denoting by `π : E → E ⧸ N`
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
  -- Thus, we can apply step 4 to `v`: we get that `v` is strict with closed range if
  -- and only if `v.domRestrict B` is strict with closed range.
  have step4_output : (IsStrictMap v ∧ IsClosed (v.range : Set F)) ↔
      (IsStrictMap (v.domRestrict B) ∧ IsClosed (map v.toLinearMap B : Set F)) := by
    simp [step4 v B B_closed v_ker, coe_domRestrict, ← range_restrict]
  -- Now, we wish to reduce our statement about `u` and `u.domRestrict A`
  -- to what we know about `v` and `v.domRestrict B`.
  -- First, it is clear that `range u = range v` and `map u A = map v B`.
  have range_eq : v.range = u.range := range_liftQ _ _ _
  have image_eq : map v.toLinearMap B = map u.toLinearMap A := by
    simp [B, ← v_comp_π_eq_u, π, ← map_comp]
  -- Furthermore, since `π` is a quotient map and `u = v ∘ π`, we have that `u` is strict
  -- if and only if `v` is strict.
  have strict_iff : IsStrictMap u ↔ IsStrictMap v := by
    rw [← v_comp_π_eq_u, coe_comp, ← π_quot.isQuotientMap.isStrictMap_iff]
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
    rw [← v_comp_π'_eq_u, coe_comp, ← π'_quot.isQuotientMap.isStrictMap_iff]
  -- Thus, we are done!
  rw [strict_iff, strict_iff_restrict, ← range_eq, ← image_eq]
  exact step4_output

end FiniteCodimSubspace

/-!
## Consequences
-/

section FiniteRank

/-- If `u, v : E →L[𝕜] F` agree on a closed subspace `A` of `E` with finite codimension,
then `u` is strict with closed range if and only if `v` is strict with closed range. -/
public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_eqOn [T2Space F]
    (u v : E →L[𝕜] F) (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [codim_A : FiniteDimensional 𝕜 (E ⧸ A)] (h_eqOn : EqOn u v A) :
    (IsStrictMap u ∧ IsClosed (u.range : Set F)) ↔
      (IsStrictMap v ∧ IsClosed (v.range : Set F)) := by
  simp_rw [u.isStrictMap_isClosed_range_iff_restrict A,
    v.isStrictMap_isClosed_range_iff_restrict A, ← LinearMap.range_domRestrict,
    LinearMap.coe_range, LinearMap.coe_domRestrict, ContinuousLinearMap.coe_domRestrict,
    ContinuousLinearMap.coe_coe, restrict_eq_restrict_iff.mpr h_eqOn]

open LinearMap.FiniteRangeSetoid

/-- If `u, v : E →L[𝕜] F` differ by a finite rank continuous linear map (recall that this is
denoted `u.toLinearMap ≈ v.toLinearMap` in scope `LinearMap.FiniteRangeSetoid`), then `u` is
strict with closed range if and only if `v` is strict with closed range.

This is [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 1, Cor. 1][bourbaki2023]. -/
public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_finiteRangeSetoid [T1Space F]
    (u v : E →L[𝕜] F) (h_equiv : u.toLinearMap ≈ v.toLinearMap) :
    (IsStrictMap u ∧ IsClosed (u.range : Set F)) ↔
      (IsStrictMap v ∧ IsClosed (v.range : Set F)) := by
  let A := u.toLinearMap.eqLocus v.toLinearMap
  have A_closed : IsClosed (A : Set E) := u.isClosed_eqLocus v
  have : FiniteDimensional 𝕜 (E ⧸ A) := equiv_iff_eqLocus_coFG.mp h_equiv
  exact ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_eqOn u v A A_closed (fun _ ↦ id)

end FiniteRank

section FiniteDimQuotient

open LinearMap.FiniteRangeSetoid

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
  set p : F →L[𝕜] F := S.projectionL A A_compl_S.symm with p_def
  have eq : i ∘ Φ ∘ A.mkQ = p := rfl
  have : u.toLinearMap ≈ (p ∘L u).toLinearMap := by
    grw [toLinearMap_comp, p_def, toLinearMap_projectionL, projection_equiv_id, LinearMap.id_comp]
  calc  IsStrictMap u ∧ IsClosed (range u)
    _ ↔ (IsStrictMap (p ∘ u) ∧ IsClosed (range (p ∘ u))) :=
          ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_finiteRangeSetoid _ _ this
    _ ↔ (IsStrictMap (i ∘ Φ ∘ A.mkQ ∘ u) ∧ IsClosed (range (i ∘ Φ ∘ A.mkQ ∘ u))) := by
          simp_rw [← eq, Function.comp_assoc]
    _ ↔ (IsStrictMap (Φ ∘ A.mkQ ∘ u) ∧ IsClosed (range (Φ ∘ A.mkQ ∘ u))) := by
          rw [i_clemb.isStrictMap_iff, i_clemb.isClosed_iff_image_isClosed, ← range_comp]
    _ ↔ (IsStrictMap (A.mkQ ∘ u) ∧ IsClosed (range (A.mkQ ∘ u))) := by
          rw [Φ.toHomeomorph.isEmbedding.isStrictMap_iff, ← Φ.toHomeomorph.isClosed_image,
              ← range_comp, Φ.coe_toHomeomorph]

end FiniteDimQuotient
