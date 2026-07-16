/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.Topology.Maps.Strict.Module
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
* `ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_finiteRangeSetoid`: if `u, v : E →L[𝕜] F`
  differ by a finite rank continuous linear map, then `u` is strict with closed range if and only
  if `v` is strict with closed range.
* `ContinuousLinearMap.isStrictMap_isClosed_range_iff_quotient`: given a *complemented*
  finite dimensional subspace `B` of `F`, we have that `u` is strict with closed range
  if and only if `B.mkQL ∘L u` is strict with closed range.

These three results show up crucially when developing the theory of Fredholm operators
between topological vector spaces. Note that none of the results here use the Hahn-Banach
theorem, so there is no significant restriction on the field.

## Implementation details

This file covers almost exactly the content of
[N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 1][bourbaki2023]. However,
there are two notable changes compared to Bourbaki :
* We treat all topological vector spaces over complete nontrivially normed fields,
  where Bourbaki restricts to locally convex spaces over `ℝ` or `ℂ`. To do so, we have to
  tweak one statement by assuming that a finite dimensional subspace is complemented, which
  is always the case when you have Hahn-Banach available.
* We give a different proof, where we reduce the statement to
  `AddMonoidHom.isStrictMap_prodMap_iff`. This gives a slightly longer proof, but we
  claim that it is more natural.

Note that these two changes are independent: the extra generality could have been achieved
with Bourbaki's proof.

## References

* [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 1][bourbaki2023]

-/

open Topology Set Submodule Function ContinuousLinearMap

variable {𝕜 : Type*}
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {E F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]

section FiniteCodimSubspace

/-!
## Proof of `ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict`

Let `u : E → F` be a continuous linear map, and `A` a finite codimension closed
subspace of `E`. We want to show that `u` is strict with closed range if and only if
its restriction `u.domRestrict A : A → F` is strict with closed range.

We do the proof in five steps. Note that we have commented the whole proof, so hopefully
you can follow the argument by reading the source code.
-/

/-!
### Step 1

We prove the theorem under the assumptions that
- `u` is surjective
- `u.ker` is disjoint from `A` (i.e. `u` is injective on `A`)
- `u.domRestrict A` has closed range

The strategy of proof is to decompose both spaces into complementary subspace,
with one of the spaces being finite dimensional and `u` preserving this decomposition.

The result then follows from `AddMonoidHom.isStrictMap_prodMap_iff` and
`ContinuousLinearMap.isStrictMap_of_finiteDimensional`.
-/

theorem step1 (u : E →L[𝕜] F) (A : Submodule 𝕜 E)
    (A_closed : IsClosed (A : Set E)) [A_cofg : A.CoFG]
    (h_ker : Disjoint u.ker A) (range_u : u.range = ⊤)
    (range_u_restr : IsClosed ((u.domRestrict A).range : Set F)) :
    IsStrictMap u ↔ IsStrictMap (u.domRestrict A) := by
  -- Fix `S` an algebraic complement of `A` containing `u.ker`. It has finite dimension.
  rcases h_ker.exists_isCompl with ⟨S, ker_le_S, S_compl_A⟩
  have : FiniteDimensional 𝕜 S := .of_fg <| A_cofg.fg_of_isCompl S_compl_A.symm
  -- Because `u` is assumed surjective and `S ⊔ A = ⊤`, we have `map u S ⊔ map u A = ⊤`.
  -- Furthermore, because the kernel of `u` is fully contained in `S`, we can show that
  -- `map u S ⊓ map u A = ⊥`, so that `map u S` and `map u A` are in fact algebraic complements
  -- of each other.
  have uS_compl_uA : IsCompl (map u.toLinearMap S) (map u.toLinearMap A) :=
    ⟨disjoint_map_of_ker_le_left S_compl_A.disjoint ker_le_S,
      codisjoint_map (LinearMap.range_eq_top.mp range_u) S_compl_A.codisjoint⟩
  -- Because `A` (resp. `map u A`) is closed and `S` (resp `map u S`) has finite dimension,
  -- `A` and `S` (resp `map u A` and `map u S`) are in fact *topological* complements of each other.
  replace S_compl_A : IsTopCompl S A :=
    S_compl_A.symm.isTopCompl_of_finiteDimensional_quotient A_closed |>.symm
  replace uS_compl_uA : IsTopCompl (map u.toLinearMap S) (map u.toLinearMap A) :=
    uS_compl_uA.symm.isTopCompl_of_isClosed_of_finiteDimensional
      (by simpa using range_u_restr) |>.symm
  -- In particular, `S` and `map u S` are T2.
  have : T2Space (map u.toLinearMap S) := uS_compl_uA.t2Space (by simpa using range_u_restr)
  -- Thus, we have decomposed both the domain and the codomain into topological complements,
  -- and `u` preserves this decomposition, inducing maps `uₛ : S → map u S` and `uₐ : A → map u A`.
  set uₛ : S →L[𝕜] map u.toLinearMap S := u.restrict (fun _ ↦ mem_map_of_mem)
  set uₐ : A →L[𝕜] map u.toLinearMap A := u.restrict (fun _ ↦ mem_map_of_mem)
  -- Using the corresponding isomorphisms `(S × A) ≃L[𝕜] E` and `(map u S × map u A) ≃L[𝕜] F`,
  -- we have to show that the map `uₛ.prodMap uₐ : S × A → map u S × map u A` is strict
  -- if and only if `uₐ : A → map u A` is strict.
  -- This follows from `AddMonoidHom.isStrictMap_prodMap_iff`, and the fact that `uₛ` is a
  -- continuous linear map between T2 finite dimensional spaces, hence a strict map.
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
  simp_rw [← coe_coe, ContinuousLinearMap.coe_prodMap, LinearMap.isStrictMap_prodMap_iff, coe_coe,
    uₛ.isStrictMap_of_finiteDimensional, true_and]

/-!
### Step 2

We prove the theorem under the assumptions that
- `u` is surjective
- `u.ker` is disjoint from `A` (i.e. `u` is injective on `A`)
-/

theorem step2 (u : E →L[𝕜] F) (A : Submodule 𝕜 E)
    (A_closed : IsClosed (A : Set E)) [A.CoFG]
    (h_ker : Disjoint u.ker A) (h_range : u.range = ⊤) :
    IsStrictMap u ↔ IsStrictMap (u.domRestrict A) ∧ IsClosed ((u.domRestrict A).range : Set F) := by
  -- To reduce to step 1, it suffices to show that `IsStrictMap u → IsClosed (map u A)`.
  suffices IsStrictMap u → IsClosed ((u.domRestrict A).range : Set F) by grind only [step1]
  -- So, we assume that `u` is strict. Because it is surjective, it is a quotient map.
  intro u_strict
  have u_quot : IsQuotientMap u := by
    rw [LinearMap.range_eq_top, coe_coe] at h_range
    simp [isQuotientMap_iff_isStrictMap_surjective, h_range, u_strict]
  -- Hence, we have to check that `comap u (map u A)` is closed. This follows from
  -- `A ≤ comap u (map u A)` and the fact that `A` is closed with finite codimension.
  rw [← u_quot.isClosed_preimage, ← coe_coe, ← Submodule.comap_coe, toLinearMap_domRestrict,
    LinearMap.range_domRestrict]
  exact Submodule.isClosed_mono_of_finiteDimensional_quotient A_closed (le_comap_map _ _)

/-!
### Step 3

We prove the theorem under the assumptions that
- `u` has closed range
- `u.ker` is disjoint from `A` (i.e. `u` is injective on `A`)
-/

theorem step3 (u : E →L[𝕜] F) (A : Submodule 𝕜 E)
    (A_closed : IsClosed (A : Set E)) [A.CoFG]
    (h_ker : Disjoint u.ker A) (h_range : IsClosed (u.range : Set F)) :
    IsStrictMap u ↔ IsStrictMap (u.domRestrict A) ∧ IsClosed ((u.domRestrict A).range : Set F) := by
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
  simp_rw [eq2, eq1, coe_comp, ← i_clemb.isEmbedding.isStrictMap_iff, toLinearMap_comp,
    LinearMap.range_comp, map_coe i.toLinearMap, coe_coe, ← i_clemb.isClosed_iff_image_isClosed]
  -- We finish by applying step 2 (using that `u.ker = u'.ker`).
  exact step2 u' A A_closed (u.ker_rangeRestrict ▸ h_ker) range_u'

/-!
### Step 4

We prove the theorem under the assumption that `u.ker` is disjoint from `A`
(i.e. `u` is injective on `A`).
-/

theorem step4 (u : E →L[𝕜] F) (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E))
    [A.CoFG] (h_ker : Disjoint u.ker A) :
    (IsStrictMap u ∧ IsClosed (u.range : Set F)) ↔
      IsStrictMap (u.domRestrict A) ∧ IsClosed ((u.domRestrict A).range : Set F) := by
  -- To reduce to step 3, it suffices to show that, if `u.domRestrict A` has closed range,
  -- then so does `u`.
  suffices IsClosed ((u.domRestrict A).range : Set F) → IsClosed (u.range : Set F) by
    grind only [step3]
  -- This follows from a general lemma, but we recall the proof below for completeness
  simpa using u.toLinearMap.isClosed_range_of_isClosed_map_of_finiteDimensional_quotient
  -- Assume that `map u A` is closed, and fix `S` an algebraic complement of `A`.
  -- It has finite dimension. Then `u.range = map u A ⊔ map u S` is the supremum of
  -- a closed subspace and a finite dimensional subspace, hence it is closed.

/-!
### Step 5

We now deduce from the previous steps the full strength of the theorem.
-/

/-- Let `u : E → F` be a continuous linear map, and `A` a closed subspace of `E` of finite
codimension. Then `u` is strict with closed range if and only if its restriction
`u.domRestrict A : A → F` is strict with closed range.

This is [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 1, Prop. 1][bourbaki2023]. -/
public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict
    (u : E →L[𝕜] F) (A : Submodule 𝕜 E) (A_closed : IsClosed (A : Set E)) [A.CoFG] :
    (IsStrictMap u ∧ IsClosed (u.range : Set F)) ↔
      (IsStrictMap (u.domRestrict A) ∧ IsClosed ((u.domRestrict A).range : Set F)) := by
  -- To reduce to step 4, we quotient by `N := A ⊓ u.ker`. Denoting by `π : E → E ⧸ N`
  -- the (automatically open) quotient map, `u` factors as `v ∘ π` with `v : E ⧸ N → F`.
  set N : Submodule 𝕜 E := A ⊓ u.ker
  set π : E →L[𝕜] E ⧸ N := N.mkQL
  set v : E ⧸ N →L[𝕜] F := N.liftQL u inf_le_right
  have π_quot : IsOpenQuotientMap π := N.isOpenQuotientMap_mkQL
  have u_eq : u = v ∘L π := rfl
  -- We also consider the submodule `B := map π A` of `E ⧸ N`. It has finite codimension and,
  -- by construction, it is disjoint from the kernel of `v`.
  set B : Submodule 𝕜 (E ⧸ N) := map N.mkQ A
  have B_cofg : B.CoFG :=
    quotientQuotientEquivQuotient N A inf_le_left |>.symm.finiteDimensional
  have v_ker : Disjoint v.ker B := by
    simp [disjoint_iff, v, B, toLinearMap_liftQL, ker_liftQ,
      map_inf_eq_map_inf_comap, comap_map_mkQ, N, inf_comm]
  -- Because `A` contains `N`, we have `A = comap π B`. In particular, `B` is closed.
  have comap_B : comap π.toLinearMap B = A := by simp [B, N, π]
  have A_mapsTo_B : MapsTo π A B := fun _ ↦ by simp [← comap_B]
  have B_closed : IsClosed (B : Set <| E ⧸ N) := by
    rwa [← π_quot.isQuotientMap.isClosed_preimage, ← π.coe_coe, ← comap_coe, comap_B]
  -- Thus, we can apply step 4 to `v` and `B`: we get that `v` is strict with closed range if
  -- and only if `v.domRestrict B` is strict with closed range.
  have step4_output : (IsStrictMap v ∧ IsClosed (v.range : Set F)) ↔
      (IsStrictMap (v.domRestrict B) ∧ IsClosed ((v.domRestrict B).range : Set F)) :=
    step4 v B B_closed v_ker
  -- Now, we wish to reduce our statement about `u` and `u.domRestrict A`
  -- to what we know about `v` and `v.domRestrict B`.
  -- First, it is clear that `range u = range v` and `map u A = map v B`.
  have range_eq : v.range = u.range := range_liftQ _ _ _
  have range_restr_eq : (v.domRestrict B).range = (u.domRestrict A).range := by
    simp [B, u_eq, π, ← map_comp]
  -- Now, recall the equality `A = comap π B`; it ensures that the restriction
  -- `π' : A → B` of the open quotient map `π` is *still* an (open) quotient map.
  set π' : A →L[𝕜] B := π.restrict A_mapsTo_B
  have π'_quot : IsOpenQuotientMap π' := by
    let φ : (N.mkQL ⁻¹' B) ≃ₜ A := .setCongr congr(SetLike.coe $comap_B)
    exact N.isOpenQuotientMap_mkQL.restrictPreimage B |>.comp
      φ.symm.isOpenQuotientMap
  -- Note that `u.domRestrict A` factors as `v.domRestrict B ∘ π'`.
  have u_restr_eq : u.domRestrict A = v.domRestrict B ∘L π' := rfl
  -- We conclude by invoking `IsQuotientMap.isStrictMap_iff` twice, to get that strictness of
  -- `u` (resp. `u.domRestrict A`) is equivalent to strictness of `v` (resp. `v.domRestrict B`).
  calc IsStrictMap u ∧ IsClosed (u.range : Set F)
      ↔ IsStrictMap v ∧ IsClosed (v.range : Set F) := by
        rw [← range_eq, u_eq, coe_comp, π_quot.isQuotientMap.isStrictMap_iff]
    _ ↔ IsStrictMap (v.domRestrict B) ∧ IsClosed ((v.domRestrict B).range : Set F) :=
        step4_output
    _ ↔ IsStrictMap (u.domRestrict A) ∧ IsClosed ((u.domRestrict A).range : Set F) := by
        rw [← range_restr_eq, u_restr_eq, coe_comp, π'_quot.isQuotientMap.isStrictMap_iff]

end FiniteCodimSubspace

/-!
## Consequences
-/

section FiniteRank

/-- If two continuous linear maps `u, v : E → F` agree on a subspace `A` of `E` with finite
codimension, then `u` is strict with closed range if and only if `v` is strict with closed range. -/
public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_eqOn [T2Space F]
    (u v : E →L[𝕜] F) (A : Submodule 𝕜 E) [A.CoFG] (h_eqOn : EqOn u v A) :
    (IsStrictMap u ∧ IsClosed (u.range : Set F)) ↔
      (IsStrictMap v ∧ IsClosed (v.range : Set F)) := by
  replace h_eqOn : EqOn u v A.topologicalClosure := h_eqOn.closure (by fun_prop) (by fun_prop)
  simp_rw [u.isStrictMap_isClosed_range_iff_restrict _ A.isClosed_topologicalClosure,
    v.isStrictMap_isClosed_range_iff_restrict _ A.isClosed_topologicalClosure,
    LinearMap.coe_range, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_domRestrict,
    restrict_eq_restrict_iff.mpr h_eqOn]

open LinearMap.FiniteRangeSetoid

/-- If two linear maps `u, v : E → F` differ by a finite rank linear map (recall that this is
denoted `u.toLinearMap ≈ v.toLinearMap` in scope `LinearMap.FiniteRangeSetoid`), then `u` is
strict with closed range if and only if `v` is strict with closed range.

This is [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 1, Cor. 1][bourbaki2023]. -/
public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_finiteRangeSetoid [T2Space F]
    (u v : E →L[𝕜] F) (h_equiv : u.toLinearMap ≈ v.toLinearMap) :
    (IsStrictMap u ∧ IsClosed (u.range : Set F)) ↔
      (IsStrictMap v ∧ IsClosed (v.range : Set F)) := by
  let A := u.toLinearMap.eqLocus v.toLinearMap
  have : A.CoFG := equiv_iff_eqLocus_coFG.mp h_equiv
  exact ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_eqOn u v A
    LinearMap.eqOn_eqLocus

end FiniteRank

section FiniteDimQuotient

open LinearMap.FiniteRangeSetoid

/-- Let `u : E → F` be a continuous linear map, and `A` a *complemented* finite dimensional
subspace of `F`. Then `u` is strict with closed range if and only if the induced map `E → F ⧸ A`
is strict with closed range.

This is [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 1, Cor. 2][bourbaki2023]. -/
public theorem ContinuousLinearMap.isStrictMap_isClosed_range_iff_quotient [T2Space F]
    (u : E →L[𝕜] F) (A : Submodule 𝕜 F) [FiniteDimensional 𝕜 A]
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
          rw [Φ.isHomeomorph.isEmbedding.isStrictMap_iff,
            Φ.isHomeomorph.isClosedEmbedding.isClosed_iff_image_isClosed,
            ← range_comp]

end FiniteDimQuotient
