/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.NonemptyFiniteChains
public import Mathlib.AlgebraicTopology.SimplicialSet.NonsingularColimit
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Preorder

import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
# The subdivision functors

In this file, we define the subdivision functor `sd : SSet ⥤ SSet`
and its right adjoint `ex`.

## References
* [J. F. Jardine, *Simplicial approximation*][jardine-2004]

-/

@[expose] public section

universe u

open CategoryTheory Opposite Limits Simplicial

/-- The functor `SimplexCategory ⥤ SSet` which sends `⦋n⦌` to the nerve of the
partially ordered type of nonempty finite chains in `{0, ..., n}` (ulifted to `Type u`).
Vertices in `SimplexCategory.sd.obj ⦋n⦌` identify to nonempty subsets of `{0, ..., n}`. -/
noncomputable def SimplexCategory.sd : SimplexCategory ⥤ SSet.{u} :=
  toPartOrd ⋙ PartOrd.nonemptyFiniteChainsFunctor ⋙ PartOrd.nerveFunctor

/-- The functor `PartOrd ⥤ PartOrd` which sends a partially ordered type `X`
to the type of nondegenerate simplices in the nerve of `X` is isomorphic to
the functor which sends `X` to `NonemptyFiniteChains X`. -/
noncomputable def PartOrd.nerveFunctorCompNIso :
    nerveFunctor.{u} ⋙ SSet.N.functor ≅ nonemptyFiniteChainsFunctor :=
      NatIso.ofComponents
        (fun _ ↦ PartOrd.Iso.mk (PartialOrder.NonemptyFiniteChains.nerveNEquiv)) (by
          intro X Y f
          ext x : 3
          dsimp at x ⊢
          ext y : 2
          simp [SSet.mapN_coe, nerveMap_app, PartialOrder.NonemptyFiniteChains.nerveNEquiv_apply,
            PartialOrder.NonemptyFiniteChains.range_toN_simplex_obj.{u}])

/-- The natural isomorphism of functors `SimplexCategory ⥤ SSet` which
identifies the standard simplex `Δ[n]` to the nerve of `ULift (Fin (n + 1))`
for all `n : ℕ`. -/
def SSet.stdSimplex.toPartOrdCompNerveFunctorIso :
    SSet.stdSimplex.{u} ≅ SimplexCategory.toPartOrd ⋙ PartOrd.nerveFunctor :=
  NatIso.ofComponents (fun _ ↦ isoNerve _)

namespace SSet

/-- The subdivision functor on simplicial sets. -/
@[no_expose]
noncomputable def sd : SSet.{u} ⥤ SSet.{u} :=
  stdSimplex.leftKanExtension SimplexCategory.sd

/-- The right adjoint to the subdivision functor on simplicial sets. -/
@[no_expose]
noncomputable def ex : SSet.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} SimplexCategory.sd

/-- The adjunction between the subdivision functor `sd` and `ex`. -/
@[no_expose]
noncomputable def sdExAdjunction : sd.{u} ⊣ ex :=
  (Presheaf.restrictedULiftYonedaAdjunction.{0}
    (uliftYoneda.{u}.leftKanExtensionUnit SimplexCategory.sd) :)

instance : sd.{u}.IsLeftAdjoint := sdExAdjunction.isLeftAdjoint

instance : ex.{u}.IsRightAdjoint := sdExAdjunction.isRightAdjoint

/-- An alternative subdivision functor for simplicial sets. It sends `X : SSet` to
the nerve of the partially ordered type `X.N` of nondegenerate simplices in `X`.
There is a natural transformation `sdToSd' : sd ⟶ sd'` which is an isomorphism when
evaluated on a nonsingular simplicial set. -/
@[simps! +dsimpLhs, implicit_reducible]
noncomputable def sd' : SSet.{u} ⥤ SSet.{u} :=
  SSet.N.functor ⋙ PartOrd.nerveFunctor

namespace stdSimplex

/-- The natural isomorphism `stdSimplex ⋙ sd ≅ SimplexCategory.sd`. -/
@[no_expose]
noncomputable def sdIso : stdSimplex.{u} ⋙ sd ≅ SimplexCategory.sd :=
  (asIso (uliftYoneda.{u}.leftKanExtensionUnit SimplexCategory.sd.{u})).symm

open Functor in
/-- The natural isomorphism `stdSimplex ⋙ sd' ≅ SimplexCategory.sd`. -/
noncomputable def sd'Iso : stdSimplex.{u} ⋙ sd' ≅ SimplexCategory.sd :=
  isoWhiskerRight (SSet.stdSimplex.toPartOrdCompNerveFunctorIso) _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    isoWhiskerLeft _ (isoWhiskerRight PartOrd.nerveFunctorCompNIso PartOrd.nerveFunctor)

end stdSimplex

instance : sd.{u}.IsLeftKanExtension stdSimplex.sdIso.inv :=
  inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.leftKanExtensionUnit SimplexCategory.sd.{u}))

/-- The natural transformation `sd ⟶ sd'`. It is an isomorphism when evaluated
on nonsingular simplicial sets. -/
@[no_expose]
noncomputable def sdToSd' : sd.{u} ⟶ sd'.{u} :=
  sd.{u}.descOfIsLeftKanExtension stdSimplex.sdIso.inv _ stdSimplex.sd'Iso.{u}.inv

@[reassoc (attr := simp)]
lemma stdSimplex.sdIso_inv_comp_whiskerLeft_sdToSd' :
    stdSimplex.sdIso.{u}.inv ≫ stdSimplex.whiskerLeft sdToSd' =
      stdSimplex.sd'Iso.inv := by
  simp [sdToSd']

@[reassoc (attr := simp)]
lemma stdSimplex.sdIso_inv_app_comp_sdToSd'_app (n : SimplexCategory) :
    stdSimplex.sdIso.{u}.inv.app n ≫ sdToSd'.app _ =
      stdSimplex.sd'Iso.inv.app n :=
  congr($(sdIso_inv_comp_whiskerLeft_sdToSd').app n)

@[reassoc (attr := simp)]
lemma stdSimplex.whiskerLeft_sdToSd'_comp_sd'Iso_hom :
    stdSimplex.whiskerLeft sdToSd' ≫ stdSimplex.sd'Iso.{u}.hom =
      stdSimplex.sdIso.{u}.hom := by
  simp [← cancel_epi stdSimplex.sdIso.{u}.inv]

@[reassoc (attr := simp)]
lemma stdSimplex.sdToSd'_app_comp_sd'Iso_hom_app (n : SimplexCategory) :
    sdToSd'.app _ ≫ stdSimplex.sd'Iso.{u}.hom.app n =
      stdSimplex.sdIso.hom.app n :=
  congr($(whiskerLeft_sdToSd'_comp_sd'Iso_hom).app n)

@[reassoc]
lemma stdSimplex.sdToSd'_app (n : SimplexCategory) :
    sdToSd'.{u}.app (stdSimplex.obj n) =
      stdSimplex.sdIso.hom.app n ≫ stdSimplex.sd'Iso.inv.app n := by
  simp [← stdSimplex.sdToSd'_app_comp_sd'Iso_hom_app]

instance (n : SimplexCategory) : IsIso (sdToSd'.{u}.app (stdSimplex.obj n)) := by
  rw [stdSimplex.sdToSd'_app]
  infer_instance

instance : IsIso (stdSimplex.whiskerLeft sdToSd') := by
  rw [NatTrans.isIso_iff_isIso_app]
  dsimp
  infer_instance

private lemma preservesColimit_functorN_sd'_aux {X : SSet.{u}}
    {n : ℕ} {i : X.N} (x : ComposableArrows i.subcomplex.toSSet.N n)
    {k : X.N} (hk : mapN i.subcomplex.ι (x.obj (Fin.last _)) = k) :
    ∃ (z : ComposableArrows k.subcomplex.toSSet.N n), ∀ (d : Fin (n + 1)),
      mapN k.subcomplex.ι (z.obj d) = mapN i.subcomplex.ι (x.obj d) := by
  let φ (d : Fin (n + 1)) : k.subcomplex.toSSet.N :=
    (mapN i.subcomplex.ι (x.obj d)).toSubcomplex (by
      simp only [← Subfunctor.ofSection_le_iff, subcomplex_mapN]
      have h₁ := x.monotone d.le_last
      rw [N.le_iff] at h₁
      exact (Subcomplex.image_monotone i.subcomplex.ι h₁).trans (by simp [← hk]))
  have hφ : Monotone φ := by
    intro d d' h
    dsimp [φ]
    rw [N.toSubcomplex_le_toSubcomplex_iff]
    exact (mapN _).monotone (x.monotone h)
  exact ⟨hφ.functor, fun d ↦ by simp [φ]⟩

open Functor in
instance (X : SSet.{u}) : PreservesColimit X.functorN sd' :=
  preservesColimit_of_preserves_colimit_cocone X.isColimitCoconeN
    (evaluationJointlyReflectsColimits _ (fun ⟨n⟩ ↦ by
      induction n with | mk n
      refine Nonempty.some ((Types.isColimit_iff_coconeTypesIsColimit ..).2
        ⟨?_, fun b ↦ ?_⟩)
      · intro x y h
        let F := (X.functorN ⋙ sd') ⋙ (evaluation _ _).obj (op ⦋n⦌)
        obtain ⟨i, x, rfl⟩ := F.ιColimitType_jointly_surjective x
        obtain ⟨j, y, rfl⟩ := F.ιColimitType_jointly_surjective y
        dsimp [F] at x y h
        generalize hx : mapN i.subcomplex.ι (x.obj (Fin.last _)) = k
        have hy : mapN j.subcomplex.ι (y.obj (Fin.last _)) = k := by
          rw [← hx]
          exact Functor.congr_obj h.symm (Fin.last _)
        have hki : k ≤ i := by
          rw [← hx, N.le_iff_toS_le_toS, toS_mapN_of_mono, S.le_def]
          simp
        have hkj : k ≤ j := by
          rw [← hy, N.le_iff_toS_le_toS, toS_mapN_of_mono, S.le_def]
          simp
        obtain ⟨z, hz⟩ := preservesColimit_functorN_sd'_aux x hx
        obtain ⟨z', hz'⟩ := preservesColimit_functorN_sd'_aux y hy
        obtain rfl : z = z' :=
          ComposableArrows.ext_of_isThin
            (fun d ↦ mapN_injective_of_mono k.subcomplex.ι (by
              rw [hz, hz']
              exact congr($(h).obj d)))
        trans Functor.ιColimitType _ k z
        · rw [← ιColimitType_map F (homOfLE hki)]
          congr
          refine ComposableArrows.ext_of_isThin (fun d ↦ ?_)
          apply mapN_injective_of_mono i.subcomplex.ι
          simp [F, dsimp% sd'_map_app_hom_apply_obj (f := X.functorN.map (homOfLE hki)),
            mapN_mapN, hz d]
        · rw [← ιColimitType_map F (homOfLE hkj)]
          congr
          refine ComposableArrows.ext_of_isThin (fun d ↦ ?_)
          apply mapN_injective_of_mono j.subcomplex.ι
          simp [F, dsimp% sd'_map_app_hom_apply_obj (f := X.functorN.map (homOfLE hkj)),
            mapN_mapN, hz' d]
      · refine ⟨ιColimitType _ (b.obj (Fin.last _))
          (Monotone.functor (f := fun i ↦ (b.obj i).toSubcomplex ?_) (fun i j hij ↦ ?_)),
          nerve.ext_of_isThin ?_⟩
        · dsimp
          rw [← Subfunctor.ofSection_le_iff, ← N.le_iff]
          exact b.monotone (Fin.le_last _)
        · rw [N.toSubcomplex_le_toSubcomplex_iff]
          exact b.monotone hij
        · ext i : 1
          rw [N.ext_iff]
          have : Mono (X.coconeN.ι.app (b.obj (Fin.last n))) := by
            dsimp; infer_instance
          apply toS_mapN_of_mono))

instance (X : SSet.{u}) [Nonsingular X] : PreservesColimit X.functorN' sd' :=
  preservesColimit_of_iso_diagram _ X.functorN'Iso.symm

instance (X : SSet.{u}) [Nonsingular X] : IsIso (sdToSd'.app X) :=
  MorphismProperty.colimitsOfShape_le (W := .isomorphisms SSet.{u}) _
    (.mk' _ _ _ _ (isColimitOfPreserves sd X.isColimitCoconeN')
      (isColimitOfPreserves sd' X.isColimitCoconeN') (Functor.whiskerLeft _ sdToSd')
      (fun s ↦ (by dsimp; infer_instance)) _ (fun x ↦ by simp))

instance : sd'.{u}.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    rw [NatTrans.mono_iff_mono_app]
    rintro ⟨n⟩
    rw [mono_iff_injective]
    intro s t h
    rw [nerve.ext_of_isThin_iff]
    ext i
    exact mapN_injective_of_mono f (congr($(h).obj i))

instance (n : ℕ) : Mono (sd.map (boundary.{u} n).ι) :=
  ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk (asIso (sdToSd'.app _)) (asIso (sdToSd'.app _)))).mpr
      (.infer_property (sd'.map (boundary.{u} n).ι))

instance : PreservesWellOrderContinuousOfShape ℕ sd.{u} where

open MorphismProperty modelCategoryQuillen in
instance : sd.{u}.PreservesMonomorphisms where
  preserves {X Y} i _ := by
    have : (coproducts.{u} I).pushouts ≤ (monomorphisms _).inverseImage sd.{u} := by
      rw [← MorphismProperty.map_le_iff]
      refine ((coproducts.{u} I).map_pushouts_le sd.{u}).trans ?_
      rw [pushouts_le_iff, map_le_iff, coproducts_le_iff.{u}]
      intro _ _ _ ⟨n⟩
      simp only [inverseImage_iff, monomorphisms.iff]
      infer_instance
    exact ((monomorphisms _).inverseImage sd).transfiniteCompositionsOfShape_le _ _
      (((relativeCellComplexOfMono i).transfiniteCompositionOfShape'
        (fun s ↦ boundary_ι_mem_I s.j)).ofLE this).mem

lemma mem_range_sd'_map_ι_app_iff {X : SSet.{u}} (A : X.Subcomplex)
    {d : ℕ} (x : (sd'.obj X) _⦋d⦌) :
    dsimp% x ∈ Set.range ((sd'.map A.ι).app (op ⦋d⦌)) ↔
      (x.obj (Fin.last d)).simplex ∈ A.obj _ := by
  let f : A.toSSet.N ↪o X.N :=
    { toFun := mapN A.ι
      inj' := mapN_injective_of_mono A.ι
      map_rel_iff' {s t} := by
        refine ⟨fun h ↦ ?_, fun h ↦ (mapN A.ι).monotone h⟩
        dsimp at h
        simp only [N.le_iff, subcomplex_mapN] at h ⊢
        simpa only [Subcomplex.preimage_image] using Subcomplex.preimage_monotone A.ι h }
  dsimp [sd']
  simp only [dsimp% [f] nerve.mem_range_nerveMap_app_iff_of_orderEmbedding f,
    mem_range_mapN_ι_iff, ← Subcomplex.ofSimplex_le_iff]
  exact ⟨fun hx ↦ hx _, fun hx i ↦ (N.le_iff.1 (x.monotone (Fin.le_last i))).trans hx⟩

end SSet

namespace PartialOrder

open SSet

/-- If `X` is a partially ordered type, then this is the isomorphism
between `sd'.obj (nerve X)` and `nerve (NonemptyFiniteChains X)`. -/
noncomputable def sd'ObjNerveIso (X : Type u) [PartialOrder X] :
    sd'.obj (nerve X) ≅ nerve (NonemptyFiniteChains X) :=
  PartOrd.nerveFunctor.mapIso (PartOrd.Iso.mk (α := .of _) (β := .of _)
    NonemptyFiniteChains.nerveNEquiv)

lemma sd'ObjNerveIso_hom_app_obj_finset
    {X : Type u} [DecidableEq X] [PartialOrder X] {n : ℕ}
    (t : ComposableArrows (nerve X).N n) (i : Fin (n + 1)) :
    dsimp% (((sd'ObjNerveIso X).hom.app (op ⦋n⦌) t).obj i).finset =
      Finset.image (t.obj i).simplex.obj .univ := by
  ext x
  simp [sd'ObjNerveIso, nerveMap_app]

lemma finsetImage_sd'ObjNerveIso_inv_app_simplex_obj_univ
    {X : Type u} [DecidableEq X] [PartialOrder X] {n : ℕ}
    (s : (nerve (NonemptyFiniteChains X)) _⦋n⦌) (i : Fin (n + 1)) :
    dsimp% Finset.image (((sd'ObjNerveIso X).inv.app _ s).obj i).simplex.obj .univ =
      (s.obj i).finset := by
  simp [← sd'ObjNerveIso_hom_app_obj_finset]

/-- If `X` is a partially ordered type, then this is the isomorphism
between `sd.obj (nerve X)` and `nerve (NonemptyFiniteChains X)`. -/
@[simps! -isSimp hom inv]
noncomputable def sdObjNerveIso (X : Type u) [PartialOrder X] :
    sd.obj (nerve X) ≅ nerve (NonemptyFiniteChains X) :=
  asIso (sdToSd'.app _) ≪≫ sd'ObjNerveIso X

end PartialOrder
