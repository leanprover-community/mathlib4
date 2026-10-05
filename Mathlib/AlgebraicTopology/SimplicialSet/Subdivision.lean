/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NonsingularColimit
public import Mathlib.AlgebraicTopology.SimplicialSet.NonemptyFiniteChains
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# The subdivision functors

In this file, we define the subdivision functor `sd : SSet ⥤ SSet`
and its right adjoint `ex`.

## References
* [J. F. Jardine, *Simplicial approximation*][jardine-2004]

-/

@[expose] public section

universe v u

open CategoryTheory Opposite Limits Simplicial

/-- The functor `SimplexCategory ⥤ SSet` which sends `⦋n⦌` to the nerve of the
partially ordered type of nonempty finite chains in `{0, ..., n}` (ulifted to `Type u`).
Vertices in `SimplexCategory.sd.obj ⦋n⦌` identify to nonempty subsets of `{0, ..., n}`. -/
noncomputable def SimplexCategory.sd : SimplexCategory ⥤ SSet.{u} :=
  toPartOrd ⋙ PartOrd.nonemptyFiniteChainsFunctor ⋙ PartOrd.nerveFunctor

noncomputable def PartOrd.nerveFunctorCompNIso :
    nerveFunctor.{u} ⋙ SSet.N.functor ≅ nonemptyFiniteChainsFunctor :=
      NatIso.ofComponents
        (fun _ ↦ PartOrd.Iso.mk (PartialOrder.NonemptyFiniteChains.nerveNEquiv)) (by
          intro X Y f
          ext x : 3
          dsimp at x ⊢
          ext y : 2
          simp [SSet.mapN_coe, nerveMap_app,
            PartialOrder.NonemptyFiniteChains.range_toN_simplex_obj.{u}])

def SSet.stdSimplex.toPartOrdCompNerveFunctorIso :
    SSet.stdSimplex.{u} ≅ SimplexCategory.toPartOrd ⋙ PartOrd.nerveFunctor :=
  NatIso.ofComponents (fun _ ↦ isoNerve _)

namespace SSet

/-- The subdivision functor on simplicial sets. -/
noncomputable def sd : SSet.{u} ⥤ SSet.{u} :=
  stdSimplex.leftKanExtension SimplexCategory.sd

/-- The right adjoint to the subdivision functor on simplicial sets. -/
noncomputable def ex : SSet.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} SimplexCategory.sd

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction between the subdivision functor `sd` and `ex`. -/
noncomputable def sdExAdjunction : sd.{u} ⊣ ex :=
  Presheaf.uliftYonedaAdjunction.{0}
    (SSet.stdSimplex.{u}.leftKanExtension SimplexCategory.sd)
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.sd)

instance : sd.{u}.IsLeftAdjoint := sdExAdjunction.isLeftAdjoint

instance : ex.{u}.IsRightAdjoint := sdExAdjunction.isRightAdjoint

/-- An alternative subdivision functor for simplicial sets. It sends `X : SSet` to
the nerve of the partially ordered type `X.N` of nondegenerate simplices in `X`.li
There is a natural transformation `sdToSd' : sd ⟶ sd'` which is an isomorphism when
evaluated on a nonsingular simplicial set. -/
@[simps!, implicit_reducible]
noncomputable def sd' : SSet.{u} ⥤ SSet.{u} :=
  SSet.N.functor ⋙ PartOrd.nerveFunctor

namespace stdSimplex

/-- The natural isomorphism `stdSimplex ⋙ sd ≅ SimplexCategory.sd`. -/
noncomputable def sdIso : stdSimplex.{u} ⋙ sd ≅ SimplexCategory.sd :=
  Presheaf.isExtensionAlongULiftYoneda _

open Functor in
noncomputable def sd'Iso : stdSimplex.{u} ⋙ sd' ≅ SimplexCategory.sd :=
  isoWhiskerRight (SSet.stdSimplex.toPartOrdCompNerveFunctorIso) _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    isoWhiskerLeft _ (isoWhiskerRight PartOrd.nerveFunctorCompNIso PartOrd.nerveFunctor)

end stdSimplex

instance : sd.{u}.IsLeftKanExtension stdSimplex.sdIso.inv :=
  inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.leftKanExtensionUnit SimplexCategory.sd.{u}))

noncomputable def sdToSd' : sd.{u} ⟶ sd'.{u} :=
  sd.{u}.descOfIsLeftKanExtension stdSimplex.sdIso.inv _ stdSimplex.sd'Iso.{u}.inv

@[reassoc]
lemma sdToSd'_app_stdSimplex_obj (n : SimplexCategory) :
    sdToSd'.{u}.app (stdSimplex.obj n) =
      stdSimplex.sdIso.hom.app n ≫ stdSimplex.sd'Iso.inv.app n := by
  simp only [← sd.{u}.descOfIsLeftKanExtension_fac_app
    stdSimplex.sdIso.inv _ stdSimplex.sd'Iso.{u}.inv n, Iso.hom_inv_id_app_assoc, sdToSd']

instance (n : SimplexCategory) : IsIso (sdToSd'.{u}.app (stdSimplex.obj n)) := by
  rw [sdToSd'_app_stdSimplex_obj]
  infer_instance

instance : IsIso (Functor.whiskerLeft stdSimplex sdToSd') := by
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
instance (X : SSet.{u}) [Nonsingular X] : PreservesColimit X.functorN sd' :=
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

end SSet
