/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang

! This file was ported from Lean 3 source module category_theory.limits.preserves.shapes.pullbacks
! leanprover-community/mathlib commit f11e306adb9f2a393539d2bb4293bf1b42caa7ac
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving pullbacks

Constructions to relate the notions of preserving pullbacks and reflecting pullbacks to concrete
pullback cones.

In particular, we show that `pullback_comparison G f g` is an isomorphism iff `G` preserves
the pullback of `f` and `g`.

The dual is also given.

## TODO

* Generalise to wide pullbacks

-/


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory.Limits

section Pullback

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

variable {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ X} {k : W ⟶ Y} (comm : h ≫ f = k ≫ g)

/-- The map of a pullback cone is a limit iff the fork consisting of the mapped morphisms is a
limit. This essentially lets us commute `pullback_cone.mk` with `functor.map_cone`. -/
def isLimitMapConePullbackConeEquiv :
    IsLimit (G.mapCone (PullbackCone.mk h k comm)) ≃
      IsLimit
        (PullbackCone.mk (G.map h) (G.map k) (by simp only [← G.map_comp, comm]) :
          PullbackCone (G.map f) (G.map g)) :=
  (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₂} _) _).symm.trans <|
    IsLimit.equivIsoLimit <|
      Cones.ext (Iso.refl _) <| by
        rintro (_ | _ | _) <;> dsimp <;> simp only [comp_id, id_comp, G.map_comp]
#align category_theory.limits.is_limit_map_cone_pullback_cone_equiv CategoryTheory.Limits.isLimitMapConePullbackConeEquiv

/-- The property of preserving pullbacks expressed in terms of binary fans. -/
def isLimitPullbackConeMapOfIsLimit [PreservesLimit (cospan f g) G]
    (l : IsLimit (PullbackCone.mk h k comm)) : IsLimit (PullbackCone.mk (G.map h) (G.map k) _) :=
  isLimitMapConePullbackConeEquiv G comm (PreservesLimit.preserves l)
#align category_theory.limits.is_limit_pullback_cone_map_of_is_limit CategoryTheory.Limits.isLimitPullbackConeMapOfIsLimit

/-- The property of reflecting pullbacks expressed in terms of binary fans. -/
def isLimitOfIsLimitPullbackConeMap [ReflectsLimit (cospan f g) G]
    (l : IsLimit (PullbackCone.mk (G.map h) (G.map k) _)) : IsLimit (PullbackCone.mk h k comm) :=
  ReflectsLimit.reflects ((isLimitMapConePullbackConeEquiv G comm).symm l)
#align category_theory.limits.is_limit_of_is_limit_pullback_cone_map CategoryTheory.Limits.isLimitOfIsLimitPullbackConeMap

variable (f g) [PreservesLimit (cospan f g) G]

/-- If `G` preserves pullbacks and `C` has them, then the pullback cone constructed of the mapped
morphisms of the pullback cone is a limit. -/
def isLimitOfHasPullbackOfPreservesLimit [HasPullback f g] :
    IsLimit (PullbackCone.mk (G.map pullback.fst) (G.map pullback.snd) _) :=
  isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback f g)
#align category_theory.limits.is_limit_of_has_pullback_of_preserves_limit CategoryTheory.Limits.isLimitOfHasPullbackOfPreservesLimit

/-- If `F` preserves the pullback of `f, g`, it also preserves the pullback of `g, f`. -/
def preservesPullbackSymmetry : PreservesLimit (cospan g f) G
    where preserves c hc :=
    by
    apply (is_limit.postcompose_hom_equiv (diagramIsoCospan.{v₂} _) _).toFun
    apply is_limit.of_iso_limit _ (pullback_cone.iso_mk _).symm
    apply pullback_cone.flip_is_limit
    apply (is_limit_map_cone_pullback_cone_equiv _ _).toFun
    · apply (config := { instances := false }) preserves_limit.preserves
      · dsimp
        infer_instance
      apply pullback_cone.flip_is_limit
      apply is_limit.of_iso_limit _ (pullback_cone.iso_mk _)
      exact (is_limit.postcompose_hom_equiv (diagramIsoCospan.{v₁} _) _).invFun hc
    ·
      exact
        (c.π.naturality walking_cospan.hom.inr).symm.trans
          (c.π.naturality walking_cospan.hom.inl : _)
#align category_theory.limits.preserves_pullback_symmetry CategoryTheory.Limits.preservesPullbackSymmetry

theorem hasPullback_of_preserves_pullback [HasPullback f g] : HasPullback (G.map f) (G.map g) :=
  ⟨⟨⟨_, isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback _ _)⟩⟩⟩
#align category_theory.limits.has_pullback_of_preserves_pullback CategoryTheory.Limits.hasPullback_of_preserves_pullback

variable [HasPullback f g] [HasPullback (G.map f) (G.map g)]

/-- If `G` preserves the pullback of `(f,g)`, then the pullback comparison map for `G` at `(f,g)` is
an isomorphism. -/
def PreservesPullback.iso : G.obj (pullback f g) ≅ pullback (G.map f) (G.map g) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasPullbackOfPreservesLimit G f g) (limit.isLimit _)
#align category_theory.limits.preserves_pullback.iso CategoryTheory.Limits.PreservesPullback.iso

@[reassoc.1]
theorem PreservesPullback.iso_hom_fst :
    (PreservesPullback.iso G f g).Hom ≫ pullback.fst = G.map pullback.fst := by
  simp [preserves_pullback.iso]
#align category_theory.limits.preserves_pullback.iso_hom_fst CategoryTheory.Limits.PreservesPullback.iso_hom_fst

@[reassoc.1]
theorem PreservesPullback.iso_hom_snd :
    (PreservesPullback.iso G f g).Hom ≫ pullback.snd = G.map pullback.snd := by
  simp [preserves_pullback.iso]
#align category_theory.limits.preserves_pullback.iso_hom_snd CategoryTheory.Limits.PreservesPullback.iso_hom_snd

@[simp, reassoc.1]
theorem PreservesPullback.iso_inv_fst :
    (PreservesPullback.iso G f g).inv ≫ G.map pullback.fst = pullback.fst := by
  simp [preserves_pullback.iso, iso.inv_comp_eq]
#align category_theory.limits.preserves_pullback.iso_inv_fst CategoryTheory.Limits.PreservesPullback.iso_inv_fst

@[simp, reassoc.1]
theorem PreservesPullback.iso_inv_snd :
    (PreservesPullback.iso G f g).inv ≫ G.map pullback.snd = pullback.snd := by
  simp [preserves_pullback.iso, iso.inv_comp_eq]
#align category_theory.limits.preserves_pullback.iso_inv_snd CategoryTheory.Limits.PreservesPullback.iso_inv_snd

end Pullback

section Pushout

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

variable {W X Y Z : C} {h : X ⟶ Z} {k : Y ⟶ Z} {f : W ⟶ X} {g : W ⟶ Y} (comm : f ≫ h = g ≫ k)

/-- The map of a pushout cocone is a colimit iff the cofork consisting of the mapped morphisms is a
colimit. This essentially lets us commute `pushout_cocone.mk` with `functor.map_cocone`. -/
def isColimitMapCoconePushoutCoconeEquiv :
    IsColimit (G.mapCocone (PushoutCocone.mk h k comm)) ≃
      IsColimit
        (PushoutCocone.mk (G.map h) (G.map k) (by simp only [← G.map_comp, comm]) :
          PushoutCocone (G.map f) (G.map g)) :=
  (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).symm.trans <|
    IsColimit.equivIsoColimit <|
      Cocones.ext (Iso.refl _) <| by
        rintro (_ | _ | _) <;> dsimp <;>
          simp only [category.comp_id, category.id_comp, ← G.map_comp]
#align category_theory.limits.is_colimit_map_cocone_pushout_cocone_equiv CategoryTheory.Limits.isColimitMapCoconePushoutCoconeEquiv

/-- The property of preserving pushouts expressed in terms of binary cofans. -/
def isColimitPushoutCoconeMapOfIsColimit [PreservesColimit (span f g) G]
    (l : IsColimit (PushoutCocone.mk h k comm)) :
    IsColimit (PushoutCocone.mk (G.map h) (G.map k) _) :=
  isColimitMapCoconePushoutCoconeEquiv G comm (PreservesColimit.preserves l)
#align category_theory.limits.is_colimit_pushout_cocone_map_of_is_colimit CategoryTheory.Limits.isColimitPushoutCoconeMapOfIsColimit

/-- The property of reflecting pushouts expressed in terms of binary cofans. -/
def isColimitOfIsColimitPushoutCoconeMap [ReflectsColimit (span f g) G]
    (l : IsColimit (PushoutCocone.mk (G.map h) (G.map k) _)) :
    IsColimit (PushoutCocone.mk h k comm) :=
  ReflectsColimit.reflects ((isColimitMapCoconePushoutCoconeEquiv G comm).symm l)
#align category_theory.limits.is_colimit_of_is_colimit_pushout_cocone_map CategoryTheory.Limits.isColimitOfIsColimitPushoutCoconeMap

variable (f g) [PreservesColimit (span f g) G]

/-- If `G` preserves pushouts and `C` has them, then the pushout cocone constructed of the mapped
morphisms of the pushout cocone is a colimit. -/
def isColimitOfHasPushoutOfPreservesColimit [HasPushout f g] :
    IsColimit (PushoutCocone.mk (G.map pushout.inl) (G.map pushout.inr) _) :=
  isColimitPushoutCoconeMapOfIsColimit G _ (pushoutIsPushout f g)
#align category_theory.limits.is_colimit_of_has_pushout_of_preserves_colimit CategoryTheory.Limits.isColimitOfHasPushoutOfPreservesColimit

/-- If `F` preserves the pushout of `f, g`, it also preserves the pushout of `g, f`. -/
def preservesPushoutSymmetry : PreservesColimit (span g f) G
    where preserves c hc :=
    by
    apply (is_colimit.precompose_hom_equiv (diagramIsoSpan.{v₂} _).symm _).toFun
    apply is_colimit.of_iso_colimit _ (pushout_cocone.iso_mk _).symm
    apply pushout_cocone.flip_is_colimit
    apply (is_colimit_map_cocone_pushout_cocone_equiv _ _).toFun
    · apply (config := { instances := false }) preserves_colimit.preserves
      · dsimp
        infer_instance
      apply pushout_cocone.flip_is_colimit
      apply is_colimit.of_iso_colimit _ (pushout_cocone.iso_mk _)
      exact (is_colimit.precompose_hom_equiv (diagramIsoSpan.{v₁} _) _).invFun hc
    · exact (c.ι.naturality walking_span.hom.snd).trans (c.ι.naturality walking_span.hom.fst).symm
#align category_theory.limits.preserves_pushout_symmetry CategoryTheory.Limits.preservesPushoutSymmetry

theorem hasPushout_of_preserves_pushout [HasPushout f g] : HasPushout (G.map f) (G.map g) :=
  ⟨⟨⟨_, isColimitPushoutCoconeMapOfIsColimit G _ (pushoutIsPushout _ _)⟩⟩⟩
#align category_theory.limits.has_pushout_of_preserves_pushout CategoryTheory.Limits.hasPushout_of_preserves_pushout

variable [HasPushout f g] [HasPushout (G.map f) (G.map g)]

/-- If `G` preserves the pushout of `(f,g)`, then the pushout comparison map for `G` at `(f,g)` is
an isomorphism. -/
def PreservesPushout.iso : pushout (G.map f) (G.map g) ≅ G.obj (pushout f g) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasPushoutOfPreservesColimit G f g)
#align category_theory.limits.preserves_pushout.iso CategoryTheory.Limits.PreservesPushout.iso

@[reassoc.1]
theorem PreservesPushout.inl_iso_hom :
    pushout.inl ≫ (PreservesPushout.iso G f g).Hom = G.map pushout.inl :=
  by
  delta preserves_pushout.iso
  simp
#align category_theory.limits.preserves_pushout.inl_iso_hom CategoryTheory.Limits.PreservesPushout.inl_iso_hom

@[reassoc.1]
theorem PreservesPushout.inr_iso_hom :
    pushout.inr ≫ (PreservesPushout.iso G f g).Hom = G.map pushout.inr :=
  by
  delta preserves_pushout.iso
  simp
#align category_theory.limits.preserves_pushout.inr_iso_hom CategoryTheory.Limits.PreservesPushout.inr_iso_hom

@[simp, reassoc.1]
theorem PreservesPushout.inl_iso_inv :
    G.map pushout.inl ≫ (PreservesPushout.iso G f g).inv = pushout.inl := by
  simp [preserves_pushout.iso, iso.comp_inv_eq]
#align category_theory.limits.preserves_pushout.inl_iso_inv CategoryTheory.Limits.PreservesPushout.inl_iso_inv

@[simp, reassoc.1]
theorem PreservesPushout.inr_iso_inv :
    G.map pushout.inr ≫ (PreservesPushout.iso G f g).inv = pushout.inr := by
  simp [preserves_pushout.iso, iso.comp_inv_eq]
#align category_theory.limits.preserves_pushout.inr_iso_inv CategoryTheory.Limits.PreservesPushout.inr_iso_inv

end Pushout

section

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₁} D]

variable (G : C ⥤ D)

section Pullback

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}

variable [HasPullback f g] [HasPullback (G.map f) (G.map g)]

/-- If the pullback comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
pullback of `(f,g)`. -/
def PreservesPullback.ofIsoComparison [i : IsIso (pullbackComparison G f g)] :
    PreservesLimit (cospan f g) G :=
  by
  apply preserves_limit_of_preserves_limit_cone (pullback_is_pullback f g)
  apply (is_limit_map_cone_pullback_cone_equiv _ _).symm _
  apply is_limit.of_point_iso (limit.is_limit (cospan (G.map f) (G.map g)))
  apply i
#align category_theory.limits.preserves_pullback.of_iso_comparison CategoryTheory.Limits.PreservesPullback.ofIsoComparison

variable [PreservesLimit (cospan f g) G]

@[simp]
theorem PreservesPullback.iso_hom : (PreservesPullback.iso G f g).Hom = pullbackComparison G f g :=
  rfl
#align category_theory.limits.preserves_pullback.iso_hom CategoryTheory.Limits.PreservesPullback.iso_hom

instance : IsIso (pullbackComparison G f g) :=
  by
  rw [← preserves_pullback.iso_hom]
  infer_instance

end Pullback

section Pushout

variable {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}

variable [HasPushout f g] [HasPushout (G.map f) (G.map g)]

/-- If the pushout comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
pushout of `(f,g)`. -/
def PreservesPushout.ofIsoComparison [i : IsIso (pushoutComparison G f g)] :
    PreservesColimit (span f g) G :=
  by
  apply preserves_colimit_of_preserves_colimit_cocone (pushout_is_pushout f g)
  apply (is_colimit_map_cocone_pushout_cocone_equiv _ _).symm _
  apply is_colimit.of_point_iso (colimit.is_colimit (span (G.map f) (G.map g)))
  apply i
#align category_theory.limits.preserves_pushout.of_iso_comparison CategoryTheory.Limits.PreservesPushout.ofIsoComparison

variable [PreservesColimit (span f g) G]

@[simp]
theorem PreservesPushout.iso_hom : (PreservesPushout.iso G f g).Hom = pushoutComparison G f g :=
  rfl
#align category_theory.limits.preserves_pushout.iso_hom CategoryTheory.Limits.PreservesPushout.iso_hom

instance : IsIso (pushoutComparison G f g) :=
  by
  rw [← preserves_pushout.iso_hom]
  infer_instance

end Pushout

end

end CategoryTheory.Limits

