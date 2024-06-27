/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Basic

#align_import category_theory.limits.preserves.shapes.pullbacks from "leanprover-community/mathlib"@"f11e306adb9f2a393539d2bb4293bf1b42caa7ac"

/-!
# Preserving pullbacks

Constructions to relate the notions of preserving pullbacks and reflecting pullbacks to concrete
pullback cones.

In particular, we show that `pullbackComparison G f g` is an isomorphism iff `G` preserves
the pullback of `f` and `g`.

The dual is also given.

## TODO

* Generalise to wide pullbacks

-/


noncomputable section

universe v₁ v₂ u₁ u₂

-- Porting note: need Functor namespace for mapCone
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory.Limits

section Pullback

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)
variable {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ X} {k : W ⟶ Y} (comm : h ≫ f = k ≫ g)

/-- The map of a pullback cone is a limit iff the fork consisting of the mapped morphisms is a
limit. This essentially lets us commute `PullbackCone.mk` with `Functor.mapCone`. -/
def isLimitMapConePullbackConeEquiv :
    IsLimit (mapCone G (PullbackCone.mk h k comm)) ≃
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
    (l : IsLimit (PullbackCone.mk h k comm)) :
    have : G.map h ≫ G.map f = G.map k ≫ G.map g := by rw [← G.map_comp, ← G.map_comp,comm]
    IsLimit (PullbackCone.mk (G.map h) (G.map k) this) :=
  isLimitMapConePullbackConeEquiv G comm (PreservesLimit.preserves l)
#align category_theory.limits.is_limit_pullback_cone_map_of_is_limit CategoryTheory.Limits.isLimitPullbackConeMapOfIsLimit

/-- The property of reflecting pullbacks expressed in terms of binary fans. -/
def isLimitOfIsLimitPullbackConeMap [ReflectsLimit (cospan f g) G]
    (l : IsLimit (PullbackCone.mk (G.map h) (G.map k) (show G.map h ≫ G.map f = G.map k ≫ G.map g
    from by simp only [← G.map_comp,comm]))) : IsLimit (PullbackCone.mk h k comm) :=
  ReflectsLimit.reflects ((isLimitMapConePullbackConeEquiv G comm).symm l)
#align category_theory.limits.is_limit_of_is_limit_pullback_cone_map CategoryTheory.Limits.isLimitOfIsLimitPullbackConeMap

variable (f g) [PreservesLimit (cospan f g) G]

/-- If `G` preserves pullbacks and `C` has them, then the pullback cone constructed of the mapped
morphisms of the pullback cone is a limit. -/
def isLimitOfHasPullbackOfPreservesLimit [i : HasPullback f g] :
    have : G.map pullback.fst ≫ G.map f = G.map pullback.snd ≫ G.map g := by
      simp only [← G.map_comp, pullback.condition];
    IsLimit (PullbackCone.mk (G.map (@pullback.fst _ _ _ _ _ f g i)) (G.map pullback.snd) this) :=
  isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback f g)
#align category_theory.limits.is_limit_of_has_pullback_of_preserves_limit CategoryTheory.Limits.isLimitOfHasPullbackOfPreservesLimit

/-- If `F` preserves the pullback of `f, g`, it also preserves the pullback of `g, f`. -/
def preservesPullbackSymmetry : PreservesLimit (cospan g f) G where
  preserves {c} hc := by
    apply (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₂} _) _).toFun
    apply IsLimit.ofIsoLimit _ (PullbackCone.isoMk _).symm
    apply PullbackCone.isLimitOfFlip
    apply (isLimitMapConePullbackConeEquiv _ _).toFun
    · refine @PreservesLimit.preserves _ _ _ _ _ _ _ _ ?_ _ ?_
      · dsimp
        infer_instance
      apply PullbackCone.isLimitOfFlip
      apply IsLimit.ofIsoLimit _ (PullbackCone.isoMk _)
      exact (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₁} _) _).invFun hc
    · exact
        (c.π.naturality WalkingCospan.Hom.inr).symm.trans
          (c.π.naturality WalkingCospan.Hom.inl : _)
#align category_theory.limits.preserves_pullback_symmetry CategoryTheory.Limits.preservesPullbackSymmetry

theorem hasPullback_of_preservesPullback [HasPullback f g] : HasPullback (G.map f) (G.map g) :=
  ⟨⟨⟨_, isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback _ _)⟩⟩⟩
#align category_theory.limits.has_pullback_of_preserves_pullback CategoryTheory.Limits.hasPullback_of_preservesPullback

variable [HasPullback f g] [HasPullback (G.map f) (G.map g)]

/-- If `G` preserves the pullback of `(f,g)`, then the pullback comparison map for `G` at `(f,g)` is
an isomorphism. -/
def PreservesPullback.iso : G.obj (pullback f g) ≅ pullback (G.map f) (G.map g) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasPullbackOfPreservesLimit G f g) (limit.isLimit _)
#align category_theory.limits.preserves_pullback.iso CategoryTheory.Limits.PreservesPullback.iso

@[simp]
theorem PreservesPullback.iso_hom : (PreservesPullback.iso G f g).hom = pullbackComparison G f g :=
  rfl
#align category_theory.limits.preserves_pullback.iso_hom CategoryTheory.Limits.PreservesPullback.iso_hom

@[reassoc]
theorem PreservesPullback.iso_hom_fst :
    (PreservesPullback.iso G f g).hom ≫ pullback.fst = G.map pullback.fst := by
  simp [PreservesPullback.iso]
#align category_theory.limits.preserves_pullback.iso_hom_fst CategoryTheory.Limits.PreservesPullback.iso_hom_fst

@[reassoc]
theorem PreservesPullback.iso_hom_snd :
    (PreservesPullback.iso G f g).hom ≫ pullback.snd = G.map pullback.snd := by
  simp [PreservesPullback.iso]
#align category_theory.limits.preserves_pullback.iso_hom_snd CategoryTheory.Limits.PreservesPullback.iso_hom_snd

@[reassoc (attr := simp)]
theorem PreservesPullback.iso_inv_fst :
    (PreservesPullback.iso G f g).inv ≫ G.map pullback.fst = pullback.fst := by
  simp [PreservesPullback.iso, Iso.inv_comp_eq]
#align category_theory.limits.preserves_pullback.iso_inv_fst CategoryTheory.Limits.PreservesPullback.iso_inv_fst

@[reassoc (attr := simp)]
theorem PreservesPullback.iso_inv_snd :
    (PreservesPullback.iso G f g).inv ≫ G.map pullback.snd = pullback.snd := by
  simp [PreservesPullback.iso, Iso.inv_comp_eq]
#align category_theory.limits.preserves_pullback.iso_inv_snd CategoryTheory.Limits.PreservesPullback.iso_inv_snd

end Pullback

section Pushout

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)
variable {W X Y Z : C} {h : X ⟶ Z} {k : Y ⟶ Z} {f : W ⟶ X} {g : W ⟶ Y} (comm : f ≫ h = g ≫ k)

/-- The map of a pushout cocone is a colimit iff the cofork consisting of the mapped morphisms is a
colimit. This essentially lets us commute `PushoutCocone.mk` with `Functor.mapCocone`. -/
def isColimitMapCoconePushoutCoconeEquiv :
    IsColimit (mapCocone G (PushoutCocone.mk h k comm)) ≃
      IsColimit
        (PushoutCocone.mk (G.map h) (G.map k) (by simp only [← G.map_comp, comm]) :
          PushoutCocone (G.map f) (G.map g)) :=
  (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).symm.trans <|
    IsColimit.equivIsoColimit <|
      Cocones.ext (Iso.refl _) <| by
        rintro (_ | _ | _) <;> dsimp <;>
          simp only [Category.comp_id, Category.id_comp, ← G.map_comp]
#align category_theory.limits.is_colimit_map_cocone_pushout_cocone_equiv CategoryTheory.Limits.isColimitMapCoconePushoutCoconeEquiv

/-- The property of preserving pushouts expressed in terms of binary cofans. -/
def isColimitPushoutCoconeMapOfIsColimit [PreservesColimit (span f g) G]
    (l : IsColimit (PushoutCocone.mk h k comm)) :
    IsColimit (PushoutCocone.mk (G.map h) (G.map k) (show G.map f ≫ G.map h = G.map g ≫ G.map k
      from by simp only [← G.map_comp,comm] )) :=
  isColimitMapCoconePushoutCoconeEquiv G comm (PreservesColimit.preserves l)
#align category_theory.limits.is_colimit_pushout_cocone_map_of_is_colimit CategoryTheory.Limits.isColimitPushoutCoconeMapOfIsColimit

/-- The property of reflecting pushouts expressed in terms of binary cofans. -/
def isColimitOfIsColimitPushoutCoconeMap [ReflectsColimit (span f g) G]
    (l : IsColimit (PushoutCocone.mk (G.map h) (G.map k) (show G.map f ≫ G.map h =
      G.map g ≫ G.map k from by simp only [← G.map_comp,comm]))) :
    IsColimit (PushoutCocone.mk h k comm) :=
  ReflectsColimit.reflects ((isColimitMapCoconePushoutCoconeEquiv G comm).symm l)
#align category_theory.limits.is_colimit_of_is_colimit_pushout_cocone_map CategoryTheory.Limits.isColimitOfIsColimitPushoutCoconeMap

variable (f g) [PreservesColimit (span f g) G]

/-- If `G` preserves pushouts and `C` has them, then the pushout cocone constructed of the mapped
morphisms of the pushout cocone is a colimit. -/
def isColimitOfHasPushoutOfPreservesColimit [i : HasPushout f g] :
    IsColimit (PushoutCocone.mk (G.map pushout.inl) (G.map (@pushout.inr _ _ _ _ _ f g i))
    (show G.map f ≫ G.map pushout.inl = G.map g ≫ G.map pushout.inr from by
      simp only [← G.map_comp, pushout.condition])) :=
  isColimitPushoutCoconeMapOfIsColimit G _ (pushoutIsPushout f g)
#align category_theory.limits.is_colimit_of_has_pushout_of_preserves_colimit CategoryTheory.Limits.isColimitOfHasPushoutOfPreservesColimit

/-- If `F` preserves the pushout of `f, g`, it also preserves the pushout of `g, f`. -/
def preservesPushoutSymmetry : PreservesColimit (span g f) G where
  preserves {c} hc := by
    apply (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).toFun
    apply IsColimit.ofIsoColimit _ (PushoutCocone.isoMk _).symm
    apply PushoutCocone.isColimitOfFlip
    apply (isColimitMapCoconePushoutCoconeEquiv _ _).toFun
    · refine @PreservesColimit.preserves _ _ _ _ _ _ _ _ ?_ _ ?_ -- Porting note: more TC coddling
      · dsimp
        infer_instance
      · exact PushoutCocone.flipIsColimit hc
#align category_theory.limits.preserves_pushout_symmetry CategoryTheory.Limits.preservesPushoutSymmetry

theorem hasPushout_of_preservesPushout [HasPushout f g] : HasPushout (G.map f) (G.map g) :=
  ⟨⟨⟨_, isColimitPushoutCoconeMapOfIsColimit G _ (pushoutIsPushout _ _)⟩⟩⟩
#align category_theory.limits.has_pushout_of_preserves_pushout CategoryTheory.Limits.hasPushout_of_preservesPushout

variable [HasPushout f g] [HasPushout (G.map f) (G.map g)]

/-- If `G` preserves the pushout of `(f,g)`, then the pushout comparison map for `G` at `(f,g)` is
an isomorphism. -/
def PreservesPushout.iso : pushout (G.map f) (G.map g) ≅ G.obj (pushout f g) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasPushoutOfPreservesColimit G f g)
#align category_theory.limits.preserves_pushout.iso CategoryTheory.Limits.PreservesPushout.iso

@[simp]
theorem PreservesPushout.iso_hom : (PreservesPushout.iso G f g).hom = pushoutComparison G f g :=
  rfl
#align category_theory.limits.preserves_pushout.iso_hom CategoryTheory.Limits.PreservesPushout.iso_hom

@[reassoc]
theorem PreservesPushout.inl_iso_hom :
    pushout.inl ≫ (PreservesPushout.iso G f g).hom = G.map pushout.inl := by
  delta PreservesPushout.iso
  simp
#align category_theory.limits.preserves_pushout.inl_iso_hom CategoryTheory.Limits.PreservesPushout.inl_iso_hom

@[reassoc]
theorem PreservesPushout.inr_iso_hom :
    pushout.inr ≫ (PreservesPushout.iso G f g).hom = G.map pushout.inr := by
  delta PreservesPushout.iso
  simp
#align category_theory.limits.preserves_pushout.inr_iso_hom CategoryTheory.Limits.PreservesPushout.inr_iso_hom

@[reassoc (attr := simp)]
theorem PreservesPushout.inl_iso_inv :
    G.map pushout.inl ≫ (PreservesPushout.iso G f g).inv = pushout.inl := by
  simp [PreservesPushout.iso, Iso.comp_inv_eq]
#align category_theory.limits.preserves_pushout.inl_iso_inv CategoryTheory.Limits.PreservesPushout.inl_iso_inv

@[reassoc (attr := simp)]
theorem PreservesPushout.inr_iso_inv :
    G.map pushout.inr ≫ (PreservesPushout.iso G f g).inv = pushout.inr := by
  simp [PreservesPushout.iso, Iso.comp_inv_eq]
#align category_theory.limits.preserves_pushout.inr_iso_inv CategoryTheory.Limits.PreservesPushout.inr_iso_inv

end Pushout

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)

section Pullback

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
variable [HasPullback f g] [HasPullback (G.map f) (G.map g)]

/-- If the pullback comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
pullback of `(f,g)`. -/
def PreservesPullback.ofIsoComparison [i : IsIso (pullbackComparison G f g)] :
    PreservesLimit (cospan f g) G := by
  apply preservesLimitOfPreservesLimitCone (pullbackIsPullback f g)
  apply (isLimitMapConePullbackConeEquiv _ _).symm _
  refine @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (cospan (G.map f) (G.map g))) ?_
  apply i
#align category_theory.limits.preserves_pullback.of_iso_comparison CategoryTheory.Limits.PreservesPullback.ofIsoComparison

variable [PreservesLimit (cospan f g) G]

instance : IsIso (pullbackComparison G f g) := by
  rw [← PreservesPullback.iso_hom]
  infer_instance

end Pullback

section Pushout

variable {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
variable [HasPushout f g] [HasPushout (G.map f) (G.map g)]

/-- If the pushout comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
pushout of `(f,g)`. -/
def PreservesPushout.ofIsoComparison [i : IsIso (pushoutComparison G f g)] :
    PreservesColimit (span f g) G := by
  apply preservesColimitOfPreservesColimitCocone (pushoutIsPushout f g)
  apply (isColimitMapCoconePushoutCoconeEquiv _ _).symm _
  -- Porting note: apply no longer creates goals for instances
  refine @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (span (G.map f) (G.map g))) ?_
  apply i
#align category_theory.limits.preserves_pushout.of_iso_comparison CategoryTheory.Limits.PreservesPushout.ofIsoComparison

variable [PreservesColimit (span f g) G]

instance : IsIso (pushoutComparison G f g) := by
  rw [← PreservesPushout.iso_hom]
  infer_instance

end Pushout

end

end CategoryTheory.Limits
