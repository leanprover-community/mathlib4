/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks
import Mathlib.CategoryTheory.Limits.Yoneda

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

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory.Limits

section Pullback

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace PullbackCone

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) (G : C ⥤ D)

/-- The image of a pullback cone by a functor. -/
abbrev map : PullbackCone (G.map f) (G.map g) :=
  PullbackCone.mk (G.map c.fst) (G.map c.snd)
    (by simpa using G.congr_map c.condition)

/-- The map (as a cone) of a pullback cone is limit iff
the map (as a pullback cone) is limit. -/
def isLimitMapConeEquiv :
    IsLimit (mapCone G c) ≃ IsLimit (c.map G) :=
  (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₂} _) _).symm.trans <|
    IsLimit.equivIsoLimit <| by
      refine PullbackCone.ext (Iso.refl _) ?_ ?_
      · dsimp only [fst]
        simp
      · dsimp only [snd]
        simp

end PullbackCone

variable (G : C ⥤ D)
variable {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ X} {k : W ⟶ Y} (comm : h ≫ f = k ≫ g)

/-- The map of a pullback cone is a limit iff the fork consisting of the mapped morphisms is a
limit. This essentially lets us commute `PullbackCone.mk` with `Functor.mapCone`. -/
def isLimitMapConePullbackConeEquiv :
    IsLimit (mapCone G (PullbackCone.mk h k comm)) ≃
      IsLimit
        (PullbackCone.mk (G.map h) (G.map k) (by simp only [← G.map_comp, comm]) :
          PullbackCone (G.map f) (G.map g)) :=
  (PullbackCone.mk _ _ comm).isLimitMapConeEquiv G

/-- The property of preserving pullbacks expressed in terms of binary fans. -/
def isLimitPullbackConeMapOfIsLimit [PreservesLimit (cospan f g) G]
    (l : IsLimit (PullbackCone.mk h k comm)) :
    have : G.map h ≫ G.map f = G.map k ≫ G.map g := by rw [← G.map_comp, ← G.map_comp,comm]
    IsLimit (PullbackCone.mk (G.map h) (G.map k) this) :=
  (PullbackCone.isLimitMapConeEquiv _ G).1 (isLimitOfPreserves G l)

/-- The property of reflecting pullbacks expressed in terms of binary fans. -/
def isLimitOfIsLimitPullbackConeMap [ReflectsLimit (cospan f g) G]
    (l : IsLimit (PullbackCone.mk (G.map h) (G.map k) (show G.map h ≫ G.map f = G.map k ≫ G.map g
    from by simp only [← G.map_comp, comm]))) : IsLimit (PullbackCone.mk h k comm) :=
  isLimitOfReflects G
    ((PullbackCone.isLimitMapConeEquiv (PullbackCone.mk _ _ comm) G).2 l)

variable (f g) [PreservesLimit (cospan f g) G]

/-- If `G` preserves pullbacks and `C` has them, then the pullback cone constructed of the mapped
morphisms of the pullback cone is a limit. -/
def isLimitOfHasPullbackOfPreservesLimit [HasPullback f g] :
    have : G.map (pullback.fst f g) ≫ G.map f = G.map (pullback.snd f g) ≫ G.map g := by
      simp only [← G.map_comp, pullback.condition]
    IsLimit (PullbackCone.mk (G.map (pullback.fst f g)) (G.map (pullback.snd f g)) this) :=
  isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback f g)

/-- If `F` preserves the pullback of `f, g`, it also preserves the pullback of `g, f`. -/
lemma preservesPullback_symmetry : PreservesLimit (cospan g f) G where
  preserves {c} hc := ⟨by
    apply (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₂} _) _).toFun
    apply IsLimit.ofIsoLimit _ (PullbackCone.isoMk _).symm
    apply PullbackCone.isLimitOfFlip
    apply (isLimitMapConePullbackConeEquiv _ _).toFun
    · refine @isLimitOfPreserves _ _ _ _ _ _ _ _ _ ?_ ?_
      · apply PullbackCone.isLimitOfFlip
        apply IsLimit.ofIsoLimit _ (PullbackCone.isoMk _)
        exact (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₁} _) _).invFun hc
      · dsimp
        infer_instance
    · exact
        (c.π.naturality WalkingCospan.Hom.inr).symm.trans
          (c.π.naturality WalkingCospan.Hom.inl :)⟩

theorem hasPullback_of_preservesPullback [HasPullback f g] : HasPullback (G.map f) (G.map g) :=
  ⟨⟨⟨_, isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback _ _)⟩⟩⟩

variable [HasPullback f g] [HasPullback (G.map f) (G.map g)]

/-- If `G` preserves the pullback of `(f,g)`, then the pullback comparison map for `G` at `(f,g)` is
an isomorphism. -/
def PreservesPullback.iso : G.obj (pullback f g) ≅ pullback (G.map f) (G.map g) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasPullbackOfPreservesLimit G f g) (limit.isLimit _)

@[simp]
theorem PreservesPullback.iso_hom : (PreservesPullback.iso G f g).hom = pullbackComparison G f g :=
  rfl

@[reassoc]
theorem PreservesPullback.iso_hom_fst :
    (PreservesPullback.iso G f g).hom ≫ pullback.fst _ _ = G.map (pullback.fst f g) := by
  simp [PreservesPullback.iso]

@[reassoc]
theorem PreservesPullback.iso_hom_snd :
    (PreservesPullback.iso G f g).hom ≫ pullback.snd _ _ = G.map (pullback.snd f g) := by
  simp [PreservesPullback.iso]

@[reassoc (attr := simp)]
theorem PreservesPullback.iso_inv_fst :
    (PreservesPullback.iso G f g).inv ≫ G.map (pullback.fst f g) = pullback.fst _ _ := by
  simp [PreservesPullback.iso, Iso.inv_comp_eq]

@[reassoc (attr := simp)]
theorem PreservesPullback.iso_inv_snd :
    (PreservesPullback.iso G f g).inv ≫ G.map (pullback.snd f g) = pullback.snd _ _ := by
  simp [PreservesPullback.iso, Iso.inv_comp_eq]

/-- A pullback cone in `C` is limit iff if it is so after the application
of `coyoneda.obj X` for all `X : Cᵒᵖ`. -/
def PullbackCone.isLimitCoyonedaEquiv (c : PullbackCone f g) :
    IsLimit c ≃ ∀ (X : Cᵒᵖ), IsLimit (c.map (coyoneda.obj X)) :=
  (Cone.isLimitCoyonedaEquiv c).trans
    (Equiv.piCongrRight (fun X ↦ c.isLimitMapConeEquiv (coyoneda.obj X)))

end Pullback

section Pushout

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace PushoutCocone

variable {W X Y : C} {f : W ⟶ X} {g : W ⟶ Y} (c : PushoutCocone f g) (G : C ⥤ D)

/-- The image of a pullback cone by a functor. -/
abbrev map : PushoutCocone (G.map f) (G.map g) :=
  PushoutCocone.mk (G.map c.inl) (G.map c.inr) (by simpa using G.congr_map c.condition)

/-- The map (as a cocone) of a pushout cocone is colimit iff
the map (as a pushout cocone) is limit. -/
def isColimitMapCoconeEquiv :
    IsColimit (mapCocone G c) ≃ IsColimit (c.map G) :=
  (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).symm.trans <|
    IsColimit.equivIsoColimit <| by
      refine PushoutCocone.ext (Iso.refl _) ?_ ?_
      · dsimp only [inl]
        simp
      · dsimp only [inr]
        simp

end PushoutCocone

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

/-- The property of preserving pushouts expressed in terms of binary cofans. -/
def isColimitPushoutCoconeMapOfIsColimit [PreservesColimit (span f g) G]
    (l : IsColimit (PushoutCocone.mk h k comm)) :
    IsColimit (PushoutCocone.mk (G.map h) (G.map k) (show G.map f ≫ G.map h = G.map g ≫ G.map k
      from by simp only [← G.map_comp,comm] )) :=
  isColimitMapCoconePushoutCoconeEquiv G comm (isColimitOfPreserves G l)

/-- The property of reflecting pushouts expressed in terms of binary cofans. -/
def isColimitOfIsColimitPushoutCoconeMap [ReflectsColimit (span f g) G]
    (l : IsColimit (PushoutCocone.mk (G.map h) (G.map k) (show G.map f ≫ G.map h =
      G.map g ≫ G.map k from by simp only [← G.map_comp, comm]))) :
    IsColimit (PushoutCocone.mk h k comm) :=
  isColimitOfReflects G ((isColimitMapCoconePushoutCoconeEquiv G comm).symm l)

variable (f g) [PreservesColimit (span f g) G]

/-- If `G` preserves pushouts and `C` has them, then the pushout cocone constructed of the mapped
morphisms of the pushout cocone is a colimit. -/
def isColimitOfHasPushoutOfPreservesColimit [i : HasPushout f g] :
    IsColimit (PushoutCocone.mk (G.map (pushout.inl _ _)) (G.map (@pushout.inr _ _ _ _ _ f g i))
    (show G.map f ≫ G.map (pushout.inl _ _) = G.map g ≫ G.map (pushout.inr _ _) from by
      simp only [← G.map_comp, pushout.condition])) :=
  isColimitPushoutCoconeMapOfIsColimit G _ (pushoutIsPushout f g)

/-- If `F` preserves the pushout of `f, g`, it also preserves the pushout of `g, f`. -/
lemma preservesPushout_symmetry : PreservesColimit (span g f) G where
  preserves {c} hc := ⟨by
    apply (IsColimit.precomposeHomEquiv (diagramIsoSpan.{v₂} _).symm _).toFun
    apply IsColimit.ofIsoColimit _ (PushoutCocone.isoMk _).symm
    apply PushoutCocone.isColimitOfFlip
    apply (isColimitMapCoconePushoutCoconeEquiv _ _).toFun
    · -- Need to unfold these to allow the `PreservesColimit` instance to be found.
      dsimp only [span_map_fst, span_map_snd]
      exact isColimitOfPreserves _ (PushoutCocone.flipIsColimit hc)⟩

theorem hasPushout_of_preservesPushout [HasPushout f g] : HasPushout (G.map f) (G.map g) :=
  ⟨⟨⟨_, isColimitPushoutCoconeMapOfIsColimit G _ (pushoutIsPushout _ _)⟩⟩⟩

variable [HasPushout f g] [HasPushout (G.map f) (G.map g)]

/-- If `G` preserves the pushout of `(f,g)`, then the pushout comparison map for `G` at `(f,g)` is
an isomorphism. -/
def PreservesPushout.iso : pushout (G.map f) (G.map g) ≅ G.obj (pushout f g) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasPushoutOfPreservesColimit G f g)

@[simp]
theorem PreservesPushout.iso_hom : (PreservesPushout.iso G f g).hom = pushoutComparison G f g :=
  rfl

@[reassoc]
theorem PreservesPushout.inl_iso_hom :
    pushout.inl _ _ ≫ (PreservesPushout.iso G f g).hom = G.map (pushout.inl _ _) := by
  simp

@[reassoc]
theorem PreservesPushout.inr_iso_hom :
    pushout.inr _ _ ≫ (PreservesPushout.iso G f g).hom = G.map (pushout.inr _ _) := by
  simp

@[reassoc (attr := simp)]
theorem PreservesPushout.inl_iso_inv :
    G.map (pushout.inl _ _) ≫ (PreservesPushout.iso G f g).inv = pushout.inl _ _ := by
  simp [PreservesPushout.iso, Iso.comp_inv_eq]

@[reassoc (attr := simp)]
theorem PreservesPushout.inr_iso_inv :
    G.map (pushout.inr _ _) ≫ (PreservesPushout.iso G f g).inv = pushout.inr _ _ := by
  simp [PreservesPushout.iso, Iso.comp_inv_eq]

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
lemma PreservesPullback.of_iso_comparison [i : IsIso (pullbackComparison G f g)] :
    PreservesLimit (cospan f g) G := by
  apply preservesLimit_of_preserves_limit_cone (pullbackIsPullback f g)
  apply (isLimitMapConePullbackConeEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (cospan (G.map f) (G.map g))) i

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
lemma PreservesPushout.of_iso_comparison [i : IsIso (pushoutComparison G f g)] :
    PreservesColimit (span f g) G := by
  apply preservesColimit_of_preserves_colimit_cocone (pushoutIsPushout f g)
  apply (isColimitMapCoconePushoutCoconeEquiv _ _).symm _
  exact IsColimit.ofPointIso _ (i := i)

variable [PreservesColimit (span f g) G]

instance : IsIso (pushoutComparison G f g) := by
  rw [← PreservesPushout.iso_hom]
  infer_instance

/-- A pushout cocone in `C` is colimit iff it becomes limit
after the application of `yoneda.obj X` for all `X : C`. -/
def PushoutCocone.isColimitYonedaEquiv (c : PushoutCocone f g) :
    IsColimit c ≃ ∀ (X : C), IsLimit (c.op.map (yoneda.obj X)) :=
  (Limits.Cocone.isColimitYonedaEquiv c).trans
    (Equiv.piCongrRight (fun X ↦
      (IsLimit.whiskerEquivalenceEquiv walkingSpanOpEquiv.symm).trans
        ((IsLimit.postcomposeHomEquiv
          (isoWhiskerRight (cospanOp f g).symm (yoneda.obj X)) _).symm.trans
            (Equiv.trans (IsLimit.equivIsoLimit
              (by exact Cones.ext (Iso.refl _) (by rintro (_ | _ | _) <;> simp)))
                (c.op.isLimitMapConeEquiv (yoneda.obj X))))))

end Pushout

end

end CategoryTheory.Limits
