/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monad.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Adjunctions related to the over category

In a category with pullbacks, for any morphism `f : X ⟶ Y`, the functor
`Over.map f : Over X ⥤ Over Y` has a right adjoint `Over.pullback f`.

In a category with binary products, for any object `X` the functor
`Over.forget X : Over X ⥤ C` has a right adjoint `Over.star X`.

## Main declarations

- `Over.pullback f : Over Y ⥤ Over X` is the functor induced by a morphism `f : X ⟶ Y`.
- `Over.mapPullbackAdj` is the adjunction `Over.map f ⊣ Over.pullback f`.
- `star : C ⥤ Over X` is the functor induced by an object `X`.
- `forgetAdjStar` is the adjunction  `forget X ⊣ star X`.

## TODO
Show `star X` itself has a right adjoint provided `C` is Cartesian closed and has pullbacks.
-/

noncomputable section

universe v v₂ u u₂

namespace CategoryTheory

open Category Limits Comonad

variable {C : Type u} [Category.{v} C] (X Y : C)
variable {D : Type u₂} [Category.{v₂} D]


namespace Over

open Limits

attribute [local instance] hasPullback_of_right_iso

/-- In a category with pullbacks, a morphism `f : X ⟶ Y` induces a functor `Over Y ⥤ Over X`,
by pulling back a morphism along `f`. -/
@[simps! +simpRhs obj_left obj_hom map_left]
def pullback {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    Over Y ⥤ Over X where
  obj g := Over.mk (pullback.snd g.hom f)
  map := fun g {h} {k} =>
    Over.homMk (pullback.lift (pullback.fst _ _ ≫ k.left) (pullback.snd _ _)
      (by simp [pullback.condition]))

/-- `Over.map f` is left adjoint to `Over.pullback f`. -/
@[simps! unit_app counit_app]
def mapPullbackAdj {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    Over.map f ⊣ pullback f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun x y =>
        { toFun := fun u =>
            Over.homMk (pullback.lift u.left x.hom <| by simp)
          invFun := fun v => Over.homMk (v.left ≫ pullback.fst _ _) <| by
            simp [← Over.w v, pullback.condition]
          left_inv := by cat_disch
          right_inv := fun v => by
            ext
            dsimp
            ext
            · simp
            · simpa using (Over.w v).symm } }

/-- The pullback along an epi that's preserved under pullbacks is faithful.

This "preserved under pullbacks" condition is automatically satisfied in abelian categories:
```
example [Abelian C] [Epi f] : (pullback f).Faithful := inferInstance
```
-/
instance faithful_pullback {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    [∀ Z (g : Z ⟶ Y), Epi (pullback.fst g f)] : (pullback f).Faithful := by
  have (Z : Over Y) : Epi ((mapPullbackAdj f).counit.app Z) := by
    simp only [Functor.comp_obj, Functor.id_obj, mapPullbackAdj_counit_app]; infer_instance
  exact (mapPullbackAdj f).faithful_R_of_epi_counit_app

/-- pullback (𝟙 X) : Over X ⥤ Over X is the identity functor. -/
def pullbackId {X : C} : pullback (𝟙 X) ≅ 𝟭 _ :=
  conjugateIsoEquiv (mapPullbackAdj (𝟙 _)) (Adjunction.id (C := Over _)) (Over.mapId _).symm

/-- pullback commutes with composition (up to natural isomorphism). -/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasPullbacksAlong f] [HasPullbacksAlong g] :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  conjugateIsoEquiv (mapPullbackAdj _) ((mapPullbackAdj _).comp (mapPullbackAdj _))
    (Over.mapComp _ _).symm

instance pullbackIsRightAdjoint {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    (pullback f).IsRightAdjoint :=
  ⟨_, ⟨mapPullbackAdj f⟩⟩

open pullback in
/-- If `F` is a left adjoint and its source category has pullbacks, then so is
`post F : Over Y ⥤ Over (G Y)`.

If the right adjoint of `F` is `G`, then the right adjoint of `post F` is given by
`(Y ⟶ F X) ↦ (G Y ⟶ X ×_{G F X} G Y ⟶ X)`. -/
@[simps!]
def postAdjunctionLeft [HasPullbacks C] {X : C} {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) :
    post F ⊣ post G ⋙ pullback (a.unit.app X) :=
  ((mapPullbackAdj (a.unit.app X)).comp (postAdjunctionRight a)).ofNatIsoLeft <|
    NatIso.ofComponents fun Y ↦ isoMk (.refl _)

instance isLeftAdjoint_post [HasPullbacks C] {F : C ⥤ D} [F.IsLeftAdjoint] :
    (post (X := X) F).IsLeftAdjoint :=
  let ⟨G, ⟨a⟩⟩ := ‹F.IsLeftAdjoint›; ⟨_, ⟨postAdjunctionLeft a⟩⟩

open Limits

/-- The category over any object `X` factors through the category over the terminal object `T`. -/
@[simps!]
noncomputable def forgetMapTerminal {T : C} (hT : IsTerminal T) :
    forget X ≅ map (hT.from X) ⋙ (equivalenceOfIsTerminal hT).functor :=
  NatIso.ofComponents fun X ↦ .refl _

section HasBinaryProducts
variable [HasBinaryProducts C]

/--
The functor from `C` to `Over X` which sends `Y : C` to `π₁ : X ⨯ Y ⟶ X`, sometimes denoted `X*`.
-/
@[simps! obj_left obj_hom map_left]
def star : C ⥤ Over X := cofree _ ⋙ coalgebraToOver X

/-- The functor `Over.forget X : Over X ⥤ C` has a right adjoint given by `star X`.

Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
def forgetAdjStar : forget X ⊣ star X := (coalgebraEquivOver X).symm.toAdjunction.comp (adj _)

instance : (star X).IsRightAdjoint := ⟨_, ⟨forgetAdjStar X⟩⟩

/-- Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`. -/
instance : (forget X).IsLeftAdjoint := ⟨_, ⟨forgetAdjStar X⟩⟩

end HasBinaryProducts
end Over

namespace Under

attribute [local instance] hasPushout_of_right_iso

/-- When `C` has pushouts, a morphism `f : X ⟶ Y` induces a functor `Under X ⥤ Under Y`,
by pushing a morphism forward along `f`. -/
@[simps]
def pushout {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] :
    Under X ⥤ Under Y where
  obj x := Under.mk (pushout.inr x.hom f)
  map := fun x {x'} {u} =>
    Under.homMk (pushout.desc (u.right ≫ pushout.inl _ _) (pushout.inr _ _)
      (by simp [← pushout.condition]))

/-- `Under.pushout f` is left adjoint to `Under.map f`. -/
@[simps! unit_app counit_app]
def mapPushoutAdj {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] :
    pushout f ⊣ map f :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun x y => {
      toFun := fun u => Under.homMk (pushout.inl _ _ ≫ u.right) <| by
        simp only [map_obj_hom]
        rw [← Under.w u]
        simp only [Functor.const_obj_obj, map_obj_right, Functor.id_obj, pushout_obj, mk_right,
          mk_hom]
        rw [← assoc, ← assoc, pushout.condition]
      invFun := fun v => Under.homMk (pushout.desc v.right y.hom <| by simp)
      left_inv := fun u => by
        ext
        dsimp
        ext
        · simp
        · simpa using (Under.w u).symm
      right_inv := by cat_disch
    }
  }

/-- The pushout along a mono that's preserved under pushouts is faithful.

This "preserved under pushouts" condition is automatically satisfied in abelian categories:
```
example [Abelian C] [Mono f] : (pushout f).Faithful := inferInstance
```
-/
instance faithful_pushout {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f]
    [∀ Z (g : X ⟶ Z), Mono (pushout.inl g f)] : (pushout f).Faithful := by
  have (Z : Under X) : Mono ((mapPushoutAdj f).unit.app Z) := by simp; infer_instance
  exact (mapPushoutAdj f).faithful_L_of_mono_unit_app

/-- pushout (𝟙 X) : Under X ⥤ Under X is the identity functor. -/
def pushoutId {X : C} : pushout (𝟙 X) ≅ 𝟭 _ :=
  (conjugateIsoEquiv (Adjunction.id (C := Under _)) (mapPushoutAdj (𝟙 _)) ).symm
    (Under.mapId X).symm

/-- pushout commutes with composition (up to natural isomorphism). -/
def pushoutComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasPushoutsAlong f] [HasPushoutsAlong g] :
    pushout (f ≫ g) ≅ pushout f ⋙ pushout g :=
  (conjugateIsoEquiv ((mapPushoutAdj _).comp (mapPushoutAdj _)) (mapPushoutAdj _) ).symm
    (mapComp f g).symm

@[deprecated (since := "2025-04-15")]
noncomputable alias pullbackComp := pushoutComp

instance pushoutIsLeftAdjoint {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] :
    (pushout f).IsLeftAdjoint :=
  ⟨_, ⟨mapPushoutAdj f⟩⟩

open pushout in
/-- If `G` is a right adjoint and its source category has pushouts, then so is
`post G : Under Y ⥤ Under (G Y)`.

If the left adjoint of `G` is `F`, then the left adjoint of `post G` is given by
`(G Y ⟶ X) ↦ (Y ⟶ Y ⨿_{F G Y} F X ⟶ F X)`. -/
@[simps!]
def postAdjunctionRight [HasPushouts D] {Y : D} {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) :
    post F ⋙ pushout (a.counit.app Y) ⊣ post G :=
  ((postAdjunctionLeft a).comp (mapPushoutAdj (a.counit.app Y))).ofNatIsoRight <|
    NatIso.ofComponents fun Y ↦ isoMk (.refl _)

open pushout in
instance isRightAdjoint_post [HasPushouts D] {Y : D} {G : D ⥤ C} [G.IsRightAdjoint] :
    (post (X := Y) G).IsRightAdjoint :=
  let ⟨F, ⟨a⟩⟩ := ‹G.IsRightAdjoint›; ⟨_, ⟨postAdjunctionRight a⟩⟩

/-- The category under any object `X` factors through the category under the initial object `I`. -/
@[simps!]
noncomputable def forgetMapInitial {I : C} (hI : IsInitial I) :
    forget X ≅ map (hI.to X) ⋙ (equivalenceOfIsInitial hI).functor :=
  NatIso.ofComponents fun X ↦ .refl _

section HasBinaryCoproducts
variable [HasBinaryCoproducts C]

/-- The functor from `C` to `Under X` which sends `Y : C` to `in₁ : X ⟶ X ⨿ Y`. -/
@[simps! obj_left obj_hom map_left]
def costar : C ⥤ Under X := Monad.free _ ⋙ algebraToUnder X

/-- The functor `Under.forget X : Under X ⥤ C` has a left adjoint given by `costar X`.

Note that the binary coproducts assumption is necessary: the existence of a left adjoint to
`Under.forget X` is equivalent to the existence of each binary coproduct `X ⨿ -`. -/
def costarAdjForget : costar X ⊣ forget X := (Monad.adj _).comp (algebraEquivUnder X).toAdjunction

instance : (costar X).IsLeftAdjoint := ⟨_, ⟨costarAdjForget X⟩⟩

/-- Note that the binary coproducts assumption is necessary: the existence of a left adjoint to
`Under.forget X` is equivalent to the existence of each binary coproduct `X ⨿ -`. -/
instance : (forget X).IsRightAdjoint := ⟨_, ⟨costarAdjForget X⟩⟩

end HasBinaryCoproducts
end Under

end CategoryTheory
