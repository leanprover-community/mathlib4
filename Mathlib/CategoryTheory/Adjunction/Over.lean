/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monad.Products
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Adjunction.Unique

#align_import category_theory.adjunction.over from "leanprover-community/mathlib"@"cea27692b3fdeb328a2ddba6aabf181754543184"

/-!
# Adjunctions related to the over category

In a category with pullbacks, for any morphism `f : X ⟶ Y`, the functor `Over.map f : Over X ⥤ Over Y` has a right adjoint `Over.pullback f`.

In a category with binary products, for any object `X` the functor `Over.forget X : Over X ⥤ C` has a right adjoint `Over.star X`.

## Main declarations

- `Over.pullback f : Over Y ⥤ Over X` is the functor induced by a morphism `f : X ⟶ Y`.
- `Over.mapPullbackAdj` is the adjunction `Over.map f ⊣ Over.pullback f`.
- `star : C ⥤ Over X` is the functor induced by an object `X`.
- `forgetAdjStar` is the adjunction  `forget X ⊣ star X`.

## TODO
Show `star X` itself has a right adjoint provided `C` is cartesian closed and has pullbacks.
-/

noncomputable section

universe v u

namespace CategoryTheory

open Category Limits Comonad

variable {C : Type u} [Category.{v} C] (X : C)


namespace Over

open Limits

variable [HasPullbacks C]

/-- In a category with pullbacks, a morphism `f : X ⟶ Y` induces a functor `Over Y ⥤ Over X`,
by pulling back a morphism along `f`. -/
@[simps! (config := { simpRhs := true}) obj_left obj_hom map_left]
def pullback {X Y : C} (f : X ⟶ Y) : Over Y ⥤ Over X where
  obj g := Over.mk (pullback.snd : CategoryTheory.Limits.pullback g.hom f ⟶ X)
  map := fun g {h} {k} =>
    Over.homMk (pullback.lift (pullback.fst ≫ k.left) pullback.snd (by simp [pullback.condition]))
#align category_theory.over.pullback CategoryTheory.Over.pullback
#align category_theory.limits.base_change CategoryTheory.Over.pullback

@[deprecated (since := "2024-05-15")]
noncomputable alias Limits.baseChange := Over.pullback

@[deprecated (since := "2024-07-08")]
noncomputable alias baseChange := pullback

/-- `Over.map f` is left adjoint to `Over.pullback f`. -/
@[simps! unit_app counit_app]
def mapPullbackAdj {A B : C} (f : A ⟶ B) : Over.map f ⊣ pullback f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun g h =>
        { toFun := fun X =>
            Over.homMk (pullback.lift X.left g.hom <| by simp)
          invFun := fun Y => Over.homMk (Y.left ≫ pullback.fst) <| by
            simp [← Over.w Y, pullback.condition]
          left_inv := by aesop_cat
          right_inv := fun Y => by
            ext
            dsimp
            ext
            · simp
            · simpa using Over.w Y |>.symm } }
#align category_theory.over.map_pullback_adj CategoryTheory.Over.mapPullbackAdj

@[deprecated (since := "2024-07-08")]
noncomputable alias mapAdjunction := mapPullbackAdj

/-- pullback (𝟙 A) : Over A ⥤ Over A is the identity functor. -/
def pullbackId {A : C} : pullback (𝟙 A) ≅ 𝟭 _ :=
  Adjunction.rightAdjointUniq (mapPullbackAdj _) (Adjunction.id.ofNatIsoLeft (Over.mapId A).symm)
#align category_theory.over.pullback_id CategoryTheory.Over.pullbackId

/-- pullback commutes with composition (up to natural isomorphism). -/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  Adjunction.rightAdjointUniq (mapPullbackAdj _)
    (((mapPullbackAdj _).comp (mapPullbackAdj _)).ofNatIsoLeft (Over.mapComp _ _).symm)
#align category_theory.over.pullback_comp CategoryTheory.Over.pullbackComp

instance pullbackIsRightAdjoint {A B : C} (f : A ⟶ B) : (pullback f).IsRightAdjoint  :=
  ⟨_, ⟨mapPullbackAdj f⟩⟩
#align category_theory.over.pullback_is_right_adjoint CategoryTheory.Over.pullbackIsRightAdjoint

/--
The functor from `C` to `Over X` which sends `Y : C` to `π₁ : X ⨯ Y ⟶ X`, sometimes denoted `X*`.
-/
@[simps! obj_left obj_hom map_left]
def star [HasBinaryProducts C] : C ⥤ Over X :=
  cofree _ ⋙ coalgebraToOver X
#align category_theory.star CategoryTheory.Over.star

/-- The functor `Over.forget X : Over X ⥤ C` has a right adjoint given by `star X`.

Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
def forgetAdjStar [HasBinaryProducts C] : forget X ⊣ star X :=
  (coalgebraEquivOver X).symm.toAdjunction.comp (adj _)
#align category_theory.forget_adj_star CategoryTheory.Over.forgetAdjStar

/-- Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
instance [HasBinaryProducts C] : (forget X).IsLeftAdjoint  :=
  ⟨_, ⟨forgetAdjStar X⟩⟩

end Over

@[deprecated (since := "2024-05-18")] noncomputable alias star := Over.star

@[deprecated (since := "2024-05-18")] noncomputable alias forgetAdjStar := Over.forgetAdjStar

namespace Under

variable [HasPushouts C]

/-- When `C` has pushouts, a morphism `f : X ⟶ Y` induces a functor `Under X ⥤ Under Y`,
by pushing a morphism forward along `f`. -/
@[simps]
def pushout {X Y : C} (f : X ⟶ Y) : Under X ⥤ Under Y where
  obj g := Under.mk (pushout.inr : Y ⟶ CategoryTheory.Limits.pushout g.hom f)
  map := fun g {h} {k} =>
    Under.homMk (pushout.desc (k.right ≫ pushout.inl) pushout.inr (by simp [← pushout.condition]))
#align category_theory.under.pushout CategoryTheory.Under.pushout

end Under

end CategoryTheory
