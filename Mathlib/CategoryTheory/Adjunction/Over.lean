/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang, Sina Hazratpour
-/

import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monad.Products
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

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
  obj g := Over.mk (pullback.snd g.hom f)
  map := fun g {h} {k} =>
    Over.homMk (pullback.lift (pullback.fst _ _ ≫ k.left) (pullback.snd _ _)
      (by simp [pullback.condition]))

@[deprecated (since := "2024-05-15")]
noncomputable alias Limits.baseChange := Over.pullback

@[deprecated (since := "2024-07-08")]
noncomputable alias baseChange := pullback

/-- `Over.map f` is left adjoint to `Over.pullback f`. -/
@[simps! unit_app counit_app]
def mapPullbackAdj {X Y : C} (f : X ⟶ Y) : Over.map f ⊣ pullback f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun x y =>
        { toFun := fun u =>
            Over.homMk (pullback.lift u.left x.hom <| by simp)
          invFun := fun v => Over.homMk (v.left ≫ pullback.fst _ _) <| by
            simp [← Over.w v, pullback.condition]
          left_inv := by aesop_cat
          right_inv := fun v => by
            ext
            dsimp
            ext
            · simp
            · simpa using (Over.w v).symm } }

@[deprecated (since := "2024-07-08")]
noncomputable alias mapAdjunction := mapPullbackAdj

/-- pullback (𝟙 X) : Over X ⥤ Over X is the identity functor. -/
def pullbackId {X : C} : pullback (𝟙 X) ≅ 𝟭 _ :=
  conjugateIsoEquiv (mapPullbackAdj (𝟙 _)) (Adjunction.id (C := Over _)) (Over.mapId _).symm

/-- pullback commutes with composition (up to natural isomorphism). -/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  conjugateIsoEquiv (mapPullbackAdj _) ((mapPullbackAdj _).comp (mapPullbackAdj _))
    (Over.mapComp _ _).symm

instance pullbackIsRightAdjoint {X Y : C} (f : X ⟶ Y) : (pullback f).IsRightAdjoint  :=
  ⟨_, ⟨mapPullbackAdj f⟩⟩

namespace mapPullbackAdj

variable {X}

set_option quotPrecheck false in
scoped notation " Σ_ " => fun (Y : Over X) => (Over.map (Y.hom)).obj

set_option quotPrecheck false in
scoped notation " Δ_ " => fun (Y : Over X) => (Over.pullback (Y.hom)).obj

/-- Push-pull of `Z` of along `Y` is isomorphic to the push-pull of `Y` along `Z` as objects in
`Over X`. -/
@[simps!]
def swapIso (Y Z : Over X) :
  Σ_ Y (Δ_ Y Z) ≅ Σ_ Z (Δ_ Z Y) := by
  apply Over.isoMk _ _
  · exact pullbackSymmetry _ _
  · simp [pullback.condition]

lemma SwapIso_hom_pullbackSymmetry {Y Z : Over X} :
    (Σ_ Y (Δ_ Y Z)).hom = (pullbackSymmetry _ _).hom ≫ (Σ_ Z (Δ_ Z Y)).hom  := by
  simp [← pullback.condition]

set_option quotPrecheck false in
scoped notation " μ_ " => fun Y Z => (mapPullbackAdj Y.hom).counit.app Z

set_option quotPrecheck false in
scoped notation " π_ " => fun Y Z => (swapIso Y Z).hom ≫ (mapPullbackAdj Z.hom).counit.app Y

lemma counit_app_pullback_fst {Y Z : Over X} :
    μ_ Y Z = Over.homMk (pullback.fst Z.hom Y.hom) (by simp [pullback.condition]) := by
  simp

lemma counit_app_pullback_snd {Y Z : Over X} :
    π_ Y Z = Over.homMk (pullback.snd Z.hom Y.hom) (by simp)  := by
  aesop

end mapPullbackAdj

section tensorLeft

open mapPullbackAdj MonoidalCategory Functor

variable {X}

/-- The binary fan provided by `μ_` and `π_` is a binary product in `Over X`. -/
def isBinaryProduct (Y Z : Over X) :
    IsLimit <| BinaryFan.mk (P:= Σ_ Y (Δ_ Y Z)) (π_ Y Z) (μ_ Y Z) := by
  rw [counit_app_pullback_fst, counit_app_pullback_snd]
  refine IsLimit.mk (?lift) ?fac ?uniq
  · intro s
    fapply Over.homMk
    · refine pullback.lift (s.π.app ⟨.right⟩).left (s.π.app ⟨ .left ⟩).left (by aesop)

  -- fapply IsLimit.mk
  -- · intro s
  --   fapply Over.homMk
  --   · refine pullback.lift (s.π.app ⟨.right⟩).left (s.π.app ⟨ .left ⟩).left (by aesop) ?_
  --   · simp
  -- · rintro s ⟨⟨l⟩|⟨r⟩⟩ <;> apply Over.OverMorphism.ext <;> simp
  -- · intro s m h
  --   apply Over.OverMorphism.ext
  --   apply pullback.hom_ext <;> simp
  --   · exact congr_arg CommaMorphism.left (h ⟨ .right⟩)
  --   · exact congr_arg CommaMorphism.left (h ⟨ .left ⟩)

attribute [local instance] monoidalOfHasFiniteProducts
attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

/-- The object `(Σ_ Y) (Δ_ Y Z)` is isomorphic to the binary product `Y × Z`
in `Over I`. -/
@[simps! (config := { simpRhs := true})]
def mapPulbackObjIsoProd (Y Z : Over X) :
    (Σ_ Y) (Δ_ Y Z) ≅ Limits.prod Y Z := by
  apply IsLimit.conePointUniqueUpToIso (isBinaryProduct Y Z) (prodIsProd Y Z)

/-- Given a morphism `f : X' ⟶ X` and an object `Y` over `X`, the `(map f).obj ((pullback f).obj Y)`
is isomorphic to the binary product of `(Over.mk f)` and `Y`. -/
def mapPulbackObjIsoProdMk {X' : C} (f : X' ⟶ X) (Y : Over X) :
    (map f).obj ((pullback f).obj Y) ≅ Limits.prod (Over.mk f) Y :=
  mapPulbackObjIsoProd (Over.mk f) _

@[simp]
lemma mapPulbackObjIsoProd_hom_comp_fst (Y Z : Over X) :
    (mapPulbackObjIsoProd Y Z).hom ≫ prod.fst = (π_ Y Z) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isBinaryProduct Y Z) (Limits.prodIsProd Y Z) ⟨.left⟩

@[simp]
lemma mapPulbackObjIsoProd_hom_comp_snd {Y Z : Over X} :
    (mapPulbackObjIsoProd Y Z).hom ≫ prod.snd = (μ_ Y Z) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isBinaryProduct Y Z) (Limits.prodIsProd Y Z) ⟨.right⟩

/-- The pull-push composition `(Over.pullback Y.hom) ⋙ (Over.map Y.hom)` is naturally isomorphic
to the left tensor product functor `Y × _` in `Over X`-/
def natIsoTensorLeft [HasFiniteWidePullbacks C] (Y : Over X) :
    (pullback Y.hom) ⋙ (map Y.hom) ≅ tensorLeft Y := by
  fapply NatIso.ofComponents
  · intro Z
    simp only [const_obj_obj, id_obj, comp_obj, tensorLeft_obj, tensorObj, pullback]
    exact mapPulbackObjIsoProd Y Z
  · intro Z Z' f
    simp
    ext1 <;> simp_rw [assoc]
    · simp_rw [prod.map_fst, comp_id]
      iterate rw [mapPulbackObjIsoProd_hom_comp_fst]
      ext
      simp
    · simp_rw [prod.map_snd]
      iterate rw [mapPulbackObjIsoProd_hom_comp_snd, ← assoc, mapPulbackObjIsoProd_hom_comp_snd]
      ext
      simp

/-- The pull-push composition `(pullback f) ⋙ (map f)` is is naturally isomorphic to the left
tensor product functor `Over.mk f ⨯ _` in `Over X`. -/
def natIsoTensorLeftOverMk [HasFiniteWidePullbacks C] {X' : C} (f : X' ⟶ X) :
    (pullback f) ⋙ (map f) ≅ tensorLeft (Over.mk f) := natIsoTensorLeft (Over.mk f)

end tensorLeft

/--
The functor from `C` to `Over X` which sends `Y : C` to `π₁ : X ⨯ Y ⟶ X`, sometimes denoted `X*`.
-/
@[simps! obj_left obj_hom map_left]
def star [HasBinaryProducts C] : C ⥤ Over X :=
  cofree _ ⋙ coalgebraToOver X

/-- The functor `Over.forget X : Over X ⥤ C` has a right adjoint given by `star X`.

Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
def forgetAdjStar [HasBinaryProducts C] : forget X ⊣ star X :=
  (coalgebraEquivOver X).symm.toAdjunction.comp (adj _)

/-- Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
instance [HasBinaryProducts C] : (forget X).IsLeftAdjoint  :=
  ⟨_, ⟨forgetAdjStar X⟩⟩

end Over

@[deprecated (since := "2024-05-18")] noncomputable alias star := Over.star

@[deprecated (since := "2024-05-18")] noncomputable alias forgetAdjStar := Over.forgetAdjStar

namespace forgetAdjStar

variable [HasBinaryProducts C]

@[simp]
theorem unit_app_left {I : C} (X : Over I):
    ((Over.forgetAdjStar I).unit.app X).left = prod.lift X.hom (𝟙 X.left) := by
  simp [Over.forgetAdjStar, Adjunction.comp, Equivalence.symm]

@[simp]
theorem unit_app {I : C} (X : Over I): (Over.forgetAdjStar I).unit.app X =
    Over.homMk (prod.lift X.hom (𝟙 X.left)) := by
  ext
  simp

@[simp]
theorem counit_app {I : C} (X : C) :
    ((Over.forgetAdjStar I).counit.app X) = prod.snd := by
  simp [Over.forgetAdjStar, Adjunction.comp, Equivalence.symm]

@[simp]
theorem homEquiv {I : C} (X : Over I) (A : C) (f : X.left ⟶ A) :
    (Over.forgetAdjStar I).homEquiv X A f =
    Over.homMk (prod.lift X.hom f) := by
  rw [Adjunction.homEquiv_unit, unit_app]
  ext
  simp

@[simp]
theorem homEquiv_symm {I : C} (X : Over I) (A : C) (f : X ⟶ (Over.star I).obj A) :
     ((Over.forgetAdjStar I).homEquiv X A).symm f = f.left ≫ prod.snd := by
   rw [Adjunction.homEquiv_counit, counit_app]
   simp

end forgetAdjStar


namespace Under

variable [HasPushouts C]

/-- When `C` has pushouts, a morphism `f : X ⟶ Y` induces a functor `Under X ⥤ Under Y`,
by pushing a morphism forward along `f`. -/
@[simps]
def pushout {X Y : C} (f : X ⟶ Y) : Under X ⥤ Under Y where
  obj x := Under.mk (pushout.inr x.hom f)
  map := fun x {x'} {u} =>
    Under.homMk (pushout.desc (u.right ≫ pushout.inl _ _) (pushout.inr _ _)
      (by simp [← pushout.condition]))

/-- `Under.pushout f` is left adjoint to `Under.map f`. -/
@[simps! unit_app counit_app]
def mapPushoutAdj {X Y : C} (f : X ⟶ Y) : pushout f ⊣ map f :=
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
      right_inv := by aesop_cat
    }
  }

/-- pushout (𝟙 X) : Under X ⥤ Under X is the identity functor. -/
def pushoutId {X : C} : pushout (𝟙 X) ≅ 𝟭 _ :=
  (conjugateIsoEquiv (Adjunction.id (C := Under _)) (mapPushoutAdj (𝟙 _)) ).symm
    (Under.mapId X).symm

/-- pushout commutes with composition (up to natural isomorphism). -/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : pushout (f ≫ g) ≅ pushout f ⋙ pushout g :=
  (conjugateIsoEquiv ((mapPushoutAdj _).comp (mapPushoutAdj _)) (mapPushoutAdj _) ).symm
    (mapComp f g).symm

instance pushoutIsLeftAdjoint {X Y : C} (f : X ⟶ Y) : (pushout f).IsLeftAdjoint  :=
  ⟨_, ⟨mapPushoutAdj f⟩⟩

end Under

end CategoryTheory
