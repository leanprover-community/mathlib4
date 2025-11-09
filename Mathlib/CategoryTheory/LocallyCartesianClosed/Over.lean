/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullback

/-!
# Cartesian monoidal structure on slices induced by chosen pullbacks

## Main declarations

- `cartesianMonoidalCategoryOver` provides a cartesian monoidal structure on the slice categories
  `Over X` for all objects `X : C`, induced by chosen pullbacks in the base category `C`.
  This is the computable analogue of the noncomputable instance
  `CategoryTheory.Over.cartesianMonoidalCategory`.

- For a cartesian monoidal category `C`, and for any object `X` of `C`,
  `toOver X` is a functor from `C` to `Over X` which maps an object `A : C` to the projection
  `A ⊗ X ⟶ X` in `Over X`. This is the computable analogue of the functor `Over.star`.

## Main results

- `cartesianMonoidalCategoryOver` proves that the slices of a category with chosen pullbacks are
  cartesian monoidal.

- `toOverPullbackIsoToOver` shows that in a category with chosen pullbacks, for any morphism
  `f : Y ⟶ X`, the functors `toOver X ⋙ pullback f` and `toOver Y` are naturally isomorphic.

- `toOverIteratedSliceForwardIsoPullback` shows that in a category with chosen pullbacks the functor
  `pullback f : Over X ⥤ Over Y` is naturally isomorphic to
  `toOver (Over.mk f) : Over X ⥤ Over (Over.mk f)` post-composed with the iterated slice equivalence
  `Over (Over.mk f) ⥤ Over Y`. Note that the functor `toOver (Over.mk f)` exists by the result
  `cartesianMonoidalCategoryOver`.

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits CartesianMonoidalCategory MonoidalCategory

namespace ChosenPullback

variable {C : Type u₁} [Category.{v₁} C]

section

variable {X : C} (Y Z : Over X)

/-- The canonical pullback cone constructed from `ChosenPullback.isPullback.`
Note: The source of noncomputability is the non-constructive implementation of `IsPullback.isLimit`.
Otherwise, `ChosenPullback.isPullback` is constructive.
-/
def isLimitPullbackCone [ChosenPullback Z.hom] :
    IsLimit (isPullback Y.hom Z.hom |>.cone) :=
  PullbackCone.IsLimit.mk condition (fun s ↦ lift s.fst s.snd s.condition)
    (by cat_disch) (by cat_disch) (by cat_disch)

/-- The binary fan provided by `fst'` and `snd'`. -/
def binaryFan [ChosenPullback Z.hom] : BinaryFan Y Z :=
  BinaryFan.mk (P:= Over.mk (Y := pullbackObj Y.hom Z.hom) (snd Y.hom Z.hom ≫ Z.hom))
    (fst' Y.hom Z.hom) (snd' Y.hom Z.hom)

@[simp]
theorem binaryFan_pt [ChosenPullback Z.hom] :
    (binaryFan Y Z).pt = Over.mk (Y:= pullbackObj Y.hom Z.hom) (snd Y.hom Z.hom ≫ Z.hom) := by
  rfl

@[simp]
theorem binaryFan_pt_hom [ChosenPullback Z.hom] :
    (binaryFan Y Z).pt.hom = snd Y.hom Z.hom ≫ Z.hom := by
  rfl

/-- The binary fan provided by `fst'` and `snd'` is a binary product in `Over X`. -/
def binaryFanIsBinaryProduct [ChosenPullback Z.hom] :
    IsLimit (binaryFan Y Z) :=
  BinaryFan.IsLimit.mk (binaryFan Y Z)
    (fun u v => Over.homMk (lift (u.left) (v.left) (by rw [Over.w u, Over.w v])) (by simp))
    (fun a b => by simp [binaryFan]; aesop)
    (fun a b => by simp [binaryFan]; aesop)
    (fun a b m h₁ h₂ => by
      apply Over.OverMorphism.ext
      simp only [Over.homMk_left]
      apply hom_ext (f:= Y.hom) (g:= Z.hom) <;> aesop)

end

/-- A computable instance of `CartesianMonoidalCategory` for `Over X` when `C` has
chosen pullbacks. Contrast this with the noncomputable instance provided by
`CategoryTheory.Over.cartesianMonoidalCategory`.
-/
instance cartesianMonoidalCategoryOver [ChosenPullbacks C] (X : C) :
    CartesianMonoidalCategory (Over X) :=
  ofChosenFiniteProducts (C:= Over X)
    ⟨asEmptyCone (Over.mk (𝟙 X)) , IsTerminal.ofUniqueHom (fun Y ↦ Over.homMk Y.hom)
      fun Y m ↦ Over.OverMorphism.ext (by simpa using m.w)⟩
    (fun Y Z ↦ ⟨ _ , binaryFanIsBinaryProduct Y Z⟩)

end ChosenPullback

section ToOver

open ChosenPullback

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

/-- The functor which maps an object `A` in `C` to the projection `A ⊗ X ⟶ X` in `Over X`.
This is the computable analogue of the functor `Over.star`. -/
@[simps! obj_left obj_hom map_left]
def toOver (X : C) : C ⥤ Over X where
  obj A := Over.mk <| CartesianMonoidalCategory.snd A X
  map f := Over.homMk (f ▷ X)

@[simp]
lemma toOver_map {X : C} {A A' : C} (f : A ⟶ A') :
    (toOver X).map f = Over.homMk (f ▷ X) := by
  simp only [toOver]

variable (C)

/-- The functor from `C` to `Over (𝟙_ C)` which sends `X : C` to `Over.mk <| toUnit X`. -/
@[simps! obj_left obj_hom map_left]
def toOverUnit : C ⥤ Over (𝟙_ C) where
  obj X := Over.mk <| toUnit X
  map f := Over.homMk f

/-- The slice category over the terminal unit object is equivalent to the original category. -/
def equivToOverUnit : Over (𝟙_ C) ≌ C :=
  CategoryTheory.Equivalence.mk (Over.forget _) (toOverUnit C)
    (NatIso.ofComponents fun X => Over.isoMk (Iso.refl _))
    (NatIso.ofComponents fun X => Iso.refl _)

attribute [local instance] ChosenPullback.cartesianMonoidalCategoryToUnit

variable {C}

/-- The isomorphism of functors `toOverUnit C ⋙ ChosenPullback.pullback (toUnit X)` and
`toOver X`. -/
def toOverUnitPullback (X : C) :
    toOverUnit C ⋙ pullback (toUnit X) ≅ toOver X :=
  NatIso.ofComponents fun X => Iso.refl _

/-- The functor `toOver X` is the right adjoint to the functor `Over.forget X`. -/
@[simps! unit_app counit_app]
def forgetAdjToOver (X : C) : Over.forget X ⊣ toOver X where
  unit.app Z := Over.homMk (lift (𝟙 Z.left) (Z.hom))
  counit.app Z := fst Z X

theorem forgetAdjToOver.homEquiv_symm {X : C} (Z : Over X) (A : C) (f : Z ⟶ (toOver X).obj A) :
     ((forgetAdjToOver X).homEquiv Z A).symm f = f.left ≫ (fst _ _) := by
   rw [Adjunction.homEquiv_counit, forgetAdjToOver_counit_app]
   simp

/-- The isomorphism of functors `toOver (𝟙_ C)` and `toOverUnit C`. -/
def toOverIsoToOverUnit : toOver (𝟙_ C) ≅ toOverUnit C  :=
  (forgetAdjToOver (𝟙_ C)).rightAdjointUniq (equivToOverUnit C |>.toAdjunction)

/-- A natural isomorphism between the functors `toOver Y` and `toOver X ⋙ pullback f`
for any morphism `f : X ⟶ Y`. -/
def toOverPullbackIsoToOver {X Y : C} (f : Y ⟶ X) [ChosenPullback f] :
    toOver X ⋙ pullback f ≅ toOver Y :=
  conjugateIsoEquiv ((mapPullbackAdj f).comp (forgetAdjToOver X))
    (forgetAdjToOver Y) (Over.mapForget f)

/-- The functor `pullback f : Over X ⥤ Over Y` is naturally isomorphic to
`toOver : Over X ⥤ Over (Over.mk f)` post-composed with the
iterated slice equivlanece `Over (Over.mk f) ⥤ Over Y`. -/
def toOverIteratedSliceForwardIsoPullback [ChosenPullbacks C] {X Y : C} (f : Y ⟶ X) :
    toOver (Over.mk f) ⋙ (Over.mk f).iteratedSliceForward ≅ pullback f :=
  conjugateIsoEquiv ((Over.mk f).iteratedSliceEquiv.symm.toAdjunction.comp (forgetAdjToOver _))
  (mapPullbackAdj f) (eqToIso (Over.iteratedSliceBackward_forget (Over.mk f)))

section

variable {X : C} {Y : C}

example : ChosenPullback.pullbackObj (toUnit X) (toUnit Y) = X ⊗ Y := by rfl

example : ChosenPullback.snd (toUnit X) (toUnit Y) = CartesianMonoidalCategory.snd X Y := rfl

example : (toOver Y).obj X = Over.mk (ChosenPullback.snd (toUnit X) (toUnit Y)) := by rfl

example : ((toOver Y).obj X).hom = CartesianMonoidalCategory.snd X Y := by rfl

end

end ToOver

end CategoryTheory
