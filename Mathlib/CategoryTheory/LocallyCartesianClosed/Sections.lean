/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullback
import Mathlib.CategoryTheory.Closed.Cartesian

/-!
# The section functor as a right adjoint to the star functor

We show that if `C` is cartesian closed then `star I : C ⥤ Over I`
has a right adjoint `sectionsFunctor` whose object part is the object of sections
of `X` over `I`.

-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianClosed CartesianMonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory


section prelim

open Over CartesianMonoidalCategory ChosenPullback

/-- The functor which maps an object `X` in `C` to the projection `I ⊗ X ⟶ I` in `Over I`.
This is the computable analogue of the functor `Over.star`. -/
@[simps! obj_left obj_hom map_left]
def toOver (I : C) : C ⥤ Over I where
  obj X := Over.mk (CartesianMonoidalCategory.snd X I)
  map {X Y} f := Over.homMk (f ▷ I)

@[reassoc (attr := simp)]
lemma toOver_map [HasBinaryProducts C] {I : C} {Y Z : C} (f : Y ⟶ Z) :
    (toOver I).map f = Over.homMk (f ▷ I) := by
  simp only [toOver]

attribute [local instance] Over.ChosenPullback.cartesianMonoidalCategoryToTerminal

variable {I : C} (X : C)

#synth ChosenPullback (toUnit I : I ⟶ 𝟙_ C)

theorem foo : pullbackObj (toUnit X) (toUnit I) = X ⊗ I := by rfl

theorem bar : ChosenPullback.snd (toUnit X) (toUnit I) = CartesianMonoidalCategory.snd X I := rfl

theorem boo : (toOver I).obj X = Over.mk (ChosenPullback.snd (toUnit X) (toUnit I)) := by rfl

theorem baz : ((toOver I).obj X).hom = CartesianMonoidalCategory.snd X I := by rfl

end prelim

variable (I : C) [Exponentiable I]

/-- The first leg of a cospan constructing a pullback diagram in `C` used to define `sections` . -/
abbrev curryId : 𝟙_ C ⟶ (I ⟹ I) :=
  curry <| (ρ_ _).hom

theorem toUnit_comp_curryId {A : C} : toUnit A ≫ curryId I = curry (fst I A) := by
  apply uncurry_injective
  simp only [uncurry_natural_left, curryId, uncurry_curry, fst_def, toUnit]

namespace Over

open ChosenPullback

variable {I} [ChosenPullback (curryId I)]

/-- The object of sections of `X : Over I` defined by the following
pullback diagram:

```
 sections X -->  I ⟹ X
   |               |
   |               |
   v               v
  ⊤_ C    ---->  I ⟹ I
```
-/
abbrev sectionsObj (X : Over I) : C :=
  pullbackObj (exp I |>.map X.hom) (curryId I)

/-- The functoriality of `sectionsObj`. -/
def sectionsMap {X X' : Over I} (u : X ⟶ X') :
    sectionsObj X ⟶ sectionsObj X' :=
  pullbackMap _ _ _ _ (exp I |>.map u.left) (𝟙 _) (𝟙 _)
    (by simp [← Functor.map_comp] ) (by simp only [comp_id, id_comp])

@[reassoc (attr := simp)]
lemma sectionsMap_id {X : Over I} : sectionsMap (𝟙 X) = 𝟙 _ := by
  apply ChosenPullback.hom_ext <;> simp [sectionsMap]

@[reassoc (attr := simp)]
lemma sectionsMap_comp {X X' X'' : Over I} (u : X ⟶ X') (v : X' ⟶ X'') :
    sectionsMap (u ≫ v) = sectionsMap u ≫ sectionsMap v := by
  apply ChosenPullback.hom_ext <;> simp [sectionsMap]

variable (I)

/-- The functor mapping an object `X` in `C` to the object of sections of `X` over `I`. -/
@[simps]
def sections : Over I ⥤ C where
  obj X := sectionsObj X
  map u := sectionsMap u

variable {I}

open ChosenPullback

/-- An auxiliary morphism used to define the currying of a morphism in `Over I` to a morphism
in `C`. See `sectionsCurry`. -/
def sectionsCurryAux {X : Over I} {A : C} (u : (toOver I).obj A ⟶ X) : A ⟶ (I ⟹ X.left) :=
  curry ((β_ I A).hom ≫ u.left)

/-- The currying operation `Hom ((star I).obj A) X → Hom A (I ⟹ X.left)`. -/
def sectionsCurry {X : Over I} {A : C} (u : (toOver I).obj A ⟶ X) :
    A ⟶ (sections I).obj X :=
  ChosenPullback.lift (curry ((β_ I A).hom ≫ u.left)) (toUnit A) (by
    rw [curry_natural_right, assoc, ← Functor.map_comp, w, toOver_obj_hom, ← curry_natural_right,
    toUnit_comp_curryId]
    congr
    simp [braiding_hom_snd])

/-- The uncurrying operation `Hom A (section X) → Hom ((star I).obj A) X`. -/
def sectionsUncurry {X : Over I} {A : C} (v : A ⟶ (sections I).obj X) :
    (toOver I).obj A ⟶ X := by
  let v₂ : A ⟶ (I ⟹ X.left) := v ≫ ChosenPullback.fst (exp I |>.map X.hom) (curryId I)
  have w : toUnit A ≫ (curryId I) = v₂ ≫ (exp I).map X.hom := by
    rw [IsTerminal.hom_ext isTerminalTensorUnit (toUnit A ) (v ≫ snd ..)]
    simp [v₂, condition]
  dsimp [curryId] at w
  have w' := (exp.adjunction I).homEquiv_naturality_right_square _ _ _ _ w
  simp [curry] at w'
  exact Over.homMk ((β_ A I).hom ≫ CartesianClosed.uncurry v₂) (by
    dsimp [CartesianClosed.uncurry] at *
    simp only [assoc, ← w', whiskerLeft_toUnit_comp_rightUnitor_hom, braiding_hom_fst])

@[simp]
theorem sections_curry_uncurry {X : Over I} {A : C} {v : A ⟶ (sections I).obj X} :
    sectionsCurry (sectionsUncurry v) = v := by
  dsimp [sectionsCurry, sectionsUncurry]
  let v₂ : A ⟶ (I ⟹ X.left) := v ≫ ChosenPullback.fst (exp I |>.map X.hom) (curryId I)
  apply ChosenPullback.hom_ext
  · simp
  · subsingleton

@[simp]
theorem sections_uncurry_curry {X : Over I} {A : C} {u : (toOver I).obj A ⟶ X} :
    sectionsUncurry (sectionsCurry u) = u := by
  dsimp [sectionsCurry, sectionsUncurry]
  ext
  simp

open Adjunction

/-- An auxiliary definition which is used to define the adjunction between the star functor
and the sections functor. See starSectionsAdjunction`. -/
@[simps]
def coreHomEquiv : CoreHomEquiv (toOver I) (sections I) where
  homEquiv A X := {
    toFun := sectionsCurry
    invFun := sectionsUncurry
    left_inv {u} := sections_uncurry_curry
    right_inv {v} := sections_curry_uncurry
  }
  homEquiv_naturality_left_symm := by
    intro A' A X g v
    dsimp [sectionsCurry, sectionsUncurry, curryId]
    simp only [toOver_map]
    rw [← Over.homMk_comp]
    congr 1
    simp [CartesianClosed.uncurry_natural_left]
  homEquiv_naturality_right := by
    intro A X' X u g
    dsimp [sectionsCurry, sectionsUncurry, curryId]
    apply ChosenPullback.hom_ext
    · simp only [ChosenPullback.lift_fst, sectionsMap, assoc, pullbackMap_fst,
      ChosenPullback.lift_fst_assoc, ← curry_natural_right, assoc]
    · aesop

variable (I)

/-- The adjunction between the star functor and the sections functor. -/
@[simps! unit_app counit_app]
def toOverSectionsAdj : toOver I ⊣ sections I :=
  .mkOfHomEquiv coreHomEquiv

theorem foo {X : C} : (toOverSectionsAdj I).unit.app X = sectionsCurry (𝟙 ((toOver I).obj X)) := rfl

#check toOverSectionsAdj_unit_app I


end Over

end CategoryTheory
