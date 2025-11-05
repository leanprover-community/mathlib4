/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullback

/-!
# The section functor as a right adjoint to the star functor

We show that if `C` is cartesian closed then `star I : C ⥤ Over I`
has a right adjoint `sectionsFunctor` whose object part is the object of sections
of `X` over `I`.

-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianClosed

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

variable (I : C) [Exponentiable I]

/-- The first leg of a cospan constructing a pullback diagram in `C` used to define `sections` . -/
def curryId : 𝟙_ C ⟶ (I ⟹ I) :=
  curry <| (ρ_ _).hom

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
  apply hom_ext <;> simp [sectionsMap]

@[reassoc (attr := simp)]
lemma sectionsMap_comp {X X' X'' : Over I} (u : X ⟶ X') (v : X' ⟶ X'') :
    sectionsMap (u ≫ v) = sectionsMap u ≫ sectionsMap v := by
  apply hom_ext <;> simp [sectionsMap]

#exit

variable (I)

/-- The functor which maps an object `X` in `C` to the projection `I ⊗ X ⟶ I` in `Over I`.
This is the computable analogue of the functor `Over.star`. -/
@[simps! obj_left obj_hom map_left]
def _root_.toOver : C ⥤ Over I where
  obj X := Over.mk (CartesianMonoidalCategory.fst I X)
  map {X Y} f := Over.homMk (I ◁ f)

/-- The functor mapping an object `X` in `C` to the object of sections of `X` over `I`. -/
@[simps]
def sections : Over I ⥤ C where
  obj X := sectionsObj X
  map u := sectionsMap u

variable {I}

open ChosenPullback

/-- An auxiliary morphism used to define the currying of a morphism in `Over I` to a morphism
in `C`. See `sectionsCurry`. -/
def sectionsCurryAux {X : Over I} {A : C} (u : (star I).obj A ⟶ X) : A ⟶ (I ⟹ X.left) :=
  curry (u.left)

/-- The currying operation `Hom ((star I).obj A) X → Hom A (I ⟹ X.left)`. -/
def sectionsCurry {X : Over I} {A : C} (u : (star I).obj A ⟶ X) :
    A ⟶ (sections I).obj X := by
  apply pullback.lift (terminal.from A)
    (CartesianClosed.curry ((prodIsoTensorObj _ _).inv ≫ u.left)) (uncurry_injective _)
  rw [uncurry_natural_left]
  simp [curryId, uncurry_natural_right, uncurry_curry]

/-- The uncurrying operation `Hom A (section X) → Hom ((star I).obj A) X`. -/
def sectionsUncurry {X : Over I} {A : C} (v : A ⟶ (sections I).obj X) :
    (star I).obj A ⟶ X := by
  let v₂ : A ⟶ (I ⟹ X.left) := v ≫ pullback.snd ..
  have w : terminal.from A ≫ (curryId I) = v₂ ≫ (exp I).map X.hom := by
    rw [IsTerminal.hom_ext terminalIsTerminal (terminal.from A ) (v ≫ (pullback.fst ..))]
    simp [v₂, pullback.condition]
  dsimp [curryId] at w
  have w' := homEquiv_naturality_right_square (F := MonoidalCategory.tensorLeft I)
    (adj := exp.adjunction I) _ _ _ _ w
  simp [CartesianClosed.curry] at w'
  refine Over.homMk ((prodIsoTensorObj I A).hom ≫ CartesianClosed.uncurry v₂) ?_
  · dsimp [CartesianClosed.uncurry] at *
    rw [Category.assoc, ← w']
    simp [star_obj_hom]

@[simp]
theorem sections_curry_uncurry {X : Over I} {A : C} {v : A ⟶ (sections I).obj X} :
    sectionsCurry (sectionsUncurry v) = v := by
  dsimp [sectionsCurry, sectionsUncurry]
  let v₂ : A ⟶ (I ⟹ X.left) := v ≫ pullback.snd _ _
  apply pullback.hom_ext
  · simp
    rw [IsTerminal.hom_ext terminalIsTerminal (terminal.from A ) (v ≫ (pullback.fst ..))]
  · simp

@[simp]
theorem sections_uncurry_curry {X : Over I} {A : C} {u : (star I).obj A ⟶ X} :
    sectionsUncurry (sectionsCurry u) = u := by
  dsimp [sectionsCurry, sectionsUncurry]
  ext
  simp

/-- An auxiliary definition which is used to define the adjunction between the star functor
and the sections functor. See starSectionsAdjunction`. -/
def coreHomEquiv : CoreHomEquiv (star I) (sections I) where
  homEquiv A X := {
    toFun := sectionsCurry
    invFun := sectionsUncurry
    left_inv {u} := sections_uncurry_curry
    right_inv {v} := sections_curry_uncurry
  }
  homEquiv_naturality_left_symm := by
    intro A' A X g v
    dsimp [sectionsCurry, sectionsUncurry, curryId]
    simp only [star_map]
    rw [← Over.homMk_comp]
    congr 1
    simp [CartesianClosed.uncurry_natural_left]
  homEquiv_naturality_right := by
    intro A X' X u g
    dsimp [sectionsCurry, sectionsUncurry, curryId]
    apply pullback.hom_ext (IsTerminal.hom_ext terminalIsTerminal _ _)
    simp [sectionsMap, curryId]
    rw [← CartesianClosed.curry_natural_right, Category.assoc]

variable (I)

/-- The adjunction between the star functor and the sections functor. -/
@[simps! unit_app counit_app]
def starSectionsAdj : star I ⊣ sections I :=
  .mkOfHomEquiv coreHomEquiv

end Over

end CategoryTheory
