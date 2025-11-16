/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong
import Mathlib.CategoryTheory.LocallyCartesianClosed.Over
import Mathlib.CategoryTheory.Closed.Cartesian

/-!
# The section functor as a right adjoint to the star functor

We show that in a cartesian monoidal category `C`, for any exponentiable object `I`, the functor
`toOver I : C ⥤ Over I` mapping an object `X` to the projection `snd : X ⊗ I ⟶ I` in `Over I`
has a right adjoint `sections I : Over I ⥤ C` whose object part is the object of sections
of `X` over `I`.

In particular, if `C` is cartesian closed, then for all objects `I` in `C`, `toOver I : C ⥤ Over I`
has a right adjoint.

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianClosed CartesianMonoidalCategory

section Sections

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

variable (I : C) [Exponentiable I]

/-- The first leg of a cospan to define `sectionsObj` as a pullback in `C`. -/
abbrev curryId : 𝟙_ C ⟶ (I ⟹ I) :=
  curry <| (ρ_ _).hom

theorem toUnit_comp_curryId {A : C} : toUnit A ≫ curryId I = curry (fst I A) := by
  apply uncurry_injective
  simp only [uncurry_natural_left, curryId, uncurry_curry, fst_def, toUnit]

namespace Over

open ChosenPullbacksAlong

variable {I} [ChosenPullbacksAlong (curryId I)]

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
    (by simp [← Functor.map_comp]) (by cat_disch)

@[simp]
lemma sectionsMap_fst {X X' : Over I} (u : X ⟶ X') :
    sectionsMap u ≫ fst _ _ = ChosenPullbacksAlong.fst _ _ ≫ (exp I).map u.left := by
  simp [sectionsMap, pullbackMap_fst]

@[simp]
lemma sectionsMap_snd {X X' : Over I} (u : X ⟶ X') :
    sectionsMap u ≫ snd _ _ = ChosenPullbacksAlong.snd _ _ := by
  simp [sectionsMap, pullbackMap_snd]

@[simp]
lemma sectionsMap_id {X : Over I} : sectionsMap (𝟙 X) = 𝟙 _ := by
  cat_disch

@[simp]
lemma sectionsMap_comp {X X' X'' : Over I} (u : X ⟶ X') (v : X' ⟶ X'') :
    sectionsMap (u ≫ v) = sectionsMap u ≫ sectionsMap v := by
  ext
  simp? [sectionsMap]

variable (I)

/-- The functor mapping an object `X` in `C` to the object of sections of `X` over `I`. -/
@[simps]
def sections : Over I ⥤ C where
  obj X := sectionsObj X
  map u := sectionsMap u

variable {I}

open ChosenPullbacksAlong

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

/-- The currying operation `Hom ((star I).obj A) X → Hom A (I ⟹ X.left)`. -/
def sectionsCurry {X : Over I} {A : C} (u : (toOver I).obj A ⟶ X) :
    A ⟶ (sections I).obj X :=
  ChosenPullbacksAlong.lift (curry ((β_ I A).hom ≫ u.left)) (toUnit A) (by
    rw [curry_natural_right, assoc, ← Functor.map_comp, w, toOver_obj_hom, ← curry_natural_right,
    toUnit_comp_curryId]
    congr
    simp [braiding_hom_snd])

/-- The uncurrying operation `Hom A (section X) → Hom ((star I).obj A) X`. -/
def sectionsUncurry {X : Over I} {A : C} (v : A ⟶ (sections I).obj X) :
    (toOver I).obj A ⟶ X := by
  let v₂ : A ⟶ (I ⟹ X.left) := v ≫ ChosenPullbacksAlong.fst (exp I |>.map X.hom) (curryId I)
  have comm : toUnit A ≫ (curryId I) = v₂ ≫ (exp I).map X.hom := by
    rw [IsTerminal.hom_ext isTerminalTensorUnit (toUnit A ) (v ≫ snd ..)]
    simp [v₂, condition]
  dsimp [curryId] at comm
  have w' := (exp.adjunction I).homEquiv_naturality_right_square _ _ _ _ comm
  simp [curry] at w'
  exact Over.homMk ((β_ A I).hom ≫ uncurry v₂) (by
    dsimp [CartesianClosed.uncurry] at *
    simp only [assoc, ← w', whiskerLeft_toUnit_comp_rightUnitor_hom, braiding_hom_fst])

@[simp]
theorem sections_curry_uncurry {X : Over I} {A : C} {v : A ⟶ (sections I).obj X} :
    sectionsCurry (sectionsUncurry v) = v := by
  dsimp [sectionsCurry, sectionsUncurry]
  let v₂ : A ⟶ (I ⟹ X.left) := v ≫ ChosenPullbacksAlong.fst (exp I |>.map X.hom) (curryId I)
  apply ChosenPullbacksAlong.hom_ext
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
def coreHomEquivToOverSections : CoreHomEquiv (toOver I) (sections I) where
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
    apply ChosenPullbacksAlong.hom_ext
    · simp only [ChosenPullbacksAlong.lift_fst, sectionsMap, assoc, pullbackMap_fst,
      ChosenPullbacksAlong.lift_fst_assoc, ← curry_natural_right, assoc]
    · aesop

variable (I) in
/-- The adjunction between the star functor and the sections functor. -/
@[simps! unit_app counit_app]
def toOverSectionsAdj : toOver I ⊣ sections I :=
  .mkOfHomEquiv coreHomEquivToOverSections

end Over

end Sections

end CategoryTheory
