/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.Over
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# The section functor as a right adjoint to the toOver functor

We show that in a cartesian monoidal category `C`, for any exponentiable object `I`, the functor
`toOver I : C ⥤ Over I` mapping an object `X` to the projection `snd : X ⊗ I ⟶ I` in `Over I`
has a right adjoint `sections I : Over I ⥤ C` whose object part is the object of sections
of `X` over `I`.

In particular, if `C` is cartesian closed, then for all objects `I` in `C`, `toOver I : C ⥤ Over I`
has a right adjoint.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed

section Sections

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

variable (I : C) [Closed I]

/-- The first leg of a cospan to define `sectionsObj` as a pullback in `C`. -/
abbrev curryRightUnitorHom : 𝟙_ C ⟶ (I ⟶[C] I) :=
  curry <| (ρ_ _).hom

variable {I}

theorem toUnit_comp_curryRightUnitorHom {A : C} :
    toUnit A ≫ curryRightUnitorHom I = curry (fst I A) := by
  apply uncurry_injective
  simp [uncurry_natural_left, curryRightUnitorHom, fst_def, toUnit]

namespace Over

open ChosenPullbacksAlong

variable (I) [ChosenPullbacksAlong (curryRightUnitorHom I)]

/-- The functor mapping an object `X : Over I` to the object of sections of `X` over `I`, defined
by the following pullback diagram. The functor's mapping of morphisms is induced by `pullbackMap`,
that is by the universal property of chosen pullbacks.

```
 sections X -->  I ⟹ X
   |               |
   |               |
   v               v
  𝟙_ C   ----->  I ⟹ I
```
-/
@[simps]
def sections : Over I ⥤ C where
  obj X := pullbackObj (ihom I |>.map X.hom) (curryRightUnitorHom I)
  map u := pullbackMap _ _ _ _ (ihom I |>.map u.left) (𝟙 _) (𝟙 _)
    (by simp [← Functor.map_comp]) (by cat_disch)

variable {I}

open ChosenPullbacksAlong

variable [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The currying operation `Hom ((toOver I).obj A) X → Hom A (I ⟹ X.left)`. -/
def sectionsCurry {X : Over I} {A : C} (u : (toOver I).obj A ⟶ X) :
    A ⟶ (sections I).obj X :=
  ChosenPullbacksAlong.lift (curry ((β_ I A).hom ≫ u.left)) (toUnit A) (by
    rw [curry_natural_right, Category.assoc, ← Functor.map_comp, w,
      ← curry_natural_right, toUnit_comp_curryRightUnitorHom]
    congr
    simp [braiding_hom_snd])

set_option backward.isDefEq.respectTransparency false in
/-- The uncurrying operation `Hom A (section X) → Hom ((toOver I).obj A) X`. -/
def sectionsUncurry {X : Over I} {A : C} (v : A ⟶ (sections I).obj X) :
    (toOver I).obj A ⟶ X :=
  letI v₂ : A ⟶ (I ⟶[C] X.left) := v ≫ fst (ihom I |>.map X.hom) (curryRightUnitorHom I)
  Over.homMk ((β_ A I).hom ≫ uncurry v₂) (by
    have comm : toUnit A ≫ (curryRightUnitorHom I) = v₂ ≫ (ihom I).map X.hom := by
      rw [IsTerminal.hom_ext isTerminalTensorUnit (toUnit A) (v ≫ snd ..)]
      simp [v₂, condition]
    dsimp [curryRightUnitorHom] at comm
    have w' := (ihom.adjunction I).homEquiv_naturality_right_square _ _ _ _ comm
    simp only [curriedTensor_obj_obj, curriedTensor_obj_map, curry,
      Equiv.symm_apply_apply] at w'
    dsimp [uncurry] at *
    rw [Category.assoc, ← w', whiskerLeft_toUnit_comp_rightUnitor_hom, braiding_hom_fst])

@[simp]
theorem sectionsCurry_sectionUncurry {X : Over I} {A : C} {v : A ⟶ (sections I).obj X} :
    sectionsCurry (sectionsUncurry v) = v := by
  dsimp [sectionsCurry, sectionsUncurry]
  cat_disch

@[simp]
theorem sectionsUncurry_sectionsCurry {X : Over I} {A : C} {u : (toOver I).obj A ⟶ X} :
    sectionsUncurry (sectionsCurry u) = u := by
  dsimp [sectionsCurry, sectionsUncurry]
  ext
  simp

open Adjunction

variable (I)

set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary definition which is used to define the adjunction between the star functor
and the sections functor. See `starSectionsAdjunction`. -/
@[simps homEquiv]
def coreHomEquivToOverSections : CoreHomEquiv (toOver I) (sections I) where
  homEquiv A X :=
    { toFun := sectionsCurry
      invFun := sectionsUncurry
      left_inv {u} := sectionsUncurry_sectionsCurry
      right_inv {v} := sectionsCurry_sectionUncurry }
  homEquiv_naturality_left_symm := by
    intro A' A X g v
    dsimp [sectionsCurry, sectionsUncurry, curryRightUnitorHom]
    simp only [toOver_map]
    rw [← Over.homMk_comp]
    congr 1
    simp [uncurry_natural_left]
  homEquiv_naturality_right := by
    intro A X' X u g
    dsimp [sectionsCurry, sectionsUncurry, curryRightUnitorHom]
    apply ChosenPullbacksAlong.hom_ext
    · simp [← curry_natural_right]
    · simp

/-- The adjunction between the toOver functor and the sections functor. -/
@[simps! unit_app counit_app]
def toOverSectionsAdj : toOver I ⊣ sections I :=
  .mkOfHomEquiv (coreHomEquivToOverSections I)

end Over

end Sections

end CategoryTheory
