/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullback
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

open Over hiding pullback mapPullbackAdj

open ChosenPullback

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

section Prelim

namespace CartesianMonoidalCategory

/-- The functor which maps an object `X` in `C` to the projection `X ⊗ I ⟶ I` in `Over I`.
This is the computable analogue of the functor `Over.star`. -/
@[simps! obj_left obj_hom map_left]
def toOver (I : C) : C ⥤ Over I where
  obj X := Over.mk <| CartesianMonoidalCategory.snd X I
  map {X Y} f := Over.homMk (f ▷ I)

@[simp]
lemma toOver_map {I : C} {Y Z : C} (f : Y ⟶ Z) :
    (toOver I).map f = Over.homMk (f ▷ I) := by
  simp only [toOver]

variable (C)

/-- The functor from `C` to `Over (𝟙_ C)` which sends `X : C` to `Over.mk <| toUnit X`. -/
@[simps! obj_left obj_hom map_left]
def toOverUnit : C ⥤ Over (𝟙_ C) where
  obj X := Over.mk <| toUnit X
  map {X Y} f := Over.homMk f

/-- The slice category over the terminal unit object is equivalent to the original category. -/
def equivOverUnit : Over (𝟙_ C) ≌ C :=
  CategoryTheory.Equivalence.mk (Over.forget _) (toOverUnit C)
    (NatIso.ofComponents fun X => Over.isoMk (Iso.refl _))
    (NatIso.ofComponents fun X => Iso.refl _)

attribute [local instance] Over.ChosenPullback.cartesianMonoidalCategoryToUnit

variable {C}

/-- The isomorphism of functors `toOverUnit C ⋙ ChosenPullback.pullback (toUnit I)` and
`toOver I`. -/
def toOverCompPullback (I : C) :
    toOverUnit C ⋙ pullback (toUnit I) ≅ toOver I :=
  NatIso.ofComponents fun X => Iso.refl _

/-- The functor `toOver I` is the right adjoint to the functor `Over.forget I`. -/
@[simps! unit_app counit_app]
def forgetAdjToOver (I : C) : Over.forget I ⊣ toOver I where
  unit.app X := Over.homMk (lift (𝟙 X.left) (X.hom))
  counit.app X := fst X I

theorem forgetAdjToOver.homEquiv_symm {I : C} (X : Over I) (A : C) (f : X ⟶ (toOver I).obj A) :
     ((forgetAdjToOver I).homEquiv X A).symm f = f.left ≫ (fst _ _) := by
   rw [Adjunction.homEquiv_counit, forgetAdjToOver_counit_app]
   simp

/-- The isomorphism of functors `toOver (𝟙_ C)` and `toOverUnit C`. -/
def toOverIsoToOverUnit : toOver (𝟙_ C) ≅ toOverUnit C  :=
  (forgetAdjToOver (𝟙_ C)).rightAdjointUniq (equivOverUnit C |>.toAdjunction)

/-- A natural isomorphism between the functors `toOver I` and `toOver J ⋙ pullback f`
for any morphism `f : X ⟶ Y`. -/
def toOverPullbackIsoToOver {I J : C} (f : I ⟶ J)
    [ChosenPullback f] :
    toOver J ⋙ ChosenPullback.pullback f ≅ toOver I :=
  conjugateIsoEquiv ((ChosenPullback.mapPullbackAdj f).comp (forgetAdjToOver J))
    (forgetAdjToOver I) (mapForget f)

/-- The functor `Over.pullback f : Over Y ⥤ Over X` is naturally isomorphic to
`Over.star : Over Y ⥤ Over (Over.mk f)` post-composed with the
iterated slice equivlanece `Over (Over.mk f) ⥤ Over X`. -/
def toOverIteratedSliceForwardIsoPullback [ChosenPullbacks C] {X Y : C} (f : X ⟶ Y) :
    toOver (Over.mk f) ⋙ (Over.mk f).iteratedSliceForward ≅ pullback f :=
  conjugateIsoEquiv ((Over.mk f).iteratedSliceEquiv.symm.toAdjunction.comp (forgetAdjToOver _))
  (mapPullbackAdj f) (eqToIso (iteratedSliceBackward_forget (Over.mk f)))

section

variable {I : C} (X : C)

example : ChosenPullback.pullbackObj (toUnit X) (toUnit I) = X ⊗ I := by rfl

example : ChosenPullback.snd (toUnit X) (toUnit I) = CartesianMonoidalCategory.snd X I := rfl

example : (toOver I).obj X = Over.mk (ChosenPullback.snd (toUnit X) (toUnit I)) := by rfl

example : ((toOver I).obj X).hom = CartesianMonoidalCategory.snd X I := by rfl

end

end CartesianMonoidalCategory

end Prelim

section Sections

variable (I : C) [Exponentiable I]

/-- The first leg of a cospan constructing a pullback diagram in `C` used to define `sections` . -/
abbrev curryId : 𝟙_ C ⟶ (I ⟹ I) :=
  curry <| (ρ_ I).hom

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

@[simp]
lemma sectionsMap_id {X : Over I} : sectionsMap (𝟙 X) = 𝟙 _ := by
  apply ChosenPullback.hom_ext <;> simp [sectionsMap]

@[simp]
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
    apply ChosenPullback.hom_ext
    · simp only [ChosenPullback.lift_fst, sectionsMap, assoc, pullbackMap_fst,
      ChosenPullback.lift_fst_assoc, ← curry_natural_right, assoc]
    · aesop

variable (I) in
/-- The adjunction between the star functor and the sections functor. -/
@[simps! unit_app counit_app]
def toOverSectionsAdj : toOver I ⊣ sections I :=
  .mkOfHomEquiv coreHomEquivToOverSections

end Over

end Sections

end CategoryTheory
