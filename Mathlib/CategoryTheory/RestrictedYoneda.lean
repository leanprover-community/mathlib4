/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# The restricted Yoneda functor

## References
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory.Presheaf

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

/-- Given a functor `F : C ⥤ D` where `D` is locally `w`-small,
this is the bifunctor `D ⥤ Cᵒᵖ ⥤ Type w` which sends `Y : D` and `X : C`
to `(shrinkYoneda.{w}.obj Y).obj (op (F.obj X))`, which is a type
that is equivalent to `F.obj X ⟶ Y`. -/
@[implicit_reducible, simps! obj_obj obj_map map_app]
noncomputable def restrictedShrinkYoneda [LocallySmall.{w} D] (F : C ⥤ D) :
    D ⥤ Cᵒᵖ ⥤ Type w :=
  shrinkYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F.op

/-- Given a functor `F : C ⥤ D` where the morphisms in `D` are in `Type v'`,
this is the bifunctor `D ⥤ Cᵒᵖ ⥤ Type v'` which sends `Y : D` and `X : C`
to `F.obj X ⟶ Y`. -/
@[implicit_reducible, simps! obj_obj obj_map map_app]
def restrictedYoneda (F : C ⥤ D) : D ⥤ Cᵒᵖ ⥤ Type v' :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F.op

/-- Given a functor `F : C ⥤ D` where the morphisms in `D` are in `Type v'`,
this is the bifunctor `D ⥤ Cᵒᵖ ⥤ Type max w v'` which sends `Y : D` and `X : C`
to `(uliftYoneda.{w}.obj Y).obj (op (F.obj X))`, which is a type
that is equivalent to `F.obj X ⟶ Y`. -/
@[implicit_reducible, simps! obj_obj obj_map map_app]
def restrictedULiftYoneda (F : C ⥤ D) : D ⥤ Cᵒᵖ ⥤ Type max w v' :=
    uliftYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ _).obj F.op

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma map_comp_uliftYonedaEquiv_down (F : C ⥤ D) {E : D} {X Y : C} (f : X ⟶ Y)
    (g : uliftYoneda.{max w v'}.obj Y ⟶ (restrictedULiftYoneda.{max w v} F).obj E) :
    dsimp% F.map f ≫ (uliftYonedaEquiv g).down =
      (uliftYonedaEquiv (uliftYoneda.map f ≫ g)).down := by
  have := (g.naturality_apply f.op) (ULift.up (𝟙 Y))
  dsimp [uliftYonedaEquiv, uliftYoneda] at this ⊢
  cat_disch

/-- Given a functor `F : C ⥤ D`, this is the isomorphism
between `restrictedULiftYoneda.{w} F` and `restrictedShrinkYoneda.{max w v'} F`
when the types of morphisms in `D` are in `Type v'`. -/
noncomputable abbrev restrictedULiftYonedaIso (F : C ⥤ D) :
    restrictedULiftYoneda.{w} F ≅ restrictedShrinkYoneda.{max w v'} F :=
  Functor.isoWhiskerRight uliftYonedaIsoShrinkYoneda _

/-- Given a functor `F : C ⥤ D`, this is the isomorphism
between `restrictedYoneda F` and `restrictedShrinkYoneda.{v'} F`
when the types of morphisms in `D` are in `Type v'`. -/
noncomputable abbrev restrictedYonedaIso (F : C ⥤ D) :
    restrictedYoneda F ≅ restrictedShrinkYoneda.{v'} F :=
  Functor.isoWhiskerRight shrinkYonedaIsoYoneda.symm _

end CategoryTheory.Presheaf
