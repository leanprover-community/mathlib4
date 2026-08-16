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
  [LocallySmall.{w} D] (F : C ⥤ D)

@[implicit_reducible, simps! obj_obj obj_map map_app]
noncomputable def restrictedShrinkYoneda : D ⥤ Cᵒᵖ ⥤ Type w :=
  shrinkYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F.op

@[implicit_reducible, simps! obj_obj obj_map map_app]
def restrictedYoneda : D ⥤ Cᵒᵖ ⥤ Type v' :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F.op

@[implicit_reducible, simps! obj_obj obj_map map_app]
def restrictedULiftYoneda : D ⥤ Cᵒᵖ ⥤ Type max w v' :=
    uliftYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ _).obj F.op

noncomputable abbrev restrictedULiftYonedaIso :
    restrictedULiftYoneda.{w} F ≅ restrictedShrinkYoneda.{max w v'} F :=
  Functor.isoWhiskerRight uliftYonedaIsoShrinkYoneda _

noncomputable abbrev restrictedYonedaIso :
    restrictedYoneda F ≅ restrictedShrinkYoneda.{v'} F :=
  Functor.isoWhiskerRight shrinkYonedaIsoYoneda.symm _

end CategoryTheory.Presheaf
