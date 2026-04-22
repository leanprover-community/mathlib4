/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Compatibility lemmas for limits and colimits in a monoidal category

For numerous simp lemmas of the form `f ≫ g = h`, we add accompanying simp lemmas of the form
`Q ◁ f ≫ Q ◁ g = Q ◁ h` and `f ▷ Q ≫ g ▷ Q = h ▷ Q`. This file and
`Mathlib.CategoryTheory.Monoidal.Limits.Shapes.Pullback` are needed to define a monoidal category
structure in `Mathlib.CategoryTheory.Monoidal.Arrow`.

## TODO
An attribute should be developed to automatically generate lemmas of this form.
-/

@[expose] public section

universe v v₁ u u₁

namespace CategoryTheory.MonoidalCategory

open Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace Limits

section HasColimit

variable {J : Type u₁} [Category.{v₁} J]
    {F G : J ⥤ C} [HasColimit F] [HasColimit G]

@[reassoc (attr := simp)]
lemma HasColimit.whiskerLeft_isoOfNatIso_ι_hom (w : F ≅ G) (j : J) {Q : C} :
    Q ◁ colimit.ι F j ≫ Q ◁ (HasColimit.isoOfNatIso w).hom =
      Q ◁ w.hom.app j ≫ Q ◁ colimit.ι G j := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
lemma HasColimit.isoOfNatIso_ι_hom_whiskerRight (w : F ≅ G) (j : J) {Q : C} :
    colimit.ι F j ▷ Q ≫ (HasColimit.isoOfNatIso w).hom ▷ Q =
      w.hom.app j ▷ Q ≫ colimit.ι G j ▷ Q := by
  simp [← MonoidalCategory.comp_whiskerRight]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma colimit.whiskerLeft_ι_desc (c : Cocone F) (j : J) {Q : C} :
    Q ◁ colimit.ι F j ≫ Q ◁ colimit.desc F c = Q ◁ c.ι.app j := by
  simp [← MonoidalCategory.whiskerLeft_comp]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma colimit.ι_desc_whiskerRight (c : Cocone F) (j : J) {Q : C} :
    colimit.ι F j ▷ Q ≫ colimit.desc F c ▷ Q = c.ι.app j ▷ Q := by
  simp [← comp_whiskerRight]

end HasColimit

end Limits

end CategoryTheory.MonoidalCategory
