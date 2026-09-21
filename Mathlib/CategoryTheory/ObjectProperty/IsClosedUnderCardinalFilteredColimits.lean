/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.Basic

/-!
# Accessibly embedded full subcategories

Given `P : ObjectProperty C` and a regular cardinal `κ`, we introduce a
typeclass `P.IsClosedUnderCardinalFilteredColimits κ` saying that
`P` is stable under colimits of shape `J` when `J` is any small
`κ`-filtered category. If this holds and `C` has `κ`-filtered colimits,
the full subcategory `P.FullSubcategory` also has `κ`-filtered colimits,
and the inclusion functor `P.ι` commutes with them (i.e. `P.ι` is
a `κ`-accessible functor).

In the terminology of the book by Adámek and Rosický,
the condition `P.IsClosedUnderCardinalFilteredColimits κ` means
that the subcategory `P.FullSubcategory` is accessibly embedded in `C`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe w

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C]

/-- For a property of object `P : ObjectProperty C` and a regular cardinal `κ`,
the typeclass `P.IsClosedUnderCardinalFilteredColimits κ` means that
`P` is stable under colimits of shape `J` for any `κ`-filtered category `J`. -/
class IsClosedUnderCardinalFilteredColimits
    (P : ObjectProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  isCardinalClosedUnderColimitsOfShape'
      (P) (κ) (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    P.IsClosedUnderColimitsOfShape J := by infer_instance

namespace IsClosedUnderCardinalFilteredColimits

variable (P : ObjectProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [P.IsClosedUnderCardinalFilteredColimits κ]

lemma isCardinalClosedUnderColimitsOfShape
    (J : Type*) [Category* J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] :
    P.IsClosedUnderColimitsOfShape J := by
  rw [P.isClosedUnderColimitsOfShape_iff_of_equivalence (equivSmallModel.{w} J)]
  have := IsCardinalFiltered.of_equivalence κ (equivSmallModel.{w} J)
  exact isCardinalClosedUnderColimitsOfShape' P κ _

instance [HasCardinalFilteredColimits C κ] :
    HasCardinalFilteredColimits P.FullSubcategory κ where
  hasColimitsOfShape J _ _ := by
    have := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    have := isCardinalClosedUnderColimitsOfShape P κ J
    infer_instance

instance [HasCardinalFilteredColimits C κ] :
    P.ι.IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    have := isCardinalClosedUnderColimitsOfShape P κ J
    infer_instance

include κ in
lemma isClosedUnderIsomorphisms : P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    have := isCardinalClosedUnderColimitsOfShape P κ PUnit
    have p : P.ColimitOfShape (PUnit.{w + 1}) Y :=
      { diag := (Functor.const _).obj X
        ι.app _ := e.hom
        isColimit :=
          { desc s := e.inv ≫ s.ι.app .unit
            uniq s m hm := by simp [← dsimp% hm .unit] }
        prop_diag_obj _ := hX }
    exact p.prop

end IsClosedUnderCardinalFilteredColimits

end CategoryTheory.ObjectProperty
