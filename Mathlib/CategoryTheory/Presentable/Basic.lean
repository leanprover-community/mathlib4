/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-! # Presentable objects

A functor `F : C ⥤ D` is `κ`-accessible (`Functor.IsAccessible`)
if it commutes with colimits of shape `J` where `J` is any `κ`-filtered category
(that is essentially small relative to the universe `w` such that `κ : Cardinal.{w}`.).

An object `X` of a category is `κ`-presentable (`IsPresentable`)
if the functor `Hom(X, _)` (i.e. `coyoneda.obj (op X)`) is `κ`-accessible.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w w' v'' v' v u'' u' u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Functor

variable (F G : C ⥤ D) (e : F ≅ G) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- A functor is `κ`-accessible (with `κ` a regular cardinal)
if it preserves colimits of shape `J` where `J` is any `κ`-filtered category. -/
class IsAccessible : Prop where
  preservesColimitOfShape (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F

lemma preservesColimitsOfShape_of_isAccessible [F.IsAccessible κ]
    (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F :=
  IsAccessible.preservesColimitOfShape κ _

lemma preservesColimitsOfShape_of_isAccessible_of_essentiallySmall [F.IsAccessible κ]
    (J : Type u'') [Category.{v''} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F := by
  have := IsCardinalFiltered.of_equivalence κ (equivSmallModel.{w} J)
  have := F.preservesColimitsOfShape_of_isAccessible κ (SmallModel.{w} J)
  exact preservesColimitsOfShape_of_equiv (equivSmallModel.{w} J).symm F

variable {κ} in
lemma isAccessible_of_le
    [F.IsAccessible κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    F.IsAccessible κ' where
  preservesColimitOfShape {J _ _} := by
    have := IsCardinalFiltered.of_le J h
    exact F.preservesColimitsOfShape_of_isAccessible κ J

include e in
variable {F G} in
lemma isAccessible_of_iso [F.IsAccessible κ] : G.IsAccessible κ where
  preservesColimitOfShape J _ hκ  := by
    have := F.preservesColimitsOfShape_of_isAccessible κ J
    exact preservesColimitsOfShape_of_natIso e

end Functor

variable (X : C) (Y : C) (e : X ≅ Y) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- An object `X` in a category is `κ`-presentable (for `κ` a regular cardinal)
when the functor `Hom(X, _)` preserves colimits indexed by
`κ`-filtered categories. -/
abbrev IsPresentable : Prop := (coyoneda.obj (op X)).IsAccessible κ

lemma preservesColimitsOfShape_of_isPresentable [IsPresentable X κ]
    (J : Type w) [SmallCategory.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
  (coyoneda.obj (op X)).preservesColimitsOfShape_of_isAccessible κ J

lemma preservesColimitsOfShape_of_isPresentable_of_essentiallySmall [IsPresentable X κ]
    (J : Type u'') [Category.{v''} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
  (coyoneda.obj (op X)).preservesColimitsOfShape_of_isAccessible_of_essentiallySmall κ J

variable {κ} in
lemma isPresentable_of_le [IsPresentable X κ]
    {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    IsPresentable X κ' :=
  (coyoneda.obj (op X)).isAccessible_of_le h

include e in
variable {X Y} in
lemma isPresentable_of_iso [IsPresentable X κ] : IsPresentable Y κ :=
  Functor.isAccessible_of_iso (coyoneda.mapIso e.symm.op) κ

end CategoryTheory
