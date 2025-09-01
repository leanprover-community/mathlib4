/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-! # Presentable objects

A functor `F : C ⥤ D` is `κ`-accessible (`Functor.IsCardinalAccessible`)
if it commutes with colimits of shape `J` where `J` is any `κ`-filtered category
(that is essentially small relative to the universe `w` such that `κ : Cardinal.{w}`.).
We also introduce another typeclass `Functor.IsAccessible` saying that there exists
a regular cardinal `κ` such that `Functor.IsCardinalAccessible`.

An object `X` of a category is `κ`-presentable (`IsCardinalPresentable`)
if the functor `Hom(X, _)` (i.e. `coyoneda.obj (op X)`) is `κ`-accessible.
Similar as for accessible functors, we define a type class `IsAccessible`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w w' v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Functor

section

variable (F G : C ⥤ D) (e : F ≅ G) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- A functor `F : C ⥤ D` is `κ`-accessible (with `κ` a regular cardinal)
if it preserves colimits of shape `J` where `J` is any `κ`-filtered category.
In the mathematical literature, some assumptions are often made on the
categories `C` or `D` (e.g. the existence of `κ`-filtered colimits,
see `HasCardinalFilteredColimits` below), but here we do not
make such assumptions. -/
class IsCardinalAccessible : Prop where
  preservesColimitOfShape (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F

lemma preservesColimitsOfShape_of_isCardinalAccessible [F.IsCardinalAccessible κ]
    (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F :=
  IsCardinalAccessible.preservesColimitOfShape κ _

lemma preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall
    [F.IsCardinalAccessible κ]
    (J : Type u₃) [Category.{v₃} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F := by
  have := IsCardinalFiltered.of_equivalence κ (equivSmallModel.{w} J)
  have := F.preservesColimitsOfShape_of_isCardinalAccessible κ (SmallModel.{w} J)
  exact preservesColimitsOfShape_of_equiv (equivSmallModel.{w} J).symm F

variable {κ} in
lemma isCardinalAccessible_of_le
    [F.IsCardinalAccessible κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    F.IsCardinalAccessible κ' where
  preservesColimitOfShape {J _ _} := by
    have := IsCardinalFiltered.of_le J h
    exact F.preservesColimitsOfShape_of_isCardinalAccessible κ J

include e in
variable {F G} in
lemma isCardinalAccessible_of_natIso [F.IsCardinalAccessible κ] : G.IsCardinalAccessible κ where
  preservesColimitOfShape J _ hκ := by
    have := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    exact preservesColimitsOfShape_of_natIso e

end

end Functor

variable (X : C) (Y : C) (e : X ≅ Y) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- An object `X` in a category is `κ`-presentable (for `κ` a regular cardinal)
when the functor `Hom(X, _)` preserves colimits indexed by
`κ`-filtered categories. -/
abbrev IsCardinalPresentable : Prop := (coyoneda.obj (op X)).IsCardinalAccessible κ

lemma preservesColimitsOfShape_of_isCardinalPresentable [IsCardinalPresentable X κ]
    (J : Type w) [SmallCategory.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
  (coyoneda.obj (op X)).preservesColimitsOfShape_of_isCardinalAccessible κ J

lemma preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall
    [IsCardinalPresentable X κ]
    (J : Type u₃) [Category.{v₃} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
  (coyoneda.obj (op X)).preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ J

variable {κ} in
lemma isCardinalPresentable_of_le [IsCardinalPresentable X κ]
    {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    IsCardinalPresentable X κ' :=
  (coyoneda.obj (op X)).isCardinalAccessible_of_le h

include e in
variable {X Y} in
lemma isCardinalPresentable_of_iso [IsCardinalPresentable X κ] : IsCardinalPresentable Y κ :=
  Functor.isCardinalAccessible_of_natIso (coyoneda.mapIso e.symm.op) κ

section

lemma isCardinalPresentable_of_equivalence
    {C' : Type u₃} [Category.{v₃} C'] [IsCardinalPresentable X κ] (e : C ≌ C') :
    IsCardinalPresentable (e.functor.obj X) κ := by
  refine ⟨fun J _ _ ↦ ⟨fun {Y} ↦ ?_⟩⟩
  have := preservesColimitsOfShape_of_isCardinalPresentable X κ J
  suffices PreservesColimit Y (coyoneda.obj (op (e.functor.obj X)) ⋙ uliftFunctor.{v₁}) from
    ⟨fun {c} hc ↦ ⟨isColimitOfReflects uliftFunctor.{v₁}
        (isColimitOfPreserves (coyoneda.obj (op (e.functor.obj X)) ⋙ uliftFunctor.{v₁}) hc)⟩⟩
  have iso : coyoneda.obj (op (e.functor.obj X)) ⋙ uliftFunctor.{v₁} ≅
    e.inverse ⋙ coyoneda.obj (op X) ⋙ uliftFunctor.{v₃} :=
    NatIso.ofComponents (fun Z ↦
      (Equiv.ulift.trans ((e.toAdjunction.homEquiv X Z).trans Equiv.ulift.symm)).toIso) (by
        intro _ _ f
        ext ⟨g⟩
        apply Equiv.ulift.injective
        simp [Adjunction.homEquiv_unit])
  exact preservesColimit_of_natIso Y iso.symm

instance isCardinalPresentable_of_isEquivalence
    {C' : Type u₃} [Category.{v₃} C'] [IsCardinalPresentable X κ] (F : C ⥤ C')
    [F.IsEquivalence] :
    IsCardinalPresentable (F.obj X) κ :=
  isCardinalPresentable_of_equivalence X κ F.asEquivalence

@[simp]
lemma isCardinalPresentable_iff_of_isEquivalence
    {C' : Type u₃} [Category.{v₃} C'] (F : C ⥤ C')
    [F.IsEquivalence] :
    IsCardinalPresentable (F.obj X) κ ↔ IsCardinalPresentable X κ := by
  constructor
  · intro
    exact isCardinalPresentable_of_iso
      (show F.inv.obj (F.obj X) ≅ X from F.asEquivalence.unitIso.symm.app X :) κ
  · intro
    infer_instance

end

section

variable (C) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- A category has `κ`-filtered colimits if it has colimits of shape `J`
for any `κ`-filtered category `J`. -/
class HasCardinalFilteredColimits : Prop where
  hasColimitsOfShape (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    HasColimitsOfShape J C := by intros; infer_instance

instance [HasColimitsOfSize.{w, w} C] : HasCardinalFilteredColimits.{w} C κ where

end

end CategoryTheory
