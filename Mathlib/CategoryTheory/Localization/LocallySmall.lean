/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.HasLocalization
public import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Logic.Small.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Locally small localizations

In this file, given `W : MorphismProperty C` and a universe `w`, we show
that there exists a term in `HasLocalization.{w} W` if and only if
there exists (or for all) localization functors `L : C ⥤ D` for `W`,
the category `D` is locally `w`-small.

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

open CategoryTheory.Functor

namespace CategoryTheory.MorphismProperty

variable {C : Type u₁} [Category.{v₁} C] (W : MorphismProperty C)

/-- If `L : C ⥤ D` is a localization functor for a class of morphisms
`W : MorphismProperty C`, and `D` is locally `w`-small, we may obtain
a `HasLocalization.{w} W` instance by shrinking the morphisms in `D`.
(This version assumes that the types of objects of the categories
`C` and `D` are in the same universe.) -/
@[implicit_reducible]
noncomputable def hasLocalizationOfLocallySmall
    {D : Type u₁} [Category.{v₂} D] [LocallySmall.{w} D]
    (L : C ⥤ D) [L.IsLocalization W] :
    HasLocalization.{w} W where
  D := ShrinkHoms D
  L := L ⋙ (ShrinkHoms.equivalence D).functor

-- adding `@[implicit_reducible]` causes downstream breakage
set_option warn.classDefReducibility false in
/-- If `L : C ⥤ D` is a localization functor for a class of morphisms
`W : MorphismProperty C`, and `D` is locally `w`-small, we may obtain
a `HasLocalization.{w} W` instance. This should be used only in the
unlikely situation where the types of objects of `C` and `D` are in
different universes. Otherwise, use `hasLocalizationOfLocallySmall`. -/
noncomputable irreducible_def hasLocalizationOfLocallySmall'
    {D : Type u₂} [Category.{v₂} D] [LocallySmall.{w} D]
    (L : C ⥤ D) [L.IsLocalization W] :
    HasLocalization.{w} W := by
  have : LocallySmall.{w} (InducedCategory _ L.obj) :=
    ⟨fun X Y ↦ small_of_injective InducedCategory.homEquiv.injective⟩
  let L' : C ⥤ (InducedCategory _ L.obj) :=
    { obj X := X
      map f := InducedCategory.homMk (L.map f) }
  have := Localization.essSurj L W
  have : (inducedFunctor L.obj).EssSurj := ⟨fun Y ↦ ⟨_, ⟨L.objObjPreimageIso Y⟩⟩⟩
  have : (inducedFunctor L.obj).IsEquivalence := { }
  let e := (inducedFunctor L.obj).asEquivalence
  let e' : (L' ⋙ e.functor) ⋙ e.inverse ≅ L' :=
    associator _ _ _ ≪≫ isoWhiskerLeft L' e.unitIso.symm ≪≫ L'.rightUnitor
  have : L'.IsLocalization W :=
    Functor.IsLocalization.of_iso W (L₁ := L ⋙ e.inverse) e'
  exact hasLocalizationOfLocallySmall.{w} W L'

/-- If a class of morphisms `W : MorphismProperty C` satisfies `HasLocalization.{w} W`,
then any localized category for `W` (i.e. any target of a localization functor
`L : C ⥤ D` for `W`) is locally `w`-small. -/
lemma locallySmall_of_hasLocalization {D : Type u₂} [Category.{v₂} D]
    (L : C ⥤ D) [L.IsLocalization W] [HasLocalization.{w} W] :
    LocallySmall.{w} D where
  hom_small _ _ := small_of_injective (fun _ _ h ↦
    (Localization.uniq L W.Q' W).functor.map_injective h)

end CategoryTheory.MorphismProperty
