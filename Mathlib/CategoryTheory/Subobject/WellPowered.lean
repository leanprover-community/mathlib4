/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.EssentiallySmall

#align_import category_theory.subobject.well_powered from "leanprover-community/mathlib"@"29b834dfbba4ed1b7950628bbf5e69ab98c15b4c"

/-!
# Well-powered categories

A category `(C : Type u) [Category.{v} C]` is `[WellPowered C]` if
for every `X : C`, we have `Small.{v} (Subobject X)`.

(Note that in this situation `Subobject X : Type (max u v)`,
so this is a nontrivial condition for large categories,
but automatic for small categories.)

This is equivalent to the category `MonoOver X` being `EssentiallySmall.{v}` for all `X : C`.

When a category is well-powered, you can obtain nonconstructive witnesses as
`Shrink (Subobject X) : Type v`
and
`equivShrink (Subobject X) : Subobject X ≃ Shrink (subobject X)`.
-/


universe v u₁ u₂

namespace CategoryTheory

variable (C : Type u₁) [Category.{v} C]

/--
A category (with morphisms in `Type v`) is well-powered if `Subobject X` is `v`-small for every `X`.

We show in `wellPowered_of_essentiallySmall_monoOver` and `essentiallySmall_monoOver`
that this is the case if and only if `MonoOver X` is `v`-essentially small for every `X`.
-/
class WellPowered : Prop where
  subobject_small : ∀ X : C, Small.{v} (Subobject X) := by infer_instance
#align category_theory.well_powered CategoryTheory.WellPowered

instance small_subobject [WellPowered C] (X : C) : Small.{v} (Subobject X) :=
  WellPowered.subobject_small X
#align category_theory.small_subobject CategoryTheory.small_subobject

instance (priority := 100) wellPowered_of_smallCategory (C : Type u₁) [SmallCategory C] :
    WellPowered C where
#align category_theory.well_powered_of_small_category CategoryTheory.wellPowered_of_smallCategory

variable {C}

theorem essentiallySmall_monoOver_iff_small_subobject (X : C) :
    EssentiallySmall.{v} (MonoOver X) ↔ Small.{v} (Subobject X) :=
  essentiallySmall_iff_of_thin
#align category_theory.essentially_small_mono_over_iff_small_subobject CategoryTheory.essentiallySmall_monoOver_iff_small_subobject

theorem wellPowered_of_essentiallySmall_monoOver (h : ∀ X : C, EssentiallySmall.{v} (MonoOver X)) :
    WellPowered C :=
  { subobject_small := fun X => (essentiallySmall_monoOver_iff_small_subobject X).mp (h X) }
#align category_theory.well_powered_of_essentially_small_mono_over CategoryTheory.wellPowered_of_essentiallySmall_monoOver

section

variable [WellPowered C]

instance essentiallySmall_monoOver (X : C) : EssentiallySmall.{v} (MonoOver X) :=
  (essentiallySmall_monoOver_iff_small_subobject X).mpr (WellPowered.subobject_small X)
#align category_theory.essentially_small_mono_over CategoryTheory.essentiallySmall_monoOver

end

section Equivalence

variable {D : Type u₂} [Category.{v} D]

theorem wellPowered_of_equiv (e : C ≌ D) [WellPowered C] : WellPowered D :=
  wellPowered_of_essentiallySmall_monoOver fun X =>
    (essentiallySmall_congr (MonoOver.congr X e.symm)).2 <| by infer_instance
#align category_theory.well_powered_of_equiv CategoryTheory.wellPowered_of_equiv

/-- Being well-powered is preserved by equivalences, as long as the two categories involved have
    their morphisms in the same universe. -/
theorem wellPowered_congr (e : C ≌ D) : WellPowered C ↔ WellPowered D :=
  ⟨fun _ => wellPowered_of_equiv e, fun _ => wellPowered_of_equiv e.symm⟩
#align category_theory.well_powered_congr CategoryTheory.wellPowered_congr

end Equivalence

end CategoryTheory
