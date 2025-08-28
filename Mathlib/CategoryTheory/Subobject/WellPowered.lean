/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Well-powered categories

A category `(C : Type u) [Category.{v} C]` is `[WellPowered.{w} C]`
if `C` is locally small relative to `w` and for every `X : C`,
we have `Small.{w} (Subobject X)`. The most common cases if when `w = v`,
in which case, it only involves the condition `Small.{v} (Subobject X)`

(Note that in this situation `Subobject X : Type (max u v)`,
so this is a nontrivial condition for large categories,
but automatic for small categories.)

This is equivalent to the category `MonoOver X` being `EssentiallySmall.{w}` for all `X : C`.

When a category is well-powered, you can obtain nonconstructive witnesses as
`Shrink (Subobject X) : Type w`
and
`equivShrink (Subobject X) : Subobject X ≃ Shrink (subobject X)`.
-/


universe w v v₂ u₁ u₂

namespace CategoryTheory

variable (C : Type u₁) [Category.{v} C]

/--
A category (with morphisms in `Type v`) is well-powered relative to a universe `w`
if it is locally small and `Subobject X` is `w`-small for every `X`.

We show in `wellPowered_of_essentiallySmall_monoOver` and `essentiallySmall_monoOver`
that this is the case if and only if `MonoOver X` is `w`-essentially small for every `X`.
-/
@[pp_with_univ]
class WellPowered [LocallySmall.{w} C] : Prop where
  subobject_small : ∀ X : C, Small.{w} (Subobject X) := by infer_instance

instance small_subobject [LocallySmall.{w} C] [WellPowered C] (X : C) :
    Small.{w} (Subobject X) :=
  WellPowered.subobject_small X

instance (priority := 100) wellPowered_of_smallCategory (C : Type u₁) [SmallCategory C] :
    WellPowered.{u₁} C where

variable {C}

theorem essentiallySmall_monoOver_iff_small_subobject (X : C) :
    EssentiallySmall.{w} (MonoOver X) ↔ Small.{w} (Subobject X) :=
  essentiallySmall_iff_of_thin

theorem wellPowered_of_essentiallySmall_monoOver [LocallySmall.{w} C]
    (h : ∀ X : C, EssentiallySmall.{w} (MonoOver X)) :
    WellPowered.{w} C :=
  { subobject_small := fun X => (essentiallySmall_monoOver_iff_small_subobject X).mp (h X) }

section

variable [LocallySmall.{w} C] [WellPowered.{w} C]

instance essentiallySmall_monoOver (X : C) : EssentiallySmall.{w} (MonoOver X) :=
  (essentiallySmall_monoOver_iff_small_subobject X).mpr (WellPowered.subobject_small X)

end

section Equivalence

variable {D : Type u₂} [Category.{v₂} D]

theorem wellPowered_of_equiv (e : C ≌ D) [LocallySmall.{w} C] [LocallySmall.{w} D]
    [WellPowered.{w} C] : WellPowered.{w} D :=
  wellPowered_of_essentiallySmall_monoOver fun X =>
    (essentiallySmall_congr (MonoOver.congr X e.symm)).2 <| by infer_instance

/-- Being well-powered is preserved by equivalences. -/
theorem wellPowered_congr (e : C ≌ D) [LocallySmall.{w} C] [LocallySmall.{w} D] :
    WellPowered.{w} C ↔ WellPowered.{w} D :=
  ⟨fun _ => wellPowered_of_equiv e, fun _ => wellPowered_of_equiv e.symm⟩

instance [LocallySmall.{w} C] [WellPowered.{w} C] :
    WellPowered.{w, w} (ShrinkHoms C) :=
  wellPowered_of_equiv.{w} (ShrinkHoms.equivalence.{w} C)

end Equivalence

end CategoryTheory
