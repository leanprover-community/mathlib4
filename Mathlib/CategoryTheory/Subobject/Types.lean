/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Subobject.WellPowered
import Mathlib.CategoryTheory.Types
import Mathlib.Data.Set.Subsingleton

#align_import category_theory.subobject.types from "leanprover-community/mathlib"@"610955826b3be3caaab5170fef04ecd5458521bf"

/-!
# `Type u` is well-powered

By building a categorical equivalence `MonoOver α ≌ Set α` for any `α : Type u`,
we deduce that `Subobject α ≃o Set α` and that `Type u` is well-powered.

One would hope that for a particular concrete category `C` (`AddCommGroup`, etc)
it's viable to prove `[WellPowered C]` without explicitly aligning `Subobject X`
with the "hand-rolled" definition of subobjects.

This may be possible using Lawvere theories,
but it remains to be seen whether this just pushes lumps around in the carpet.
-/


universe u

open CategoryTheory

open CategoryTheory.Subobject

theorem subtype_val_mono {α : Type u} (s : Set α) : Mono (↾(Subtype.val : s → α)) :=
  (mono_iff_injective _).mpr Subtype.val_injective
#align subtype_val_mono subtype_val_mono

attribute [local instance] subtype_val_mono

/-- The category of `MonoOver α`, for `α : Type u`, is equivalent to the partial order `Set α`.
-/
@[simps]
noncomputable def Types.monoOverEquivalenceSet (α : Type u) : MonoOver α ≌ Set α where
  functor :=
    { obj := fun f => Set.range f.1.hom
      map := fun {f g} t =>
        homOfLE
          (by
            rintro a ⟨x, rfl⟩
            exact ⟨t.1 x, congr_fun t.w x⟩) }
  inverse :=
    { obj := fun s => MonoOver.mk' (Subtype.val : s → α)
      map := fun {s t} b => MonoOver.homMk (fun w => ⟨w.1, Set.mem_of_mem_of_subset w.2 b.le⟩) }
  unitIso :=
    NatIso.ofComponents fun f =>
      MonoOver.isoMk (Equiv.ofInjective f.1.hom ((mono_iff_injective _).mp f.2)).toIso
  counitIso := NatIso.ofComponents fun s => eqToIso Subtype.range_val
#align types.mono_over_equivalence_set Types.monoOverEquivalenceSet

instance : WellPowered (Type u) :=
  wellPowered_of_essentiallySmall_monoOver fun α =>
    EssentiallySmall.mk' (Types.monoOverEquivalenceSet α)

/-- For `α : Type u`, `Subobject α` is order isomorphic to `Set α`.
-/
noncomputable def Types.subobjectEquivSet (α : Type u) : Subobject α ≃o Set α :=
  (Types.monoOverEquivalenceSet α).thinSkeletonOrderIso
#align types.subobject_equiv_set Types.subobjectEquivSet
