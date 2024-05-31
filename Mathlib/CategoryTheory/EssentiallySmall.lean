/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Logic.UnivLE
import Mathlib.Logic.Small.Basic

#align_import category_theory.essentially_small from "leanprover-community/mathlib"@"f7707875544ef1f81b32cb68c79e0e24e45a0e76"

/-!
# Essentially small categories.

A category given by `(C : Type u) [Category.{v} C]` is `w`-essentially small
if there exists a `SmallModel C : Type w` equipped with `[SmallCategory (SmallModel C)]` and an
equivalence `C ≌ SmallModel C`.

A category is `w`-locally small if every hom type is `w`-small.

The main theorem here is that a category is `w`-essentially small iff
the type `Skeleton C` is `w`-small, and `C` is `w`-locally small.
-/


universe w v v' u u'

open CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace CategoryTheory

/-- A category is `EssentiallySmall.{w}` if there exists
an equivalence to some `S : Type w` with `[SmallCategory S]`. -/
@[pp_with_univ]
class EssentiallySmall (C : Type u) [Category.{v} C] : Prop where
  /-- An essentially small category is equivalent to some small category. -/
  equiv_smallCategory : ∃ (S : Type w) (_ : SmallCategory S), Nonempty (C ≌ S)
#align category_theory.essentially_small CategoryTheory.EssentiallySmall

/-- Constructor for `EssentiallySmall C` from an explicit small category witness. -/
theorem EssentiallySmall.mk' {C : Type u} [Category.{v} C] {S : Type w} [SmallCategory S]
    (e : C ≌ S) : EssentiallySmall.{w} C :=
  ⟨⟨S, _, ⟨e⟩⟩⟩
#align category_theory.essentially_small.mk' CategoryTheory.EssentiallySmall.mk'

/-- An arbitrarily chosen small model for an essentially small category.
-/
-- Porting note(#5171) removed @[nolint has_nonempty_instance]
@[pp_with_univ]
def SmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] : Type w :=
  Classical.choose (@EssentiallySmall.equiv_smallCategory C _ _)
#align category_theory.small_model CategoryTheory.SmallModel

noncomputable instance smallCategorySmallModel (C : Type u) [Category.{v} C]
    [EssentiallySmall.{w} C] : SmallCategory (SmallModel C) :=
  Classical.choose (Classical.choose_spec (@EssentiallySmall.equiv_smallCategory C _ _))
#align category_theory.small_category_small_model CategoryTheory.smallCategorySmallModel

/-- The (noncomputable) categorical equivalence between
an essentially small category and its small model.
-/
noncomputable def equivSmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] :
    C ≌ SmallModel C :=
  Nonempty.some
    (Classical.choose_spec (Classical.choose_spec (@EssentiallySmall.equiv_smallCategory C _ _)))
#align category_theory.equiv_small_model CategoryTheory.equivSmallModel

theorem essentiallySmall_congr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : EssentiallySmall.{w} C ↔ EssentiallySmall.{w} D := by
  fconstructor
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    exact EssentiallySmall.mk' (e.symm.trans f)
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    exact EssentiallySmall.mk' (e.trans f)
#align category_theory.essentially_small_congr CategoryTheory.essentiallySmall_congr

theorem Discrete.essentiallySmallOfSmall {α : Type u} [Small.{w} α] :
    EssentiallySmall.{w} (Discrete α) :=
  ⟨⟨Discrete (Shrink α), ⟨inferInstance, ⟨Discrete.equivalence (equivShrink _)⟩⟩⟩⟩
#align category_theory.discrete.essentially_small_of_small CategoryTheory.Discrete.essentiallySmallOfSmall

theorem essentiallySmallSelf : EssentiallySmall.{max w v u} C :=
  EssentiallySmall.mk' (AsSmall.equiv : C ≌ AsSmall.{w} C)
#align category_theory.essentially_small_self CategoryTheory.essentiallySmallSelf

/-- A category is `w`-locally small if every hom set is `w`-small.

See `ShrinkHoms C` for a category instance where every hom set has been replaced by a small model.
-/
@[pp_with_univ]
class LocallySmall (C : Type u) [Category.{v} C] : Prop where
  /-- A locally small category has small hom-types. -/
  hom_small : ∀ X Y : C, Small.{w} (X ⟶ Y) := by infer_instance
#align category_theory.locally_small CategoryTheory.LocallySmall

instance (C : Type u) [Category.{v} C] [LocallySmall.{w} C] (X Y : C) : Small (X ⟶ Y) :=
  LocallySmall.hom_small X Y

theorem locallySmall_of_faithful {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) [F.Faithful] [LocallySmall.{w} D] : LocallySmall.{w} C where
  hom_small {_ _} := small_of_injective F.map_injective

theorem locallySmall_congr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : LocallySmall.{w} C ↔ LocallySmall.{w} D :=
  ⟨fun _ => locallySmall_of_faithful e.inverse, fun _ => locallySmall_of_faithful e.functor⟩
#align category_theory.locally_small_congr CategoryTheory.locallySmall_congr

instance (priority := 100) locallySmall_self (C : Type u) [Category.{v} C] :
    LocallySmall.{v} C where
#align category_theory.locally_small_self CategoryTheory.locallySmall_self

instance (priority := 100) locallySmall_of_univLE (C : Type u) [Category.{v} C] [UnivLE.{v, w}] :
    LocallySmall.{w} C where

theorem locallySmall_max {C : Type u} [Category.{v} C] : LocallySmall.{max v w} C where
  hom_small _ _ := small_max.{w} _

instance (priority := 100) locallySmall_of_essentiallySmall (C : Type u) [Category.{v} C]
    [EssentiallySmall.{w} C] : LocallySmall.{w} C :=
  (locallySmall_congr (equivSmallModel C)).mpr (CategoryTheory.locallySmall_self _)
#align category_theory.locally_small_of_essentially_small CategoryTheory.locallySmall_of_essentiallySmall

/-- We define a type alias `ShrinkHoms C` for `C`. When we have `LocallySmall.{w} C`,
we'll put a `Category.{w}` instance on `ShrinkHoms C`.
-/
-- Porting note(#5171): removed @[nolint has_nonempty_instance]
@[pp_with_univ]
def ShrinkHoms (C : Type u) :=
  C
#align category_theory.shrink_homs CategoryTheory.ShrinkHoms

namespace ShrinkHoms

section

variable {C' : Type*}

-- a fresh variable with no category instance attached
/-- Help the typechecker by explicitly translating from `C` to `ShrinkHoms C`. -/
def toShrinkHoms {C' : Type*} (X : C') : ShrinkHoms C' :=
  X
#align category_theory.shrink_homs.to_shrink_homs CategoryTheory.ShrinkHoms.toShrinkHoms

/-- Help the typechecker by explicitly translating from `ShrinkHoms C` to `C`. -/
def fromShrinkHoms {C' : Type*} (X : ShrinkHoms C') : C' :=
  X
#align category_theory.shrink_homs.from_shrink_homs CategoryTheory.ShrinkHoms.fromShrinkHoms

@[simp]
theorem to_from (X : C') : fromShrinkHoms (toShrinkHoms X) = X :=
  rfl
#align category_theory.shrink_homs.to_from CategoryTheory.ShrinkHoms.to_from

@[simp]
theorem from_to (X : ShrinkHoms C') : toShrinkHoms (fromShrinkHoms X) = X :=
  rfl
#align category_theory.shrink_homs.from_to CategoryTheory.ShrinkHoms.from_to

end

variable [LocallySmall.{w} C]

@[simps]
noncomputable instance : Category.{w} (ShrinkHoms C) where
  Hom X Y := Shrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)
  id X := equivShrink _ (𝟙 (fromShrinkHoms X))
  comp f g := equivShrink _ ((equivShrink _).symm f ≫ (equivShrink _).symm g)

/-- Implementation of `ShrinkHoms.equivalence`. -/
@[simps]
noncomputable def functor : C ⥤ ShrinkHoms C where
  obj X := toShrinkHoms X
  map {X Y} f := equivShrink (X ⟶ Y) f
#align category_theory.shrink_homs.functor CategoryTheory.ShrinkHoms.functor

/-- Implementation of `ShrinkHoms.equivalence`. -/
@[simps]
noncomputable def inverse : ShrinkHoms C ⥤ C where
  obj X := fromShrinkHoms X
  map {X Y} f := (equivShrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)).symm f
#align category_theory.shrink_homs.inverse CategoryTheory.ShrinkHoms.inverse

/-- The categorical equivalence between `C` and `ShrinkHoms C`, when `C` is locally small.
-/
@[simps!]
noncomputable def equivalence : C ≌ ShrinkHoms C :=
  Equivalence.mk (functor C) (inverse C)
    (NatIso.ofComponents fun X => Iso.refl X)
    (NatIso.ofComponents fun X => Iso.refl X)
#align category_theory.shrink_homs.equivalence CategoryTheory.ShrinkHoms.equivalence

end ShrinkHoms

namespace Shrink

noncomputable instance [Small.{w} C] : Category.{v} (Shrink.{w} C) :=
  InducedCategory.category (equivShrink C).symm

/-- The categorical equivalence between `C` and `Shrink C`, when `C` is small. -/
noncomputable def equivalence [Small.{w} C] : C ≌ Shrink.{w} C :=
  (inducedFunctor (equivShrink C).symm).asEquivalence.symm

end Shrink

/-- A category is essentially small if and only if
the underlying type of its skeleton (i.e. the "set" of isomorphism classes) is small,
and it is locally small.
-/
theorem essentiallySmall_iff (C : Type u) [Category.{v} C] :
    EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) ∧ LocallySmall.{w} C := by
  -- This theorem is the only bit of real work in this file.
  fconstructor
  · intro h
    fconstructor
    · rcases h with ⟨S, 𝒮, ⟨e⟩⟩
      refine ⟨⟨Skeleton S, ⟨?_⟩⟩⟩
      exact e.skeletonEquiv
    · infer_instance
  · rintro ⟨⟨S, ⟨e⟩⟩, L⟩
    let e' := (ShrinkHoms.equivalence C).skeletonEquiv.symm
    letI : Category S := InducedCategory.category (e'.trans e).symm
    refine ⟨⟨S, this, ⟨?_⟩⟩⟩
    refine (ShrinkHoms.equivalence C).trans <|
      (skeletonEquivalence (ShrinkHoms C)).symm.trans
        ((inducedFunctor (e'.trans e).symm).asEquivalence.symm)
#align category_theory.essentially_small_iff CategoryTheory.essentiallySmall_iff

theorem essentiallySmall_of_small_of_locallySmall [Small.{w} C] [LocallySmall.{w} C] :
    EssentiallySmall.{w} C :=
  (essentiallySmall_iff C).2 ⟨small_of_surjective Quotient.exists_rep, by infer_instance⟩

section FullSubcategory

instance locallySmall_fullSubcategory [LocallySmall.{w} C] (P : C → Prop) :
    LocallySmall.{w} (FullSubcategory P) :=
  locallySmall_of_faithful <| fullSubcategoryInclusion P

instance essentiallySmall_fullSubcategory_mem (s : Set C) [Small.{w} s] [LocallySmall.{w} C] :
    EssentiallySmall.{w} (FullSubcategory (· ∈ s)) :=
  suffices Small.{w} (FullSubcategory (· ∈ s)) from essentiallySmall_of_small_of_locallySmall _
  small_of_injective (f := fun x => (⟨x.1, x.2⟩ : s)) (by aesop_cat)

end FullSubcategory

/-- Any thin category is locally small.
-/
instance (priority := 100) locallySmall_of_thin {C : Type u} [Category.{v} C] [Quiver.IsThin C] :
    LocallySmall.{w} C where
#align category_theory.locally_small_of_thin CategoryTheory.locallySmall_of_thin

/--
A thin category is essentially small if and only if the underlying type of its skeleton is small.
-/
theorem essentiallySmall_iff_of_thin {C : Type u} [Category.{v} C] [Quiver.IsThin C] :
    EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) := by
  simp [essentiallySmall_iff, CategoryTheory.locallySmall_of_thin]
#align category_theory.essentially_small_iff_of_thin CategoryTheory.essentiallySmall_iff_of_thin

instance [Small.{w} C] : Small.{w} (Discrete C) := small_map discreteEquiv

end CategoryTheory
