/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.essentially_small
! leanprover-community/mathlib commit f7707875544ef1f81b32cb68c79e0e24e45a0e76
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Small.Basic
import Mathbin.CategoryTheory.Category.Ulift
import Mathbin.CategoryTheory.Skeletal

/-!
# Essentially small categories.

A category given by `(C : Type u) [category.{v} C]` is `w`-essentially small
if there exists a `small_model C : Type w` equipped with `[small_category (small_model C)]`.

A category is `w`-locally small if every hom type is `w`-small.

The main theorem here is that a category is `w`-essentially small iff
the type `skeleton C` is `w`-small, and `C` is `w`-locally small.
-/


universe w v v' u u'

open CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace CategoryTheory

/-- A category is `essentially_small.{w}` if there exists
an equivalence to some `S : Type w` with `[small_category S]`. -/
class EssentiallySmall (C : Type u) [Category.{v} C] : Prop where
  equiv_smallCategory : ∃ (S : Type w)(_ : SmallCategory S), Nonempty (C ≌ S)
#align category_theory.essentially_small CategoryTheory.EssentiallySmall

/-- Constructor for `essentially_small C` from an explicit small category witness. -/
theorem EssentiallySmall.mk' {C : Type u} [Category.{v} C] {S : Type w} [SmallCategory S]
    (e : C ≌ S) : EssentiallySmall.{w} C :=
  ⟨⟨S, _, ⟨e⟩⟩⟩
#align category_theory.essentially_small.mk' CategoryTheory.EssentiallySmall.mk'

/-- An arbitrarily chosen small model for an essentially small category.
-/
@[nolint has_nonempty_instance]
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
    (e : C ≌ D) : EssentiallySmall.{w} C ↔ EssentiallySmall.{w} D :=
  by
  fconstructor
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    skip
    exact essentially_small.mk' (e.symm.trans f)
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    skip
    exact essentially_small.mk' (e.trans f)
#align category_theory.essentially_small_congr CategoryTheory.essentiallySmall_congr

theorem Discrete.essentiallySmallOfSmall {α : Type u} [Small.{w} α] :
    EssentiallySmall.{w} (Discrete α) :=
  ⟨⟨Discrete (Shrink α), ⟨inferInstance, ⟨Discrete.equivalence (equivShrink _)⟩⟩⟩⟩
#align category_theory.discrete.essentially_small_of_small CategoryTheory.Discrete.essentiallySmallOfSmall

theorem essentiallySmallSelf : EssentiallySmall.{max w v u} C :=
  EssentiallySmall.mk' (AsSmall.equiv : C ≌ AsSmall.{w} C)
#align category_theory.essentially_small_self CategoryTheory.essentiallySmallSelf

/-- A category is `w`-locally small if every hom set is `w`-small.

See `shrink_homs C` for a category instance where every hom set has been replaced by a small model.
-/
class LocallySmall (C : Type u) [Category.{v} C] : Prop where
  hom_small : ∀ X Y : C, Small.{w} (X ⟶ Y) := by infer_instance
#align category_theory.locally_small CategoryTheory.LocallySmall

instance (C : Type u) [Category.{v} C] [LocallySmall.{w} C] (X Y : C) : Small (X ⟶ Y) :=
  LocallySmall.hom_small X Y

theorem locallySmall_congr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : LocallySmall.{w} C ↔ LocallySmall.{w} D :=
  by
  fconstructor
  · rintro ⟨L⟩
    fconstructor
    intro X Y
    specialize L (e.inverse.obj X) (e.inverse.obj Y)
    refine' (small_congr _).mpr L
    exact equiv_of_fully_faithful e.inverse
  · rintro ⟨L⟩
    fconstructor
    intro X Y
    specialize L (e.functor.obj X) (e.functor.obj Y)
    refine' (small_congr _).mpr L
    exact equiv_of_fully_faithful e.functor
#align category_theory.locally_small_congr CategoryTheory.locallySmall_congr

instance (priority := 100) locallySmall_self (C : Type u) [Category.{v} C] : LocallySmall.{v} C
    where
#align category_theory.locally_small_self CategoryTheory.locallySmall_self

instance (priority := 100) locallySmall_of_essentiallySmall (C : Type u) [Category.{v} C]
    [EssentiallySmall.{w} C] : LocallySmall.{w} C :=
  (locallySmall_congr (equivSmallModel C)).mpr (CategoryTheory.locallySmall_self _)
#align category_theory.locally_small_of_essentially_small CategoryTheory.locallySmall_of_essentiallySmall

/-- We define a type alias `shrink_homs C` for `C`. When we have `locally_small.{w} C`,
we'll put a `category.{w}` instance on `shrink_homs C`.
-/
@[nolint has_nonempty_instance]
def ShrinkHoms (C : Type u) :=
  C
#align category_theory.shrink_homs CategoryTheory.ShrinkHoms

namespace ShrinkHoms

section

variable {C' : Type _}

-- a fresh variable with no category instance attached
/-- Help the typechecker by explicitly translating from `C` to `shrink_homs C`. -/
def toShrinkHoms {C' : Type _} (X : C') : ShrinkHoms C' :=
  X
#align category_theory.shrink_homs.to_shrink_homs CategoryTheory.ShrinkHoms.toShrinkHoms

/-- Help the typechecker by explicitly translating from `shrink_homs C` to `C`. -/
def fromShrinkHoms {C' : Type _} (X : ShrinkHoms C') : C' :=
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

variable (C) [LocallySmall.{w} C]

@[simps]
noncomputable instance : Category.{w} (ShrinkHoms C)
    where
  Hom X Y := Shrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)
  id X := equivShrink _ (𝟙 (fromShrinkHoms X))
  comp X Y Z f g := equivShrink _ ((equivShrink _).symm f ≫ (equivShrink _).symm g)

/-- Implementation of `shrink_homs.equivalence`. -/
@[simps]
noncomputable def functor : C ⥤ ShrinkHoms C
    where
  obj X := toShrinkHoms X
  map X Y f := equivShrink (X ⟶ Y) f
#align category_theory.shrink_homs.functor CategoryTheory.ShrinkHoms.functor

/-- Implementation of `shrink_homs.equivalence`. -/
@[simps]
noncomputable def inverse : ShrinkHoms C ⥤ C
    where
  obj X := fromShrinkHoms X
  map X Y f := (equivShrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)).symm f
#align category_theory.shrink_homs.inverse CategoryTheory.ShrinkHoms.inverse

/-- The categorical equivalence between `C` and `shrink_homs C`, when `C` is locally small.
-/
@[simps]
noncomputable def equivalence : C ≌ ShrinkHoms C :=
  Equivalence.mk (functor C) (inverse C) (NatIso.ofComponents (fun X => Iso.refl X) (by tidy))
    (NatIso.ofComponents (fun X => Iso.refl X) (by tidy))
#align category_theory.shrink_homs.equivalence CategoryTheory.ShrinkHoms.equivalence

end ShrinkHoms

/-- A category is essentially small if and only if
the underlying type of its skeleton (i.e. the "set" of isomorphism classes) is small,
and it is locally small.
-/
theorem essentiallySmall_iff (C : Type u) [Category.{v} C] :
    EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) ∧ LocallySmall.{w} C :=
  by
  -- This theorem is the only bit of real work in this file.
  fconstructor
  · intro h
    fconstructor
    · rcases h with ⟨S, 𝒮, ⟨e⟩⟩
      skip
      refine' ⟨⟨skeleton S, ⟨_⟩⟩⟩
      exact e.skeleton_equiv
    · skip
      infer_instance
  · rintro ⟨⟨S, ⟨e⟩⟩, L⟩
    skip
    let e' := (shrink_homs.equivalence C).skeletonEquiv.symm
    refine' ⟨⟨S, _, ⟨_⟩⟩⟩
    apply induced_category.category (e'.trans e).symm
    refine'
      (shrink_homs.equivalence C).trans
        ((skeleton_equivalence _).symm.trans (induced_functor (e'.trans e).symm).asEquivalence.symm)
#align category_theory.essentially_small_iff CategoryTheory.essentiallySmall_iff

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
  simp [essentially_small_iff, CategoryTheory.locallySmall_of_thin]
#align category_theory.essentially_small_iff_of_thin CategoryTheory.essentiallySmall_iff_of_thin

end CategoryTheory

