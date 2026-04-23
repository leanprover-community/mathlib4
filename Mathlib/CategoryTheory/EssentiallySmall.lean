/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Logic.UnivLE
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Init
import Mathlib.Logic.Small.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Essentially small categories.

A category given by `(C : Type u) [Category.{v} C]` is `w`-essentially small
if there exists a `SmallModel C : Type w` equipped with `[SmallCategory (SmallModel C)]` and an
equivalence `C ≌ SmallModel C`.

A category is `w`-locally small if every hom type is `w`-small.

The main theorem here is that a category is `w`-essentially small iff
the type `Skeleton C` is `w`-small, and `C` is `w`-locally small.
-/

@[expose] public section


universe w w' v v' u u'

open CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace CategoryTheory

/-- A category is `EssentiallySmall.{w}` if there exists
an equivalence to some `S : Type w` with `[SmallCategory S]`. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the smallness universe `w` in
-- `EssentiallySmall` and `LocallySmall` would default to a universe output parameter.
-- See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
class EssentiallySmall (C : Type u) [Category.{v} C] : Prop where
  /-- An essentially small category is equivalent to some small category. -/
  equiv_smallCategory : ∃ (S : Type w) (_ : SmallCategory S), Nonempty (C ≌ S)

/-- Constructor for `EssentiallySmall C` from an explicit small category witness. -/
theorem EssentiallySmall.mk' {C : Type u} [Category.{v} C] {S : Type w} [SmallCategory S]
    (e : C ≌ S) : EssentiallySmall.{w} C :=
  ⟨⟨S, _, ⟨e⟩⟩⟩

/-- An arbitrarily chosen small model for an essentially small category.
-/
@[pp_with_univ]
def SmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] : Type w :=
  Classical.choose (@EssentiallySmall.equiv_smallCategory C _ _)

noncomputable instance smallCategorySmallModel (C : Type u) [Category.{v} C]
    [EssentiallySmall.{w} C] : SmallCategory (SmallModel C) :=
  Classical.choose (Classical.choose_spec (@EssentiallySmall.equiv_smallCategory C _ _))

/-- The (noncomputable) categorical equivalence between
an essentially small category and its small model.
-/
noncomputable def equivSmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] :
    C ≌ SmallModel C :=
  Nonempty.some
    (Classical.choose_spec (Classical.choose_spec (@EssentiallySmall.equiv_smallCategory C _ _)))

instance (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] : EssentiallySmall.{w} Cᵒᵖ :=
  EssentiallySmall.mk' (equivSmallModel C).op

theorem essentiallySmall_congr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : EssentiallySmall.{w} C ↔ EssentiallySmall.{w} D := by
  fconstructor
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    exact EssentiallySmall.mk' (e.symm.trans f)
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    exact EssentiallySmall.mk' (e.trans f)

theorem Discrete.essentiallySmallOfSmall {α : Type u} [Small.{w} α] :
    EssentiallySmall.{w} (Discrete α) :=
  ⟨⟨Discrete (Shrink α), ⟨inferInstance, ⟨Discrete.equivalence (equivShrink _)⟩⟩⟩⟩

theorem essentiallySmallSelf : EssentiallySmall.{max w v u} C :=
  EssentiallySmall.mk' (AsSmall.equiv : C ≌ AsSmall.{w} C)

/-- A category is `w`-locally small if every hom set is `w`-small.

See `ShrinkHoms C` for a category instance where every hom set has been replaced by a small model.
-/
-- See comment on `EssentiallySmall` above.
@[univ_out_params, pp_with_univ]
class LocallySmall (C : Type u) [Category.{v} C] : Prop where
  /-- A locally small category has small hom-types. -/
  hom_small : ∀ X Y : C, Small.{w} (X ⟶ Y) := by infer_instance

instance (C : Type u) [Category.{v} C] [LocallySmall.{w} C] (X Y : C) : Small.{w, v} (X ⟶ Y) :=
  LocallySmall.hom_small X Y

instance (C : Type u) [Category.{v} C] [LocallySmall.{w} C] : LocallySmall.{w} Cᵒᵖ where
  hom_small X Y := small_of_injective (opEquiv X Y).injective

theorem locallySmall_of_faithful {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) [F.Faithful] [LocallySmall.{w} D] : LocallySmall.{w} C where
  hom_small {_ _} := small_of_injective F.map_injective

theorem locallySmall_congr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : LocallySmall.{w} C ↔ LocallySmall.{w} D :=
  ⟨fun _ => locallySmall_of_faithful e.inverse, fun _ => locallySmall_of_faithful e.functor⟩

instance (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] [LocallySmall.{w'} C] :
    LocallySmall.{w'} (SmallModel.{w} C) :=
  (locallySmall_congr (equivSmallModel.{w} C)).1 inferInstance

instance (priority := 100) locallySmall_self (C : Type u) [Category.{v} C] :
    LocallySmall.{v} C where

instance (priority := 100) locallySmall_of_univLE (C : Type u) [Category.{v} C] [UnivLE.{v, w}] :
    LocallySmall.{w} C where

theorem locallySmall_max {C : Type u} [Category.{v} C] : LocallySmall.{max v w} C where
  hom_small _ _ := small_max.{w} _

instance (priority := 100) locallySmall_of_essentiallySmall (C : Type u) [Category.{v} C]
    [EssentiallySmall.{w} C] : LocallySmall.{w} C :=
  (locallySmall_congr (equivSmallModel C)).mpr (CategoryTheory.locallySmall_self _)

/-- We define a type alias `ShrinkHoms C` for `C`. When we have `LocallySmall.{w} C`,
we'll put a `Category.{w}` instance on `ShrinkHoms C`.
-/
@[pp_with_univ]
def ShrinkHoms (C : Type u) :=
  C

namespace ShrinkHoms

section

variable {C' : Type*}

-- a fresh variable with no category instance attached
/-- Help the typechecker by explicitly translating from `C` to `ShrinkHoms C`. -/
def toShrinkHoms {C' : Type*} (X : C') : ShrinkHoms C' :=
  X

/-- Help the typechecker by explicitly translating from `ShrinkHoms C` to `C`. -/
def fromShrinkHoms {C' : Type*} (X : ShrinkHoms C') : C' :=
  X

@[simp]
theorem to_from (X : C') : fromShrinkHoms (toShrinkHoms X) = X :=
  rfl

@[simp]
theorem from_to (X : ShrinkHoms C') : toShrinkHoms (fromShrinkHoms X) = X :=
  rfl

end

variable [LocallySmall.{w} C]

@[simps]
noncomputable instance : Category.{w} (ShrinkHoms C) where
  Hom X Y := Shrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)
  id X := equivShrink _ (𝟙 (fromShrinkHoms X))
  comp f g := equivShrink _ ((equivShrink _).symm f ≫ (equivShrink _).symm g)

set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `ShrinkHoms.equivalence`. -/
@[simps]
noncomputable def functor : C ⥤ ShrinkHoms C where
  obj X := toShrinkHoms X
  map {X Y} f := equivShrink (X ⟶ Y) f

/-- Implementation of `ShrinkHoms.equivalence`. -/
@[simps]
noncomputable def inverse : ShrinkHoms C ⥤ C where
  obj X := fromShrinkHoms X
  map {X Y} f := (equivShrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)).symm f

set_option backward.isDefEq.respectTransparency false in
/-- The categorical equivalence between `C` and `ShrinkHoms C`, when `C` is locally small.
-/
@[simps]
noncomputable def equivalence : C ≌ ShrinkHoms C where
  functor := functor C
  inverse := inverse C
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

instance : (functor C).IsEquivalence := (equivalence C).isEquivalence_functor
instance : (inverse C).IsEquivalence := (equivalence C).isEquivalence_inverse

instance {T : Type u} [Unique T] : Unique (ShrinkHoms.{u} T) where
  default := ShrinkHoms.toShrinkHoms (default : T)
  uniq _ := congr_arg ShrinkHoms.fromShrinkHoms (Unique.uniq _ _)

instance {T : Type u} [Category.{v} T] [IsDiscrete T] : IsDiscrete (ShrinkHoms.{u} T) where
  subsingleton _ _ := { allEq _ _ := Shrink.ext (Subsingleton.elim _ _) }
  eq_of_hom f := IsDiscrete.eq_of_hom (C := T) ((equivShrink _).symm f)

end ShrinkHoms

namespace Shrink

noncomputable instance [Small.{w} C] : Category.{v} (Shrink.{w} C) :=
  inferInstanceAs (Category (InducedCategory _ (equivShrink C).symm))

/-- The categorical equivalence between `C` and `Shrink C`, when `C` is small. -/
noncomputable def equivalence [Small.{w} C] : C ≌ Shrink.{w} C :=
  (Equivalence.induced _).symm

instance [Small.{w'} C] [LocallySmall.{w} C] :
    LocallySmall.{w} (Shrink.{w'} C) :=
  locallySmall_of_faithful.{w} (equivalence.{w'} C).inverse

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
    exact ⟨⟨InducedCategory _ (e'.trans e).symm, inferInstance,
      ⟨(ShrinkHoms.equivalence C).trans
      ((skeletonEquivalence (ShrinkHoms C)).symm.trans
      (inducedFunctor _).asEquivalence.symm)⟩⟩⟩

instance essentiallySmall_of_small_of_locallySmall [Small.{w} C] [LocallySmall.{w} C] :
    EssentiallySmall.{w} C :=
  (essentiallySmall_iff C).2 ⟨small_of_surjective Quotient.exists_rep, by infer_instance⟩

example (C : Type w) [SmallCategory C] : EssentiallySmall.{w} C := inferInstance

instance small_skeleton_of_essentiallySmall [h : EssentiallySmall.{w} C] : Small.{w} (Skeleton C) :=
  essentiallySmall_iff C |>.1 h |>.1

variable {C} in
theorem essentiallySmall_of_fully_faithful {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    [F.Full] [F.Faithful] [EssentiallySmall.{w} D] : EssentiallySmall.{w} C :=
  (essentiallySmall_iff C).2 ⟨small_of_injective F.mapSkeleton_injective,
    locallySmall_of_faithful F⟩

section FullSubcategory

instance locallySmall_fullSubcategory [LocallySmall.{w} C] (P : ObjectProperty C) :
    LocallySmall.{w} P.FullSubcategory :=
  locallySmall_of_faithful <| P.ι

instance essentiallySmall_fullSubcategory_mem (s : Set C) [Small.{w} s] [LocallySmall.{w} C] :
    EssentiallySmall.{w} (ObjectProperty.FullSubcategory (· ∈ s)) :=
  suffices Small.{w} (ObjectProperty.FullSubcategory (· ∈ s)) from
    essentiallySmall_of_small_of_locallySmall _
  small_of_injective (f := fun x => (⟨x.1, x.2⟩ : s)) (by cat_disch)

end FullSubcategory

/-- Any thin category is locally small.
-/
instance (priority := 100) locallySmall_of_thin {C : Type u} [Category.{v} C] [Quiver.IsThin C] :
    LocallySmall.{w} C where

/--
A thin category is essentially small if and only if the underlying type of its skeleton is small.
-/
theorem essentiallySmall_iff_of_thin {C : Type u} [Category.{v} C] [Quiver.IsThin C] :
    EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) := by
  simp [essentiallySmall_iff, CategoryTheory.locallySmall_of_thin]

instance [Small.{w} C] : Small.{w} (Discrete C) := small_map discreteEquiv

instance [Small.{w} C] [LocallySmall.{w} C] :
    Small.{w} (Arrow C) := by
  let φ (f : Arrow C) : Σ (s t : C), s ⟶ t := ⟨_, _, f.hom⟩
  refine small_of_injective (f := φ) ?_
  rintro ⟨s, t, f⟩ ⟨s', t', f'⟩ h
  obtain rfl : s = s' := congr_arg Sigma.fst h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and, φ] at h
  obtain rfl : t = t' := h.1
  obtain rfl : f = f' := by simpa using h
  rfl

instance [Small.{w} C] [LocallySmall.{w} C]
    {D : Type u'} [Category.{v'} D] [Small.{w} D] [LocallySmall.{w} D] :
    Small.{w} (C ⥤ D) := by
  refine small_of_injective (f := fun F (f : Arrow C) ↦ Arrow.mk (F.map f.hom))
    (fun F G h ↦ Functor.ext (fun X ↦ ?_) (fun X Y f ↦ ?_))
  · exact congr_arg Comma.left (congr_fun h (Arrow.mk (𝟙 X)))
  · have : Arrow.mk (F.map f) = Arrow.mk (G.map f) := congr_fun h (Arrow.mk f)
    rw [Arrow.mk_eq_mk_iff] at this
    tauto

instance {A : Type u'} [Category.{v'} A] [LocallySmall.{w} A] (C : Type w) [SmallCategory C] :
    LocallySmall.{w} (C ⥤ A) where
  hom_small P Q :=
    small_of_injective (f := NatTrans.app) (fun f g h ↦ by aesop)

end CategoryTheory
