/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module category_theory.limits.cone_category
! leanprover-community/mathlib commit 18302a460eb6a071cf0bfe11a4df025c8f8af244
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.Comma
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathbin.CategoryTheory.StructuredArrow
import Mathbin.CategoryTheory.Limits.Shapes.Equivalence

/-!
# Limits and the category of (co)cones

This files contains results that stem from the limit API. For the definition and the category
instance of `cone`, please refer to `category_theory/limits/cones.lean`.

## Main results
* The category of cones on `F : J ⥤ C` is equivalent to the category
  `costructured_arrow (const J) F`.
* A cone is limiting iff it is terminal in the category of cones. As a corollary, an equivalence of
  categories of cones preserves limiting properties.

-/


namespace CategoryTheory.Limits

open CategoryTheory CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]

variable {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

/-- Construct an object of the category `(Δ ↓ F)` from a cone on `F`. This is part of an
    equivalence, see `cone.equiv_costructured_arrow`. -/
@[simps]
def Cone.toCostructuredArrow (F : J ⥤ C) : Cone F ⥤ CostructuredArrow (const J) F
    where
  obj c := CostructuredArrow.mk c.π
  map c d f :=
    CostructuredArrow.homMk f.Hom <| by
      ext
      simp
#align category_theory.limits.cone.to_costructured_arrow CategoryTheory.Limits.Cone.toCostructuredArrow

/-- Construct a cone on `F` from an object of the category `(Δ ↓ F)`. This is part of an
    equivalence, see `cone.equiv_costructured_arrow`. -/
@[simps]
def Cone.fromCostructuredArrow (F : J ⥤ C) : CostructuredArrow (const J) F ⥤ Cone F
    where
  obj c := ⟨c.left, c.Hom⟩
  map c d f :=
    { Hom := f.left
      w' := fun j => by
        convert congr_fun (congr_arg nat_trans.app f.w) j
        dsimp
        simp }
#align category_theory.limits.cone.from_costructured_arrow CategoryTheory.Limits.Cone.fromCostructuredArrow

/-- The category of cones on `F` is just the comma category `(Δ ↓ F)`, where `Δ` is the constant
    functor. -/
@[simps]
def Cone.equivCostructuredArrow (F : J ⥤ C) : Cone F ≌ CostructuredArrow (const J) F :=
  Equivalence.mk (Cone.toCostructuredArrow F) (Cone.fromCostructuredArrow F)
    (NatIso.ofComponents Cones.eta (by tidy))
    (NatIso.ofComponents (fun c => (CostructuredArrow.eta _).symm) (by tidy))
#align category_theory.limits.cone.equiv_costructured_arrow CategoryTheory.Limits.Cone.equivCostructuredArrow

/-- A cone is a limit cone iff it is terminal. -/
def Cone.isLimitEquivIsTerminal {F : J ⥤ C} (c : Cone F) : IsLimit c ≃ IsTerminal c :=
  IsLimit.isoUniqueConeMorphism.toEquiv.trans
    { toFun := fun h => is_terminal.of_unique _
      invFun := fun h s => ⟨⟨IsTerminal.from h s⟩, fun a => IsTerminal.hom_ext h a _⟩
      left_inv := by tidy
      right_inv := by tidy }
#align category_theory.limits.cone.is_limit_equiv_is_terminal CategoryTheory.Limits.Cone.isLimitEquivIsTerminal

theorem hasLimit_iff_hasTerminal_cone (F : J ⥤ C) : HasLimit F ↔ HasTerminal (Cone F) :=
  ⟨fun h => (cone.is_limit_equiv_is_terminal _ (limit.is_limit F)).HasTerminal, fun h =>
    ⟨⟨⟨⊤_ _, (cone.is_limit_equiv_is_terminal _).symm terminal_is_terminal⟩⟩⟩⟩
#align category_theory.limits.has_limit_iff_has_terminal_cone CategoryTheory.Limits.hasLimit_iff_hasTerminal_cone

theorem hasLimitsOfShape_iff_isLeftAdjoint_const :
    HasLimitsOfShape J C ↔ Nonempty (IsLeftAdjoint (const J : C ⥤ _)) :=
  calc
    HasLimitsOfShape J C ↔ ∀ F : J ⥤ C, HasLimit F :=
      ⟨fun h => h.HasLimit, fun h => has_limits_of_shape.mk⟩
    _ ↔ ∀ F : J ⥤ C, HasTerminal (Cone F) := (forall_congr' hasLimit_iff_hasTerminal_cone)
    _ ↔ ∀ F : J ⥤ C, HasTerminal (CostructuredArrow (const J) F) :=
      (forall_congr' fun F => (Cone.equivCostructuredArrow F).hasTerminal_iff)
    _ ↔ Nonempty (IsLeftAdjoint (const J : C ⥤ _)) :=
      nonempty_isLeftAdjoint_iff_hasTerminal_costructuredArrow.symm
    
#align category_theory.limits.has_limits_of_shape_iff_is_left_adjoint_const CategoryTheory.Limits.hasLimitsOfShape_iff_isLeftAdjoint_const

theorem IsLimit.liftConeMorphism_eq_isTerminal_from {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
    (s : Cone F) : hc.liftConeMorphism s = IsTerminal.from (Cone.isLimitEquivIsTerminal _ hc) _ :=
  rfl
#align category_theory.limits.is_limit.lift_cone_morphism_eq_is_terminal_from CategoryTheory.Limits.IsLimit.liftConeMorphism_eq_isTerminal_from

theorem IsTerminal.from_eq_liftConeMorphism {F : J ⥤ C} {c : Cone F} (hc : IsTerminal c)
    (s : Cone F) :
    IsTerminal.from hc s = ((Cone.isLimitEquivIsTerminal _).symm hc).liftConeMorphism s := by
  convert (is_limit.lift_cone_morphism_eq_is_terminal_from _ s).symm
#align category_theory.limits.is_terminal.from_eq_lift_cone_morphism CategoryTheory.Limits.IsTerminal.from_eq_liftConeMorphism

/-- If `G : cone F ⥤ cone F'` preserves terminal objects, it preserves limit cones. -/
def IsLimit.ofPreservesConeTerminal {F : J ⥤ C} {F' : K ⥤ D} (G : Cone F ⥤ Cone F')
    [PreservesLimit (Functor.empty.{0} _) G] {c : Cone F} (hc : IsLimit c) : IsLimit (G.obj c) :=
  (Cone.isLimitEquivIsTerminal _).symm <| (Cone.isLimitEquivIsTerminal _ hc).isTerminalObj _ _
#align category_theory.limits.is_limit.of_preserves_cone_terminal CategoryTheory.Limits.IsLimit.ofPreservesConeTerminal

/-- If `G : cone F ⥤ cone F'` reflects terminal objects, it reflects limit cones. -/
def IsLimit.ofReflectsConeTerminal {F : J ⥤ C} {F' : K ⥤ D} (G : Cone F ⥤ Cone F')
    [ReflectsLimit (Functor.empty.{0} _) G] {c : Cone F} (hc : IsLimit (G.obj c)) : IsLimit c :=
  (Cone.isLimitEquivIsTerminal _).symm <| (Cone.isLimitEquivIsTerminal _ hc).isTerminalOfObj _ _
#align category_theory.limits.is_limit.of_reflects_cone_terminal CategoryTheory.Limits.IsLimit.ofReflectsConeTerminal

/-- Construct an object of the category `(F ↓ Δ)` from a cocone on `F`. This is part of an
    equivalence, see `cocone.equiv_structured_arrow`. -/
@[simps]
def Cocone.toStructuredArrow (F : J ⥤ C) : Cocone F ⥤ StructuredArrow F (const J)
    where
  obj c := StructuredArrow.mk c.ι
  map c d f :=
    StructuredArrow.homMk f.Hom <| by
      ext
      simp
#align category_theory.limits.cocone.to_structured_arrow CategoryTheory.Limits.Cocone.toStructuredArrow

/-- Construct a cocone on `F` from an object of the category `(F ↓ Δ)`. This is part of an
    equivalence, see `cocone.equiv_structured_arrow`. -/
@[simps]
def Cocone.fromStructuredArrow (F : J ⥤ C) : StructuredArrow F (const J) ⥤ Cocone F
    where
  obj c := ⟨c.right, c.Hom⟩
  map c d f :=
    { Hom := f.right
      w' := fun j => by
        convert (congr_fun (congr_arg nat_trans.app f.w) j).symm
        dsimp
        simp }
#align category_theory.limits.cocone.from_structured_arrow CategoryTheory.Limits.Cocone.fromStructuredArrow

/-- The category of cocones on `F` is just the comma category `(F ↓ Δ)`, where `Δ` is the constant
    functor. -/
@[simps]
def Cocone.equivStructuredArrow (F : J ⥤ C) : Cocone F ≌ StructuredArrow F (const J) :=
  Equivalence.mk (Cocone.toStructuredArrow F) (Cocone.fromStructuredArrow F)
    (NatIso.ofComponents Cocones.eta (by tidy))
    (NatIso.ofComponents (fun c => (StructuredArrow.eta _).symm) (by tidy))
#align category_theory.limits.cocone.equiv_structured_arrow CategoryTheory.Limits.Cocone.equivStructuredArrow

/-- A cocone is a colimit cocone iff it is initial. -/
def Cocone.isColimitEquivIsInitial {F : J ⥤ C} (c : Cocone F) : IsColimit c ≃ IsInitial c :=
  IsColimit.isoUniqueCoconeMorphism.toEquiv.trans
    { toFun := fun h => is_initial.of_unique _
      invFun := fun h s => ⟨⟨IsInitial.to h s⟩, fun a => IsInitial.hom_ext h a _⟩
      left_inv := by tidy
      right_inv := by tidy }
#align category_theory.limits.cocone.is_colimit_equiv_is_initial CategoryTheory.Limits.Cocone.isColimitEquivIsInitial

theorem hasColimit_iff_hasInitial_cocone (F : J ⥤ C) : HasColimit F ↔ HasInitial (Cocone F) :=
  ⟨fun h => (cocone.is_colimit_equiv_is_initial _ (colimit.is_colimit F)).HasInitial, fun h =>
    ⟨⟨⟨⊥_ _, (cocone.is_colimit_equiv_is_initial _).symm initial_is_initial⟩⟩⟩⟩
#align category_theory.limits.has_colimit_iff_has_initial_cocone CategoryTheory.Limits.hasColimit_iff_hasInitial_cocone

theorem hasColimitsOfShape_iff_isRightAdjoint_const :
    HasColimitsOfShape J C ↔ Nonempty (IsRightAdjoint (const J : C ⥤ _)) :=
  calc
    HasColimitsOfShape J C ↔ ∀ F : J ⥤ C, HasColimit F :=
      ⟨fun h => h.HasColimit, fun h => has_colimits_of_shape.mk⟩
    _ ↔ ∀ F : J ⥤ C, HasInitial (Cocone F) := (forall_congr' hasColimit_iff_hasInitial_cocone)
    _ ↔ ∀ F : J ⥤ C, HasInitial (StructuredArrow F (const J)) :=
      (forall_congr' fun F => (Cocone.equivStructuredArrow F).hasInitial_iff)
    _ ↔ Nonempty (IsRightAdjoint (const J : C ⥤ _)) :=
      nonempty_isRightAdjoint_iff_hasInitial_structuredArrow.symm
    
#align category_theory.limits.has_colimits_of_shape_iff_is_right_adjoint_const CategoryTheory.Limits.hasColimitsOfShape_iff_isRightAdjoint_const

theorem IsColimit.descCoconeMorphism_eq_isInitial_to {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    (s : Cocone F) :
    hc.descCoconeMorphism s = IsInitial.to (Cocone.isColimitEquivIsInitial _ hc) _ :=
  rfl
#align category_theory.limits.is_colimit.desc_cocone_morphism_eq_is_initial_to CategoryTheory.Limits.IsColimit.descCoconeMorphism_eq_isInitial_to

theorem IsInitial.to_eq_descCoconeMorphism {F : J ⥤ C} {c : Cocone F} (hc : IsInitial c)
    (s : Cocone F) :
    IsInitial.to hc s = ((Cocone.isColimitEquivIsInitial _).symm hc).descCoconeMorphism s := by
  convert (is_colimit.desc_cocone_morphism_eq_is_initial_to _ s).symm
#align category_theory.limits.is_initial.to_eq_desc_cocone_morphism CategoryTheory.Limits.IsInitial.to_eq_descCoconeMorphism

/-- If `G : cocone F ⥤ cocone F'` preserves initial objects, it preserves colimit cocones. -/
def IsColimit.ofPreservesCoconeInitial {F : J ⥤ C} {F' : K ⥤ D} (G : Cocone F ⥤ Cocone F')
    [PreservesColimit (Functor.empty.{0} _) G] {c : Cocone F} (hc : IsColimit c) :
    IsColimit (G.obj c) :=
  (Cocone.isColimitEquivIsInitial _).symm <| (Cocone.isColimitEquivIsInitial _ hc).isInitialObj _ _
#align category_theory.limits.is_colimit.of_preserves_cocone_initial CategoryTheory.Limits.IsColimit.ofPreservesCoconeInitial

/-- If `G : cocone F ⥤ cocone F'` reflects initial objects, it reflects colimit cocones. -/
def IsColimit.ofReflectsCoconeInitial {F : J ⥤ C} {F' : K ⥤ D} (G : Cocone F ⥤ Cocone F')
    [ReflectsColimit (Functor.empty.{0} _) G] {c : Cocone F} (hc : IsColimit (G.obj c)) :
    IsColimit c :=
  (Cocone.isColimitEquivIsInitial _).symm <|
    (Cocone.isColimitEquivIsInitial _ hc).isInitialOfObj _ _
#align category_theory.limits.is_colimit.of_reflects_cocone_initial CategoryTheory.Limits.IsColimit.ofReflectsCoconeInitial

end CategoryTheory.Limits

