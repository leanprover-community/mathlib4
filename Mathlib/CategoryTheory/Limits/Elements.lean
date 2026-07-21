/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Limits in the category of elements

We show that if `C` has limits of shape `I` and `A : C ⥤ Type w` preserves limits of shape `I`, then
the category of elements of `A` has limits of shape `I` and the forgetful functor
`π : A.Elements ⥤ C` creates them.

## Further results

- If `A` is (co)representable, then `A.Elements` has an initial object.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe w v₁ v u₁ u

namespace CategoryTheory

open Limits Opposite ConcreteCategory

variable {C : Type u} [Category.{v} C]

namespace CategoryOfElements

variable {A : C ⥤ Type w} {I : Type u₁} [Category.{v₁} I] [Small.{w} I]

namespace CreatesLimitsAux

variable (F : I ⥤ A.Elements)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (implementation) A system `(Fi, fi)_i` of elements induces an element in `lim_i A(Fi)`. -/
noncomputable def liftedConeElement' : limit ((F ⋙ π A) ⋙ A) :=
  Types.Limit.mk _ (fun i => (F.obj i).2) (by simp)

@[simp]
lemma π_liftedConeElement' (i : I) :
    dsimp% limit.π ((F ⋙ π A) ⋙ A) i (liftedConeElement' F) = (F.obj i).2 :=
  Types.Limit.π_mk _ _ _ _

variable [HasLimitsOfShape I C] [PreservesLimitsOfShape I A]

/-- (implementation) A system `(Fi, fi)_i` of elements induces an element in `A(lim_i Fi)`. -/
noncomputable def liftedConeElement : A.obj (limit (F ⋙ π A)) :=
  (preservesLimitIso A (F ⋙ π A)).inv (liftedConeElement' F)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma map_lift_mapCone (c : Cone F) :
    dsimp% A.map (limit.lift (F ⋙ π A) ((π A).mapCone c)) c.pt.snd = liftedConeElement F := by
  apply (preservesLimitIso A (F ⋙ π A)).toEquiv.injective
  ext i
  have h₁ := congr_hom (preservesLimitIso_hom_π A (F ⋙ π A) i)
    (A.map (limit.lift (F ⋙ π A) ((π A).mapCone c)) c.pt.snd)
  have h₂ := (c.π.app i).property
  simpa [-Functor.comp_obj, ← comp_apply, ← Functor.map_comp, liftedConeElement, liftedConeElement']

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma map_π_liftedConeElement (i : I) :
    dsimp% A.map (limit.π (F ⋙ π A) i) (liftedConeElement F) = (F.obj i).snd := by
  have := congr_hom
    (preservesLimitIso_inv_π A (F ⋙ π A) i) (liftedConeElement' F)
  simp [liftedConeElement, ← comp_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-- (implementation) The constructed limit cone. -/
@[simps]
noncomputable def liftedCone : Cone F where
  pt := ⟨_, liftedConeElement F⟩
  π :=
    { app := fun i => ⟨limit.π (F ⋙ π A) i, by simpa using! map_π_liftedConeElement _ _⟩
      naturality := fun i i' f => by ext; simpa using! (limit.w _ _).symm }

set_option backward.isDefEq.respectTransparency.types false in
/-- (implementation) The constructed limit cone is a lift of the limit cone in `C`. -/
noncomputable def isValidLift : (π A).mapCone (liftedCone F) ≅ limit.cone (F ⋙ π A) :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- (implementation) The constructed limit cone is a limit cone. -/
noncomputable def isLimit : IsLimit (liftedCone F) where
  lift s := ⟨limit.lift (F ⋙ π A) ((π A).mapCone s), by simp⟩
  uniq s m h := ext _ _ _ <| limit.hom_ext
    fun i => by simpa using congrArg Subtype.val (h i)

end CreatesLimitsAux

variable [HasLimitsOfShape I C] [PreservesLimitsOfShape I A]

section

open CreatesLimitsAux

noncomputable instance (F : I ⥤ A.Elements) : CreatesLimit F (π A) :=
  createsLimitOfReflectsIso' (limit.isLimit _) ⟨⟨liftedCone F, isValidLift F⟩, isLimit F⟩

end

noncomputable instance : CreatesLimitsOfShape I (π A) where

instance : HasLimitsOfShape I A.Elements :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (π A)

section Initial

instance {F : Cᵒᵖ ⥤ Type*} [F.IsRepresentable] : HasInitial F.Elements :=
  (Functor.Elements.isInitialOfRepresentableBy F.representableBy).hasInitial

instance {F : C ⥤ Type*} [F.IsCorepresentable] : HasInitial F.Elements :=
  (Functor.Elements.isInitialOfCorepresentableBy F.corepresentableBy).hasInitial

end Initial

end CategoryOfElements

namespace Functor

/-- An initial object in the category `F.Elements` of a covariant functor defines a
corepresentation for that functor. -/
def CorepresentableBy.ofIsInitial {F : C ⥤ Type v} (E : Elements F) (he : IsInitial E) :
    CorepresentableBy F E.fst where
      homEquiv := by
        intro Y
        refine {
          toFun f := F.map f E.snd
          invFun y := (he.to ⟨Y, y⟩).1
          left_inv f := by
              have := he.hom_ext (he.to ⟨Y, F.map f E.snd⟩) ⟨f, rfl⟩
              simpa using congrArg (fun m => m.1) this
          right_inv y := (he.to ⟨Y, y⟩).2
        }
      homEquiv_comp := by
        intro Y Y' g f
        simp only [Equiv.coe_fn_mk, Functor.map_comp_apply]

instance (F : C ⥤ Type v) [HasInitial (Elements F)] :
    IsCorepresentable F where
      has_corepresentation :=
        ⟨(⊥_ F.Elements).fst,
          (Nonempty.intro (CorepresentableBy.ofIsInitial (⊥_ F.Elements) initialIsInitial))⟩

theorem isCorepresentable_iff_hasInitial (F : C ⥤ Type v) :
    HasInitial (Elements F) ↔ IsCorepresentable F where
      mp _ := inferInstance
      mpr _ := inferInstance

/-- An initial object in the category `F.Elements` of a contravariant functor defines a
representation for that functor. -/
def RepresentableBy.ofIsInitial {F : Cᵒᵖ ⥤ Type v} (E : Elements F) (he : IsInitial E) :
    RepresentableBy F (E.fst.unop) where
      homEquiv := by
        intro Y
        refine {
          toFun f := F.map f.op E.snd
          invFun y := (he.to ⟨op Y, y⟩).1.unop
          left_inv f := by
            have := he.hom_ext (he.to ⟨op Y, F.map f.op E.snd⟩) ⟨f.op, rfl⟩
            simpa using congrArg (fun m => m.1.unop) this
          right_inv y := (he.to ⟨op Y, y⟩).2
        }
      homEquiv_comp := by
        intro Y Y' g f
        sorry

instance (F : Cᵒᵖ ⥤ Type v) [HasInitial (Elements F)] :
    IsRepresentable F where
      has_representation :=
        ⟨(⊥_ F.Elements).fst.unop,
          (Nonempty.intro (RepresentableBy.ofIsInitial (⊥_ F.Elements) initialIsInitial))⟩

theorem isRepresentable_iff_hasInitial (F : Cᵒᵖ ⥤ Type v) :
    HasInitial (Elements F) ↔ IsCorepresentable F where
      mp _ := inferInstance
      mpr _ := inferInstance

end Functor

end CategoryTheory
