/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
-- import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Limits in the category of elements

We show that if `C` has limits of shape `I` and `A : C ⥤ Type w` preserves limits of shape `I`, then
the category of elements of `A` has limits of shape `I` and the forgetful functor
`π : A.Elements ⥤ C` creates them.

-/

universe w v₁ v u₁ u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

namespace CategoryOfElements

variable {A : C ⥤ Type w} {I : Type u₁} [Category.{v₁} I] [Small.{w} I] [HasLimitsOfShape I C]
  [PreservesLimitsOfShape I A]

namespace CreatesLimitsAux

variable (F : I ⥤ A.Elements)

/-- (implementation) A system `(Fi, fi)_i` of elements induces an element in `lim_i A(Fi)`. -/
noncomputable def liftedConeElement' : limit ((F ⋙ π A) ⋙ A) :=
  Types.Limit.mk _ (fun i => (F.obj i).2) (by simp)

@[simp]
lemma π_liftedConeElement' (i : I) :
    limit.π ((F ⋙ π A) ⋙ A) i (liftedConeElement' F) = (F.obj i).2 :=
  Types.Limit.π_mk _ _ _ _

/-- (implementation) A system `(Fi, fi)_i` of elements induces an element in `A(lim_i Fi)`.-/
noncomputable def liftedConeElement : A.obj (limit (F ⋙ π A)) :=
  (preservesLimitIso A (F ⋙ π A)).inv (liftedConeElement' F)

@[simp]
lemma map_lift_mapCone (c : Cone F) :
    A.map (limit.lift (F ⋙ π A) ((π A).mapCone c)) c.pt.snd = liftedConeElement F := by
  apply (preservesLimitIso A (F ⋙ π A)).toEquiv.injective
  ext i
  have h₁ := congrFun (preservesLimitsIso_hom_π A (F ⋙ π A) i)
    (A.map (limit.lift (F ⋙ π A) ((π A).mapCone c)) c.pt.snd)
  have h₂ := (c.π.app i).property
  simp_all [← FunctorToTypes.map_comp_apply, liftedConeElement]

@[simp]
lemma map_π_liftedConeElement (i : I) :
    A.map (limit.π (F ⋙ π A) i) (liftedConeElement F) = (F.obj i).snd := by
  have := congrFun
    (preservesLimitsIso_inv_π A (F ⋙ π A) i) (liftedConeElement' F)
  simp_all [liftedConeElement]

/-- (implementation) The constructured limit cone. -/
@[simps]
noncomputable def liftedCone : Cone F where
  pt := ⟨_, liftedConeElement F⟩
  π :=
    { app := fun i => ⟨limit.π (F ⋙ π A) i, by simp⟩
      naturality := fun i i' f => by ext; simpa using (limit.w _ _).symm }

/-- (implementation) The constructed limit cone is a lift of the limit cone in `C`. -/
noncomputable def isValidLift : (π A).mapCone (liftedCone F) ≅ limit.cone (F ⋙ π A) :=
  Iso.refl _

/-- (implementation) The constuctured limit cone is a limit cone. -/
noncomputable def isLimit : IsLimit (liftedCone F) where
  lift s := ⟨limit.lift (F ⋙ π A) ((π A).mapCone s), by simp⟩
  uniq s m h := ext _ _ _ <| limit.hom_ext
    fun i => by simpa using congrArg Subtype.val (h i)

end CreatesLimitsAux

section

open CreatesLimitsAux

noncomputable instance (F : I ⥤ A.Elements) : CreatesLimit F (π A) :=
  createsLimitOfReflectsIso' (limit.isLimit _) ⟨⟨liftedCone F, isValidLift F⟩, isLimit F⟩

end

noncomputable instance : CreatesLimitsOfShape I (π A) where

instance : HasLimitsOfShape I A.Elements :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (π A)

end CategoryOfElements

section Presheaf

variable {A : Cᵒᵖ ⥤ Type v}

section

variable {I : Type u₁} [Category.{v₁} I] [Small.{v} I] [HasColimitsOfShape I C]
  [PreservesLimitsOfShape Iᵒᵖ A]

open CategoryOfElements

instance : Small.{v} Iᵒᵖ :=
  small_map equivToOpposite.symm

noncomputable instance (F : I ⥤ CostructuredArrow yoneda A) :
    CreatesColimit F (CostructuredArrow.proj yoneda A) := by
  suffices CreatesColimit F ((costructuredArrowYonedaEquivalence A).inverse ⋙ (π A).leftOp) from
    createsColimitOfNatIso (costructuredArrowYonedaEquivalenceCompπ A)
  suffices CreatesColimit (F ⋙ (costructuredArrowYonedaEquivalence A).inverse) (π A).leftOp from
    compCreatesColimit _ _
  suffices CreatesLimit (F ⋙ (costructuredArrowYonedaEquivalence A).inverse).leftOp (π A) from
    createsColimitLeftOp _ _
  have : HasColimitsOfShape Iᵒᵖᵒᵖ C := hasColimitsOfShape_of_equivalence (opOpEquivalence I).symm
  have : HasLimitsOfShape Iᵒᵖ Cᵒᵖ := hasLimitsOfShape_op_of_hasColimitsOfShape
  infer_instance

noncomputable instance : CreatesColimitsOfShape I (CostructuredArrow.proj yoneda A) where

instance : HasColimitsOfShape I (CostructuredArrow yoneda A) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (CostructuredArrow.proj yoneda A)

end

theorem isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits [HasFiniteColimits C]
    [PreservesFiniteLimits A] : IsFiltered (CostructuredArrow yoneda A) := by
  have : HasFiniteColimits (CostructuredArrow yoneda A) :=
    { out := fun J _ _ => inferInstance }
  apply IsFiltered.of_hasFiniteColimits

end Presheaf

end CategoryTheory
