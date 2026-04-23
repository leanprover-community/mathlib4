/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Limits in the category of elements

We show that if `C` has limits of shape `I` and `A : C ⥤ Type w` preserves limits of shape `I`, then
the category of elements of `A` has limits of shape `I` and the forgetful functor
`π : A.Elements ⥤ C` creates them.

## Further results

- If `A` is (co)representable, then `A.Elements` has an initial object.

## TODOs

- Show that `A` is (co)representable if `A.Elements` has an initial object.

-/

@[expose] public section

universe w v₁ v u₁ u

namespace CategoryTheory

open Limits Opposite ConcreteCategory

variable {C : Type u} [Category.{v} C]

namespace CategoryOfElements

variable {A : C ⥤ Type w} {I : Type u₁} [Category.{v₁} I] [Small.{w} I]

namespace CreatesLimitsAux

variable (F : I ⥤ A.Elements)

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

/-- (implementation) The constructed limit cone. -/
@[simps]
noncomputable def liftedCone : Cone F where
  pt := ⟨_, liftedConeElement F⟩
  π :=
    { app := fun i => ⟨limit.π (F ⋙ π A) i, by simpa using map_π_liftedConeElement _ _⟩
      naturality := fun i i' f => by ext; simpa using (limit.w _ _).symm }

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

end CategoryTheory
