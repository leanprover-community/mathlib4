/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.Action.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite

/-!

# Actions from the monoidal opposite of a category.

In this file, given a monoidal category `C` and a category `D`,
we construct a left `C`-action on `D` out of the data of a right `Cᴹᵒᵖ`-action
on `D`. We also construct a right `C`-action on `D`from the data of a left
`Cᴹᵒᵖ`-action on `D`. Conversely, given left/right `C`-actions on `D`,
we construct a`Cᴹᵒᵖ` actions with the conjugate variance.

These constructions are not made instances in order to avoid instance loops,
you should bring them as local instances if you intend to use them.

-/

namespace CategoryTheory.MonoidalCategory

variable (C D : Type*)

variable [Category C] [MonoidalCategory C] [Category D]

namespace MonoidalLeftAction
open scoped MonoidalLeftAction MonoidalRightAction
open MonoidalOpposite


/-- Define a left action of `C` on `D` from a right action of `Cᴹᵒᵖ` on `D` via
the formula `c ⊙ₗ d := d ⊙ᵣ (mop c)`. -/
@[simps -isSimp]
def leftActionOfMonoidalOppositeRightAction [MonoidalRightAction Cᴹᵒᵖ D] :
    MonoidalLeftAction C D where
  actionObj c d := d ⊙ᵣ mop c
  actionHomLeft {c c'} f d := d ⊴ᵣ f.mop
  actionHomRight c {d d'} f := f ⊵ᵣ mop c
  actionHom {c c'} {d d} f g := g ⊙ᵣₘ f.mop
  actionAssocIso _ _ _ := αᵣ _ _ _
  actionUnitIso _ := ρᵣ _
  actionHom_def _ _ := MonoidalRightAction.actionHom_def' _ _
  actionAssocIso_hom_naturality _ _ _ :=
    MonoidalRightAction.actionAssocIso_hom_naturality _ _ _
  actionUnitIso_hom_naturality _ :=
    MonoidalRightAction.actionUnitIso_hom_naturality _
  rightUnitor_actionHom c d :=
    MonoidalRightAction.actionHom_leftUnitor _ _
  associator_actionHom c₁ c₂ c₃ d := by
    simpa only [mop_tensorObj, mop_hom_associator,
      MonoidalRightAction.actionHomRight_inv_hom_assoc] using
      (d ⊴ᵣ (α_ (mop c₃) (mop c₂) (mop c₁)).inv) ≫=
        MonoidalRightAction.actionHom_associator
          (mop c₃) (mop c₂) (mop c₁) d|>.symm

/-- Define a left action of `Cᴹᵒᵖ` on `D` from a right action of `C` on `D` via
the formula `mop c ⊙ₗ d = d ⊙ᵣ c`. -/
@[simps -isSimp]
def monoidalOppositeLeftAction [MonoidalRightAction C D] :
    MonoidalLeftAction Cᴹᵒᵖ D where
  actionObj c d := d ⊙ᵣ unmop c
  actionHomLeft {c c'} f d := d ⊴ᵣ f.unmop
  actionHomRight c {d d'} f := f ⊵ᵣ unmop c
  actionHom {c c'} {d d} f g := g ⊙ᵣₘ f.unmop
  actionAssocIso _ _ _ := αᵣ _ _ _
  actionUnitIso _ := ρᵣ _
  actionHom_def _ _ := MonoidalRightAction.actionHom_def' _ _
  actionAssocIso_hom_naturality _ _ _ :=
    MonoidalRightAction.actionAssocIso_hom_naturality _ _ _
  actionUnitIso_hom_naturality _ :=
    MonoidalRightAction.actionUnitIso_hom_naturality _
  rightUnitor_actionHom c d :=
    MonoidalRightAction.actionHom_leftUnitor _ _
  associator_actionHom c₁ c₂ c₃ d := by
    simpa only [mop_tensorObj, mop_hom_associator,
      MonoidalRightAction.actionHomRight_inv_hom_assoc] using
      (d ⊴ᵣ (α_ (unmop c₃) (unmop c₂) (unmop c₁)).inv) ≫=
        MonoidalRightAction.actionHom_associator
          (unmop c₃) (unmop c₂) (unmop c₁) d|>.symm

section

attribute [local instance] monoidalOppositeLeftAction
variable [MonoidalRightAction C D]

lemma monoidalOppositeLeftAction_actionObj_mop (c : C) (d : D) :
    mop c ⊙ₗ d = d ⊙ᵣ c := rfl

lemma monoidalOppositeLeftAction_actionHomLeft_mop
    {c c' : C} (f : c ⟶ c') (d : D) :
    f.mop ⊵ₗ d = d ⊴ᵣ f := rfl

lemma monoidalOppositeLeftAction_actionRight_mop
    (c : C) {d d' : D} (f : d ⟶ d') :
    mop c ⊴ₗ f = f ⊵ᵣ c := rfl

lemma monoidalOppositeLeftAction_actionHom_mop_mop
    {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') :
    f.mop ⊙ₗₘ g = g ⊙ᵣₘ f := rfl

lemma monoidalOppositeLeftAction_actionAssocIso_mop_mop (c c' : C) (d : D) :
    αₗ (mop c) (mop c') d = αᵣ d c' c := rfl

end

end MonoidalLeftAction

namespace MonoidalRightAction
open scoped MonoidalLeftAction MonoidalRightAction
open MonoidalOpposite

/-- Define a right action of `C` on `D` from a left action of `Cᴹᵒᵖ` on `D` via
the formula `d ⊙ᵣ c := (mop c) ⊙ₗ d`. -/
@[simps -isSimp]
def rightActionOfMonoidalOppositeLeftAction [MonoidalLeftAction Cᴹᵒᵖ D] :
    MonoidalRightAction C D where
  actionObj d c := mop c ⊙ₗ d
  actionHomLeft {d d'} f c := mop c ⊴ₗ f
  actionHomRight d _ _ f := f.mop ⊵ₗ d
  actionHom {c c'} {d d'} f g := g.mop ⊙ₗₘ f
  actionAssocIso _ _ _ := αₗ _ _ _
  actionUnitIso _ := λₗ _
  actionHom_def _ _ := MonoidalLeftAction.actionHom_def' _ _
  actionAssocIso_hom_naturality _ _ _ :=
    MonoidalLeftAction.actionAssocIso_hom_naturality _ _ _
  actionUnitIso_hom_naturality _ :=
    MonoidalLeftAction.actionUnitIso_hom_naturality _
  actionHom_associator c₁ c₂ c₃ d := by
    simpa only [mop_tensorObj, mop_hom_associator,
      MonoidalLeftAction.inv_hom_actionHomLeft_assoc] using
      (α_ (mop c₃) (mop c₂) (mop c₁)).inv ⊵ₗ d ≫=
        MonoidalLeftAction.associator_actionHom
          (mop c₃) (mop c₂) (mop c₁) d|>.symm

/-- Define a right action of `Cᴹᵒᵖ` on `D` from a left action of `C` on `D` via
the formula `d ⊙ᵣ mop c = c ⊙ₗ d`. -/
@[simps -isSimp]
def monoidalOppositeRightAction [MonoidalLeftAction C D] :
    MonoidalRightAction Cᴹᵒᵖ D where
  actionObj d c := unmop c ⊙ₗ d
  actionHomLeft {d d'} f c := unmop c ⊴ₗ f
  actionHomRight d _ _ f := f.unmop ⊵ₗ d
  actionHom {c c'} {d d'} f g := g.unmop ⊙ₗₘ f
  actionAssocIso _ _ _ := αₗ _ _ _
  actionUnitIso _ := λₗ _
  actionHom_def _ _ := MonoidalLeftAction.actionHom_def' _ _
  actionAssocIso_hom_naturality _ _ _ :=
    MonoidalLeftAction.actionAssocIso_hom_naturality _ _ _
  actionUnitIso_hom_naturality _ :=
    MonoidalLeftAction.actionUnitIso_hom_naturality _
  actionHom_associator c₁ c₂ c₃ d := by
    simpa only [mop_tensorObj, mop_hom_associator,
      MonoidalLeftAction.inv_hom_actionHomLeft_assoc] using
      (α_ (unmop c₃) (unmop c₂) (unmop c₁)).inv ⊵ₗ d ≫=
        MonoidalLeftAction.associator_actionHom
          (unmop c₃) (unmop c₂) (unmop c₁) d|>.symm

section

attribute [local instance] monoidalOppositeRightAction
variable [MonoidalLeftAction C D]

lemma monoidalOppositeRightAction_actionObj_mop (c : C) (d : D) :
    d ⊙ᵣ mop c = c ⊙ₗ d := rfl

lemma monoidalOppositeRightAction_actionHomRight_mop
    {c c' : C} (f : c ⟶ c') (d : D) :
    d ⊴ᵣ f.mop = f ⊵ₗ d := rfl

lemma monoidalOppositeRightAction_actionRight_mop
    (c : C) {d d' : D} (f : d ⟶ d') :
    f ⊵ᵣ mop c = c ⊴ₗ f := rfl

lemma monoidalOppositeRightAction_actionHom_mop_mop
    {c c' : D} {d d' : C} (f : c ⟶ c') (g : d ⟶ d') :
    f ⊙ᵣₘ g.mop = g ⊙ₗₘ f := rfl

lemma monoidalOppositeRightAction_actionAssocIso_mop_mop (c c' : C) (d : D) :
    αᵣ d (mop c) (mop c') = αₗ c' c d := rfl

end

end MonoidalRightAction

end CategoryTheory.MonoidalCategory
