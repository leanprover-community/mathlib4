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

We construct similar actions for `Cᵒᵖ`, namely, left/right `Cᵒᵖ`-actions
on `Dᵒᵖ` from left/right-actions of `C` on `D`, and vice-versa.

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
the formula `c ⊙ₗ d := d ᵣ⊙ (mop c)`. -/
@[simps -isSimp]
def leftActionOfMonoidalOppositeRightAction [MonoidalRightAction Cᴹᵒᵖ D] :
    MonoidalLeftAction C D where
  actionObj c d := d ᵣ⊙ (mop c)
  actionHomLeft {c c'} f d := d ᵣ⊴ f.mop
  actionHomRight c {d d'} f := f ᵣ⊵ mop c
  actionHom {c c'} {d d} f g := g ᵣ⊙ f.mop
  actionAssocIso _ _ _ := ᵣσ_ _ _ _
  actionUnitIso _ := ᵣυ_ _
  actionHom_def _ _ := MonoidalRightAction.actionHom_def' _ _
  actionAssocIso_naturality _ _ _ :=
    MonoidalRightAction.actionAssocIso_naturality _ _ _
  actionUnitIso_naturality _ :=
    MonoidalRightAction.actionUnitIso_naturality _
  rightUnitor_actionHom c d :=
    MonoidalRightAction.actionHom_leftUnitor _ _
  associator_actionHom c₁ c₂ c₃ d := by
    simpa only [mop_tensorObj, mop_hom_associator,
      MonoidalRightAction.actionHomRight_inv_hom_assoc] using
      (d ᵣ⊴ (α_ (mop c₃) (mop c₂) (mop c₁)).inv) ≫=
        MonoidalRightAction.actionHom_associator
          (mop c₃) (mop c₂) (mop c₁) d|>.symm

/-- Define a left action of `Cᴹᵒᵖ` on `D` from a right action of `C` on `D` via
the formula `mop c ⊙ₗ d = d ᵣ⊙ c`. -/
@[simps -isSimp]
def monoidalOppositeLeftAction [MonoidalRightAction C D] :
    MonoidalLeftAction Cᴹᵒᵖ D where
  actionObj c d := d ᵣ⊙ (unmop c)
  actionHomLeft {c c'} f d := d ᵣ⊴ f.unmop
  actionHomRight c {d d'} f := f ᵣ⊵ unmop c
  actionHom {c c'} {d d} f g := g ᵣ⊙ f.unmop
  actionAssocIso _ _ _ := ᵣσ_ _ _ _
  actionUnitIso _ := ᵣυ_ _
  actionHom_def _ _ := MonoidalRightAction.actionHom_def' _ _
  actionAssocIso_naturality _ _ _ :=
    MonoidalRightAction.actionAssocIso_naturality _ _ _
  actionUnitIso_naturality _ :=
    MonoidalRightAction.actionUnitIso_naturality _
  rightUnitor_actionHom c d :=
    MonoidalRightAction.actionHom_leftUnitor _ _
  associator_actionHom c₁ c₂ c₃ d := by
    simpa only [mop_tensorObj, mop_hom_associator,
      MonoidalRightAction.actionHomRight_inv_hom_assoc] using
      (d ᵣ⊴ (α_ (unmop c₃) (unmop c₂) (unmop c₁)).inv) ≫=
        MonoidalRightAction.actionHom_associator
          (unmop c₃) (unmop c₂) (unmop c₁) d|>.symm

section

attribute [local instance] monoidalOppositeLeftAction
variable [MonoidalRightAction C D]

lemma monoidalOppositeLeftAction_actionObj_mop (c : C) (d : D) :
    mop c ⊙ₗ d = d ᵣ⊙ c := rfl

lemma monoidalOppositeLeftAction_actionHomLeft_mop
    {c c' : C} (f : c ⟶ c') (d : D) :
    f.mop ⊵ₗ d = d ᵣ⊴ f := rfl

lemma monoidalOppositeLeftAction_actionRight_mop
    (c : C) {d d' : D} (f : d ⟶ d') :
    mop c ⊴ₗ f = f ᵣ⊵ c := rfl

lemma monoidalOppositeLeftAction_actionHom_mop_mop
    {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') :
    f.mop ⊙ₗ g = g ᵣ⊙ f := rfl

lemma monoidalOppositeLeftAction_actionAssocIso_mop_mop (c c' : C) (d : D) :
    σ_ₗ (mop c) (mop c') d = ᵣσ_ d c' c := rfl

end

open Opposite

@[simps]
def oppositeLeftAction [MonoidalLeftAction C D] :
    MonoidalLeftAction Cᵒᵖ Dᵒᵖ where
  actionObj c d := op <| c.unop ⊙ₗ d.unop
  actionHomLeft {c c'} f d := (f.unop ⊵ₗ unop d).op
  actionHomRight c {d d'} f := (unop c ⊴ₗ f.unop).op
  actionHom {c c'} {d d} f g := (f.unop ⊙ₗ g.unop).op
  actionAssocIso _ _ _ := Iso.op <| (σ_ₗ _ _ _|>.symm)
  actionUnitIso _ := Iso.op <| (υ_ₗ _|>.symm)
  actionHom_def
    | op f, op g => by
        apply Quiver.Hom.unop_inj
        simpa [MonoidalLeftAction.action_exchange] using
          MonoidalLeftAction.actionHom_def f g
  actionAssocIso_naturality
    | op f, op g, op h => by
        apply Quiver.Hom.unop_inj
        haveI := (σ_ₗ (unop _) (unop _) (unop _)).inv ≫=
          MonoidalLeftAction.actionAssocIso_naturality f g h
        simp only [Iso.inv_hom_id_assoc] at this
        simp [← this]
  actionUnitIso_naturality _ := by
      apply Quiver.Hom.unop_inj
      simp
  whiskerRight_actionHomLeft _ _ _ := by
      apply Quiver.Hom.unop_inj
      simp
  associator_actionHom _ _ _ _ := by
      apply Quiver.Hom.unop_inj
      apply IsIso.inv_eq_inv.mp
      simp
  leftUnitor_actionHom _ _ := by
      apply Quiver.Hom.unop_inj
      apply IsIso.inv_eq_inv.mp
      simp
  rightUnitor_actionHom _ _ := by
      apply Quiver.Hom.unop_inj
      apply IsIso.inv_eq_inv.mp
      simp

@[simps]
def leftActionOfOppositeLeftAction [MonoidalLeftAction Cᵒᵖ Dᵒᵖ] :
    MonoidalLeftAction C D where
  actionObj c d := unop <| op c ⊙ₗ op d
  actionHomLeft {c c'} f d := (f.op ⊵ₗ op d).unop
  actionHomRight c {d d'} f := (op c ⊴ₗ f.op).unop
  actionHom {c c'} {d d} f g := (f.op ⊙ₗ g.op).unop
  actionAssocIso _ _ _ := Iso.unop <| (σ_ₗ _ _ _|>.symm)
  actionUnitIso _ := Iso.unop <| (υ_ₗ _|>.symm)
  actionHom_def f g := by
    apply Quiver.Hom.op_inj
    simpa [MonoidalLeftAction.action_exchange] using
      MonoidalLeftAction.actionHom_def f.op g.op
  actionAssocIso_naturality f g h := by
    apply Quiver.Hom.op_inj
    haveI := (σ_ₗ (op _) (op _) (op _)).inv ≫=
      MonoidalLeftAction.actionAssocIso_naturality f.op g.op h.op
    simp only [Iso.inv_hom_id_assoc] at this
    simp [← this]
  actionUnitIso_naturality _ := by
      apply Quiver.Hom.op_inj
      simp
  whiskerRight_actionHomLeft _ _ _ := by
      apply Quiver.Hom.op_inj
      simp
  associator_actionHom _ _ _ _ := by
      apply Quiver.Hom.op_inj
      apply IsIso.inv_eq_inv.mp
      simp
  leftUnitor_actionHom _ _ := by
      apply Quiver.Hom.op_inj
      apply IsIso.inv_eq_inv.mp
      simp
  rightUnitor_actionHom _ _ := by
      apply Quiver.Hom.op_inj
      apply IsIso.inv_eq_inv.mp
      simp

end MonoidalLeftAction

namespace MonoidalRightAction
open scoped MonoidalLeftAction MonoidalRightAction
open MonoidalOpposite

/-- Define a right action of `C` on `D` from a left action of `Cᴹᵒᵖ` on `D` via
the formula `d ᵣ⊙ c := (mop c) ⊙ₗ d`. -/
@[simps -isSimp]
def rightActionOfMonoidalOppositeLeftAction [MonoidalLeftAction Cᴹᵒᵖ D] :
    MonoidalRightAction C D where
  actionObj d c := (mop c) ⊙ₗ d
  actionHomLeft {d d'} f c := (mop c) ⊴ₗ f
  actionHomRight d _ _ f := f.mop ⊵ₗ d
  actionHom {c c'} {d d'} f g := g.mop ⊙ₗ f
  actionAssocIso _ _ _ := σ_ₗ _ _ _
  actionUnitIso _ := υ_ₗ _
  actionHom_def _ _ := MonoidalLeftAction.actionHom_def' _ _
  actionAssocIso_naturality _ _ _ :=
    MonoidalLeftAction.actionAssocIso_naturality _ _ _
  actionUnitIso_naturality _ :=
    MonoidalLeftAction.actionUnitIso_naturality _
  actionHom_associator c₁ c₂ c₃ d := by
    simpa only [mop_tensorObj, mop_hom_associator,
      MonoidalLeftAction.inv_hom_actionHomLeft_assoc] using
      (α_ (mop c₃) (mop c₂) (mop c₁)).inv ⊵ₗ d ≫=
        MonoidalLeftAction.associator_actionHom
          (mop c₃) (mop c₂) (mop c₁) d|>.symm

/-- Define a right action of `Cᴹᵒᵖ` on `D` from a left action of `C` on `D` via
the formula `d ᵣ⊙ mop c = c ⊙ₗ d`. -/
@[simps -isSimp]
def monoidalOppositeRightAction [MonoidalLeftAction C D] :
    MonoidalRightAction Cᴹᵒᵖ D where
  actionObj d c := (unmop c) ⊙ₗ d
  actionHomLeft {d d'} f c := (unmop c) ⊴ₗ f
  actionHomRight d _ _ f := f.unmop ⊵ₗ d
  actionHom {c c'} {d d'} f g := g.unmop ⊙ₗ f
  actionAssocIso _ _ _ := σ_ₗ _ _ _
  actionUnitIso _ := υ_ₗ _
  actionHom_def _ _ := MonoidalLeftAction.actionHom_def' _ _
  actionAssocIso_naturality _ _ _ :=
    MonoidalLeftAction.actionAssocIso_naturality _ _ _
  actionUnitIso_naturality _ :=
    MonoidalLeftAction.actionUnitIso_naturality _
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
    d ᵣ⊙ mop c = c ⊙ₗ d := rfl

lemma monoidalOppositeRightAction_actionHomRight_mop
    {c c' : C} (f : c ⟶ c') (d : D) :
    d ᵣ⊴ f.mop = f ⊵ₗ d := rfl

lemma monoidalOppositeRightAction_actionRight_mop
    (c : C) {d d' : D} (f : d ⟶ d') :
    f ᵣ⊵ (mop c) = c ⊴ₗ f := rfl

lemma monoidalOppositeRightAction_actionHom_mop_mop
    {c c' : D} {d d' : C} (f : c ⟶ c') (g : d ⟶ d') :
    f ᵣ⊙ g.mop = g ⊙ₗ f := rfl

lemma monoidalOppositeRightAction_actionAssocIso_mop_mop (c c' : C) (d : D) :
    ᵣσ_ d (mop c) (mop c') = σ_ₗ c' c d := rfl

end

end MonoidalRightAction

end CategoryTheory.MonoidalCategory
