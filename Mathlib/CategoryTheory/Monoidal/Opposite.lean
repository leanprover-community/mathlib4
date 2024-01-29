/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence

#align_import category_theory.monoidal.opposite from "leanprover-community/mathlib"@"14b69e9f3c16630440a2cbd46f1ddad0d561dee7"

/-!
# Monoidal opposites

We write `Cᵐᵒᵖ` for the monoidal opposite of a monoidal category `C`.
-/


universe v₁ v₂ u₁ u₂

variable {C : Type u₁}

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

/-- A type synonym for the monoidal opposite. Use the notation `Cᴹᵒᵖ`. -/
-- @[nolint has_nonempty_instance] -- Porting note: This linter does not exist yet.
def MonoidalOpposite (C : Type u₁) :=
  C
#align category_theory.monoidal_opposite CategoryTheory.MonoidalOpposite

namespace MonoidalOpposite

notation:max C "ᴹᵒᵖ" => MonoidalOpposite C

/-- Think of an object of `C` as an object of `Cᴹᵒᵖ`. -/
-- @[pp_nodot] -- Porting note: removed
def mop (X : C) : Cᴹᵒᵖ :=
  X
#align category_theory.monoidal_opposite.mop CategoryTheory.MonoidalOpposite.mop

/-- Think of an object of `Cᴹᵒᵖ` as an object of `C`. -/
-- @[pp_nodot] -- Porting note: removed
def unmop (X : Cᴹᵒᵖ) : C :=
  X
#align category_theory.monoidal_opposite.unmop CategoryTheory.MonoidalOpposite.unmop

theorem op_injective : Function.Injective (mop : C → Cᴹᵒᵖ) :=
  fun _ _ => id
#align category_theory.monoidal_opposite.op_injective CategoryTheory.MonoidalOpposite.op_injective

theorem unop_injective : Function.Injective (unmop : Cᴹᵒᵖ → C) :=
  fun _ _ => id
#align category_theory.monoidal_opposite.unop_injective CategoryTheory.MonoidalOpposite.unop_injective

@[simp]
theorem op_inj_iff (x y : C) : mop x = mop y ↔ x = y :=
  Iff.rfl
#align category_theory.monoidal_opposite.op_inj_iff CategoryTheory.MonoidalOpposite.op_inj_iff

@[simp]
theorem unop_inj_iff (x y : Cᴹᵒᵖ) : unmop x = unmop y ↔ x = y :=
  Iff.rfl
#align category_theory.monoidal_opposite.unop_inj_iff CategoryTheory.MonoidalOpposite.unop_inj_iff

@[simp]
theorem mop_unmop (X : Cᴹᵒᵖ) : mop (unmop X) = X :=
  rfl
#align category_theory.monoidal_opposite.mop_unmop CategoryTheory.MonoidalOpposite.mop_unmop

@[simp]
theorem unmop_mop (X : C) : unmop (mop X) = X :=
  rfl
#align category_theory.monoidal_opposite.unmop_mop CategoryTheory.MonoidalOpposite.unmop_mop

instance monoidalOppositeCategory [Category.{v₁} C] : Category Cᴹᵒᵖ :=
  InducedCategory.category unmop
#align category_theory.monoidal_opposite.monoidal_opposite_category CategoryTheory.MonoidalOpposite.monoidalOppositeCategory

end MonoidalOpposite

end CategoryTheory

open CategoryTheory

open CategoryTheory.MonoidalOpposite

variable [Category.{v₁} C]

/-- The monoidal opposite of a morphism `f : X ⟶ Y` is just `f`, thought of as `mop X ⟶ mop Y`. -/
def Quiver.Hom.mop {X Y : C} (f : X ⟶ Y) : @Quiver.Hom Cᴹᵒᵖ _ (mop X) (mop Y) :=
  f
#align quiver.hom.mop Quiver.Hom.mop

/-- We can think of a morphism `f : mop X ⟶ mop Y` as a morphism `X ⟶ Y`. -/
def Quiver.Hom.unmop {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) : unmop X ⟶ unmop Y :=
  f
#align quiver.hom.unmop Quiver.Hom.unmop

namespace CategoryTheory

theorem mop_inj {X Y : C} : Function.Injective (Quiver.Hom.mop : (X ⟶ Y) → (mop X ⟶ mop Y)) :=
  fun _ _ H => congr_arg Quiver.Hom.unmop H
#align category_theory.mop_inj CategoryTheory.mop_inj

theorem unmop_inj {X Y : Cᴹᵒᵖ} :
    Function.Injective (Quiver.Hom.unmop : (X ⟶ Y) → (unmop X ⟶ unmop Y)) :=
  fun _ _ H => congr_arg Quiver.Hom.mop H
#align category_theory.unmop_inj CategoryTheory.unmop_inj

@[simp]
theorem unmop_mop {X Y : C} {f : X ⟶ Y} : f.mop.unmop = f :=
  rfl
#align category_theory.unmop_mop CategoryTheory.unmop_mop

@[simp]
theorem mop_unmop {X Y : Cᴹᵒᵖ} {f : X ⟶ Y} : f.unmop.mop = f :=
  rfl
#align category_theory.mop_unmop CategoryTheory.mop_unmop

@[simp]
theorem mop_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).mop = f.mop ≫ g.mop :=
  rfl
#align category_theory.mop_comp CategoryTheory.mop_comp

@[simp]
theorem mop_id {X : C} : (𝟙 X).mop = 𝟙 (mop X) :=
  rfl
#align category_theory.mop_id CategoryTheory.mop_id

@[simp]
theorem unmop_comp {X Y Z : Cᴹᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).unmop = f.unmop ≫ g.unmop :=
  rfl
#align category_theory.unmop_comp CategoryTheory.unmop_comp

@[simp]
theorem unmop_id {X : Cᴹᵒᵖ} : (𝟙 X).unmop = 𝟙 (unmop X) :=
  rfl
#align category_theory.unmop_id CategoryTheory.unmop_id

@[simp]
theorem unmop_id_mop {X : C} : (𝟙 (mop X)).unmop = 𝟙 X :=
  rfl
#align category_theory.unmop_id_mop CategoryTheory.unmop_id_mop

@[simp]
theorem mop_id_unmop {X : Cᴹᵒᵖ} : (𝟙 (unmop X)).mop = 𝟙 X :=
  rfl
#align category_theory.mop_id_unmop CategoryTheory.mop_id_unmop

namespace Iso

variable {X Y : C}

/-- An isomorphism in `C` gives an isomorphism in `Cᴹᵒᵖ`. -/
@[simps]
def mop (f : X ≅ Y) : mop X ≅ mop Y where
  hom := f.hom.mop
  inv := f.inv.mop
  -- Porting note: it's a pity `attribute [aesop safe apply (rule_sets [CategoryTheory])] unmop_inj`
  -- doesn't automate these proofs.
  hom_inv_id := unmop_inj (by simp)
  inv_hom_id := unmop_inj (by simp)
#align category_theory.iso.mop CategoryTheory.Iso.mop

end Iso

variable [MonoidalCategory.{v₁} C]

open Opposite MonoidalCategory

instance monoidalCategoryOp : MonoidalCategory Cᵒᵖ where
  tensorObj X Y := op (unop X ⊗ unop Y)
  whiskerLeft X _ _ f := (X.unop ◁ f.unop).op
  whiskerRight f X := (f.unop ▷ X.unop).op
  tensorHom f g := (f.unop ⊗ g.unop).op
  tensorHom_def f g := Quiver.Hom.unop_inj (tensorHom_def' _ _)
  tensorUnit := op (𝟙_ C)
  associator X Y Z := (α_ (unop X) (unop Y) (unop Z)).symm.op
  leftUnitor X := (λ_ (unop X)).symm.op
  rightUnitor X := (ρ_ (unop X)).symm.op
  associator_naturality f g h := Quiver.Hom.unop_inj (by simp)
  leftUnitor_naturality f := Quiver.Hom.unop_inj (by simp)
  rightUnitor_naturality f := Quiver.Hom.unop_inj (by simp)
  triangle X Y := Quiver.Hom.unop_inj (by dsimp; coherence)
  pentagon W X Y Z := Quiver.Hom.unop_inj (by dsimp; coherence)
#align category_theory.monoidal_category_op CategoryTheory.monoidalCategoryOp

theorem op_tensorObj (X Y : Cᵒᵖ) : X ⊗ Y = op (unop X ⊗ unop Y) :=
  rfl
#align category_theory.op_tensor_obj CategoryTheory.op_tensorObj

theorem op_tensorUnit : 𝟙_ Cᵒᵖ = op (𝟙_ C) :=
  rfl
#align category_theory.op_tensor_unit CategoryTheory.op_tensorUnit

theorem op_tensorHom {W X Y Z : Cᵒᵖ} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ g = (f.unop ⊗ g.unop).op :=
  rfl

theorem op_leftUnitor {X : Cᵒᵖ} : λ_ X = (λ_ (unop X)).symm.op := rfl

theorem op_rightUnitor {X : Cᵒᵖ} : ρ_ X = (ρ_ (unop X)).symm.op := rfl

theorem op_associator {X Y Z : Cᵒᵖ} : α_ X Y Z = (α_ (unop X) (unop Y) (unop Z)).symm.op := rfl

theorem op_tensor_op {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f.op ⊗ g.op = (f ⊗ g).op := rfl

theorem unop_tensor_unop {W X Y Z : Cᵒᵖ} (f : W ⟶ X) (g : Y ⟶ Z) :
    f.unop ⊗ g.unop = (f ⊗ g).unop := rfl

instance monoidalCategoryMop : MonoidalCategory Cᴹᵒᵖ where
  tensorObj X Y := mop (unmop Y ⊗ unmop X)
  whiskerLeft X _ _ f := (f.unmop ▷ X.unmop).mop
  whiskerRight f X := (X.unmop ◁ f.unmop).mop
  tensorHom f g := (g.unmop ⊗ f.unmop).mop
  tensorHom_def f g := unmop_inj (tensorHom_def' _ _)
  tensorUnit := mop (𝟙_ C)
  associator X Y Z := (α_ (unmop Z) (unmop Y) (unmop X)).symm.mop
  leftUnitor X := (ρ_ (unmop X)).mop
  rightUnitor X := (λ_ (unmop X)).mop
  associator_naturality f g h := unmop_inj (by simp)
  leftUnitor_naturality f := unmop_inj (by simp)
  rightUnitor_naturality f := unmop_inj (by simp)
  triangle X Y := unmop_inj (by simp) -- Porting note: Changed `by coherence` to `by simp`
  pentagon W X Y Z := unmop_inj (by dsimp; coherence)
#align category_theory.monoidal_category_mop CategoryTheory.monoidalCategoryMop

theorem mop_tensorObj (X Y : Cᴹᵒᵖ) : X ⊗ Y = mop (unmop Y ⊗ unmop X) :=
  rfl
#align category_theory.mop_tensor_obj CategoryTheory.mop_tensorObj

theorem mop_tensorUnit : 𝟙_ Cᴹᵒᵖ = mop (𝟙_ C) :=
  rfl
#align category_theory.mop_tensor_unit CategoryTheory.mop_tensorUnit

end CategoryTheory
