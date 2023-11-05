/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

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

namespace MonoidalOpposite

notation:max C "ᴹᵒᵖ" => MonoidalOpposite C

/-- Think of an object of `C` as an object of `Cᴹᵒᵖ`. -/
-- @[pp_nodot] -- Porting note: removed
def mop (X : C) : Cᴹᵒᵖ :=
  X

/-- Think of an object of `Cᴹᵒᵖ` as an object of `C`. -/
-- @[pp_nodot] -- Porting note: removed
def unmop (X : Cᴹᵒᵖ) : C :=
  X

theorem op_injective : Function.Injective (mop : C → Cᴹᵒᵖ) :=
  fun _ _ => id

theorem unop_injective : Function.Injective (unmop : Cᴹᵒᵖ → C) :=
  fun _ _ => id

@[simp]
theorem op_inj_iff (x y : C) : mop x = mop y ↔ x = y :=
  Iff.rfl

@[simp]
theorem unop_inj_iff (x y : Cᴹᵒᵖ) : unmop x = unmop y ↔ x = y :=
  Iff.rfl

@[simp]
theorem mop_unmop (X : Cᴹᵒᵖ) : mop (unmop X) = X :=
  rfl

@[simp]
theorem unmop_mop (X : C) : unmop (mop X) = X :=
  rfl

instance monoidalOppositeCategory [Category.{v₁} C] : Category Cᴹᵒᵖ :=
  InducedCategory.category unmop

end MonoidalOpposite

end CategoryTheory

open CategoryTheory

open CategoryTheory.MonoidalOpposite

variable [Category.{v₁} C]

/-- The monoidal opposite of a morphism `f : X ⟶ Y` is just `f`, thought of as `mop X ⟶ mop Y`. -/
def Quiver.Hom.mop {X Y : C} (f : X ⟶ Y) : @Quiver.Hom Cᴹᵒᵖ _ (mop X) (mop Y) :=
  f

/-- We can think of a morphism `f : mop X ⟶ mop Y` as a morphism `X ⟶ Y`. -/
def Quiver.Hom.unmop {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) : unmop X ⟶ unmop Y :=
  f

namespace CategoryTheory

theorem mop_inj {X Y : C} : Function.Injective (Quiver.Hom.mop : (X ⟶ Y) → (mop X ⟶ mop Y)) :=
  fun _ _ H => congr_arg Quiver.Hom.unmop H

theorem unmop_inj {X Y : Cᴹᵒᵖ} :
    Function.Injective (Quiver.Hom.unmop : (X ⟶ Y) → (unmop X ⟶ unmop Y)) :=
  fun _ _ H => congr_arg Quiver.Hom.mop H

@[simp]
theorem unmop_mop {X Y : C} {f : X ⟶ Y} : f.mop.unmop = f :=
  rfl

@[simp]
theorem mop_unmop {X Y : Cᴹᵒᵖ} {f : X ⟶ Y} : f.unmop.mop = f :=
  rfl

@[simp]
theorem mop_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).mop = f.mop ≫ g.mop :=
  rfl

@[simp]
theorem mop_id {X : C} : (𝟙 X).mop = 𝟙 (mop X) :=
  rfl

@[simp]
theorem unmop_comp {X Y Z : Cᴹᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).unmop = f.unmop ≫ g.unmop :=
  rfl

@[simp]
theorem unmop_id {X : Cᴹᵒᵖ} : (𝟙 X).unmop = 𝟙 (unmop X) :=
  rfl

@[simp]
theorem unmop_id_mop {X : C} : (𝟙 (mop X)).unmop = 𝟙 X :=
  rfl

@[simp]
theorem mop_id_unmop {X : Cᴹᵒᵖ} : (𝟙 (unmop X)).mop = 𝟙 X :=
  rfl

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

theorem op_tensorObj (X Y : Cᵒᵖ) : X ⊗ Y = op (unop X ⊗ unop Y) :=
  rfl

theorem op_tensorUnit : 𝟙_ Cᵒᵖ = op (𝟙_ C) :=
  rfl

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

theorem mop_tensorObj (X Y : Cᴹᵒᵖ) : X ⊗ Y = mop (unmop Y ⊗ unmop X) :=
  rfl

theorem mop_tensorUnit : 𝟙_ Cᴹᵒᵖ = mop (𝟙_ C) :=
  rfl

end CategoryTheory
