/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Braided category structures on opposite categories

If `C` is braided, so are `Cᵒᵖ` and `Cᴹᵒᵖ`.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory Opposite Functor.LaxMonoidal
  Functor.OplaxMonoidal

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]

namespace CategoryTheory

instance : BraidedCategory Cᵒᵖ where
  braiding X Y := (β_ (unop Y) (unop X)).op

section OppositeLemmas

@[simp] lemma op_braiding (X Y : C) : (β_ X Y).op = β_ (op Y) (op X) := rfl
@[simp] lemma unop_braiding (X Y : Cᵒᵖ) : (β_ X Y).unop = β_ (unop Y) (unop X) := rfl

@[simp] lemma op_hom_braiding (X Y : C) : (β_ X Y).hom.op = (β_ (op Y) (op X)).hom := rfl
@[simp] lemma unop_hom_braiding (X Y : Cᵒᵖ) : (β_ X Y).hom.unop = (β_ (unop Y) (unop X)).hom := rfl

@[simp] lemma op_inv_braiding (X Y : C) : (β_ X Y).inv.op = (β_ (op Y) (op X)).inv := rfl
@[simp] lemma unop_inv_braiding (X Y : Cᵒᵖ) : (β_ X Y).inv.unop = (β_ (unop Y) (unop X)).inv := rfl

@[simp] lemma BraidedCategory.unop_tensorμ {C : Type*} [Category* C] [MonoidalCategory C]
    [BraidedCategory C] (X Y W Z : Cᵒᵖ) :
    (tensorμ X W Y Z).unop = tensorμ X.unop Y.unop W.unop Z.unop := by
  simp only [unop_tensorObj, tensorμ, unop_comp, unop_inv_associator, unop_whiskerLeft,
    unop_hom_associator, unop_whiskerRight, unop_hom_braiding, Category.assoc]

@[simp] lemma BraidedCategory.op_tensorμ {C : Type*} [Category* C] [MonoidalCategory C]
    [BraidedCategory C] (X Y W Z : C) :
    (tensorμ X W Y Z).op = tensorμ (op X) (op Y) (op W) (op Z) := by
  simp only [op_tensorObj, tensorμ, op_comp, op_inv_associator, op_whiskerLeft, op_hom_associator,
    op_whiskerRight, op_hom_braiding, Category.assoc]

end OppositeLemmas

namespace MonoidalOpposite

instance instBraiding : BraidedCategory Cᴹᵒᵖ where
  braiding X Y := (β_ Y.unmop X.unmop).mop
  braiding_naturality_right X {_ _} f := Quiver.Hom.unmop_inj <| by simp
  braiding_naturality_left {_ _} f Z := Quiver.Hom.unmop_inj <| by simp

section MonoidalOppositeLemmas

@[simp] lemma mop_braiding (X Y : C) : (β_ X Y).mop = β_ (mop Y) (mop X) := rfl
@[simp] lemma unmop_braiding (X Y : Cᴹᵒᵖ) : (β_ X Y).unmop = β_ (unmop Y) (unmop X) := rfl

@[simp] lemma mop_hom_braiding (X Y : C) : (β_ X Y).hom.mop = (β_ (mop Y) (mop X)).hom := rfl
@[simp]
lemma unmop_hom_braiding (X Y : Cᴹᵒᵖ) : (β_ X Y).hom.unmop = (β_ (unmop Y) (unmop X)).hom := rfl

@[simp] lemma mop_inv_braiding (X Y : C) : (β_ X Y).inv.mop = (β_ (mop Y) (mop X)).inv := rfl
@[simp]
lemma unmop_inv_braiding (X Y : Cᴹᵒᵖ) : (β_ X Y).inv.unmop = (β_ (unmop Y) (unmop X)).inv := rfl

end MonoidalOppositeLemmas

set_option backward.defeqAttrib.useBackward true in
instance : (mopFunctor C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun X Y ↦ β_ (mop X) (mop Y)
      associativity := fun X Y Z ↦ by simp [← yang_baxter_assoc] }

@[simp] lemma mopFunctor_ε : ε (mopFunctor C) = 𝟙 _ := rfl
@[simp] lemma mopFunctor_η : η (mopFunctor C) = 𝟙 _ := rfl
@[simp] lemma mopFunctor_μ (X Y : C) : μ (mopFunctor C) X Y = (β_ (mop X) (mop Y)).hom := rfl
@[simp] lemma mopFunctor_δ (X Y : C) : δ (mopFunctor C) X Y = (β_ (mop X) (mop Y)).inv := rfl

set_option backward.defeqAttrib.useBackward true in
instance : (unmopFunctor C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun X Y ↦ β_ (unmop X) (unmop Y)
      associativity := fun X Y Z ↦ by simp [← yang_baxter_assoc] }

@[simp] lemma unmopFunctor_ε : ε (unmopFunctor C) = 𝟙 _ := rfl
@[simp] lemma unmopFunctor_η : η (unmopFunctor C) = 𝟙 _ := rfl
@[simp] lemma unmopFunctor_μ (X Y : Cᴹᵒᵖ) :
    μ (unmopFunctor C) X Y = (β_ (unmop X) (unmop Y)).hom := rfl
@[simp] lemma unmopFunctor_δ (X Y : Cᴹᵒᵖ) :
    δ (unmopFunctor C) X Y = (β_ (unmop X) (unmop Y)).inv := rfl

/-- The identity functor on `C`, viewed as a functor from `C` to its
monoidal opposite, upgraded to a braided functor. -/
instance : (mopFunctor C).Braided where

/-- The identity functor on `C`, viewed as a functor from the
monoidal opposite of `C` to `C`, upgraded to a braided functor. -/
instance : (unmopFunctor C).Braided where

end MonoidalOpposite

end CategoryTheory
