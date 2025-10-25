/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Opposites

/-!
# Opposite bicategories

We construct the 1-cell opposite of a bicategory `B`, called `Bᵒᵖ`. It is defined as follows
* The objects of `Bᵒᵖ` correspond to objects of `B`.
* The morphisms `X ⟶ Y` in `Bᵒᵖ` are the morphisms `Y ⟶ X` in `B`.
* The 2-morphisms `f ⟶ g` in `Bᵒᵖ` are the 2-morphisms `f ⟶ g` in `B`. In other words, the
  directions of the 2-morphisms are preserved.

Note that the standard notation for the opposite of a bicategory is `Bᵒᵖ`, however this clashes
with the notation for the opposite of a 1-category, so we use `Bᵒᵖ` instead.

# Remarks
There are multiple notions of opposite categories for bicategories.
- There is 1-cell dual `Bᵒᵖ` as defined above.
- There is the 2-cell dual, `Cᶜᵒ` where only the natural transformations are reversed
- There is the bi-dual `Cᶜᵒᵒᵖ` where the directions of both the morphisms and the natural
  transformations are reversed.

## TODO

* Define the 2-cell dual `Cᶜᵒ`.
* Provide various lemmas for going between `LocallyDiscrete Cᵒᵖ` and `(LocallyDiscrete C)ᵒᵖ`.

Note: `Cᶜᵒᵒᵖ` is WIP by Christian Merten.

-/

universe w v u

open CategoryTheory Bicategory Opposite

namespace Bicategory.Opposite

variable {B : Type u} [Bicategory.{w, v} B]

/-- `Bᵒᵖ` preserves the direction of all 2-morphisms in `B` -/
instance Hom (a b : Bᵒᵖ) : Quiver (a ⟶ b) where
  Hom f g := f.unop ⟶ g.unop

/-- The 2-morphism in `Bᵒᵖ` corresponding to 2-morphism `η : f ⟶ g` in `B`. -/
abbrev op2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : f.op ⟶ g.op := η

@[simps]
instance homCategory (a b : Bᵒᵖ) : Category.{w} (a ⟶ b) where
  id f := (𝟙 f.unop)
  comp η θ := η ≫ θ

-- @[simp]
-- theorem op2_id {a b : B} {f : a ⟶ b} : op2 (𝟙 f) = 𝟙 f.op :=
--   rfl

-- @[simp]
-- theorem unop2_id_op {a b : B} {f : a ⟶ b} : unop2 (𝟙 f.op) = 𝟙 f :=
--   rfl

-- @[simp]
-- theorem op2_id_unop {a b : Bᵒᵖ} {f : a ⟶ b} : op2 (𝟙 f.unop) = 𝟙 f :=
--   rfl

/-- The natural functor from the hom-category `a ⟶ b` in `B` to its bicategorical opposite
`bop b ⟶ bop a`. -/
@[simps]
def opFunctor (a b : B) : (a ⟶ b) ⥤ (op b ⟶ op a) where
  obj f := f.op
  map η := η

/-- The functor from the hom-category `a ⟶ b` in `Bᵒᵖ` to its bicategorical opposite
`unop b ⟶ unop a`. -/
@[simps]
def unopFunctor (a b : Bᵒᵖ) : (a ⟶ b) ⥤ (unop b ⟶ unop a) where
  obj f := f.unop
  map η := η

end Bicategory.Opposite

namespace CategoryTheory.Iso

open Bicategory.Opposite

variable {B : Type u} [Bicategory.{w, v} B]

/-- A 2-isomorphism in `B` gives a 2-isomorphism in `Bᵒᵖ` -/
@[simps!]
abbrev op2 {a b : B} {f g : a ⟶ b} (η : f ≅ g) : f.op ≅ g.op := (opFunctor a b).mapIso η

/-- A 2-isomorphism in `B` gives a 2-isomorphism in `Bᵒᵖ` -/
@[simps!]
abbrev op2_unop {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f.unop ≅ g.unop) : f ≅ g :=
  (opFunctor b.unop a.unop).mapIso η

/-- A 2-isomorphism in `Bᵒᵖ` gives a 2-isomorphism in `B` -/
@[simps!]
abbrev unop2 {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f ≅ g) : f.unop ≅ g.unop :=
  (unopFunctor a b).mapIso η

/-- A 2-isomorphism in `Bᵒᵖ` gives a 2-isomorphism in `B` -/
@[simps!]
abbrev unop2_op {a b : B} {f g : a ⟶ b} (η : f.op ≅ g.op) : f ≅ g :=
  (unopFunctor (op b) (op a)).mapIso η

@[simp]
theorem unop2_bop2 {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f ≅ g) : η.unop2.op2 = η := rfl

end CategoryTheory.Iso

namespace Bicategory.Opposite

variable {B : Type u} [Bicategory.{w, v} B]

/-- The 1-cell dual bicategory `Bᵒᵖ`.

It is defined as follows.
* The objects of `Bᵒᵖ` correspond to objects of `B`.
* The morphisms `X ⟶ Y` in `Bᵒᵖ` are the morphisms `Y ⟶ X` in `B`.
* The 2-morphisms `f ⟶ g` in `Bᵒᵖ` are the 2-morphisms `f ⟶ g` in `B`. In other words, the
  directions of the 2-morphisms are preserved.
-/
@[simps!]
instance bicategory : Bicategory.{w, v} Bᵒᵖ where
  homCategory := homCategory
  whiskerLeft f g h η := η ▷ f.unop
  whiskerRight η h := h.unop ◁ η
  associator f g h := (associator h.unop g.unop f.unop).op2_unop.symm
  leftUnitor f := (rightUnitor f.unop).op2_unop
  rightUnitor f := (leftUnitor f.unop).op2_unop
  whisker_exchange η θ := (whisker_exchange _ _).symm

attribute [-simp] bicategory_Hom bicategory_comp

end Bicategory.Opposite
