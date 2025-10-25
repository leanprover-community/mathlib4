/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# Opposite bicategories

We construct the 1-cell opposite of a bicategory `B`, called `Bᴮᵒᵖ`. It is defined as follows
* The objects of `Bᴮᵒᵖ` correspond to objects of `B`.
* The morphisms `X ⟶ Y` in `Bᴮᵒᵖ` are the morphisms `Y ⟶ X` in `B`.
* The 2-morphisms `f ⟶ g` in `Bᴮᵒᵖ` are the 2-morphisms `f ⟶ g` in `B`. In other words, the
  directions of the 2-morphisms are preserved.

Note that the standard notation for the opposite of a bicategory is `Bᵒᵖ`, however this clashes
with the notation for the opposite of a 1-category, so we use `Bᴮᵒᵖ` instead.

# Remarks
There are multiple notions of opposite categories for bicategories.
- There is 1-cell dual `Bᴮᵒᵖ` as defined above.
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


/-- The type of objects of the 1-cell opposite of a bicategory `B` -/
structure Bicategory.Opposite (B : Type u) where
  /-- The object of `Bᴮᵒᵖ` that represents `b : B` -/  bop ::
  /-- The object of `B` that represents `b : Bᴮᵒᵖ` -/ unbop : B

namespace Bicategory.Opposite

variable {B : Type u}

@[inherit_doc]
notation:max B "ᴮᵒᵖ" => Bicategory.Opposite B

theorem bop_injective : Function.Injective (bop : B → Bᴮᵒᵖ) := fun _ _ => congr_arg Opposite.unbop

theorem unbop_injective : Function.Injective (unbop : Bᴮᵒᵖ → B) := fun _ _ h => congrArg bop h

theorem bop_inj_iff (x y : B) : bop x = bop y ↔ x = y :=
  bop_injective.eq_iff

@[simp]
theorem unbop_inj_iff (x y : Bᴮᵒᵖ) : unbop x = unbop y ↔ x = y :=
  unbop_injective.eq_iff

@[simp]
theorem bop_unbop (a : Bᴮᵒᵖ) : bop (unbop a) = a :=
  rfl

/-- The type-level equivalence between a type and its opposite. -/
def equivToOpposite : B ≃ Bᴮᵒᵖ where
  toFun := bop
  invFun := unbop
  left_inv := unop_op -- Q: why does this "trick" work?
  right_inv := bop_unbop

theorem bop_surjective : Function.Surjective (bop : B → Bᴮᵒᵖ) := equivToOpposite.surjective

theorem unbop_surjective : Function.Surjective (unbop : Bᴮᵒᵖ → B) := equivToOpposite.symm.surjective

@[simp]
theorem equivToBopposite_coe : (equivToOpposite : B → Bᴮᵒᵖ) = bop :=
  rfl

@[simp]
theorem equivToBopposite_symm_coe : (equivToOpposite.symm : Bᴮᵒᵖ → B) = unbop :=
  rfl

theorem bop_eq_iff_eq_unbop {x : B} {y} : bop x = y ↔ x = unbop y :=
  equivToOpposite.apply_eq_iff_eq_symm_apply

theorem unbop_eq_iff_eq_bop {x} {y : B} : unbop x = y ↔ x = bop y :=
  equivToOpposite.symm.apply_eq_iff_eq_symm_apply

variable {B : Type u} [Bicategory.{w, v} B]

/-- `Bᴮᵒᵖ` reverses the 1-morphisms in `B` -/
instance Hom : Quiver Bᴮᵒᵖ where
  Hom := fun a b => (unbop b ⟶ unbop a)ᴮᵒᵖ

/-- The opposite of a 1-morphism in `B`.

This abbrev is necessary since for `f : a ⟶ b`, `bop f` has type `(a ⟶ b)ᴮᵒᵖ`, but we want
to have `(b ⟶ a)ᴮᵒᵖ` instead. -/
abbrev _root_.Quiver.Hom.bop1 {a b : B} (f : a ⟶ b) : bop b ⟶ bop a :=
  Bicategory.Opposite.bop f

/-- `Bᴮᵒᵖ` preserves the direction of all 2-morphisms in `B` -/
instance Hom2 (a b : Bᴮᵒᵖ) : Quiver (a ⟶ b) where
  Hom := fun f g => (f.unbop ⟶ g.unbop)ᴮᵒᵖ

/-- The 2-morphism in `Bᴮᵒᵖ` corresponding to 2-morphism `η : f ⟶ g` in `B`. -/
abbrev bop2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : f.bop1 ⟶ g.bop1 :=
  bop η

@[simps]
instance homCategory {a b : Bᴮᵒᵖ} : Category.{w} (a ⟶ b) where
  id := fun f => bop2 (𝟙 f.unbop)
  comp := fun η θ => bop2 (η.unbop ≫ θ.unbop)
  id_comp := fun {f g} η => by simp only [bop_unbop, Category.id_comp (η.unbop)]

@[simp]
theorem bop2_id {a b : B} {f : a ⟶ b} : bop2 (𝟙 f) = 𝟙 f.bop1 :=
  rfl

@[simp]
theorem unbop2_id_bop {a b : B} {f : a ⟶ b} : unbop (𝟙 f.bop1) = 𝟙 f :=
  rfl

@[simp]
theorem bop2_id_unbop {a b : Bᴮᵒᵖ} {f : a ⟶ b} : bop2 (𝟙 f.unbop) = 𝟙 f :=
  rfl

/-- The natural functor from the hom-category `a ⟶ b` in `B` to its bicategorical opposite
`bop b ⟶ bop a`. -/
@[simps?]
def bopFunctor (a b : B) : (a ⟶ b) ⥤ (bop b ⟶ bop a) where
  obj f := f.bop1
  map η := bop2 η

/-- The functor from the hom-category `a ⟶ b` in `Bᴮᵒᵖ` to its bicategorical opposite
`unbop b ⟶ unbop a`. -/
@[simps]
def unbopFunctor (a b : Bᴮᵒᵖ) : (a ⟶ b) ⥤ (unbop b ⟶ unbop a) where
  obj f := f.unbop
  map η := η.unbop


end Bicategory.Opposite

namespace CategoryTheory.Iso

open Bicategory.Opposite

variable {B : Type u} [Bicategory.{w, v} B]

/-- A 2-isomorphism in `B` gives a 2-isomorphism in `Bᴮᵒᵖ` -/
@[simps!]
abbrev bop2 {a b : B} {f g : a ⟶ b} (η : f ≅ g) : f.bop1 ≅ g.bop1 := (bopFunctor a b).mapIso η

/-- A 2-isomorphism in `Bᴮᵒᵖ` gives a 2-isomorphism in `Bᴮ` -/
@[simps!]
abbrev unbop2 {a b : Bᴮᵒᵖ} {f g : a ⟶ b} (η : f ≅ g) : f.unbop ≅ g.unbop :=
  (unbopFunctor a b).mapIso η

@[simp]
theorem unbop2_bop2 {a b : Bᴮᵒᵖ} {f g : a ⟶ b} (η : f ≅ g) : η.unbop2.bop2 = η := rfl

end CategoryTheory.Iso

namespace Bicategory.Opposite

variable {B : Type u} [Bicategory.{w, v} B]

/-- The 1-cell dual bicategory `Bᴮᵒᵖ`.

It is defined as follows.
* The objects of `Bᴮᵒᵖ` correspond to objects of `B`.
* The morphisms `X ⟶ Y` in `Bᴮᵒᵖ` are the morphisms `Y ⟶ X` in `B`.
* The 2-morphisms `f ⟶ g` in `Bᴮᵒᵖ` are the 2-morphisms `f ⟶ g` in `B`. In other words, the
  directions of the 2-morphisms are preserved.
-/
@[simps!]
instance bicategory : Bicategory.{w, v} Bᴮᵒᵖ where
  id a := (𝟙 a.unbop).bop1
  comp f g := (g.unbop ≫ f.unbop).bop1
  whiskerLeft f g h η := bop2 ((unbop η) ▷ f.unbop)
  whiskerRight η h := bop2 (h.unbop ◁ (unbop η))
  associator f g h := (associator h.unbop g.unbop f.unbop).symm.bop2
  leftUnitor f := (rightUnitor f.unbop).bop2
  rightUnitor f := (leftUnitor f.unbop).bop2
  whiskerLeft_id f g := congrArg bop <| id_whiskerRight g.unbop f.unbop
  whiskerLeft_comp f g h i η θ := congrArg bop <| comp_whiskerRight (unbop η) (unbop θ) f.unbop
  id_whiskerLeft η := congrArg bop <| whiskerRight_id (unbop η)
  comp_whiskerLeft {a b c d} f g {h h'} η := congrArg bop <| whiskerRight_comp (unbop η) _ _
  id_whiskerRight f g := congrArg bop <| whiskerLeft_id g.unbop f.unbop
  comp_whiskerRight η θ i := congrArg bop <| whiskerLeft_comp i.unbop (unbop η) (unbop θ)
  whiskerRight_id η := congrArg bop <| id_whiskerLeft (unbop η)
  whiskerRight_comp η g h := congrArg bop <| comp_whiskerLeft h.unbop g.unbop (unbop η)
  whisker_assoc f g g' η i := by apply congrArg bop; simp only [bop_unbop, Functor.mapIso_symm,
    Iso.symm_hom, Functor.mapIso_inv, bopFunctor_map_unbop, whisker_assoc i.unbop η.unbop f.unbop,
    Iso.symm_inv,
    Functor.mapIso_hom, homCategory_comp_unbop, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]
  whisker_exchange η θ := congrArg bop <| (whisker_exchange _ _).symm
  pentagon f g h i := congrArg bop <| pentagon_inv _ _ _ _
  triangle f g := congrArg bop <| triangle_assoc_comp_right _ _

attribute [-simp] bicategory_Hom -- this seems to cause issues with automation

end Bicategory.Opposite
