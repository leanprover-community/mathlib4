/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Opposites

/-!
# Opposite bicategories

We construct the 1-cell opposite of a bicategory `B`, called `Bᴮᵒᵖ`. It is defined as follows
* The objects of `Bᴮᵒᵖ` correspond to objects of `B`.
* The morphisms `X ⟶ Y` in `Bᴮᵒᵖ` are the morphisms `Y ⟶ X` in `B`.
* The 2-morphisms `f ⟶ g` in `Bᴮᵒᵖ` are the 2-morphisms `f ⟶ g` in `B`. In other words, the
  directions of the 2-morphisms are preserved.


# Remarks
There are multiple notions of opposite categories for bicategories.
- There is 1-cell dual `Bᴮᵒᵖ` as defined above.
- There is the 2-cell dual, `Cᶜᵒ` where only the natural transformations are reversed
- There is the bi-dual `Cᶜᵒᵒᵖ` where the directions of both the morphisms and the natural
  transformations are reversed.

## TODO

* Define the 2-cell dual `Cᶜᵒ`.
* Provide various lemmas for going between `LocallyDiscrete Cᵒᵖ` and `(LocallyDiscrete C)ᵒᵖ`.

Note: `Cᶜᵒᵒᵖ` is WIP by Joël Riou and Christian Mertner.

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

@[simp]
theorem unbop_bop (a : B) : unbop (bop a) = a :=
  rfl

/-- The type-level equivalence between a type and its opposite. -/
def equivToOpposite : B ≃ Bᴮᵒᵖ where
  toFun := bop
  invFun := unbop
  left_inv := unbop_bop -- TODO: type with unop_op works here!!??
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

/-- The opposite of a 1-morphism in `B`. -/
abbrev _root_.Quiver.Hom.bop1 {a b : B} (f : a ⟶ b) : bop b ⟶ bop a :=
  Bicategory.Opposite.bop f

/-- Given a 1-morhpism in `Bᴮᵒᵖ`, we can take the "unopposite" back in `B`. -/
abbrev _root_.Quiver.Hom.unbop1 {a b : Bᴮᵒᵖ} (f : a ⟶ b) : unbop b ⟶ unbop a :=
  Bicategory.Opposite.unbop f

/-- `Bᴮᵒᵖ` preserves the direction of all 2-morphisms in `B` -/
@[simps]
instance (a b : Bᴮᵒᵖ) : Quiver (a ⟶ b) where
  Hom := fun f g => (f.unbop1 ⟶ g.unbop1)ᴮᵒᵖ

/-- The 1-cell opposite of a 2-morphism `η : f ⟶ g` in `B`. -/
abbrev bop2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : f.bop1 ⟶ g.bop1 :=
  bop η

/-- The 1-cell opposite of a 2-morphism `η : f ⟶ g` in `Bᴮᵒᵖ`. -/
abbrev unbop2 {a b : Bᴮᵒᵖ} {f g : a ⟶ b} (η : f ⟶ g) : f.unbop ⟶ g.unbop :=
  unbop η

instance homCategory {a b : Bᴮᵒᵖ} : Category.{w} (a ⟶ b) where
  id := fun f => bop2 (𝟙 f.unbop1)
  comp := fun η θ => bop2 (unbop2 η ≫ unbop2 θ)
  id_comp := fun {f g} η => by simp only [bop_unbop, Category.id_comp (unbop2 η)]

@[simp]
theorem bop2_comp {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    bop2 (η ≫ θ) = bop2 η ≫ bop2 θ :=
  rfl

@[simp]
theorem bop2_id {a b : B} {f : a ⟶ b} : bop2 (𝟙 f) = 𝟙 f.bop1 :=
  rfl

@[simp]
theorem unbop2_comp {a b : Bᴮᵒᵖ} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    unbop2 (η ≫ θ) = unbop2 η ≫ unbop2 θ :=
  rfl

@[simp]
theorem unbop2_id {a b : Bᴮᵒᵖ} {f : a ⟶ b} : unbop2 (𝟙 f) = 𝟙 f.unbop1 :=
  rfl

@[simp]
theorem unbop2_id_bop {a b : B} {f : a ⟶ b} : unbop2 (𝟙 f.bop1) = 𝟙 f :=
  rfl

@[simp]
theorem bop2_id_unbop {a b : Bᴮᵒᵖ} {f : a ⟶ b} : bop2 (𝟙 f.unbop1) = 𝟙 f :=
  rfl

/-- The natural functor from the hom-category `a ⟶ b` in `B` to its bicategorical opposite
`bop b ⟶ bop a`. -/
@[simps]
def bopFunctor (a b : B) : (a ⟶ b) ⥤ (bop b ⟶ bop a) where
  obj f := f.bop1
  map η := bop2 η

/-- The functor from the hom-category `a ⟶ b` in `Bᴮᵒᵖ` to its bicategorical opposite
`unbop b ⟶ unbop a`. -/
@[simps]
def unbopFunctor (a b : Bᴮᵒᵖ) : (a ⟶ b) ⥤ (unbop b ⟶ unbop a) where
  obj f := f.unbop1
  map η := unbop2 η

end Bicategory.Opposite

-- TODO: namespace here should include bicategory?
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
@[simps!] -- TODO: custom simp lemmas
instance bicategory : Bicategory.{w, v} Bᴮᵒᵖ where
  id := fun a => (𝟙 a.unbop).bop1
  comp := fun f g => (g.unbop1 ≫ f.unbop1).bop1
  whiskerLeft f g h η := bop2 ((unbop2 η) ▷ f.unbop)
  whiskerRight η h := bop2 (h.unbop ◁ (unbop2 η))
  associator f g h := (associator h.unbop g.unbop f.unbop).symm.bop2
  leftUnitor f := (rightUnitor f.unbop).bop2
  rightUnitor f := (leftUnitor f.unbop).bop2
  whiskerLeft_id f g := congrArg bop <| id_whiskerRight g.unbop f.unbop
  whiskerLeft_comp f g h i η θ := congrArg bop <| comp_whiskerRight (unbop2 η) (unbop2 θ) f.unbop
  id_whiskerLeft η := congrArg bop <| whiskerRight_id (unbop2 η)
  comp_whiskerLeft {a b c d} f g {h h'} η := congrArg bop <| whiskerRight_comp (unbop2 η) _ _
  id_whiskerRight f g := congrArg bop <| whiskerLeft_id g.unbop f.unbop
  comp_whiskerRight η θ i := congrArg bop <| whiskerLeft_comp i.unbop (unbop2 η) (unbop2 θ)
  whiskerRight_id η := congrArg bop <| id_whiskerLeft (unbop2 η)
  whiskerRight_comp η g h := congrArg bop <| comp_whiskerLeft h.unbop g.unbop (unbop2 η)
  whisker_assoc f g g' η i := by apply congrArg bop; dsimp; simp
  whisker_exchange η θ := congrArg bop <| (whisker_exchange _ _).symm
  pentagon f g h i := congrArg bop <| pentagon_inv _ _ _ _
  triangle f g := congrArg bop <| triangle_assoc_comp_right _ _

end Bicategory.Opposite
