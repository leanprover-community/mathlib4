/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
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

Provide various lemmas in going between `LocallyDiscrete Cᵒᵖ` and `(LocallyDiscrete C)ᵒᵖ`.
Define the natural pseudofunctor from `B` to `Bᴮᵒᵖ`.
Expand API (do after I have started using it)

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
  left_inv := unop_op -- todo whyyy is this typo OK??
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

end Bicategory.Opposite

variable {B : Type u} [Bicategory.{w, v} B]

section

-- renaming to make bop_inj and unbop_inj work... TODO
open Bicategory.Opposite

/-- `Bᴮᵒᵖ` reverses the 1-morphisms in `B` -/
instance Hom : Quiver (Bᴮᵒᵖ) where
  -- TODO: maybe this here should be ᵒᵖ? So that we can get some of that API (like op of a functor)
  Hom := fun a b => (unbop b ⟶ unbop a)ᵒᵖ

namespace Quiver.Hom

/-- The opposite of a 1-morphism in `B`. -/
def bop {a b : B} (f : a ⟶ b) : bop b ⟶ bop a := ⟨f⟩

/-- Given a 1-morhpism in `Bᴮᵒᵖ`, we can take the "unopposite" back in `B`. -/
def unbop {a b : Bᴮᵒᵖ} (f : a ⟶ b) : unbop b ⟶ unbop a :=
  -- TODO: namespace?
  Opposite.unop f

-- theorem bop_inj {X Y : B} :
--     Function.Injective (bop : (X ⟶ Y) → (bop' X ⟶ bop' Y)) :=
--   fun _ _ H => congr_arg Quiver.Hom.unbop H

-- theorem unbop_inj {X Y : Bᴮᵒᵖ} :
--     Function.Injective (Quiver.Hom.unbop : (X ⟶ Y) → (unbop' X ⟶ unbop' Y)) :=
--   fun _ _ H => congr_arg Quiver.Hom.mop H

@[simp]
theorem unbop_bop {X Y : B} (f : X ⟶ Y) : f.bop.unbop = f :=
  rfl

@[simp]
theorem bop_unbop {X Y : Bᴮᵒᵖ} (f : X ⟶ Y) : f.unbop.bop = f :=
  rfl

end Quiver.Hom

end

namespace Bicategory.Opposite

/-- `Bᴮᵒᵖ` preserves the direction of all 2-morphisms in `B` -/
instance homCategory (a b : Bᴮᵒᵖ) : Quiver (a ⟶ b) where
  Hom := fun f g => (f.unbop ⟶ g.unbop)ᴮᵒᵖ

/-- The 1-cell opposite of a natural transformation `η : f ⟶ g` in `B`. -/
abbrev bop2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : f.bop ⟶ g.bop :=
  Bicategory.Opposite.bop η

/-- The 1-cell opposite of a natural transformation `η : f ⟶ g` in `Bᴮᵒᵖ`. -/
abbrev unbop2 {a b : Bᴮᵒᵖ} {f g : a ⟶ b} (η : f ⟶ g) : f.unbop ⟶ g.unbop :=
  Bicategory.Opposite.unbop η

-- @[simps] here causes a loop!!!!
instance homCategory.Opposite {a b : Bᴮᵒᵖ} : Category.{w} (a ⟶ b) where
  id := fun f => bop2 (𝟙 f.unbop)
  comp := fun η θ => bop2 ((unbop2 η) ≫ (unbop2 θ))
  -- TODO: why do I need to specify Category.id_comp here...
  id_comp := fun {f g} η => by simp [Category.id_comp (unbop2 η)]

@[simp]
theorem bop2_comp {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    bop2 (η ≫ θ) = bop2 η ≫ bop2 θ :=
  rfl

@[simp]
theorem bop2_id {a b : B} {f : a ⟶ b} : bop2 (𝟙 f) = 𝟙 f.bop :=
  rfl

@[simp]
theorem unbop2_comp {a b : Bᴮᵒᵖ} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    unbop2 (η ≫ θ) = unbop2 η ≫ unbop2 θ :=
  rfl

@[simp]
theorem unbop2_id {a b : Bᴮᵒᵖ} {f : a ⟶ b} : unbop2 (𝟙 f) = 𝟙 f.unbop :=
  rfl

@[simp]
theorem unbop2_id_bop {a b : B} {f : a ⟶ b} : unbop2 (𝟙 f.bop) = 𝟙 f :=
  rfl

@[simp]
theorem bop2_id_unbop {a b : Bᴮᵒᵖ} {f : a ⟶ b} : bop2 (𝟙 f.unbop) = 𝟙 f :=
  rfl

/-- The natural functor from the hom-category `a ⟶ b` in `B` to its bicategorical opposite
`bop b ⟶ bop a`. -/
@[simps]
def bopFunctor (a b : B) : (a ⟶ b) ⥤ (bop b ⟶ bop a) where
  obj f := f.bop
  map η := bop2 η

/-- The functor from the hom-category `a ⟶ b` in `Bᴮᵒᵖ` to its bicategorical opposite
`unbop b ⟶ unbop a`. -/
@[simps]
def unbopFunctor (a b : Bᴮᵒᵖ) : (a ⟶ b) ⥤ (unbop b ⟶ unbop a) where
  obj f := f.unbop
  map η := unbop2 η

end Bicategory.Opposite

namespace CategoryTheory.Iso

open Bicategory.Opposite

/-- A 2-isomorphism in `B` gives a 2-isomorphism in `Bᴮᵒᵖ` -/
@[simps!]
abbrev bop2 {a b : B} {f g : a ⟶ b} (η : f ≅ g) : f.bop ≅ g.bop := (bopFunctor a b).mapIso η

/-- A 2-isomorphism in `Bᴮᵒᵖ` gives a 2-isomorphism in `Bᴮ` -/
@[simps!]
abbrev unbop2 {a b : Bᴮᵒᵖ} {f g : a ⟶ b} (η : f ≅ g) : f.unbop ≅ g.unbop :=
  (unbopFunctor a b).mapIso η

@[simp]
theorem unbop2_bop2 {a b : Bᴮᵒᵖ} {f g : a ⟶ b} (η : f ≅ g) : η.unbop2.bop2 = η := by (ext; rfl)

@[simp]
theorem unbop2_bop {a b : Bᴮᵒᵖ} {f g : a ⟶ b} (η : f ≅ g) : η.unbop2.bop2 = η := by (ext; rfl)

end CategoryTheory.Iso

namespace Bicategory.Opposite

/-- The 1-cell dual bicategory `Bᴮᵒᵖ`.

It is defined as follows.
* The objects of `Bᴮᵒᵖ` correspond to objects of `B`.
* The morphisms `X ⟶ Y` in `Bᴮᵒᵖ` are the morphisms `Y ⟶ X` in `B`.
* The 2-morphisms `f ⟶ g` in `Bᴮᵒᵖ` are the 2-morphisms `f ⟶ g` in `B`. In other words, the
  directions of the 2-morphisms are preserved.
-/
@[simps!]
instance bicategory : Bicategory.{w, v} Bᴮᵒᵖ where
  id := fun a => (𝟙 a.unbop).bop
  comp := fun f g => (g.unbop ≫ f.unbop).bop
  whiskerLeft f g h η := bop2 ((unbop2 η) ▷ f.unbop)
  whiskerRight η h := bop2 (h.unbop ◁ (unbop2 η))
  -- I'm not sure why I need to do `by exact` here...
  associator f g h := by exact (Bicategory.associator h.unbop g.unbop f.unbop).symm.bop2
  leftUnitor f := by exact (Bicategory.rightUnitor f.unbop).bop2
  rightUnitor f := by exact (Bicategory.leftUnitor f.unbop).bop2
  whiskerLeft_id f g := unbop_injective <| Bicategory.id_whiskerRight g.unbop f.unbop
  whiskerLeft_comp f g h i η θ := unbop_injective <|
    Bicategory.comp_whiskerRight (unbop2 η) (unbop2 θ) f.unbop
  id_whiskerLeft η := unbop_injective <| whiskerRight_id (unbop2 η)
  comp_whiskerLeft {a b c d} f g {h h'} η := unbop_injective <|
    whiskerRight_comp (unbop2 η) g.unbop f.unbop
  id_whiskerRight f g := unbop_injective <| Bicategory.whiskerLeft_id g.unbop f.unbop
  comp_whiskerRight η θ i := unbop_injective <|
    Bicategory.whiskerLeft_comp i.unbop (unbop2 η) (unbop2 θ)
  whiskerRight_id η := unbop_injective <| id_whiskerLeft (unbop2 η)
  whiskerRight_comp η g h := unbop_injective <| comp_whiskerLeft h.unbop g.unbop (unbop2 η)
  whisker_assoc f g g' η i := by apply unbop_injective; simp
  whisker_exchange η θ := by apply unbop_injective; simp [(whisker_exchange _ _).symm]
  pentagon f g h i := by apply unbop_injective; simp
  triangle f g := by apply unbop_injective; simp

-- TODO: initialize simps projections here...

end Bicategory.Opposite
