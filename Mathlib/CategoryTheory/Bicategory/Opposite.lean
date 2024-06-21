/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Opposites

/-!
# Opposite bicategories

We provide a bicategory instance on `Cᵒᵖ` given a bicategory instance on `C`.
The morphisms `X ⟶ Y` in `Cᵒᵖ` are the morphisms `Y ⟶ X` in `C`.
The natural transformations `F ⟶ G` in `Cᵒᵖ` are the natural transformations `unop F ⟶ unop G` in
`C`, in other words the directions of natural transformations are preserved.

We also provide various lemmas in going between `LocallyDiscrete Cᵒᵖ` and `(LocallyDiscrete C)ᵒᵖ`.

# Remarks
There are multiple notions of opposite categories for bicategories.
- There is `Cᵒᵖ` as defined above, also known as the "1-cell dual".
- There is the "2-cell dual", `Cᶜᵒ` where only the natural transformations are reversed
- There is the "bi-dual" `Cᶜᵒᵒᵖ` where the directions of both the morphisms and the natural
  transformations are reversed.
-/

universe w v u

open CategoryTheory Bicategory Opposite


/-- The type of objects of the 1-cell opposite of a bicategory `B` -/
structure Bicategory.opposite (B : Type u) :=
  /-- The canonical map `Bᴮᵒᵖ` -/
  unbop : B

namespace Bicategory.opposite

variable {B : Type u}

notation:max B "ᴮᵒᵖ" => Bicategory.opposite B

def bop (a : B) : Bᴮᵒᵖ := ⟨a⟩

theorem bop_injective : Function.Injective (bop : B → Bᴮᵒᵖ) := fun _ _ => congr_arg opposite.unbop

theorem unbop_injective : Function.Injective (unbop : Bᴮᵒᵖ → B) := fun ⟨_⟩⟨_⟩ => by simp

theorem bop_inj_iff (x y : B) : bop x = bop y ↔ x = y := bop_injective.eq_iff

@[simp]
theorem unmop_inj_iff (x y : Bᴮᵒᵖ) : unbop x = unbop y ↔ x = y := unbop_injective.eq_iff

@[simp]
theorem bop_unbop (a : Bᴮᵒᵖ) : bop (unbop a) = a :=
  rfl

@[simp]
theorem unbop_bop (a : B) : unbop (bop a) = a :=
  rfl

-- TODO: could have more api here, see Data.Opposite

end Bicategory.opposite

open Bicategory.opposite

variable {B : Type u} [Bicategory.{w, v} B]

/-- `Bᴮᵒᵖ` reverses the 1-morphisms in `B` -/
instance Hom : Quiver (Bᴮᵒᵖ) where
  Hom := fun a b => (unbop b ⟶ unbop a)ᴮᵒᵖ

/-- The opposite of a 1-morphism in `B`. -/
def Quiver.Hom.bop {a b : B} (f : a ⟶ b) : bop b ⟶ bop a := ⟨f⟩

/-- Given a 1-morhpism in `Bᴮᵒᵖ`, we can take the "unopposite" back in `B`. -/
def Quiver.Hom.unbop {a b : Bᴮᵒᵖ} (f : a ⟶ b) : unbop b ⟶ unbop a :=
  Bicategory.opposite.unbop f

-- TODO: op/unop inj can be added here
@[simp]
theorem Quiver.Hom.unbop_bop {X Y : B} (f : X ⟶ Y) : f.bop.unbop = f :=
  rfl

@[simp]
theorem Quiver.Hom.bop_unbop {X Y : Bᴮᵒᵖ} (f : X ⟶ Y) : f.unbop.bop = f :=
  rfl

/-- `Bᴮᵒᵖ` preserves the direction of all 2-morphisms in `B` -/
instance homCategory (a b : Bᴮᵒᵖ) : Quiver (a ⟶ b) where
  Hom := fun f g => (f.unbop ⟶ g.unbop)ᴮᵒᵖ

def bop2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : f.bop ⟶ g.bop :=
  Bicategory.opposite.bop η

def unbop2 {a b : Bᴮᵒᵖ} {f g : a ⟶ b} (η : f ⟶ g) : f.unbop ⟶ g.unbop :=
  Bicategory.opposite.unbop η

theorem bop2_inj {a b : B} {f g : a ⟶ b} :
    Function.Injective (bop2 : (f ⟶ g) → (f.bop ⟶ g.bop)) :=
  fun _ _ H => congr_arg unbop2 H

theorem unbop2_inj {a b : Bᴮᵒᵖ} {f g : a ⟶ b} :
    Function.Injective (unbop2 : (f ⟶ g) → (f.unbop ⟶ g.unbop)) :=
  fun _ _ H => congr_arg bop2 H

-- TODO: iff versions of these?

@[simp]
theorem unbop_bop2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : unbop2 (bop2 η) = η := rfl

@[simp]
theorem bop_unbop2 {a b : Bᴮᵒᵖ} {f g : a ⟶ b} (η : f ⟶ g) : bop2 (unbop2 η) = η := rfl

-- @[simps] here causes a loop!!!!
instance homCategory.opposite {a b : Bᴮᵒᵖ} : Category.{w} (a ⟶ b) where
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

namespace CategoryTheory.Iso

/-- The opposite natural isomorphism  -/
@[simps]
protected def bop2 {a b : B} {f g : a ⟶ b} (η : f ≅ g) : f.bop ≅ g.bop where
  hom := bop2 η.hom
  inv := bop2 η.inv
  hom_inv_id := unbop2_inj <| by simp
  inv_hom_id := unbop2_inj <| by simp

/-- The natural isomorphism obtained from a natural isomorphism in `Bᴮᵒᵖ` -/
@[simps]
protected def unbop2 {a b : Bᴮᵒᵖ} {f g : a ⟶ b} (η : f ≅ g) : f.unbop ≅ g.unbop where
  hom := unbop2 η.hom
  inv := unbop2 η.inv
  hom_inv_id := bop2_inj <| by simp
  inv_hom_id := bop2_inj <| by simp

@[simp]
theorem unbop2_bop2 {a b : Bᴮᵒᵖ} {f g : a ⟶ b} (η : f ≅ g) : η.unbop2.bop2 = η := by (ext; rfl)

@[simp]
theorem unbop2_bop {a b : Bᴮᵒᵖ} {f g : a ⟶ b} (η : f ≅ g) : η.unbop2.bop2 = η := by (ext; rfl)

-- TODO: more iso API? removeOp?

end CategoryTheory.Iso

/-- The 1-dual bicategory `Cᵒᵖ`

See ...
-/
@[simps!]
instance Bicategory.Opposite : Bicategory.{w, v} Bᴮᵒᵖ where
  -- Need to break these out and add lemmas for them probably?
  id := fun a => (𝟙 a.unbop).bop
  comp := fun f g => (g.unbop ≫ f.unbop).bop
  whiskerLeft f g h η := bop2 ((unbop2 η) ▷ f.unbop)
  whiskerRight η h := bop2 (h.unbop ◁ (unbop2 η))
  associator f g h := by exact (Bicategory.associator h.unbop g.unbop f.unbop).symm.bop2
  -- TODO: alternative is to use leftUnitor + symm
  leftUnitor f := by exact (Bicategory.rightUnitor f.unbop).bop2
  rightUnitor f := by exact (Bicategory.leftUnitor f.unbop).bop2
  whiskerLeft_id f g := unbop2_inj <| Bicategory.id_whiskerRight g.unbop f.unbop
  whiskerLeft_comp f g h i η θ := unbop2_inj <|
    Bicategory.comp_whiskerRight (unbop2 η) (unbop2 θ) f.unbop
  id_whiskerLeft η := unbop2_inj <| whiskerRight_id (unbop2 η)
  comp_whiskerLeft {a b c d} f g {h h'} η := unbop2_inj <|
    whiskerRight_comp (unbop2 η) g.unbop f.unbop
  id_whiskerRight f g := unbop2_inj <| Bicategory.whiskerLeft_id g.unbop f.unbop
  comp_whiskerRight η θ i := unbop2_inj <| Bicategory.whiskerLeft_comp i.unbop (unbop2 η) (unbop2 θ)
  whiskerRight_id η := unbop2_inj <| id_whiskerLeft (unbop2 η)
  whiskerRight_comp η g h := unbop2_inj <| comp_whiskerLeft h.unbop g.unbop (unbop2 η)
  whisker_assoc f g g' η i := by apply unbop2_inj; simp
  whisker_exchange η θ := by apply unbop2_inj; simp [(whisker_exchange (unbop2 θ) (unbop2 η)).symm]
  pentagon f g h i := by apply unbop2_inj; simp
  triangle f g := by apply unbop2_inj; simp


/-
TODO:
- simp lemmas
- compatability with LocallyDiscrete
-- Want a functor between them?

-/
