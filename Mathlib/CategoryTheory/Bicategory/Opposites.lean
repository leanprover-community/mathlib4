/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.Opposites

/-!
# Opposite bicategories

We construct the 1-cell opposite of a bicategory `B`, called `Bᵒᵖ`. It is defined as follows
* The objects of `Bᵒᵖ` correspond to objects of `B`.
* The morphisms `X ⟶ Y` in `Bᵒᵖ` are the morphisms `Y ⟶ X` in `B`.
* The 2-morphisms `f ⟶ g` in `Bᵒᵖ` are the 2-morphisms `f.unop ⟶ g.unop` in `B`. In other
  words, the directions of the 2-morphisms are preserved.

## Remarks
There are multiple notions of opposite categories for bicategories.
- There is 1-cell dual `Bᵒᵖ` as defined above.
- There is the 2-cell dual, `Cᶜᵒ` where only the 2-morphisms are reversed
- There is the bi-dual `Cᶜᵒᵒᵖ` where the directions of both the 1-morphisms and the 2-morphisms
  are reversed.

## TODO

* Define the 2-cell dual `Cᶜᵒ`.
* Provide various lemmas for going between `LocallyDiscrete Cᵒᵖ` and `(LocallyDiscrete C)ᵒᵖ`.

Note: `Cᶜᵒᵒᵖ` is WIP by Christian Merten.

-/

@[expose] public section

universe w v u

open CategoryTheory Bicategory Opposite

namespace Bicategory.Opposite

variable {B : Type u} [Bicategory.{w, v} B]

/-- Type synonym for 2-morphisms in the opposite bicategory. -/
structure Hom2 {a b : Bᵒᵖ} (f g : a ⟶ b) where
  op2' ::
  /-- `Bᵒᵖ` preserves the direction of all 2-morphisms in `B` -/
  unop2 : f.unop ⟶ g.unop

open Hom2

@[simps!]
instance homCategory (a b : Bᵒᵖ) : Category.{w} (a ⟶ b) where
  Hom f g := Hom2 f g
  id f := op2' (𝟙 f.unop)
  comp η θ := op2' (η.unop2 ≫ θ.unop2)

/-- Synonym for constructor of `Hom2` where the 1-morphisms `f` and `g` lie in `B` and not `Bᵒᵖ`. -/
def op2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : f.op ⟶ g.op :=
  op2' η

@[simp]
theorem unop2_op2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : (op2 η).unop2 = η :=
  rfl

@[simp]
theorem op2_unop2 {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f ⟶ g) : op2 η.unop2 = η :=
  rfl

@[simp]
theorem op2_comp {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    op2 (η ≫ θ) = (op2 η) ≫ (op2 θ) :=
  rfl

@[simp]
theorem op2_id {a b : B} {f : a ⟶ b} : op2 (𝟙 f) = 𝟙 f.op :=
  rfl

@[simp]
theorem unop2_comp {a b : Bᵒᵖ} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    unop2 (η ≫ θ) = unop2 η ≫ unop2 θ :=
  rfl

@[simp]
theorem unop2_id {a b : Bᵒᵖ} {f : a ⟶ b} : unop2 (𝟙 f) = 𝟙 f.unop :=
  rfl

@[simp]
theorem unop2_id_bop {a b : B} {f : a ⟶ b} : unop2 (𝟙 f.op) = 𝟙 f :=
  rfl

@[simp]
theorem op2_id_unbop {a b : Bᵒᵖ} {f : a ⟶ b} : op2 (𝟙 f.unop) = 𝟙 f :=
  rfl

/-- The natural functor from the hom-category `a ⟶ b` in `B` to its bicategorical opposite
`op b ⟶ op a`. -/
@[simps]
def opFunctor (a b : B) : (a ⟶ b) ⥤ (op b ⟶ op a) where
  obj f := f.op
  map η := op2 η

/-- The functor from the hom-category `a ⟶ b` in `Bᵒᵖ` to its bicategorical opposite
`unop b ⟶ unop a`. -/
@[simps]
def unopFunctor (a b : Bᵒᵖ) : (a ⟶ b) ⥤ (unop b ⟶ unop a) where
  obj f := f.unop
  map η := unop2 η

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
theorem unop2_op2 {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f ≅ g) : η.unop2.op2 = η := rfl

end CategoryTheory.Iso

namespace Bicategory.Opposite

open Hom2

variable {B : Type u} [Bicategory.{w, v} B]

/-- The 1-cell dual bicategory `Bᵒᵖ`.

It is defined as follows.
* The objects of `Bᵒᵖ` correspond to objects of `B`.
* The morphisms `X ⟶ Y` in `Bᵒᵖ` are the morphisms `Y ⟶ X` in `B`.
* The 2-morphisms `f ⟶ g` in `Bᵒᵖ` are the 2-morphisms `f.unop ⟶ g.unop` in `B`. In other
  words, the directions of the 2-morphisms are preserved.
-/
@[simps! homCategory_id_unop2 homCategory_comp_unop2 whiskerLeft_unop2 whiskerRight_unop2
  associator_hom_unop2 associator_inv_unop2 leftUnitor_hom_unop2 leftUnitor_inv_unop2
  rightUnitor_hom_unop2 rightUnitor_inv_unop2]
instance bicategory : Bicategory.{w, v} Bᵒᵖ where
  homCategory := homCategory
  whiskerLeft f g h η := op2 <| (unop2 η) ▷ f.unop
  whiskerRight η h := op2 <| h.unop ◁ unop2 η
  associator f g h := (associator h.unop g.unop f.unop).op2_unop.symm
  leftUnitor f := (rightUnitor f.unop).op2_unop
  rightUnitor f := (leftUnitor f.unop).op2_unop
  whisker_exchange η θ := congrArg op2 <| (whisker_exchange _ _).symm
  whisker_assoc f g g' η i := congrArg op2 <| by simp
  pentagon f g h i := congrArg op2 <| by simp
  triangle f g := congrArg op2 <| by simp

@[simp]
lemma op2_whiskerLeft {a b c : B} {f : a ⟶ b} {g g' : b ⟶ c} (η : g ⟶ g') :
    op2 (f ◁ η) = (op2 η) ▷ f.op :=
  rfl

@[simp]
lemma op2_whiskerRight {a b c : B} {f f' : a ⟶ b} {g : b ⟶ c} (η : f ⟶ f') :
    op2 (η ▷ g) = g.op ◁ (op2 η) :=
  rfl

@[simp]
lemma op2_associator {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).op2 = (α_ h.op g.op f.op).symm :=
  rfl

@[simp]
lemma op2_associator_hom {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    op2 (α_ f g h).hom = (α_ h.op g.op f.op).symm.hom :=
  rfl

@[simp]
lemma op2_associator_inv {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    op2 (α_ f g h).inv = (α_ h.op g.op f.op).symm.inv :=
  rfl

@[simp]
lemma op2_leftUnitor {a b : B} (f : a ⟶ b) :
    (λ_ f).op2 = ρ_ f.op :=
  rfl

@[simp]
lemma op2_leftUnitor_hom {a b : B} (f : a ⟶ b) :
    op2 (λ_ f).hom = (ρ_ f.op).hom :=
  rfl

@[simp]
lemma op2_leftUnitor_inv {a b : B} (f : a ⟶ b) :
    op2 (λ_ f).inv = (ρ_ f.op).inv :=
  rfl

@[simp]
lemma op2_rightUnitor {a b : B} (f : a ⟶ b) :
    (ρ_ f).op2 = λ_ f.op :=
  rfl

@[simp]
lemma op2_rightUnitor_hom {a b : B} (f : a ⟶ b) :
    op2 (ρ_ f).hom = (λ_ f.op).hom :=
  rfl

@[simp]
lemma op2_rightUnitor_inv {a b : B} (f : a ⟶ b) :
    op2 (ρ_ f).inv = (λ_ f.op).inv :=
  rfl

end Opposite

end Bicategory
