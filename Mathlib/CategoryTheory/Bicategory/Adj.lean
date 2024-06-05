/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Bicategory.Adjunction

/-!
# The bicategory of adjunctions in a bicategory

Given a bicategory `B`, we construct a bicategory `Adj B` that has the same
objects but whose `1`-morphisms are adjunctions, and `2`-morphisms are tuples
of mate maps between the left and right adjoints (where the map between right
adjoints is in the opposite direction).

Certain pseudofunctors to the bicategory `Adj Cat` are analogous to bifibered categories:
in various contexts, this may be used in order to formalize the properties of
both pushforward and pullback functors.

## References

* https://ncatlab.org/nlab/show/2-category+of+adjunctions
* https://ncatlab.org/nlab/show/transformation+of+adjoints
* https://ncatlab.org/nlab/show/mate

-/

universe w v u

namespace CategoryTheory

namespace Bicategory

variable (B : Type u) [Bicategory.{w, v} B]

/--
The bicategory that has the same objects as a bicategory `B`, in which `1`-morphisms
are adjunctions, and `2`-morphisms are tuples of mate maps between the left and right
adjoints (where the map between right adjoints is in the opposite direction).
-/
def Adj : Type u := B

namespace Adj

variable {B}

variable (a b c d : B)

/--
Given two objects `a` and `b` in a bicategory,
this is the type of adjunctions between `a` and `b`.
-/
structure Hom where
  /-- the left adjoint -/
  f : a ⟶ b
  /-- the right adjoint -/
  g : b ⟶ a
  /-- the adjunction -/
  adj : f ⊣ g

instance : CategoryStruct (Adj B) where
  Hom (a : B) b := Hom a b
  id (a : B) := { adj := Adjunction.id a }
  comp f g := { adj := f.adj.comp g.adj }

@[simp] lemma id_f (a : Adj B) : Hom.f (𝟙 a) = 𝟙 _ := rfl
@[simp] lemma id_g (a : Adj B) : Hom.g (𝟙 a) = 𝟙 _ := rfl

variable {a b c d : Adj B}

@[simp] lemma comp_f (α : a ⟶ b) (β : b ⟶ c) : (α ≫ β).f = α.f ≫ β.f := rfl
@[simp] lemma comp_g (α : a ⟶ b) (β : b ⟶ c) : (α ≫ β).g = β.g ≫ α.g := rfl

/--
Given two adjunctions `α` and `β` between two objects in a bicategory, the data
of a morphism between the left adjoints is equivalent to the data of a morphism
in the other direction between the right adjoints.
-/
@[simps]
def hom₂Equiv (α β : a ⟶ b) : (α.f ⟶ β.f) ≃ (β.g ⟶ α.g) where
  toFun τ := 𝟙 _ ⊗≫ β.g ◁ α.adj.unit ≫ β.g ◁ (τ ▷ α.g) ⊗≫ (β.adj.counit ▷ α.g) ⊗≫ 𝟙 _
  invFun τ' := 𝟙 _ ⊗≫ β.adj.unit ▷ α.f ≫ (β.f ◁ τ') ▷ α.f ⊗≫ β.f ◁ α.adj.counit ⊗≫ 𝟙 _
  left_inv := sorry
  right_inv := sorry

/-- A morphism between two adjunctions consists of a tuple of mate maps. -/
@[ext]
structure Hom₂ (α β : a ⟶ b) where
  /-- the morphism between left adjoints -/
  τf : α.f ⟶ β.f
  /-- the morphism in the opposite direction between right adjoints -/
  τg : β.g ⟶ α.g
  hom₂Equiv_τf : hom₂Equiv α β τf = τg

instance : CategoryStruct (a ⟶ b) where
  Hom α β := Hom₂ α β
  id α :=
    { τf := 𝟙 _
      τg := 𝟙 _
      hom₂Equiv_τf := sorry }
  comp x y :=
    { τf := x.τf ≫ y.τf
      τg := y.τg ≫ x.τg
      hom₂Equiv_τf := sorry }

@[ext]
lemma hom₂_ext {α β : a ⟶ b} {x y : α ⟶ β} (hf : x.τf = y.τf) : x = y := by
  apply Hom₂.ext _ _ hf
  rw [← x.hom₂Equiv_τf, ← y.hom₂Equiv_τf, hf]

@[simp] lemma id_τf (α : a ⟶ b) : Hom₂.τf (𝟙 α) = 𝟙 α.f := rfl
@[simp] lemma id_τg (α : a ⟶ b) : Hom₂.τg (𝟙 α) = 𝟙 α.g := rfl

section

variable {α β γ : a ⟶ b}

@[simp, reassoc] lemma comp_τf (x : α ⟶ β) (y : β ⟶ γ) : (x ≫ y).τf = x.τf ≫ y.τf := rfl
@[simp, reassoc] lemma comp_τg (x : α ⟶ β) (y : β ⟶ γ) : (x ≫ y).τf = x.τf ≫ y.τf := rfl

end

instance : Category (a ⟶ b) where

/-- Constructor for isomorphisms between 1-morphisms in the bicategory `Adj B`. -/
@[simps]
def iso₂Mk {α β : a ⟶ b} (ef : α.f ≅ β.f) (eg : β.g ≅ α.g) (h : hom₂Equiv α β ef.hom = eg.hom) :
    α ≅ β where
  hom :=
    { τf := ef.hom
      τg := eg.hom
      hom₂Equiv_τf := h }
  inv :=
    { τf := ef.inv
      τg := eg.inv
      hom₂Equiv_τf := sorry }

/-- The associator in the bicategory `Adj B`. -/
@[simps!]
def associator (α : a ⟶ b) (β : b ⟶ c) (γ : c ⟶ d) : (α ≫ β) ≫ γ ≅ α ≫ β ≫ γ :=
  iso₂Mk (α_ _ _ _) (α_ _ _ _) sorry

/-- The left unitor in the bicategory `Adj B`. -/
@[simps!]
def leftUnitor (α : a ⟶ b) : 𝟙 a ≫ α ≅ α :=
  iso₂Mk (λ_ _) (ρ_ _).symm sorry

/-- The right unitor in the bicategory `Adj B`. -/
@[simps!]
def rightUnitor (α : a ⟶ b) : α ≫ 𝟙 b ≅ α :=
  iso₂Mk (ρ_ _) (λ_ _).symm sorry

/-- The left whiskering in the bicategory `Adj B`. -/
@[simps]
def whiskerLeft (α : a ⟶ b) {β β' : b ⟶ c} (y : β ⟶ β') : α ≫ β ⟶ α ≫ β' where
  τf := _ ◁ y.τf
  τg := y.τg ▷ _
  hom₂Equiv_τf := sorry

/-- The right whiskering in the bicategory `Adj B`. -/
@[simps]
def whiskerRight {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c) : α ≫ β ⟶ α' ≫ β where
  τf := x.τf ▷ _
  τg := _ ◁ x.τg
  hom₂Equiv_τf := sorry

attribute [local simp] whisker_exchange

instance : Bicategory (Adj B) where
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

end Adj

end Bicategory

end CategoryTheory
