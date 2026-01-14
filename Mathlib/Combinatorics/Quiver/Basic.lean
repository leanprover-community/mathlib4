/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Kim Morrison
-/
import Mathlib.Data.Opposite

/-!
# Quivers

This module defines quivers. A quiver on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. This
is a very permissive notion of directed graph.

## Implementation notes

Currently `Quiver` is defined with `Hom : V → V → Sort v`.
This is different from the category theory setup,
where we insist that morphisms live in some `Type`.
There's some balance here: it's nice to allow `Prop` to ensure there are no multiple arrows,
but it is also results in error-prone universe signatures when constraints require a `Type`.
-/

open Opposite

-- We use the same universe order as in category theory.
-- See note [category theory universes]
universe v v₁ v₂ u u₁ u₂

/-- A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
a type `a ⟶ b` of arrows from `a` to `b`.

For graphs with no repeated edges, one can use `Quiver.{0} V`, which ensures
`a ⟶ b : Prop`. For multigraphs, one can use `Quiver.{v+1} V`, which ensures
`a ⟶ b : Type v`.

Because `Category` will later extend this class, we call the field `Hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` notation instead.
-/
class Quiver (V : Type u) where
  /-- The type of edges/arrows/morphisms between a given source and target. -/
  Hom : V → V → Sort v

/--
Notation for the type of edges/arrows/morphisms between a given source and target
in a quiver or category.
-/
infixr:10 " ⟶ " => Quiver.Hom

namespace Quiver

/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
instance opposite {V} [Quiver V] : Quiver Vᵒᵖ :=
  ⟨fun a b => (unop b ⟶ unop a)ᵒᵖ⟩

/-- The opposite of an arrow in `V`. -/
def Hom.op {V} [Quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X := ⟨f⟩

/-- Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`. -/
def Hom.unop {V} [Quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X := Opposite.unop f

/-- The bijection `(X ⟶ Y) ≃ (op Y ⟶ op X)`. -/
@[simps]
def Hom.opEquiv {V} [Quiver V] {X Y : V} :
    (X ⟶ Y) ≃ (Opposite.op Y ⟶ Opposite.op X) where
  toFun := Opposite.op
  invFun := Opposite.unop

/-- A type synonym for a quiver with no arrows. -/
def Empty (V : Type u) : Type u := V

instance emptyQuiver (V : Type u) : Quiver.{u} (Empty V) := ⟨fun _ _ => PEmpty⟩

@[simp]
theorem empty_arrow {V : Type u} (a b : Empty V) : (a ⟶ b) = PEmpty := rfl

/-- A quiver is thin if it has no parallel arrows. -/
abbrev IsThin (V : Type u) [Quiver V] : Prop := ∀ a b : V, Subsingleton (a ⟶ b)


section

variable {V : Type*} [Quiver V]

/-- An arrow in a quiver can be transported across equalities between the source and target
objects. -/
def homOfEq {X Y : V} (f : X ⟶ Y) {X' Y' : V} (hX : X = X') (hY : Y = Y') : X' ⟶ Y' := by
  subst hX hY
  exact f

@[simp]
lemma homOfEq_trans {X Y : V} (f : X ⟶ Y) {X' Y' : V} (hX : X = X') (hY : Y = Y')
    {X'' Y'' : V} (hX' : X' = X'') (hY' : Y' = Y'') :
    homOfEq (homOfEq f hX hY) hX' hY' = homOfEq f (hX.trans hX') (hY.trans hY') := by
  subst hX hY hX' hY'
  rfl

lemma homOfEq_injective {X X' Y Y' : V} (hX : X = X') (hY : Y = Y')
    {f g : X ⟶ Y} (h : Quiver.homOfEq f hX hY = Quiver.homOfEq g hX hY) : f = g := by
  subst hX hY
  exact h

@[simp]
lemma homOfEq_rfl {X Y : V} (f : X ⟶ Y) : Quiver.homOfEq f rfl rfl = f := rfl

lemma heq_of_homOfEq_ext {X Y X' Y' : V} (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (e : Quiver.homOfEq f hX hY = f') : f ≍ f' := by
  subst hX hY
  rw [Quiver.homOfEq_rfl] at e
  rw [e]

lemma homOfEq_eq_iff {X X' Y Y' : V} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hX : X = X') (hY : Y = Y') :
    Quiver.homOfEq f hX hY = g ↔ f = Quiver.homOfEq g hX.symm hY.symm := by
  subst hX hY; simp

lemma eq_homOfEq_iff {X X' Y Y' : V} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hX : X' = X) (hY : Y' = Y) :
    f = Quiver.homOfEq g hX hY ↔ Quiver.homOfEq f hX.symm hY.symm = g := by
  subst hX hY; simp

lemma homOfEq_heq {X Y X' Y' : V} (hX : X = X') (hY : Y = Y') (f : X ⟶ Y) :
    homOfEq f hX hY ≍ f := (heq_of_homOfEq_ext hX hY rfl).symm

lemma homOfEq_heq_left_iff {X Y X' Y' : V} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hX : X = X') (hY : Y = Y') :
    homOfEq f hX hY ≍ g ↔ f ≍ g := by
  cases hX; cases hY; rfl

lemma homOfEq_heq_right_iff {X Y X' Y' : V} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hX : X' = X) (hY : Y' = Y) :
    f ≍ homOfEq g hX hY ↔ f ≍ g := by
  cases hX; cases hY; rfl


end

end Quiver
