/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.DiscreteCategory.Basic
import Mathlib.CategoryTheory.Sums.Basic
import Mathlib.CategoryTheory.Products.Basic
/-! # Sums and products of discrete categories.

This file shows that binary products and binary sums of discrete categories
are also discrete, both in the form of explicit equivalences and through the
`IsDiscrete` typeclass.

## Main declarations

* `Discrete.productEquiv`: The equivalence of categories between `Discrete (J × K)`
  and `Discrete J × Discrete K`
* `Discrete.sumEquiv`: The equivalence of categories between `Discrete (J ⊕ K)`
  and `Discrete J ⊕ Discrete K`.
* `IsDiscrete.prod`: an `IsDiscrete` instance on the product of two discrete categories.
* `IsDiscrete.sum`: an `IsDiscrete` instance on the sum of two discrete categories.

-/
universe v₁ u₁

namespace CategoryTheory

namespace Discrete

/-- The discrete category on a product is equivalent to the product of the
discrete categories. -/
@[simps!]
def productEquiv {J K : Type*} : Discrete (J × K) ≌ Discrete J × Discrete K where
  functor := Discrete.functor <| fun ⟨j, k⟩ ↦ ⟨.mk j, .mk k⟩
  inverse := {
    obj := fun ⟨x, y⟩ ↦ .mk (⟨x.as, y.as⟩)
    map := fun ⟨f₁, f₂⟩ ↦ eqToHom (by discrete_cases; dsimp; rw [f₁, f₂]) }
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- The discrete category on a sum is equivalent to the sum of the
discrete categories. -/
@[simps!]
def sumEquiv {J K : Type u₁} : Discrete (J ⊕ K) ≌ Discrete J ⊕ Discrete K where
  functor := Discrete.functor <| fun t ↦
    match t with
    | .inl j => Sum.inl (Discrete.mk j)
    | .inr k => Sum.inr (Discrete.mk k)
  inverse := {
    obj t :=
      match t with
      | .inl j => .mk (.inl j.as)
      | .inr k => .mk (.inr k.as)
    map {x y} f :=
      match x, y, f with
      | .inl x, .inl y, f => eqToHom (by change x ⟶ y at f; discrete_cases; subst f; rfl)
      | .inr x, .inr y, f => eqToHom (by change x ⟶ y at f; discrete_cases; subst f; rfl)
      | .inr _, .inl _, u => PEmpty.elim u
      | .inl _, .inr _, u => PEmpty.elim u }
  unitIso := NatIso.ofComponents (fun ⟨x⟩ ↦
      match x with
      | .inl j => Iso.refl _
      | .inr k => Iso.refl _)
  counitIso := NatIso.ofComponents
    (fun x ↦
      match x with
      | .inl j => Iso.refl _
      | .inr k => Iso.refl _)
    (fun {x y} f ↦
      match x, y, f with
      | .inl j, .inl j', f => by change j ⟶ j' at f; discrete_cases; dsimp at f; subst f; rfl
      | .inr j, .inr j', f => by change j ⟶ j' at f; discrete_cases; dsimp at f; subst f; rfl
      | .inr _, .inl _, u => PEmpty.elim u
      | .inl _, .inr _, u => PEmpty.elim u)

end Discrete

namespace IsDiscrete

variable (C C': Type u₁) [Category.{v₁} C] [Category.{v₁} C'] (D : Type*) [Category D]
  [IsDiscrete C] [IsDiscrete C'] [IsDiscrete D]

/-- A product of discrete categories is discrete. -/
instance prod : IsDiscrete (C × D) where
  subsingleton x y := inferInstanceAs (Subsingleton ((x.1 ⟶ y.1) × (x.2 ⟶ y.2)))
  eq_of_hom f := Prod.ext (IsDiscrete.eq_of_hom f.1) (IsDiscrete.eq_of_hom f.2)

/-- A product of discrete categories is discrete. -/
instance sum : IsDiscrete (C ⊕ C') where
  subsingleton x y :=
    match x, y with
    | .inl x, .inl y => inferInstanceAs (Subsingleton (x ⟶ y))
    | .inr x, .inr y => inferInstanceAs (Subsingleton (x ⟶ y))
    | .inl x, .inr y => inferInstanceAs (Subsingleton PEmpty)
    | .inr x, .inl y => inferInstanceAs (Subsingleton PEmpty)
  eq_of_hom {x y} f :=
    match x, y, f with
    | .inl x, .inl y, f => by simp only [Sum.inl.injEq]; exact IsDiscrete.eq_of_hom f
    | .inr x, .inr y, f => by simp only [Sum.inr.injEq]; exact IsDiscrete.eq_of_hom f
    | .inl x, .inr y, u => PEmpty.elim u
    | .inr x, .inl y, u => PEmpty.elim u

end CategoryTheory.IsDiscrete
