/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Sums.Basic

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

@[expose] public section

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

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The discrete category on a sum is equivalent to the sum of the
discrete categories. -/
@[simps!]
def sumEquiv {J K : Type*} : Discrete (J ⊕ K) ≌ Discrete J ⊕ Discrete K where
  functor := Discrete.functor <| fun t ↦
    match t with
    | .inl j => Sum.inl (Discrete.mk j)
    | .inr k => Sum.inr (Discrete.mk k)
  inverse := (Discrete.functor <| fun t ↦ Discrete.mk (Sum.inl t)).sum'
    (Discrete.functor <| fun t ↦ Discrete.mk (Sum.inr t))
  unitIso := NatIso.ofComponents (fun ⟨x⟩ ↦
    match x with
    | .inl x => Iso.refl _
    | .inr x => Iso.refl _)
  counitIso := Functor.sumIsoExt
    (Discrete.natIso <| fun _ ↦ Iso.refl _)
    (Discrete.natIso <| fun _ ↦ Iso.refl _)

end Discrete

namespace IsDiscrete

variable (C C' : Type*) [Category* C] [Category* C'] (D : Type*) [Category* D]
  [IsDiscrete C] [IsDiscrete C'] [IsDiscrete D]

/-- A product of discrete categories is discrete. -/
instance prod : IsDiscrete (C × D) where
  subsingleton x y := inferInstanceAs (Subsingleton ((x.1 ⟶ y.1) × (x.2 ⟶ y.2)))
  eq_of_hom f := Prod.ext (IsDiscrete.eq_of_hom f.1) (IsDiscrete.eq_of_hom f.2)

/-- A sum of discrete categories is discrete. -/
instance sum : IsDiscrete (C ⊕ C') where
  subsingleton x y :=
    { allEq f g := by
        cases f <;> cases g
        · case inl x y f g => rw [((by assumption : IsDiscrete C).subsingleton x y).allEq f g]
        · case inr x y f g => rw [((by assumption : IsDiscrete C').subsingleton x y).allEq f g] }
  eq_of_hom {x y} f := by
    cases f with
    | inl x y f => rw [(by assumption : IsDiscrete C).eq_of_hom f]
    | inr x y f => rw [(by assumption : IsDiscrete C').eq_of_hom f]

end CategoryTheory.IsDiscrete
