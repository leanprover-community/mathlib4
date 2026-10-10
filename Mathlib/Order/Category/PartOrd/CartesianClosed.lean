/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Category.PartOrd.Reflective
public import Mathlib.Order.Category.Preord.CartesianClosed
public import Mathlib.CategoryTheory.Skeletal

/-!
# Cartesian closed structure on `PartOrd`

`PartOrd` is a reflective exponential ideal in `Preord`: functor categories with thin,
skeletal codomain are thin and skeletal. Hence `PartOrd` is cartesian closed.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CartesianClosed

noncomputable section

instance : ExponentialIdeal (forget₂ PartOrd.{u} Preord.{u}) := by
  apply ExponentialIdeal.mk'
  intro P A
  let B := (ihom A).obj ((forget₂ PartOrd Preord).obj P)
  let : PartialOrder B :=
    { B.str with
      le_antisymm F G hFG hGF :=
        CategoryTheory.Functor.eq_of_iso (C := P) (D := A) (fun _ _ h ↦ h.some.to_eq)
          (iso_of_both_ways (C := A ⥤ P) hFG.some hGF.some) }
  exact ⟨PartOrd.of B, ⟨Iso.refl _⟩⟩

namespace PartOrd

instance : CartesianMonoidalCategory PartOrd.{u} :=
  .ofReflective (forget₂ PartOrd Preord)

instance : BraidedCategory PartOrd.{u} := .ofCartesianMonoidalCategory

instance : MonoidalClosed PartOrd.{u} :=
  cartesianClosedOfReflective (forget₂ PartOrd Preord)

end PartOrd

instance : Limits.PreservesFiniteProducts preordToPartOrd.{u} :=
  .of_exponentialIdeal (forget₂ PartOrd Preord)
