/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Distributive.Monoidal
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike

/-!

# Distributive categories

## Main definitions

A category `C` with finite products and binary coproducts is called distributive if the
canonical distributivity morphism `(X ⨯ Y) ⨿ (X ⨯ Z) ⟶ X ⨯ (Y ⨿ Z)` is an isomorphism
for all objects `X`, `Y`, and `Z` in `C`.

## Implementation Details

A Cartesian distributive category is defined as a Cartesian monoidal category which is
monoidal distributive.

## Main results

- The coproduct coprojections are monic in a Cartesian distributive category.


## TODO

- Every Cartesian distributive category is finitary distributive, meaning that
  the left tensor product functor `X ⊗ -` preserves all finite coproducts.

- Show that any extensive distributive category can be embedded into a topos.

## References

- [J.R.B.Cockett, Introduction to distributive categories, 1993][cockett1993]
- [Carboni et al, Introduction to extensive and distributive categories][CARBONI1993145]
-/

@[expose] public section

universe v v₂ u u₂

noncomputable section

namespace CategoryTheory

open Category Limits MonoidalCategory Distributive CartesianMonoidalCategory

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] [HasBinaryCoproducts C]

/-- A category `C` with finite products is Cartesian distributive if it is monoidal distributive
with respect to the Cartesian monoidal structure. -/
abbrev IsCartesianDistributive :=
  IsMonoidalDistrib C

namespace IsCartesianDistributive

/-- To show a category is Cartesian distributive it is enough to show it is left distributive.
The right distributivity is inferred from symmetry of the Cartesian monoidal structure. -/
lemma of_isMonoidalLeftDistrib [IsMonoidalLeftDistrib C] : IsCartesianDistributive C :=
  letI : BraidedCategory C := Nonempty.some inferInstance
  SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib

set_option backward.isDefEq.respectTransparency false in
/-- The coproduct coprojections are monic in a Cartesian distributive category. -/
instance monoCoprod [IsCartesianDistributive C] : MonoCoprod C :=
  MonoCoprod.mk' fun A B =>
    ⟨_, coprodIsCoprod A B, ⟨fun {Z} f g he ↦ by
      let ι := coprod.inl (X := A) (Y := B)
      have : Mono (Z ◁ ι) := SplitMono.mono
        { retraction := (∂L Z A B).inv ≫ coprod.desc (𝟙 _) (fst Z B ≫ lift (𝟙 Z) f) }
      have : lift (𝟙 Z) f = lift (𝟙 Z) g := by rw [← cancel_mono (Z ◁ ι)]; aesop
      simpa only [lift_snd] using this =≫ snd _ _⟩⟩

end IsCartesianDistributive

end CategoryTheory
