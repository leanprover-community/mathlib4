/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Internal.Limits
import Mathlib.CategoryTheory.Monoidal.Bimon_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Comon_

/-!
# Bimonoid objects in a cartesian monoidal category.

The category of bimonoid objects in a cartesian monoidal category is equivalent
to the category of monoid objects, via the forgetful functor.
-/

open CategoryTheory MonoidalCategory Limits

universe v u

noncomputable section

variable (C : Type u) [Category.{v} C] [HasTerminal C] [HasBinaryProducts C]

def Cartesian := C

instance : Category (Cartesian C) := inferInstanceAs <| Category C
instance : HasTerminal (Cartesian C) := inferInstanceAs <| HasTerminal C
instance : HasBinaryProducts (Cartesian C) := inferInstanceAs <| HasBinaryProducts C

@[simp] theorem terminalCartesian : (⊤_ (Cartesian C)) = (⊤_ C) := rfl

section

attribute [local instance] monoidalOfHasFiniteProducts symmetricOfHasFiniteProducts
instance : MonoidalCategory (Cartesian C) := inferInstanceAs <| MonoidalCategory C
instance : SymmetricCategory (Cartesian C) := inferInstanceAs <| SymmetricCategory C

end

@[simps!]
def foo : Cartesian (Mon_ (Cartesian C)) ≌ Mon_ (Cartesian C) := CategoryTheory.Equivalence.refl

def fooMonoidalFunctor : MonoidalFunctor (Cartesian (Mon_ (Cartesian C))) (Mon_ (Cartesian C)) where
  toFunctor := (foo C).functor
  ε :=
  { hom := (Mon_.terminal_X_iso (Cartesian C)).inv
    one_hom := by
      apply (cancel_mono ((Mon_.terminal_X_iso (Cartesian C)).hom)).mp
      ext
    mul_hom := by
      apply (cancel_mono ((Mon_.terminal_X_iso (Cartesian C)).hom)).mp
      ext }
  μ A B :=
  { hom := (Mon_.prod_X_iso (Cartesian C) A B).inv
    one_hom := by
      apply (cancel_mono ((Mon_.prod_X_iso (Cartesian C) A B).hom)).mp
      simp
      ext
      · simp [Mon_.prod_X_iso]; sorry
      · sorry
    mul_hom := sorry }

instance : (fooMonoidalFunctor C).IsEquivalence := inferInstanceAs <| (foo C).functor.IsEquivalence

def bar : Comon_ (Cartesian (Mon_ (Cartesian C))) ≌ Comon_ (Mon_ (Cartesian C)) :=
  (fooMonoidalFunctor C).equivalenceMapComon_ (foo C).toAdjunction

-- Ideally we could construct `Bimon_ C ≌ Mon_ C` simply as
-- `comonEquiv (Mon_ C) : Comon_ (Mon_ C) ≌ Mon_ C`.
-- Unfortunately there are two different monoidal structures on `Mon_ C` present,
-- which we need to compare:
-- * `Mon_ C` acquires a monoidal structure because the monoidal structure on `C` is braided
-- * `Mon_ C` acquires a monoidal structure because it has finite products.
def bimonEquiv : Bimon_ (Cartesian C) ≌ Mon_ (Cartesian C) :=
  (bar C).symm.trans (comonEquiv (Mon_ (Cartesian C)))
