/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# The monoidal structure on `QuadraticModuleCat` is symmetric.

In this file we show:

* `QuadraticModuleCat.instSymmetricCategory : SymmetricCategory (QuadraticModuleCat.{u} R)`

## Implementation notes

This file essentially mirrors `Mathlib/Algebra/Category/AlgebraCat/Symmetric.lean`.
-/

suppress_compilation

open CategoryTheory

universe v u

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace QuadraticModuleCat

open QuadraticForm

instance : BraidedCategory (QuadraticModuleCat.{u} R) :=
  braidedCategoryOfFaithful (toModuleCatMonoidalFunctor R)
    (fun X Y => ofIso <| tensorComm X.form Y.form)
    (by aesop_cat)

variable (R) in
/-- `forget₂ (QuadraticModuleCat R) (ModuleCat R)` as a braided functor. -/
@[simps toMonoidalFunctor]
def toModuleCatBraidedFunctor : BraidedFunctor (QuadraticModuleCat.{u} R) (ModuleCat.{u} R) where
  toMonoidalFunctor := toModuleCatMonoidalFunctor R

instance : (toModuleCatBraidedFunctor R).Faithful :=
  forget₂_faithful _ _

instance instSymmetricCategory : SymmetricCategory (QuadraticModuleCat.{u} R) :=
  symmetricCategoryOfFaithful (toModuleCatBraidedFunctor R)

end QuadraticModuleCat
