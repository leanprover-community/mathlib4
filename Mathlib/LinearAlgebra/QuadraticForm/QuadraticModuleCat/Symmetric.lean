/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# The monoidal structure on `QuadraticModuleCat` is symmetric.

In this file we show:

* `QuadraticModuleCat.instSymmetricCategory : SymmetricCategory (QuadraticModuleCat.{u} R)`

## Implementation notes

This file essentially mirrors `Mathlib/Algebra/Category/AlgCat/Symmetric.lean`.
-/

@[expose] public section

open CategoryTheory

universe v u

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace QuadraticModuleCat

open QuadraticForm

instance : BraidedCategory (QuadraticModuleCat.{u} R) :=
  .ofFaithful (forget₂ (QuadraticModuleCat R) (ModuleCat R))
    fun X Y ↦ ofIso <| tensorComm X.form Y.form

/-- `forget₂ (QuadraticModuleCat R) (ModuleCat R)` is a braided functor. -/
instance : (forget₂ (QuadraticModuleCat R) (ModuleCat R)).Braided where

instance instSymmetricCategory : SymmetricCategory (QuadraticModuleCat.{u} R) :=
  .ofFaithful (forget₂ (QuadraticModuleCat R) (ModuleCat R))

end QuadraticModuleCat
