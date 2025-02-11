/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Category.AlgebraCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# The monoidal structure on `AlgebraCat` is symmetric.

In this file we show:

* `AlgebraCat.instSymmetricCategory : SymmetricCategory (AlgebraCat.{u} R)`
-/
open CategoryTheory


noncomputable section

universe v u

variable {R : Type u} [CommRing R]

namespace AlgebraCat

instance : BraidedCategory (AlgebraCat.{u} R) :=
  braidedCategoryOfFaithful (forget₂ (AlgebraCat R) (ModuleCat R))
    (fun X Y => (Algebra.TensorProduct.comm R X Y).toAlgebraIso)
    (by aesop_cat)

instance : (forget₂ (AlgebraCat R) (ModuleCat R)).Braided where

instance instSymmetricCategory : SymmetricCategory (AlgebraCat.{u} R) :=
  symmetricCategoryOfFaithful (forget₂ (AlgebraCat R) (ModuleCat R))

end AlgebraCat
