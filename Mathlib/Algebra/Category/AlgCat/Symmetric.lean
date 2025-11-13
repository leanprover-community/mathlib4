/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Category.AlgCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# The monoidal structure on `AlgCat` is symmetric.

In this file we show:

* `AlgCat.instSymmetricCategory : SymmetricCategory (AlgCat.{u} R)`
-/
open CategoryTheory


noncomputable section

universe v u

variable {R : Type u} [CommRing R]

namespace AlgCat

instance : BraidedCategory (AlgCat.{u} R) :=
  .ofFaithful (forget₂ (AlgCat R) (ModuleCat R))
    fun X Y ↦ (Algebra.TensorProduct.comm R X Y).toAlgebraIso

instance : (forget₂ (AlgCat R) (ModuleCat R)).Braided where

instance instSymmetricCategory : SymmetricCategory (AlgCat.{u} R) :=
  .ofFaithful (forget₂ (AlgCat R) (ModuleCat R))

end AlgCat
