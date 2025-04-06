/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Category.Alg.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# The monoidal structure on `Alg` is symmetric.

In this file we show:

* `Alg.instSymmetricCategory : SymmetricCategory (Alg.{u} R)`
-/
open CategoryTheory


noncomputable section

universe v u

variable {R : Type u} [CommRing R]

namespace Alg

instance : BraidedCategory (Alg.{u} R) :=
  braidedCategoryOfFaithful (forget₂ (Alg R) (ModuleCat R))
    (fun X Y => (Algebra.TensorProduct.comm R X Y).toAlgebraIso)
    (by aesop_cat)

instance : (forget₂ (Alg R) (ModuleCat R)).Braided where

instance instSymmetricCategory : SymmetricCategory (Alg.{u} R) :=
  symmetricCategoryOfFaithful (forget₂ (Alg R) (ModuleCat R))

end Alg
