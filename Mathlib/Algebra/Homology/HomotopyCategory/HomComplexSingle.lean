/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# Cochains from single complexes


-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace CochainComplex

namespace HomComplex

variable {X : C} {K : CochainComplex C ℤ} (n : ℤ)

namespace Cochain

def fromSingleMk

end Cochain

end HomComplex

end CochainComplex
