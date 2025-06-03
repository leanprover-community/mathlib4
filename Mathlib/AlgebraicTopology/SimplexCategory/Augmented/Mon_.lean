/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/

import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# The canonical monoid object of `AugmentedSimplexCategory`.

This files records the fact that for the monoidal structure on `AugmentedSimplexCategory`
defined in `AlgebraicTopology.SimplexCategory.Augmented.Monoidal`, the object `⦋0⦌`
admits an internal monoid object structure.

## TODO
- Prove that this is the "universal internal monoid object", i.e that evaluation at
  `⦋0⦌` induces an an equivalence of categories between monoidal functors
  `AugmentedSimplexCategory ⥤ C` and internal objects in a monoidal category `C`.
-/

namespace AugmentedSimplexCategory

open CategoryTheory MonoidalCategory
open scoped Simplicial

/-- The canonical monoid object of `AugmentedSimplexCategory`. -/
def mon_ : Mon_Class (WithInitial.of ⦋0⦌) where
  one := WithInitial.homTo _
  mul := SimplexCategory.σ (Fin.last _)
  one_mul' := by
    change (_ : ⦋0⦌ ⟶ ⦋0⦌) = _
    subsingleton
  mul_one' := by
    change (_ : ⦋0⦌ ⟶ ⦋0⦌) = _
    subsingleton
  mul_assoc' := by
    apply AugmentedSimplexCategory.tensorObj_hom_ext
    · apply AugmentedSimplexCategory.tensorObj_hom_ext
      · change (_ : ⦋0⦌ ⟶ ⦋0⦌) = _
        subsingleton
      · change (_ : ⦋0⦌ ⟶ ⦋0⦌) = _
        subsingleton
    · change (_ : ⦋0⦌ ⟶ ⦋0⦌) = _
      subsingleton

end AugmentedSimplexCategory
