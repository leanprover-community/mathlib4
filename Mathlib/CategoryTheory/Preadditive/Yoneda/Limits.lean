/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.Yoneda

#align_import category_theory.preadditive.yoneda.limits from "leanprover-community/mathlib"@"09f981f72d43749f1fa072deade828d9c1e185bb"

/-!
# The Yoneda embedding for preadditive categories preserves limits

The Yoneda embedding for preadditive categories preserves limits.

## Implementation notes

This is in a separate file to avoid having to import the development of the abelian structure on
`ModuleCat` in the main file about the preadditive Yoneda embedding.

-/


universe v u

open CategoryTheory.Preadditive Opposite CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

instance preservesLimitsPreadditiveYonedaObj (X : C) : PreservesLimits (preadditiveYonedaObj X) :=
  have : PreservesLimits (preadditiveYonedaObj X ⋙ forget _) :=
    (inferInstance : PreservesLimits (yoneda.obj X))
  preservesLimitsOfReflectsOfPreserves _ (forget _)
#align category_theory.preserves_limits_preadditive_yoneda_obj CategoryTheory.preservesLimitsPreadditiveYonedaObj

instance preservesLimitsPreadditiveCoyonedaObj (X : Cᵒᵖ) :
    PreservesLimits (preadditiveCoyonedaObj X) :=
  have : PreservesLimits (preadditiveCoyonedaObj X ⋙ forget _) :=
    (inferInstance : PreservesLimits (coyoneda.obj X))
  preservesLimitsOfReflectsOfPreserves _ (forget _)
#align category_theory.preserves_limits_preadditive_coyoneda_obj CategoryTheory.preservesLimitsPreadditiveCoyonedaObj

instance PreservesLimitsPreadditiveYoneda.obj (X : C) : PreservesLimits (preadditiveYoneda.obj X) :=
  show PreservesLimits (preadditiveYonedaObj X ⋙ forget₂ _ _) from inferInstance
#align category_theory.preserves_limits_preadditive_yoneda.obj CategoryTheory.PreservesLimitsPreadditiveYoneda.obj

instance PreservesLimitsPreadditiveCoyoneda.obj (X : Cᵒᵖ) :
    PreservesLimits (preadditiveCoyoneda.obj X) :=
  show PreservesLimits (preadditiveCoyonedaObj X ⋙ forget₂ _ _) from inferInstance
#align category_theory.preserves_limits_preadditive_coyoneda.obj CategoryTheory.PreservesLimitsPreadditiveCoyoneda.obj

end CategoryTheory
