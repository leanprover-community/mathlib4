/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective

#align_import category_theory.abelian.injective from "leanprover-community/mathlib"@"f8d8465c3c392a93b9ed226956e26dee00975946"

/-!
# Injective objects in abelian categories

* Objects in an abelian categories are injective if and only if the preadditive Yoneda functor
  on them preserves finite colimits.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Injective

open Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The preadditive Yoneda functor on `J` preserves colimits if `J` is injective. -/
def preservesFiniteColimitsPreadditiveYonedaObjOfInjective (J : C) [hP : Injective J] :
    PreservesFiniteColimits (preadditiveYonedaObj J) := by
  letI := (injective_iff_preservesEpimorphisms_preadditive_yoneda_obj' J).mp hP
  apply Functor.preservesFiniteColimitsOfPreservesEpisAndKernels
#align category_theory.preserves_finite_colimits_preadditive_yoneda_obj_of_injective CategoryTheory.preservesFiniteColimitsPreadditiveYonedaObjOfInjective

/-- An object is injective if its preadditive Yoneda functor preserves finite colimits. -/
theorem injective_of_preservesFiniteColimits_preadditiveYonedaObj (J : C)
    [hP : PreservesFiniteColimits (preadditiveYonedaObj J)] : Injective J := by
  rw [injective_iff_preservesEpimorphisms_preadditive_yoneda_obj']
  infer_instance
#align category_theory.injective_of_preserves_finite_colimits_preadditive_yoneda_obj CategoryTheory.injective_of_preservesFiniteColimits_preadditiveYonedaObj

end CategoryTheory
