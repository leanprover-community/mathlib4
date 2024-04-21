/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Projective objects in abelian categories

In an abelian category, an object `P` is projective iff the functor
`preadditiveCoyonedaObj (op P)` preserves finite colimits.

-/

universe v u

namespace CategoryTheory

open Limits Projective Opposite

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The preadditive Co-Yoneda functor on `P` preserves finite colimits if `P` is projective. -/
noncomputable def preservesFiniteColimitsPreadditiveCoyonedaObjOfProjective
    (P : C) [hP : Projective P] :
    PreservesFiniteColimits (preadditiveCoyonedaObj (op P)) := by
  haveI := (projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj' P).mp hP
  -- Porting note: this next instance wasn't necessary in Lean 3
  haveI := @Functor.preservesEpimorphisms_of_preserves_of_reflects _ _ _ _ _ _ _ _ this _
  apply Functor.preservesFiniteColimitsOfPreservesEpisAndKernels
#align category_theory.preserves_finite_colimits_preadditive_coyoneda_obj_of_projective CategoryTheory.preservesFiniteColimitsPreadditiveCoyonedaObjOfProjective

/-- An object is projective if its preadditive Co-Yoneda functor preserves finite colimits. -/
theorem projective_of_preservesFiniteColimits_preadditiveCoyonedaObj (P : C)
    [hP : PreservesFiniteColimits (preadditiveCoyonedaObj (op P))] : Projective P := by
  rw [projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj']
  -- Porting note: this next line wasn't necessary in Lean 3
  dsimp only [preadditiveCoyoneda]
  infer_instance
#align category_theory.projective_of_preserves_finite_colimits_preadditive_coyoneda_obj CategoryTheory.projective_of_preservesFiniteColimits_preadditiveCoyonedaObj

end CategoryTheory
