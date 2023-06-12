/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison

! This file was ported from Lean 3 source module category_theory.preadditive.yoneda.projective
! leanprover-community/mathlib commit f8d8465c3c392a93b9ed226956e26dee00975946
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.Algebra.Category.GroupCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
An object is projective iff the preadditive coyoneda functor on it preserves epimorphisms.
-/


universe v u

open Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

namespace Projective

theorem projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj (P : C) :
    Projective P ↔ (preadditiveCoyoneda.obj (op P)).PreservesEpimorphisms := by
  rw [projective_iff_preservesEpimorphisms_coyoneda_obj]
  refine' ⟨fun h : (preadditiveCoyoneda.obj (op P) ⋙
      forget AddCommGroupCat).PreservesEpimorphisms => _, _⟩
  · exact Functor.preservesEpimorphisms_of_preserves_of_reflects (preadditiveCoyoneda.obj (op P))
        (forget _)
  · intro
    exact (inferInstance : (preadditiveCoyoneda.obj (op P) ⋙ forget _).PreservesEpimorphisms)
#align category_theory.projective.projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj

theorem projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj' (P : C) :
    Projective P ↔ (preadditiveCoyoneda.obj (op P)).PreservesEpimorphisms := by
  rw [projective_iff_preservesEpimorphisms_coyoneda_obj]
  refine' ⟨fun h : (preadditiveCoyoneda.obj (op P) ⋙
      forget AddCommGroupCat).PreservesEpimorphisms => _, _⟩
  · exact Functor.preservesEpimorphisms_of_preserves_of_reflects (preadditiveCoyoneda.obj (op P))
        (forget _)
  · intro
    exact (inferInstance : (preadditiveCoyoneda.obj (op P) ⋙ forget _).PreservesEpimorphisms)
#align category_theory.projective.projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj' CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj'

end Projective

end Preadditive

end CategoryTheory
