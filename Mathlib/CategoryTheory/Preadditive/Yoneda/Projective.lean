/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison

! This file was ported from Lean 3 source module category_theory.preadditive.yoneda.projective
! leanprover-community/mathlib commit f8d8465c3c392a93b9ed226956e26dee00975946
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Preadditive.Yoneda.Basic
import Mathbin.CategoryTheory.Preadditive.Projective
import Mathbin.Algebra.Category.Group.EpiMono
import Mathbin.Algebra.Category.Module.EpiMono

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
    Projective P ↔ (preadditiveCoyoneda.obj (op P)).PreservesEpimorphisms :=
  by
  rw [projective_iff_preserves_epimorphisms_coyoneda_obj]
  refine' ⟨fun h : (preadditive_coyoneda.obj (op P) ⋙ forget _).PreservesEpimorphisms => _, _⟩
  ·
    exact
      functor.preserves_epimorphisms_of_preserves_of_reflects (preadditive_coyoneda.obj (op P))
        (forget _)
  · intro
    exact (inferInstance : (preadditive_coyoneda.obj (op P) ⋙ forget _).PreservesEpimorphisms)
#align category_theory.projective.projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj

theorem projective_iff_preservesEpimorphisms_preadditive_coyoneda_obj' (P : C) :
    Projective P ↔ (preadditiveCoyonedaObj (op P)).PreservesEpimorphisms :=
  by
  rw [projective_iff_preserves_epimorphisms_coyoneda_obj]
  refine' ⟨fun h : (preadditive_coyoneda_obj (op P) ⋙ forget _).PreservesEpimorphisms => _, _⟩
  ·
    exact
      functor.preserves_epimorphisms_of_preserves_of_reflects (preadditive_coyoneda_obj (op P))
        (forget _)
  · intro
    exact (inferInstance : (preadditive_coyoneda_obj (op P) ⋙ forget _).PreservesEpimorphisms)
#align category_theory.projective.projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj' CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditive_coyoneda_obj'

end Projective

end Preadditive

end CategoryTheory

