/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.Algebra.Category.GroupCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.EpiMono

#align_import category_theory.preadditive.yoneda.projective from "leanprover-community/mathlib"@"f8d8465c3c392a93b9ed226956e26dee00975946"

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
  -- ⊢ Functor.PreservesEpimorphisms (coyoneda.obj (op P)) ↔ Functor.PreservesEpimo …
  refine' ⟨fun h : (preadditiveCoyoneda.obj (op P) ⋙
      forget AddCommGroupCat).PreservesEpimorphisms => _, _⟩
  · exact Functor.preservesEpimorphisms_of_preserves_of_reflects (preadditiveCoyoneda.obj (op P))
        (forget _)
  · intro
    -- ⊢ Functor.PreservesEpimorphisms (coyoneda.obj (op P))
    exact (inferInstance : (preadditiveCoyoneda.obj (op P) ⋙ forget _).PreservesEpimorphisms)
    -- 🎉 no goals
#align category_theory.projective.projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj

theorem projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj' (P : C) :
    Projective P ↔ (preadditiveCoyoneda.obj (op P)).PreservesEpimorphisms := by
  rw [projective_iff_preservesEpimorphisms_coyoneda_obj]
  -- ⊢ Functor.PreservesEpimorphisms (coyoneda.obj (op P)) ↔ Functor.PreservesEpimo …
  refine' ⟨fun h : (preadditiveCoyoneda.obj (op P) ⋙
      forget AddCommGroupCat).PreservesEpimorphisms => _, _⟩
  · exact Functor.preservesEpimorphisms_of_preserves_of_reflects (preadditiveCoyoneda.obj (op P))
        (forget _)
  · intro
    -- ⊢ Functor.PreservesEpimorphisms (coyoneda.obj (op P))
    exact (inferInstance : (preadditiveCoyoneda.obj (op P) ⋙ forget _).PreservesEpimorphisms)
    -- 🎉 no goals
#align category_theory.projective.projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj' CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj'

end Projective

end Preadditive

end CategoryTheory
