/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types

namespace CategoryTheory.Limits.Types

universe w v₁ v₂ u₁ u₂

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]

variable (F : J ⥤ K ⥤ TypeMax.{u₁, w})

/-

  obtain ⟨j, y, hy⟩ := Types.jointly_surjective'.{v, v} ((colimitObjIsoColimitCompEvaluation F X).hom x)
  refine' ⟨j, y, ?_⟩
  apply (colimitObjIsoColimitCompEvaluation F X).toEquiv.injective
  simp [← hy, elementwise_of% colimitObjIsoColimitCompEvaluation_ι_app_hom F]
  rfl -- wat?
-/

theorem bifunctor_jointly_surjective (k : K) {t : Cocone F} (h : IsColimit t)
    (x : t.pt.obj k) : ∃ j y, x = (t.ι.app j).app k y := by
  let hev := PreservesColimit.preserves (F := (evaluation _ _).obj k) h


  sorry
  -- obtain ⟨j, y, hy⟩ := Types.jointly_surjective

end CategoryTheory.Limits.Types
