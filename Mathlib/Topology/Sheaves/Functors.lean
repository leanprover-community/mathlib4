/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu

! This file was ported from Lean 3 source module topology.sheaves.functors
! leanprover-community/mathlib commit 85d6221d32c37e68f05b2e42cde6cee658dae5e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# functors between categories of sheaves

Show that the pushforward of a sheaf is a sheaf, and define
the pushforward functor from the category of C-valued sheaves
on X to that of sheaves on Y, given a continuous map between
topological spaces X and Y.

TODO: pullback for presheaves and sheaves
-/


noncomputable section

universe w v u

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

variable {C : Type u} [Category.{v} C]

variable {X Y : TopCat.{w}} (f : X ⟶ Y)

variable ⦃ι : Type w⦄ {U : ι → Opens Y}

namespace TopCat

namespace Presheaf.SheafConditionPairwiseIntersections

theorem map_diagram : Pairwise.diagram U ⋙ Opens.map f = Pairwise.diagram ((Opens.map f).obj ∘ U) :=
  by
  apply functor.hext
  abstract obj_eq intro i; cases i <;> rfl
  intro i j g; apply Subsingleton.helim
  iterate 2 rw [map_diagram.obj_eq]
#align Top.presheaf.sheaf_condition_pairwise_intersections.map_diagram TopCat.Presheaf.SheafConditionPairwiseIntersections.map_diagram

theorem mapCocone :
    HEq ((Opens.map f).mapCocone (Pairwise.cocone U)) (Pairwise.cocone ((Opens.map f).obj ∘ U)) :=
  by
  unfold functor.map_cocone cocones.functoriality; dsimp; congr
  iterate 2 rw [map_diagram]; rw [opens.map_supr]
  apply Subsingleton.helim; rw [map_diagram, opens.map_supr]
  apply proof_irrel_heq
#align Top.presheaf.sheaf_condition_pairwise_intersections.map_cocone TopCat.Presheaf.SheafConditionPairwiseIntersections.mapCocone

theorem pushforward_sheaf_of_sheaf {F : Presheaf C X} (h : F.IsSheafPairwiseIntersections) :
    (f _* F).IsSheafPairwiseIntersections := fun ι U =>
  by
  convert h ((opens.map f).obj ∘ U) using 2
  rw [← map_diagram]; rfl
  change HEq (F.map_cone ((opens.map f).mapCocone _).op) _
  congr ; iterate 2 rw [map_diagram]; apply map_cocone
#align Top.presheaf.sheaf_condition_pairwise_intersections.pushforward_sheaf_of_sheaf TopCat.Presheaf.SheafConditionPairwiseIntersections.pushforward_sheaf_of_sheaf

end Presheaf.SheafConditionPairwiseIntersections

namespace Sheaf

open Presheaf

/-- The pushforward of a sheaf (by a continuous map) is a sheaf.
-/
theorem pushforward_sheaf_of_sheaf {F : X.Presheaf C} (h : F.IsSheaf) : (f _* F).IsSheaf := by
  rw [is_sheaf_iff_is_sheaf_pairwise_intersections] at h⊢ <;>
    exact sheaf_condition_pairwise_intersections.pushforward_sheaf_of_sheaf f h
#align Top.sheaf.pushforward_sheaf_of_sheaf TopCat.Sheaf.pushforward_sheaf_of_sheaf

/-- The pushforward functor.
-/
def pushforward (f : X ⟶ Y) : X.Sheaf C ⥤ Y.Sheaf C
    where
  obj ℱ := ⟨f _* ℱ.1, pushforward_sheaf_of_sheaf f ℱ.2⟩
  map _ _ g := ⟨pushforwardMap f g.1⟩
#align Top.sheaf.pushforward TopCat.Sheaf.pushforward

end Sheaf

end TopCat

