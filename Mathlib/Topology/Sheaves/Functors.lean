/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

#align_import topology.sheaves.functors from "leanprover-community/mathlib"@"85d6221d32c37e68f05b2e42cde6cee658dae5e9"

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

theorem map_diagram :
    Pairwise.diagram U ⋙ Opens.map f = Pairwise.diagram ((Opens.map f).obj ∘ U) := by
  have obj_eq : ∀ (j : Pairwise ι), (Pairwise.diagram U ⋙ Opens.map f).obj j =
    (Pairwise.diagram ((Opens.map f).toPrefunctor.obj ∘ U)).obj j
  · rintro ⟨i⟩ <;> rfl
    -- ⊢ (Pairwise.diagram U ⋙ Opens.map f).obj (Pairwise.single i) = (Pairwise.diagr …
                   -- 🎉 no goals
                   -- 🎉 no goals
  refine Functor.hext obj_eq ?_
  -- ⊢ ∀ (X_1 Y_1 : CategoryTheory.Pairwise ι) (f_1 : X_1 ⟶ Y_1), HEq ((Pairwise.di …
  intro i j g; apply Subsingleton.helim
  -- ⊢ HEq ((Pairwise.diagram U ⋙ Opens.map f).map g) ((Pairwise.diagram ((Opens.ma …
               -- ⊢ ((Pairwise.diagram U ⋙ Opens.map f).obj i ⟶ (Pairwise.diagram U ⋙ Opens.map  …
  rw [obj_eq, obj_eq]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_pairwise_intersections.map_diagram TopCat.Presheaf.SheafConditionPairwiseIntersections.map_diagram

theorem mapCocone :
    HEq ((Opens.map f).mapCocone (Pairwise.cocone U))
      (Pairwise.cocone ((Opens.map f).obj ∘ U)) := by
  unfold Functor.mapCocone Cocones.functoriality; dsimp; congr
  -- ⊢ HEq ((CategoryTheory.Functor.mk { obj := fun A => { pt := (Opens.map f).obj  …
                                                  -- ⊢ HEq { pt := (Opens.map f).obj (iSup U), ι := NatTrans.mk fun j => (Opens.map …
  iterate 2 rw [map_diagram]; rw [Opens.map_iSup]
  -- ⊢ HEq (fun j => (Opens.map f).map (Pairwise.coconeιApp U j)) (Pairwise.coconeι …
  apply Subsingleton.helim; rw [map_diagram, Opens.map_iSup]
  -- ⊢ ((X_1 : CategoryTheory.Pairwise ι) → (Pairwise.diagram U ⋙ Opens.map f).obj  …
                            -- ⊢ HEq (_ : ∀ ⦃X_1 Y_1 : CategoryTheory.Pairwise ι⦄ (f_1 : X_1 ⟶ Y_1), (Pairwis …
  apply proof_irrel_heq
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_pairwise_intersections.map_cocone TopCat.Presheaf.SheafConditionPairwiseIntersections.mapCocone

theorem pushforward_sheaf_of_sheaf {F : Presheaf C X} (h : F.IsSheafPairwiseIntersections) :
    (f _* F).IsSheafPairwiseIntersections := fun ι U => by
  convert h ((Opens.map f).obj ∘ U) using 2
  -- ⊢ (Pairwise.diagram U).op ⋙ f _* F = (Pairwise.diagram ((Opens.map f).toPrefun …
  rw [← map_diagram]; rfl
  -- ⊢ (Pairwise.diagram U).op ⋙ f _* F = (Pairwise.diagram U ⋙ Opens.map f).op ⋙ F
                      -- ⊢ HEq ((f _* F).mapCone (Cocone.op (Pairwise.cocone U))) (F.mapCone (Cocone.op …
  change HEq (Functor.mapCone F ((Opens.map f).mapCocone (Pairwise.cocone U)).op) _
  -- ⊢ HEq (F.mapCone (Cocone.op ((Opens.map f).mapCocone (Pairwise.cocone U)))) (F …
  congr
  iterate 2 rw [map_diagram]
  -- ⊢ HEq ((Opens.map f).mapCocone (Pairwise.cocone U)) (Pairwise.cocone ((Opens.m …
  apply mapCocone
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.sheaf_condition_pairwise_intersections.pushforward_sheaf_of_sheaf TopCat.Presheaf.SheafConditionPairwiseIntersections.pushforward_sheaf_of_sheaf

end Presheaf.SheafConditionPairwiseIntersections

namespace Sheaf

open Presheaf

/-- The pushforward of a sheaf (by a continuous map) is a sheaf.
-/
theorem pushforward_sheaf_of_sheaf {F : X.Presheaf C} (h : F.IsSheaf) : (f _* F).IsSheaf := by
  rw [isSheaf_iff_isSheafPairwiseIntersections] at h ⊢
  -- ⊢ IsSheafPairwiseIntersections (f _* F)
  exact SheafConditionPairwiseIntersections.pushforward_sheaf_of_sheaf f h
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.sheaf.pushforward_sheaf_of_sheaf TopCat.Sheaf.pushforward_sheaf_of_sheaf

/-- The pushforward functor.
-/
def pushforward (f : X ⟶ Y) : X.Sheaf C ⥤ Y.Sheaf C where
  obj ℱ := ⟨f _* ℱ.1, pushforward_sheaf_of_sheaf f ℱ.2⟩
  map {_ _} g := ⟨pushforwardMap f g.1⟩
set_option linter.uppercaseLean3 false in
#align Top.sheaf.pushforward TopCat.Sheaf.pushforward

end Sheaf

end TopCat
