/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

open TopologicalSpace Opens FundamentalGroupoid CategoryTheory Limits

universe u

variable {X : TopCat.{u}} {ι} (U : ι → Opens X)

noncomputable section

namespace CategoryTheory.Pairwise

abbrev π₁Diagram := Pairwise.diagram U ⋙ toTopCat X ⋙ fundamentalGroupoidFunctor

abbrev π₁Cocone : Cocone (π₁Diagram U) :=
  (toTopCat X ⋙ fundamentalGroupoidFunctor).mapCocone (Pairwise.cocone U)

variable {U} (c : Cocone (π₁Diagram U)) (x y : (π₁Cocone U).pt)

def π₁CoconeDescObj : c.pt :=
  (c.ι.app <| single (mem_iSup.mp x.2).choose).obj ⟨x.1, (mem_iSup.mp x.2).choose_spec⟩

lemma π₁CoconeDescObj_eq (i : ι) (hi : x.1 ∈ U i) :
    π₁CoconeDescObj c x = (c.ι.app <| single i).obj ⟨x.1, hi⟩ := by
  have := mem_iSup.mp x.2
  let x : ↥(U i ⊓ U this.choose) := ⟨x.1, hi, (mem_iSup.mp x.2).choose_spec⟩
  change ((π₁Diagram U).map (Hom.right i _) ≫ c.ι.app (single _)).obj x =
         ((π₁Diagram U).map (Hom.left i _)  ≫ c.ι.app (single i)).obj x
  rw [c.w, c.w]

variable {x y}

def π₁CoconeDescMapPath (p : Path (toTop x) (toTop y)) :
    π₁CoconeDescObj c x ⟶ π₁CoconeDescObj c y := by


private abbrev pairwiseπ₁Cocone_desc (c : Cocone (π₁Diagram U)) :
    (π₁Cocone U).pt ⟶ c.pt where
  obj := π₁CoconeDescObj c
  map {x y} p := _
  map_id := _
  map_comp := _

end CategoryTheory.Pairwise

def vanKampen : IsColimit (pairwiseFundamentalGroupoidCocone U) :=
  ⟨_, _, _⟩




open TopologicalSpace TopCat Opposite CategoryTheory CategoryTheory.Limits
