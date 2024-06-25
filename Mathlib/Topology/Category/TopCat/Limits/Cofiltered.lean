/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang
-/
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Filtered.Basic

#align_import topology.category.Top.limits.cofiltered from "leanprover-community/mathlib"@"dbdf71cee7bb20367cb7e37279c08b0c218cf967"

/-!
# Cofiltered limits in the category of topological spaces

Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `Set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/

set_option linter.uppercaseLean3 false

open TopologicalSpace

open CategoryTheory

open CategoryTheory.Limits

universe u v w

noncomputable section

namespace TopCat

section CofilteredLimit

variable {J : Type v} [SmallCategory J] [IsCofiltered J] (F : J ⥤ TopCat.{max v u}) (C : Cone F)
  (hC : IsLimit C)

/-- Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `Set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/
theorem isTopologicalBasis_cofiltered_limit (T : ∀ j, Set (Set (F.obj j)))
    (hT : ∀ j, IsTopologicalBasis (T j)) (univ : ∀ i : J, Set.univ ∈ T i)
    (inter : ∀ (i) (U1 U2 : Set (F.obj i)), U1 ∈ T i → U2 ∈ T i → U1 ∩ U2 ∈ T i)
    (compat : ∀ (i j : J) (f : i ⟶ j) (V : Set (F.obj j)) (_hV : V ∈ T j), F.map f ⁻¹' V ∈ T i) :
    IsTopologicalBasis
      {U : Set C.pt | ∃ (j : _) (V : Set (F.obj j)), V ∈ T j ∧ U = C.π.app j ⁻¹' V} := by
  classical
  -- The limit cone for `F` whose topology is defined as an infimum.
  let D := limitConeInfi F
  -- The isomorphism between the cone point of `C` and the cone point of `D`.
  let E : C.pt ≅ D.pt := hC.conePointUniqueUpToIso (limitConeInfiIsLimit _)
  have hE : Inducing E.hom := (TopCat.homeoOfIso E).inducing
  -- Reduce to the assertion of the theorem with `D` instead of `C`.
  suffices
    IsTopologicalBasis
      {U : Set D.pt | ∃ (j : _) (V : Set (F.obj j)), V ∈ T j ∧ U = D.π.app j ⁻¹' V} by
    convert this.inducing hE
    ext U0
    constructor
    · rintro ⟨j, V, hV, rfl⟩
      exact ⟨D.π.app j ⁻¹' V, ⟨j, V, hV, rfl⟩, rfl⟩
    · rintro ⟨W, ⟨j, V, hV, rfl⟩, rfl⟩
      exact ⟨j, V, hV, rfl⟩
  -- Using `D`, we can apply the characterization of the topological basis of a
  -- topology defined as an infimum...
  convert IsTopologicalBasis.iInf_induced hT fun j (x : D.pt) => D.π.app j x using 1
  ext U0
  constructor
  · rintro ⟨j, V, hV, rfl⟩
    let U : ∀ i, Set (F.obj i) := fun i => if h : i = j then by rw [h]; exact V else Set.univ
    refine ⟨U, {j}, ?_, ?_⟩
    · simp only [Finset.mem_singleton]
      rintro i rfl
      simpa [U]
    · simp [U]
  · rintro ⟨U, G, h1, h2⟩
    obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists G
    let g : ∀ e ∈ G, j ⟶ e := fun _ he => (hj he).some
    let Vs : J → Set (F.obj j) := fun e => if h : e ∈ G then F.map (g e h) ⁻¹' U e else Set.univ
    let V : Set (F.obj j) := ⋂ (e : J) (_he : e ∈ G), Vs e
    refine ⟨j, V, ?_, ?_⟩
    · -- An intermediate claim used to apply induction along `G : Finset J` later on.
      have :
        ∀ (S : Set (Set (F.obj j))) (E : Finset J) (P : J → Set (F.obj j)) (_univ : Set.univ ∈ S)
          (_inter : ∀ A B : Set (F.obj j), A ∈ S → B ∈ S → A ∩ B ∈ S)
          (_cond : ∀ (e : J) (_he : e ∈ E), P e ∈ S), (⋂ (e) (_he : e ∈ E), P e) ∈ S := by
        intro S E
        induction E using Finset.induction_on with
        | empty =>
          intro P he _hh
          simpa
        | @insert a E _ha hh1 =>
          intro hh2 hh3 hh4 hh5
          rw [Finset.set_biInter_insert]
          refine hh4 _ _ (hh5 _ (Finset.mem_insert_self _ _)) (hh1 _ hh3 hh4 ?_)
          intro e he
          exact hh5 e (Finset.mem_insert_of_mem he)
      -- use the intermediate claim to finish off the goal using `univ` and `inter`.
      refine this _ _ _ (univ _) (inter _) ?_
      intro e he
      dsimp [Vs]
      rw [dif_pos he]
      exact compat j e (g e he) (U e) (h1 e he)
    · -- conclude...
      rw [h2]
      change _ = (D.π.app j)⁻¹' ⋂ (e : J) (_ : e ∈ G), Vs e
      rw [Set.preimage_iInter]
      apply congrArg
      ext1 e
      erw [Set.preimage_iInter]
      apply congrArg
      ext1 he
      -- Porting note: needed more hand holding here
      change (D.π.app e)⁻¹' U e =
        (D.π.app j) ⁻¹' if h : e ∈ G then F.map (g e h) ⁻¹' U e else Set.univ
      rw [dif_pos he, ← Set.preimage_comp]
      apply congrFun
      apply congrArg
      erw [← coe_comp, D.w] -- now `erw` after #13170
      rfl
#align Top.is_topological_basis_cofiltered_limit TopCat.isTopologicalBasis_cofiltered_limit

end CofilteredLimit

end TopCat
