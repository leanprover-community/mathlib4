/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang

! This file was ported from Lean 3 source module topology.category.Top.limits.cofiltered
! leanprover-community/mathlib commit dbdf71cee7bb20367cb7e37279c08b0c218cf967
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.Category.Top.Limits.Basic

/-!
# Cofiltered limits in Top.

Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/


open TopologicalSpace

open CategoryTheory

open CategoryTheory.Limits

universe u v w

noncomputable section

namespace TopCat

section CofilteredLimit

variable {J : Type v} [SmallCategory J] [IsCofiltered J] (F : J ⥤ TopCat.{max v u}) (C : Cone F)
  (hC : IsLimit C)

include hC

/-- Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/
theorem isTopologicalBasis_cofiltered_limit (T : ∀ j, Set (Set (F.obj j)))
    (hT : ∀ j, IsTopologicalBasis (T j)) (univ : ∀ i : J, Set.univ ∈ T i)
    (inter : ∀ (i) (U1 U2 : Set (F.obj i)), U1 ∈ T i → U2 ∈ T i → U1 ∩ U2 ∈ T i)
    (compat : ∀ (i j : J) (f : i ⟶ j) (V : Set (F.obj j)) (hV : V ∈ T j), F.map f ⁻¹' V ∈ T i) :
    IsTopologicalBasis
      {U : Set C.pt | ∃ (j : _) (V : Set (F.obj j)), V ∈ T j ∧ U = C.π.app j ⁻¹' V} := by
  classical
  -- The limit cone for `F` whose topology is defined as an infimum.
  let D := limit_cone_infi F
  -- The isomorphism between the cone point of `C` and the cone point of `D`.
  let E : C.X ≅ D.X := hC.cone_point_unique_up_to_iso (limit_cone_infi_is_limit _)
  have hE : Inducing E.hom := (TopCat.homeoOfIso E).Inducing
  -- Reduce to the assertion of the theorem with `D` instead of `C`.
  suffices
    is_topological_basis
      {U : Set D.X | ∃ (j : _) (V : Set (F.obj j)), V ∈ T j ∧ U = D.π.app j ⁻¹' V} by
    convert this.inducing hE
    ext U0
    constructor
    · rintro ⟨j, V, hV, rfl⟩
      refine' ⟨D.π.app j ⁻¹' V, ⟨j, V, hV, rfl⟩, rfl⟩
    · rintro ⟨W, ⟨j, V, hV, rfl⟩, rfl⟩
      refine' ⟨j, V, hV, rfl⟩
  -- Using `D`, we can apply the characterization of the topological basis of a
  -- topology defined as an infimum...
  convert isTopologicalBasis_iInf hT fun j (x : D.X) => D.π.app j x
  ext U0
  constructor
  · rintro ⟨j, V, hV, rfl⟩
    let U : ∀ i, Set (F.obj i) := fun i => if h : i = j then by rw [h]; exact V else Set.univ
    refine' ⟨U, {j}, _, _⟩
    · rintro i h
      rw [Finset.mem_singleton] at h
      dsimp [U]
      rw [dif_pos h]
      subst h
      exact hV
    · dsimp [U]
      simp
  · rintro ⟨U, G, h1, h2⟩
    obtain ⟨j, hj⟩ := is_cofiltered.inf_objs_exists G
    let g : ∀ (e) (he : e ∈ G), j ⟶ e := fun _ he => (hj he).some
    let Vs : J → Set (F.obj j) := fun e => if h : e ∈ G then F.map (g e h) ⁻¹' U e else Set.univ
    let V : Set (F.obj j) := ⋂ (e : J) (he : e ∈ G), Vs e
    refine' ⟨j, V, _, _⟩
    · -- An intermediate claim used to apply induction along `G : finset J` later on.
      have :
        ∀ (S : Set (Set (F.obj j))) (E : Finset J) (P : J → Set (F.obj j)) (univ : Set.univ ∈ S)
          (inter : ∀ A B : Set (F.obj j), A ∈ S → B ∈ S → A ∩ B ∈ S)
          (cond : ∀ (e : J) (he : e ∈ E), P e ∈ S), (⋂ (e) (he : e ∈ E), P e) ∈ S := by
        intro S E
        apply E.induction_on
        · intro P he hh
          simpa
        · intro a E ha hh1 hh2 hh3 hh4 hh5
          rw [Finset.set_biInter_insert]
          refine' hh4 _ _ (hh5 _ (Finset.mem_insert_self _ _)) (hh1 _ hh3 hh4 _)
          intro e he
          exact hh5 e (Finset.mem_insert_of_mem he)
      -- use the intermediate claim to finish off the goal using `univ` and `inter`.
      refine' this _ _ _ (univ _) (inter _) _
      intro e he
      dsimp [Vs]
      rw [dif_pos he]
      exact compat j e (g e he) (U e) (h1 e he)
    · -- conclude...
      rw [h2]
      dsimp [V]
      rw [Set.preimage_iInter]
      congr 1
      ext1 e
      rw [Set.preimage_iInter]
      congr 1
      ext1 he
      dsimp [Vs]
      rw [dif_pos he, ← Set.preimage_comp]
      congr 1
      change _ = ⇑(D.π.app j ≫ F.map (g e he))
      rw [D.w]
#align Top.is_topological_basis_cofiltered_limit TopCat.isTopologicalBasis_cofiltered_limit

end CofilteredLimit

end TopCat
