/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.normalized
! leanprover-community/mathlib commit d1d69e99ed34c95266668af4e288fc1c598b9a7f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.FunctorN

/-!

# Comparison with the normalized Moore complex functor

TODO (@joelriou) continue adding the various files referenced below

In this file, we show that when the category `A` is abelian,
there is an isomorphism `N₁_iso_normalized_Moore_complex_comp_to_karoubi` between
the functor `N₁ : simplicial_object A ⥤ karoubi (chain_complex A ℕ)`
defined in `functor_n.lean` and the composition of
`normalized_Moore_complex A` with the inclusion
`chain_complex A ℕ ⥤ karoubi (chain_complex A ℕ)`.

This isomorphism shall be used in `equivalence.lean` in order to obtain
the Dold-Kan equivalence
`category_theory.abelian.dold_kan.equivalence : simplicial_object A ≌ chain_complex A ℕ`
with a functor (definitionally) equal to `normalized_Moore_complex A`.

-/


open
  CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Subobject CategoryTheory.Idempotents

open DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

universe v

variable {A : Type _} [Category A] [Abelian A] {X : SimplicialObject A}

theorem HigherFacesVanish.inclusionOfMooreComplexMap (n : ℕ) :
    HigherFacesVanish (n + 1) ((inclusionOfMooreComplexMap X).f (n + 1)) := fun j hj =>
  by
  dsimp [inclusion_of_Moore_complex_map]
  rw [←
    factor_thru_arrow _ _
      (finset_inf_arrow_factors Finset.univ _ j (by simp only [Finset.mem_univ])),
    assoc, kernel_subobject_arrow_comp, comp_zero]
#align algebraic_topology.dold_kan.higher_faces_vanish.inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.HigherFacesVanish.inclusionOfMooreComplexMap

theorem factors_normalized_Moore_complex_pInfty (n : ℕ) :
    Subobject.Factors (NormalizedMooreComplex.objX X n) (PInfty.f n) :=
  by
  cases n
  · apply top_factors
  · rw [P_infty_f, normalized_Moore_complex.obj_X, finset_inf_factors]
    intro i hi
    apply kernel_subobject_factors
    exact (higher_faces_vanish.of_P (n + 1) n) i le_add_self
#align algebraic_topology.dold_kan.factors_normalized_Moore_complex_P_infty AlgebraicTopology.DoldKan.factors_normalized_Moore_complex_pInfty

/-- P_infty factors through the normalized Moore complex -/
@[simps]
def pInftyToNormalizedMooreComplex (X : SimplicialObject A) : K[X] ⟶ N[X] :=
  ChainComplex.ofHom _ _ _ _ _ _
    (fun n => factorThru _ _ (factors_normalized_Moore_complex_pInfty n)) fun n =>
    by
    rw [← cancel_mono (normalized_Moore_complex.obj_X X n).arrow, assoc, assoc, factor_thru_arrow, ←
      inclusion_of_Moore_complex_map_f, ← normalized_Moore_complex_obj_d, ←
      (inclusion_of_Moore_complex_map X).comm' (n + 1) n rfl, inclusion_of_Moore_complex_map_f,
      factor_thru_arrow_assoc, ← alternating_face_map_complex_obj_d]
    exact P_infty.comm' (n + 1) n rfl
#align algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex AlgebraicTopology.DoldKan.pInftyToNormalizedMooreComplex

@[simp, reassoc.1]
theorem pInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap (X : SimplicialObject A) :
    pInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X = PInfty := by tidy
#align algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.pInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap

@[simp, reassoc.1]
theorem pInftyToNormalizedMooreComplex_naturality {X Y : SimplicialObject A} (f : X ⟶ Y) :
    AlternatingFaceMapComplex.map f ≫ pInftyToNormalizedMooreComplex Y =
      pInftyToNormalizedMooreComplex X ≫ NormalizedMooreComplex.map f :=
  by tidy
#align algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex_naturality AlgebraicTopology.DoldKan.pInftyToNormalizedMooreComplex_naturality

@[simp, reassoc.1]
theorem pInfty_comp_pInftyToNormalizedMooreComplex (X : SimplicialObject A) :
    PInfty ≫ pInftyToNormalizedMooreComplex X = pInftyToNormalizedMooreComplex X := by tidy
#align algebraic_topology.dold_kan.P_infty_comp_P_infty_to_normalized_Moore_complex AlgebraicTopology.DoldKan.pInfty_comp_pInftyToNormalizedMooreComplex

@[simp, reassoc.1]
theorem inclusionOfMooreComplexMap_comp_pInfty (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ PInfty = inclusionOfMooreComplexMap X :=
  by
  ext n
  cases n
  · dsimp
    simp only [comp_id]
  · exact (higher_faces_vanish.inclusion_of_Moore_complex_map n).comp_P_eq_self
#align algebraic_topology.dold_kan.inclusion_of_Moore_complex_map_comp_P_infty AlgebraicTopology.DoldKan.inclusionOfMooreComplexMap_comp_pInfty

instance : Mono (inclusionOfMooreComplexMap X) :=
  ⟨fun Y f₁ f₂ hf => by
    ext n
    exact HomologicalComplex.congr_hom hf n⟩

/-- `inclusion_of_Moore_complex_map X` is a split mono. -/
def splitMonoInclusionOfMooreComplexMap (X : SimplicialObject A) :
    SplitMono (inclusionOfMooreComplexMap X)
    where
  retraction := pInftyToNormalizedMooreComplex X
  id' := by
    simp only [← cancel_mono (inclusion_of_Moore_complex_map X), assoc, id_comp,
      P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map,
      inclusion_of_Moore_complex_map_comp_P_infty]
#align algebraic_topology.dold_kan.split_mono_inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap

variable (A)

/-- When the category `A` is abelian,
the functor `N₁ : simplicial_object A ⥤ karoubi (chain_complex A ℕ)` defined
using `P_infty` identifies to the composition of the normalized Moore complex functor
and the inclusion in the Karoubi envelope. -/
def n₁IsoNormalizedMooreComplexCompToKaroubi : N₁ ≅ normalizedMooreComplex A ⋙ toKaroubi _
    where
  Hom :=
    { app := fun X =>
        { f := pInftyToNormalizedMooreComplex X
          comm := by erw [comp_id, P_infty_comp_P_infty_to_normalized_Moore_complex] }
      naturality' := fun X Y f => by
        simp only [functor.comp_map, normalized_Moore_complex_map,
          P_infty_to_normalized_Moore_complex_naturality, karoubi.hom_ext, karoubi.comp_f, N₁_map_f,
          P_infty_comp_P_infty_to_normalized_Moore_complex_assoc, to_karoubi_map_f, assoc] }
  inv :=
    { app := fun X =>
        { f := inclusionOfMooreComplexMap X
          comm := by erw [inclusion_of_Moore_complex_map_comp_P_infty, id_comp] }
      naturality' := fun X Y f => by
        ext
        simp only [functor.comp_map, normalized_Moore_complex_map, karoubi.comp_f, to_karoubi_map_f,
          HomologicalComplex.comp_f, normalized_Moore_complex.map_f,
          inclusion_of_Moore_complex_map_f, factor_thru_arrow, N₁_map_f,
          inclusion_of_Moore_complex_map_comp_P_infty_assoc, alternating_face_map_complex.map_f] }
  hom_inv_id' := by
    ext X : 3
    simp only [P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map,
      nat_trans.comp_app, karoubi.comp_f, N₁_obj_p, nat_trans.id_app, karoubi.id_eq]
  inv_hom_id' := by
    ext X : 3
    simp only [← cancel_mono (inclusion_of_Moore_complex_map X), nat_trans.comp_app, karoubi.comp_f,
      assoc, nat_trans.id_app, karoubi.id_eq,
      P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map,
      inclusion_of_Moore_complex_map_comp_P_infty]
    dsimp only [functor.comp_obj, to_karoubi]
    rw [id_comp]
#align algebraic_topology.dold_kan.N₁_iso_normalized_Moore_complex_comp_to_karoubi AlgebraicTopology.DoldKan.n₁IsoNormalizedMooreComplexCompToKaroubi

end DoldKan

end AlgebraicTopology

