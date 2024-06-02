/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.DoldKan.FunctorN

#align_import algebraic_topology.dold_kan.normalized from "leanprover-community/mathlib"@"32a7e535287f9c73f2e4d2aef306a39190f0b504"

/-!

# Comparison with the normalized Moore complex functor

In this file, we show that when the category `A` is abelian,
there is an isomorphism `N₁_iso_normalizedMooreComplex_comp_toKaroubi` between
the functor `N₁ : SimplicialObject A ⥤ Karoubi (ChainComplex A ℕ)`
defined in `FunctorN.lean` and the composition of
`normalizedMooreComplex A` with the inclusion
`ChainComplex A ℕ ⥤ Karoubi (ChainComplex A ℕ)`.

This isomorphism shall be used in `Equivalence.lean` in order to obtain
the Dold-Kan equivalence
`CategoryTheory.Abelian.DoldKan.equivalence : SimplicialObject A ≌ ChainComplex A ℕ`
with a functor (definitionally) equal to `normalizedMooreComplex A`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Subobject CategoryTheory.Idempotents DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

universe v

variable {A : Type*} [Category A] [Abelian A] {X : SimplicialObject A}

theorem HigherFacesVanish.inclusionOfMooreComplexMap (n : ℕ) :
    HigherFacesVanish (n + 1) ((inclusionOfMooreComplexMap X).f (n + 1)) := fun j _ => by
  dsimp [AlgebraicTopology.inclusionOfMooreComplexMap, NormalizedMooreComplex.objX]
  rw [← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ j
    (by simp only [Finset.mem_univ])), assoc, kernelSubobject_arrow_comp, comp_zero]
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.higher_faces_vanish.inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.HigherFacesVanish.inclusionOfMooreComplexMap

theorem factors_normalizedMooreComplex_PInfty (n : ℕ) :
    Subobject.Factors (NormalizedMooreComplex.objX X n) (PInfty.f n) := by
  rcases n with _|n
  · apply top_factors
  · rw [PInfty_f, NormalizedMooreComplex.objX, finset_inf_factors]
    intro i _
    apply kernelSubobject_factors
    exact (HigherFacesVanish.of_P (n + 1) n) i le_add_self
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.factors_normalized_Moore_complex_P_infty AlgebraicTopology.DoldKan.factors_normalizedMooreComplex_PInfty

/-- `PInfty` factors through the normalized Moore complex -/
@[simps!]
def PInftyToNormalizedMooreComplex (X : SimplicialObject A) : K[X] ⟶ N[X] :=
  ChainComplex.ofHom _ _ _ _ _ _
    (fun n => factorThru _ _ (factors_normalizedMooreComplex_PInfty n)) fun n => by
    rw [← cancel_mono (NormalizedMooreComplex.objX X n).arrow, assoc, assoc, factorThru_arrow,
      ← inclusionOfMooreComplexMap_f, ← normalizedMooreComplex_objD,
      ← (inclusionOfMooreComplexMap X).comm (n + 1) n, inclusionOfMooreComplexMap_f,
      factorThru_arrow_assoc, ← alternatingFaceMapComplex_obj_d]
    exact PInfty.comm (n + 1) n
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex

@[reassoc (attr := simp)]
theorem PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap (X : SimplicialObject A) :
    PInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X = PInfty := by aesop_cat
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap

@[reassoc (attr := simp)]
theorem PInftyToNormalizedMooreComplex_naturality {X Y : SimplicialObject A} (f : X ⟶ Y) :
    AlternatingFaceMapComplex.map f ≫ PInftyToNormalizedMooreComplex Y =
      PInftyToNormalizedMooreComplex X ≫ NormalizedMooreComplex.map f := by
  aesop_cat
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex_naturality AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_naturality

@[reassoc (attr := simp)]
theorem PInfty_comp_PInftyToNormalizedMooreComplex (X : SimplicialObject A) :
    PInfty ≫ PInftyToNormalizedMooreComplex X = PInftyToNormalizedMooreComplex X := by aesop_cat
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.P_infty_comp_P_infty_to_normalized_Moore_complex AlgebraicTopology.DoldKan.PInfty_comp_PInftyToNormalizedMooreComplex

@[reassoc (attr := simp)]
theorem inclusionOfMooreComplexMap_comp_PInfty (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ PInfty = inclusionOfMooreComplexMap X := by
  ext (_|n)
  · dsimp
    simp only [comp_id]
  · exact (HigherFacesVanish.inclusionOfMooreComplexMap n).comp_P_eq_self
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.inclusion_of_Moore_complex_map_comp_P_infty AlgebraicTopology.DoldKan.inclusionOfMooreComplexMap_comp_PInfty

instance : Mono (inclusionOfMooreComplexMap X) :=
  ⟨fun _ _ hf => by
    ext n
    dsimp
    ext
    exact HomologicalComplex.congr_hom hf n⟩

/-- `inclusionOfMooreComplexMap X` is a split mono. -/
def splitMonoInclusionOfMooreComplexMap (X : SimplicialObject A) :
    SplitMono (inclusionOfMooreComplexMap X) where
  retraction := PInftyToNormalizedMooreComplex X
  id := by
    simp only [← cancel_mono (inclusionOfMooreComplexMap X), assoc, id_comp,
      PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      inclusionOfMooreComplexMap_comp_PInfty]
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.split_mono_inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap

variable (A)

/-- When the category `A` is abelian,
the functor `N₁ : SimplicialObject A ⥤ Karoubi (ChainComplex A ℕ)` defined
using `PInfty` identifies to the composition of the normalized Moore complex functor
and the inclusion in the Karoubi envelope. -/
def N₁_iso_normalizedMooreComplex_comp_toKaroubi : N₁ ≅ normalizedMooreComplex A ⋙ toKaroubi _ where
  hom :=
    { app := fun X =>
        { f := PInftyToNormalizedMooreComplex X
          comm := by erw [comp_id, PInfty_comp_PInftyToNormalizedMooreComplex] }
      naturality := fun X Y f => by
        simp only [Functor.comp_map, normalizedMooreComplex_map,
          PInftyToNormalizedMooreComplex_naturality, Karoubi.hom_ext_iff, Karoubi.comp_f, N₁_map_f,
          PInfty_comp_PInftyToNormalizedMooreComplex_assoc, toKaroubi_map_f, assoc] }
  inv :=
    { app := fun X =>
        { f := inclusionOfMooreComplexMap X
          comm := by erw [inclusionOfMooreComplexMap_comp_PInfty, id_comp] }
      naturality := fun X Y f => by
        ext
        simp only [Functor.comp_map, normalizedMooreComplex_map, Karoubi.comp_f, toKaroubi_map_f,
          HomologicalComplex.comp_f, NormalizedMooreComplex.map_f,
          inclusionOfMooreComplexMap_f, factorThru_arrow, N₁_map_f,
          inclusionOfMooreComplexMap_comp_PInfty_assoc, AlternatingFaceMapComplex.map_f] }
  hom_inv_id := by
    ext X : 3
    simp only [PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      NatTrans.comp_app, Karoubi.comp_f, N₁_obj_p, NatTrans.id_app, Karoubi.id_eq]
  inv_hom_id := by
    ext X : 3
    rw [← cancel_mono (inclusionOfMooreComplexMap X)]
    simp only [NatTrans.comp_app, Karoubi.comp_f, assoc, NatTrans.id_app, Karoubi.id_eq,
      PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      inclusionOfMooreComplexMap_comp_PInfty]
    dsimp only [Functor.comp_obj, toKaroubi]
    erw [id_comp]
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.N₁_iso_normalized_Moore_complex_comp_to_karoubi AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi

end DoldKan

end AlgebraicTopology
