/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Moritz Firsching, Nikolas Kuhn, Amelia Livingston
-/
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
/-!
# The category of abelian groups satisfies Grothendieck's axiom AB5

-/

universe u

open CategoryTheory Limits

instance {J C : Type*} [Category J] [Category C] [HasColimitsOfShape J C] [Preadditive C] :
    (colim (J := J) (C := C)).Additive where

variable {J : Type u} [SmallCategory J] [IsFiltered J]

noncomputable instance :
    (colim (J := J) (C := AddCommGrp.{u})).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (fun S hS ↦ by
    replace hS := fun j => hS.map ((evaluation _ _).obj j)
    simp only [ShortComplex.ab_exact_iff_ker_le_range] at hS ⊢
    intro x (hx : _ = _)
    dsimp at hx
    rcases Concrete.colimit_exists_rep S.X₂ x with ⟨j, y, rfl⟩
    erw [← comp_apply, colimit.ι_map, comp_apply,
      ← map_zero (by exact colimit.ι S.X₃ j : (S.X₃).obj j →+ ↑(colimit S.X₃))] at hx
    rcases Concrete.colimit_exists_of_rep_eq.{u, u, u} S.X₃ _ _ hx
      with ⟨k, e₁, e₂, hk : _ = S.X₃.map e₂ 0⟩
    rw [map_zero, ← comp_apply, ← NatTrans.naturality, comp_apply] at hk
    rcases hS k hk with ⟨t, ht⟩
    use colimit.ι S.X₁ k t
    erw [← comp_apply, colimit.ι_map, comp_apply, ht]
    exact colimit.w_apply S.X₂ e₁ y)

noncomputable instance :
    PreservesFiniteLimits <| colim (J := J) (C := AddCommGrp.{u}) := by
  apply Functor.preservesFiniteLimits_of_preservesHomology

instance : HasFilteredColimits (AddCommGrp.{u}) where
  HasColimitsOfShape := inferInstance

noncomputable instance : AB5 (AddCommGrp.{u}) where
  ofShape _ := { preservesFiniteLimits := inferInstance }

attribute [local instance] Abelian.hasFiniteBiproducts

instance : AB4 AddCommGrp.{u} := AB4.of_AB5 _

attribute [reassoc] limit.lift_map

instance : HasExactLimitsOfShape (Discrete J) (AddCommGrp.{u}) := by
  apply ( config := {allowSynthFailures := true} )  hasExactLimitsOfShape_of_preservesEpi
  exact {
    preserves {X Y} f hf := by
      have : lim.map f = (Pi.isoLimit _).inv ≫ Limits.Pi.map (f.app ⟨·⟩) ≫ (Pi.isoLimit _).hom := by
        apply limit.hom_ext
        intro ⟨n⟩
        simp only [lim_obj, lim_map, limMap, IsLimit.map, limit.isLimit_lift, limit.lift_π,
          Cones.postcompose_obj_pt, limit.cone_x, Cones.postcompose_obj_π, NatTrans.comp_app,
          Functor.const_obj_obj, limit.cone_π, Pi.isoLimit, Limits.Pi.map, Category.assoc,
          limit.conePointUniqueUpToIso_hom_comp, Pi.cone_pt, Pi.cone_π, Discrete.natTrans_app,
          Discrete.functor_obj_eq_as]
        erw [IsLimit.conePointUniqueUpToIso_inv_comp_assoc]
        rfl
      let iX : limit X ≅ AddCommGrp.of ((i : J) → X.obj ⟨i⟩) := (Pi.isoLimit X).symm ≪≫
          (limit.isLimit _).conePointUniqueUpToIso (AddCommGrp.HasLimit.productLimitCone _).isLimit
      let iY : limit Y ≅ AddCommGrp.of ((i : J) → Y.obj ⟨i⟩) := (Pi.isoLimit Y).symm ≪≫
          (limit.isLimit _).conePointUniqueUpToIso (AddCommGrp.HasLimit.productLimitCone _).isLimit
      have : ⇑(iX.inv ≫ lim.map f ≫ iY.hom) = Pi.map (fun i ↦ f.app ⟨i⟩) := by
        rw [this]
        dsimp [iX, iY]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        simp [Pi.isoLimit, AddCommGrp.HasLimit.productLimitCone,
          IsLimit.conePointUniqueUpToIso, Limits.Pi.map, limit.cone]
        erw [limit.lift_map_assoc]
        ext g j
        simp
        erw [CategoryTheory.comp_apply]
        simp [AddCommGrp.HasLimit.lift]
        change ((getLimitCone (Discrete.functor fun j ↦ Y.obj { as := j })).cone.π.app _) _  = _
        have : (getLimitCone (Discrete.functor fun j ↦ Y.obj { as := j })).cone.π.app ⟨j⟩ =
            limit.π (Discrete.functor fun j ↦ Y.obj { as := j }) ⟨j⟩ := rfl
        rw [this]
        change (_ ≫ limit.π (Discrete.functor fun j ↦ Y.obj { as := j }) ⟨j⟩) _ = _
        simp
      suffices Epi (iX.inv ≫ lim.map f ≫ iY.hom) by
        suffices Epi (iX.hom ≫ (iX.inv ≫ lim.map f ≫ iY.hom) ≫ iY.inv) by simpa using this
        infer_instance
      rw [AddCommGrp.epi_iff_surjective]
      rw [this]
      simp_rw [CategoryTheory.NatTrans.epi_iff_epi_app, AddCommGrp.epi_iff_surjective] at hf
      intro b
      refine ⟨fun i ↦ (hf ⟨i⟩ (b i)).choose, ?_⟩
      funext i
      exact (hf ⟨i⟩ (b i)).choose_spec }

instance : AB4Star AddCommGrp.{u} where
  ofShape _ := inferInstance
