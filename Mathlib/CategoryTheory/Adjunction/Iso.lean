/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Opposites
/-!

# Isomorphisms via the unit and counit

This file proves the following result `CategoryTheory.Adjunction.isIso_counit_of_iso`:
Given an adjunction `L ⊣ R` and an isomorphism `X ≅ L.obj (R.obj X)`, with `L` fully faithful,
the counit `L.obj (R.obj X) ⟶ X` is an isomorphism.

We also prove the dual result in the case where the right adjoint is fully faithful.
-/

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

lemma isIso_counit_of_iso [L.Faithful] [L.Full] {X : D} (i : X ≅ L.obj (R.obj X)) :
    IsIso (adj.counit.app X : L.obj (R.obj X) ⟶ X) := by
  let D' := L.EssImageSubcategory
  let iD' : D' ⥤ D := L.essImageInclusion
  let L' : C ⥤ D' := L.toEssImage
  let R' : D' ⥤ C := iD' ⋙ R
  let comm₁ : L ≅ L' ⋙ iD' := Iso.refl _
  let comm₂ : iD' ⋙ R ≅ R' := Iso.refl _
  let adj' : L' ⊣ R' := adj.restrictFullyFaithful (𝟭 _) iD' comm₁ comm₂
  have : L'.IsEquivalence := Functor.IsEquivalence.ofFullyFaithfullyEssSurj L'
  let R'' := L'.asEquivalence.inverse
  let iR : R' ≅ R'' := adj'.rightAdjointUniq L'.asEquivalence.toAdjunction
  have hR' : R'.IsEquivalence := Functor.IsEquivalence.ofIso iR.symm inferInstance
  let X' : D' := ⟨X, ⟨R.obj X, ⟨i.symm⟩⟩⟩
  have : IsIso (adj'.counit.app X') := inferInstance
  have hh := @Functor.map_isIso _ _ _ _ _ _ iD' _ this
  convert hh
  simp only [Functor.comp_obj, Functor.id_obj, restrictFullyFaithful,
    equivOfFullyFaithful, Equiv.instTransSortSortSortEquivEquivEquiv_trans, Functor.id_map,
    mkOfHomEquiv_counit_app, Equiv.invFun_as_coe, Equiv.symm_trans_apply,
    Equiv.symm_symm, Iso.homCongr_symm, Iso.refl_symm, Iso.homCongr_apply, Iso.refl_inv,
    Iso.symm_hom, Iso.app_inv, Category.id_comp, homEquiv_counit, Functor.map_comp,
    Category.assoc, Iso.symm_inv, Iso.app_hom, NatTrans.id_app, Iso.refl_hom, Category.comp_id,
    Equiv.coe_fn_symm_mk, Functor.image_preimage, adj', comm₁]
  erw [Category.id_comp, Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

lemma isIso_unit_of_iso [R.Faithful] [R.Full] {X : C} (i : X ≅ R.obj (L.obj X)) :
    IsIso (adj.unit.app X : X ⟶ R.obj (L.obj X)) := by
  let C' := R.EssImageSubcategory
  let iC' : C' ⥤ C := R.essImageInclusion
  let L' : C' ⥤ D := iC' ⋙ L
  let R' : D ⥤ C' := R.toEssImage
  let comm₁ : iC' ⋙ L ≅ L' := Iso.refl _
  let comm₂ : R ≅ R' ⋙ iC' := Iso.refl _
  let adj' : L' ⊣ R' := adj.restrictFullyFaithful iC' (𝟭 _) comm₁ comm₂
  have : R'.IsEquivalence := Functor.IsEquivalence.ofFullyFaithfullyEssSurj R'
  let L'' := R'.asEquivalence.symm.functor
  let iR : L' ≅ L'' := adj'.leftAdjointUniq R'.asEquivalence.symm.toAdjunction
  have hR' : L'.IsEquivalence := Functor.IsEquivalence.ofIso iR.symm inferInstance
  let X' : C' := ⟨X, ⟨L.obj X, ⟨i.symm⟩⟩⟩
  have : IsIso (adj'.unit.app X') := inferInstance
  have hh := @Functor.map_isIso _ _ _ _ _ _ iC' _ this
  convert hh
  simp only [Functor.id_obj, Functor.comp_obj, restrictFullyFaithful, equivOfFullyFaithful,
    Functor.id_map, Iso.refl_symm, Equiv.instTransSortSortSortEquivEquivEquiv_trans,
    mkOfHomEquiv_unit_app, Equiv.trans_apply, Iso.homCongr_apply, Iso.app_inv, Iso.refl_inv,
    NatTrans.id_app, Iso.refl_hom, Category.comp_id, Category.id_comp, homEquiv_unit, Iso.app_hom,
    Equiv.coe_fn_symm_mk, Functor.image_preimage, adj', comm₁, comm₂]
  erw [Functor.map_id, Category.comp_id]
  rfl
