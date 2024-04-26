/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Adjunction.Basic
/-!

# Restricting adjunctions

`Adjunction.restrictFullyFaithful` shows that an adjunction can be restricted along fully faithful
inclusions.
-/

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂ v₃ v₄ u₃ u₄

open Category Opposite

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {C' : Type u₃} [Category.{v₃} C']
variable {D' : Type u₄} [Category.{v₄} D']
variable (iC : C ⥤ C') (iD : D ⥤ D') {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj : L' ⊣ R')
variable {L : C ⥤ D} {R : D ⥤ C} (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC)
variable [iC.Full] [iC.Faithful] [iD.Full] [iD.Faithful]

/-- If `C` is a full subcategory of `C'` and `D` is a full subcategory of `D'`, then we can restrict
an adjunction `L' ⊣ R'` where `L' : C' ⥤ D'` and `R' : D' ⥤ C'` to `C` and `D`.
The construction here is slightly more general, in that `C` is required only to have a full and
faithful "inclusion" functor `iC : C ⥤ C'` (and similarly `iD : D ⥤ D'`) which commute (up to
natural isomorphism) with the proposed restrictions.
-/
def restrictFullyFaithful : L ⊣ R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        calc
          (L.obj X ⟶ Y) ≃ (iD.obj (L.obj X) ⟶ iD.obj Y) := equivOfFullyFaithful iD
          _ ≃ (L'.obj (iC.obj X) ⟶ iD.obj Y) := Iso.homCongr (comm1.symm.app X) (Iso.refl _)
          _ ≃ (iC.obj X ⟶ R'.obj (iD.obj Y)) := adj.homEquiv _ _
          _ ≃ (iC.obj X ⟶ iC.obj (R.obj Y)) := Iso.homCongr (Iso.refl _) (comm2.app Y)
          _ ≃ (X ⟶ R.obj Y) := (equivOfFullyFaithful iC).symm

      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        apply iD.map_injective
        simpa [Trans.trans] using (comm1.inv.naturality_assoc f _).symm
      homEquiv_naturality_right := fun {X Y' Y} f g => by
        apply iC.map_injective
        suffices R'.map (iD.map g) ≫ comm2.hom.app Y = comm2.hom.app Y' ≫ iC.map (R.map g) by
          simp [Trans.trans, this]
        apply comm2.hom.naturality g }
#align category_theory.adjunction.restrict_fully_faithful CategoryTheory.Adjunction.restrictFullyFaithful

@[simp, reassoc]
lemma map_restrictFullyFaithful_unit_app (X : C) :
    iC.map ((restrictFullyFaithful iC iD adj comm1 comm2).unit.app X) =
    adj.unit.app (iC.obj X) ≫ R'.map (comm1.hom.app X) ≫ comm2.hom.app (L.obj X) := by
  simp [restrictFullyFaithful]

@[simp, reassoc]
lemma map_restrictFullyFaithful_counit_app (X : D) :
    iD.map ((restrictFullyFaithful iC iD adj comm1 comm2).counit.app X) =
    comm1.inv.app (R.obj X) ≫ L'.map (comm2.inv.app X) ≫ adj.counit.app (iD.obj X) := by
  simp only [Functor.comp_obj, Functor.id_obj, restrictFullyFaithful, equivOfFullyFaithful,
    Equiv.instTransSortSortSortEquivEquivEquiv_trans, mkOfHomEquiv_counit_app, Equiv.invFun_as_coe,
    Equiv.symm_trans_apply, Equiv.symm_symm, Iso.homCongr_symm, Iso.refl_symm, Iso.homCongr_apply,
    Iso.refl_inv, Iso.symm_hom, Iso.app_inv, id_comp, homEquiv_counit, Functor.map_comp, assoc,
    Iso.symm_inv, Iso.app_hom, Iso.refl_hom, comp_id, Equiv.coe_fn_symm_mk, Functor.image_preimage,
    NatIso.cancel_natIso_inv_left]
  change L'.map (iC.map (𝟙 _)) ≫ _ = _
  simp

end CategoryTheory.Adjunction
