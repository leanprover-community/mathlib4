/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Yoneda

#align_import category_theory.adjunction.fully_faithful from "leanprover-community/mathlib"@"9e7c80f638149bfb3504ba8ff48dfdbfc949fb1a"

/-!
# Adjoints of fully faithful functors

A left adjoint is fully faithful, if and only if the unit is an isomorphism
(and similarly for right adjoints and the counit).

`Adjunction.restrictFullyFaithful` shows that an adjunction can be restricted along fully faithful
inclusions.

## Future work

The statements from Riehl 4.5.13 for adjoints which are either full, or faithful.
-/


open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

open Category

open Opposite

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)

/-- If the left adjoint is fully faithful, then the unit is an isomorphism.

See
* Lemma 4.5.13 from [Riehl][riehl2017]
* https://math.stackexchange.com/a/2727177
* https://stacks.math.columbia.edu/tag/07RB (we only prove the forward direction!)
-/
instance unit_isIso_of_L_fully_faithful [Full L] [Faithful L] : IsIso (Adjunction.unit h) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (Adjunction.unit h) fun X =>
    @Yoneda.isIso _ _ _ _ ((Adjunction.unit h).app X)
      ⟨⟨{ app := fun Y f => L.preimage ((h.homEquiv (unop Y) (L.obj X)).symm f) },
          ⟨by
            ext x
            apply L.map_injective
            aesop_cat,
           by
            ext x
            dsimp
            simp only [Adjunction.homEquiv_counit, preimage_comp, preimage_map, Category.assoc]
            rw [← h.unit_naturality]
            simp⟩⟩⟩
set_option linter.uppercaseLean3 false in
#align category_theory.unit_is_iso_of_L_fully_faithful CategoryTheory.unit_isIso_of_L_fully_faithful

/-- If the right adjoint is fully faithful, then the counit is an isomorphism.

See <https://stacks.math.columbia.edu/tag/07RB> (we only prove the forward direction!)
-/
instance counit_isIso_of_R_fully_faithful [Full R] [Faithful R] : IsIso (Adjunction.counit h) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (Adjunction.counit h) fun X =>
    @isIso_of_op _ _ _ _ _ <|
      @Coyoneda.isIso _ _ _ _ ((Adjunction.counit h).app X).op
        ⟨⟨{ app := fun Y f => R.preimage ((h.homEquiv (R.obj X) Y) f) },
            ⟨by
              ext x
              apply R.map_injective
              simp,
             by
              ext x
              dsimp
              simp only [Adjunction.homEquiv_unit, preimage_comp, preimage_map]
              rw [← h.counit_naturality]
              simp⟩⟩⟩
set_option linter.uppercaseLean3 false in
#align category_theory.counit_is_iso_of_R_fully_faithful CategoryTheory.counit_isIso_of_R_fully_faithful

/-- If the unit of an adjunction is an isomorphism, then its inverse on the image of L is given
by L whiskered with the counit. -/
@[simp]
theorem inv_map_unit {X : C} [IsIso (h.unit.app X)] :
    inv (L.map (h.unit.app X)) = h.counit.app (L.obj X) :=
  IsIso.inv_eq_of_hom_inv_id h.left_triangle_components
#align category_theory.inv_map_unit CategoryTheory.inv_map_unit

/-- If the unit is an isomorphism, bundle one has an isomorphism `L ⋙ R ⋙ L ≅ L`. -/
@[simps!]
noncomputable def whiskerLeftLCounitIsoOfIsIsoUnit [IsIso h.unit] : L ⋙ R ⋙ L ≅ L :=
  (L.associator R L).symm ≪≫ isoWhiskerRight (asIso h.unit).symm L ≪≫ Functor.leftUnitor _
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_left_L_counit_iso_of_is_iso_unit CategoryTheory.whiskerLeftLCounitIsoOfIsIsoUnit

/-- If the counit of an adjunction is an isomorphism, then its inverse on the image of R is given
by R whiskered with the unit. -/
@[simp]
theorem inv_counit_map {X : D} [IsIso (h.counit.app X)] :
    inv (R.map (h.counit.app X)) = h.unit.app (R.obj X) :=
  IsIso.inv_eq_of_inv_hom_id h.right_triangle_components
#align category_theory.inv_counit_map CategoryTheory.inv_counit_map

/-- If the counit of an is an isomorphism, one has an isomorphism `(R ⋙ L ⋙ R) ≅ R`. -/
@[simps!]
noncomputable def whiskerLeftRUnitIsoOfIsIsoCounit [IsIso h.counit] : R ⋙ L ⋙ R ≅ R :=
  (R.associator L R).symm ≪≫ isoWhiskerRight (asIso h.counit) R ≪≫ Functor.leftUnitor _
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_left_R_unit_iso_of_is_iso_counit CategoryTheory.whiskerLeftRUnitIsoOfIsIsoCounit

/-- If the unit is an isomorphism, then the left adjoint is full-/
noncomputable def lFullOfUnitIsIso [IsIso h.unit] : Full L
    where preimage {X Y} f := h.homEquiv _ (L.obj Y) f ≫ inv (h.unit.app Y)
set_option linter.uppercaseLean3 false in
#align category_theory.L_full_of_unit_is_iso CategoryTheory.lFullOfUnitIsIso

/-- If the unit is an isomorphism, then the left adjoint is faithful-/
theorem L_faithful_of_unit_isIso [IsIso h.unit] : Faithful L :=
  ⟨fun {X Y f g} H => by
    rw [← (h.homEquiv X (L.obj Y)).apply_eq_iff_eq] at H
    simpa using H =≫ inv (h.unit.app Y)⟩
set_option linter.uppercaseLean3 false in
#align category_theory.L_faithful_of_unit_is_iso CategoryTheory.L_faithful_of_unit_isIso

/-- If the counit is an isomorphism, then the right adjoint is full-/
noncomputable def rFullOfCounitIsIso [IsIso h.counit] : Full R
    where preimage {X Y} f := inv (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f
set_option linter.uppercaseLean3 false in
#align category_theory.R_full_of_counit_is_iso CategoryTheory.rFullOfCounitIsIso

/-- If the counit is an isomorphism, then the right adjoint is faithful-/
theorem R_faithful_of_counit_isIso [IsIso h.counit] : Faithful R :=
  ⟨fun {X Y f g} H => by
    rw [← (h.homEquiv (R.obj X) Y).symm.apply_eq_iff_eq] at H
    simpa using inv (h.counit.app X) ≫= H⟩
set_option linter.uppercaseLean3 false in
#align category_theory.R_faithful_of_counit_is_iso CategoryTheory.R_faithful_of_counit_isIso

instance whiskerLeft_counit_iso_of_L_fully_faithful [Full L] [Faithful L] :
    IsIso (whiskerLeft L h.counit) := by
  have := h.left_triangle
  rw [← IsIso.eq_inv_comp] at this
  rw [this]
  infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_left_counit_iso_of_L_fully_faithful CategoryTheory.whiskerLeft_counit_iso_of_L_fully_faithful

instance whiskerRight_counit_iso_of_L_fully_faithful [Full L] [Faithful L] :
    IsIso (whiskerRight h.counit R) := by
  have := h.right_triangle
  rw [← IsIso.eq_inv_comp] at this
  rw [this]
  infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_right_counit_iso_of_L_fully_faithful CategoryTheory.whiskerRight_counit_iso_of_L_fully_faithful

instance whiskerLeft_unit_iso_of_R_fully_faithful [Full R] [Faithful R] :
    IsIso (whiskerLeft R h.unit) := by
  have := h.right_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_left_unit_iso_of_R_fully_faithful CategoryTheory.whiskerLeft_unit_iso_of_R_fully_faithful

instance whiskerRight_unit_iso_of_R_fully_faithful [Full R] [Faithful R] :
    IsIso (whiskerRight h.unit L) := by
  have := h.left_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_right_unit_iso_of_R_fully_faithful CategoryTheory.whiskerRight_unit_iso_of_R_fully_faithful

-- TODO also do the statements from Riehl 4.5.13 for full and faithful separately?
universe v₃ v₄ u₃ u₄

variable {C' : Type u₃} [Category.{v₃} C']

variable {D' : Type u₄} [Category.{v₄} D']

-- TODO: This needs some lemmas describing the produced adjunction, probably in terms of `adj`,
-- `iC` and `iD`.
/-- If `C` is a full subcategory of `C'` and `D` is a full subcategory of `D'`, then we can restrict
an adjunction `L' ⊣ R'` where `L' : C' ⥤ D'` and `R' : D' ⥤ C'` to `C` and `D`.
The construction here is slightly more general, in that `C` is required only to have a full and
faithful "inclusion" functor `iC : C ⥤ C'` (and similarly `iD : D ⥤ D'`) which commute (up to
natural isomorphism) with the proposed restrictions.
-/
def Adjunction.restrictFullyFaithful (iC : C ⥤ C') (iD : D ⥤ D') {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L' ⊣ R') {L : C ⥤ D} {R : D ⥤ C} (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC)
    [Full iC] [Faithful iC] [Full iD] [Faithful iD] : L ⊣ R :=
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

end CategoryTheory
