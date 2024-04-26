/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Yoneda

#align_import category_theory.adjunction.fully_faithful from "leanprover-community/mathlib"@"9e7c80f638149bfb3504ba8ff48dfdbfc949fb1a"

/-!
# Adjoints of fully faithful functors

A left adjoint is fully faithful, if and only if the unit is an isomorphism
(and similarly for right adjoints and the counit).

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
instance unit_isIso_of_L_fully_faithful [L.Full] [L.Faithful] : IsIso (Adjunction.unit h) :=
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
            simp only [Adjunction.homEquiv_counit, Functor.preimage_comp,
              Functor.preimage_map, Category.assoc]
            rw [← h.unit_naturality]
            simp⟩⟩⟩
set_option linter.uppercaseLean3 false in
#align category_theory.unit_is_iso_of_L_fully_faithful CategoryTheory.unit_isIso_of_L_fully_faithful

/-- If the right adjoint is fully faithful, then the counit is an isomorphism.

See <https://stacks.math.columbia.edu/tag/07RB> (we only prove the forward direction!)
-/
instance counit_isIso_of_R_fully_faithful [R.Full] [R.Faithful] : IsIso (Adjunction.counit h) :=
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
              simp only [Adjunction.homEquiv_unit, Functor.preimage_comp, Functor.preimage_map]
              rw [← h.counit_naturality]
              simp⟩⟩⟩
set_option linter.uppercaseLean3 false in
#align category_theory.counit_is_iso_of_R_fully_faithful CategoryTheory.counit_isIso_of_R_fully_faithful

/-- If the unit of an adjunction is an isomorphism, then its inverse on the image of L is given
by L whiskered with the counit. -/
@[simp]
theorem inv_map_unit {X : C} [IsIso (h.unit.app X)] :
    inv (L.map (h.unit.app X)) = h.counit.app (L.obj X) :=
  IsIso.inv_eq_of_hom_inv_id (h.left_triangle_components X)
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
  IsIso.inv_eq_of_inv_hom_id (h.right_triangle_components X)
#align category_theory.inv_counit_map CategoryTheory.inv_counit_map

/-- If the counit of an is an isomorphism, one has an isomorphism `(R ⋙ L ⋙ R) ≅ R`. -/
@[simps!]
noncomputable def whiskerLeftRUnitIsoOfIsIsoCounit [IsIso h.counit] : R ⋙ L ⋙ R ≅ R :=
  (R.associator L R).symm ≪≫ isoWhiskerRight (asIso h.counit) R ≪≫ Functor.leftUnitor _
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_left_R_unit_iso_of_is_iso_counit CategoryTheory.whiskerLeftRUnitIsoOfIsIsoCounit

/-- If the unit is an isomorphism, then the left adjoint is full-/
noncomputable def lFullOfUnitIsIso [IsIso h.unit] : L.Full where
  preimage {X Y} f := h.homEquiv _ (L.obj Y) f ≫ inv (h.unit.app Y)
set_option linter.uppercaseLean3 false in
#align category_theory.L_full_of_unit_is_iso CategoryTheory.lFullOfUnitIsIso

/-- If the unit is an isomorphism, then the left adjoint is faithful-/
theorem L_faithful_of_unit_isIso [IsIso h.unit] : L.Faithful :=
  ⟨fun {X Y f g} H => by
    rw [← (h.homEquiv X (L.obj Y)).apply_eq_iff_eq] at H
    simpa using H =≫ inv (h.unit.app Y)⟩
set_option linter.uppercaseLean3 false in
#align category_theory.L_faithful_of_unit_is_iso CategoryTheory.L_faithful_of_unit_isIso

/-- If the counit is an isomorphism, then the right adjoint is full-/
noncomputable def rFullOfCounitIsIso [IsIso h.counit] : R.Full where
  preimage {X Y} f := inv (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f
set_option linter.uppercaseLean3 false in
#align category_theory.R_full_of_counit_is_iso CategoryTheory.rFullOfCounitIsIso

/-- If the counit is an isomorphism, then the right adjoint is faithful-/
theorem R_faithful_of_counit_isIso [IsIso h.counit] : R.Faithful :=
  ⟨fun {X Y f g} H => by
    rw [← (h.homEquiv (R.obj X) Y).symm.apply_eq_iff_eq] at H
    simpa using inv (h.counit.app X) ≫= H⟩
set_option linter.uppercaseLean3 false in
#align category_theory.R_faithful_of_counit_is_iso CategoryTheory.R_faithful_of_counit_isIso

instance whiskerLeft_counit_iso_of_L_fully_faithful [L.Full] [L.Faithful] :
    IsIso (whiskerLeft L h.counit) := by
  have := h.left_triangle
  rw [← IsIso.eq_inv_comp] at this
  rw [this]
  infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_left_counit_iso_of_L_fully_faithful CategoryTheory.whiskerLeft_counit_iso_of_L_fully_faithful

instance whiskerRight_counit_iso_of_L_fully_faithful [L.Full] [L.Faithful] :
    IsIso (whiskerRight h.counit R) := by
  have := h.right_triangle
  rw [← IsIso.eq_inv_comp] at this
  rw [this]
  infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_right_counit_iso_of_L_fully_faithful CategoryTheory.whiskerRight_counit_iso_of_L_fully_faithful

instance whiskerLeft_unit_iso_of_R_fully_faithful [R.Full] [R.Faithful] :
    IsIso (whiskerLeft R h.unit) := by
  have := h.right_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_left_unit_iso_of_R_fully_faithful CategoryTheory.whiskerLeft_unit_iso_of_R_fully_faithful

instance whiskerRight_unit_iso_of_R_fully_faithful [R.Full] [R.Faithful] :
    IsIso (whiskerRight h.unit L) := by
  have := h.left_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_right_unit_iso_of_R_fully_faithful CategoryTheory.whiskerRight_unit_iso_of_R_fully_faithful

instance [L.Faithful] [L.Full] {Y : C} : IsIso (h.counit.app (L.obj Y)) :=
  isIso_of_hom_comp_eq_id _ (h.left_triangle_components Y)

lemma isIso_counit_app_iff_mem_essImage [L.Faithful] [L.Full] {X : D} :
    IsIso (h.counit.app X) ↔ X ∈ L.essImage := by
  constructor
  · intro
    exact ⟨R.obj X, ⟨asIso (h.counit.app X)⟩⟩
  · rintro ⟨_, ⟨i⟩⟩
    rw [NatTrans.isIso_app_iff_of_iso _ i.symm]
    infer_instance

lemma isIso_counit_app_of_iso [L.Faithful] [L.Full] {X : D} {Y : C} (e : X ≅ L.obj Y) :
    IsIso (h.counit.app X) :=
  (isIso_counit_app_iff_mem_essImage h).mpr ⟨Y, ⟨e.symm⟩⟩

instance [R.Faithful] [R.Full] {Y : D} : IsIso (h.unit.app (R.obj Y)) :=
  isIso_of_comp_hom_eq_id _ (h.right_triangle_components Y)

lemma isIso_unit_app_iff_mem_essImage [R.Faithful] [R.Full] {Y : C} :
    IsIso (h.unit.app Y) ↔ Y ∈ R.essImage := by
  constructor
  · intro
    exact ⟨L.obj Y, ⟨(asIso (h.unit.app Y)).symm⟩⟩
  · rintro ⟨_, ⟨i⟩⟩
    rw [NatTrans.isIso_app_iff_of_iso _ i.symm]
    infer_instance

lemma isIso_unit_app_of_iso [R.Faithful] [R.Full] {X : D} {Y : C} (e : Y ≅ R.obj X) :
    IsIso (h.unit.app Y) :=
  (isIso_unit_app_iff_mem_essImage h).mpr ⟨X, ⟨e.symm⟩⟩

end CategoryTheory
