/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Yoneda

#align_import category_theory.adjunction.fully_faithful from "leanprover-community/mathlib"@"9e7c80f638149bfb3504ba8ff48dfdbfc949fb1a"

/-!
# Adjoints of fully faithful functors

A left adjoint is
* faithful, if and only if the unit is a monomorphism
* full, if and only if the unit is a split epimorphism
* fully faithful, if and only if the unit is an isomorphism

A right adjoint is
* faithful, if and only if the counit is an epimorphism
* full, if and only if the counit is a split monomorphism
* fully faithful, if and only if the counit is an isomorphism

This is Lemma 4.5.13 in Riehl's *Category Theory in Context* [riehl2017].
See also https://stacks.math.columbia.edu/tag/07RB for the statements about fully faithful functors.

In the file `Mathlib.CategoryTheory.Monad.Adjunction`, we prove that in fact, if there exists an isomorphism `L ⋙ R ≅ 𝟭 C`, then the unit is an isomorphism, and similarly for the counit.
-/


open CategoryTheory

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂

open Category

open Opposite

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)

/-- If the left adjoint is faithful, then each component of the unit is an monomorphism. -/
instance unit_mono_of_L_faithful [L.Faithful] (X : C) : Mono (h.unit.app X) where
  right_cancellation {Y} f g hfg := by
    apply L.map_injective
    apply (h.homEquiv Y (L.obj X)).injective
    simpa using hfg

/-- If the left adjoint is full, then each component of the unit is a split epimorphism.-/
noncomputable def unitSplitEpiOfLFull [L.Full] (X : C) : SplitEpi (h.unit.app X) where
  section_ := L.preimage (h.counit.app (L.obj X))
  id := by simp [← h.unit_naturality (L.preimage (h.counit.app (L.obj X)))]

/-- If the right adjoint is full, then each component of the counit is a split monomorphism. -/
instance unit_isSplitEpi_of_L_full [L.Full] (X : C) : IsSplitEpi (h.unit.app X) :=
  ⟨⟨h.unitSplitEpiOfLFull X⟩⟩

/-- If the left adjoint is fully faithful, then the unit is an isomorphism. -/
instance unit_isIso_of_L_fully_faithful [L.Full] [L.Faithful] : IsIso (Adjunction.unit h) := by
  have : ∀ X, IsIso (h.unit.app X) := fun X ↦ isIso_of_mono_of_isSplitEpi _
  apply NatIso.isIso_of_isIso_app
set_option linter.uppercaseLean3 false in
#align category_theory.unit_is_iso_of_L_fully_faithful CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful

/-- If the right adjoint is faithful, then each component of the counit is an epimorphism.-/
instance counit_epi_of_R_faithful [R.Faithful] (X : D) : Epi (h.counit.app X) where
  left_cancellation {Y} f g hfg := by
    apply R.map_injective
    apply (h.homEquiv (R.obj X) Y).symm.injective
    simpa using hfg

/-- If the right adjoint is full, then each component of the counit is a split monomorphism. -/
noncomputable def counitSplitMonoOfRFull [R.Full] (X : D) : SplitMono (h.counit.app X) where
  retraction := R.preimage (h.unit.app (R.obj X))
  id := by simp [← h.counit_naturality (R.preimage (h.unit.app (R.obj X)))]

/-- If the right adjoint is full, then each component of the counit is a split monomorphism. -/
instance counit_isSplitMono_of_R_full [R.Full] (X : D) : IsSplitMono (h.counit.app X) :=
  ⟨⟨h.counitSplitMonoOfRFull X⟩⟩

/-- If the right adjoint is fully faithful, then the counit is an isomorphism. -/
instance counit_isIso_of_R_fully_faithful [R.Full] [R.Faithful] : IsIso (Adjunction.counit h) := by
  have : ∀ X, IsIso (h.counit.app X) := fun X ↦ isIso_of_epi_of_isSplitMono _
  apply NatIso.isIso_of_isIso_app
set_option linter.uppercaseLean3 false in
#align category_theory.counit_is_iso_of_R_fully_faithful CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful

/-- If the unit of an adjunction is an isomorphism, then its inverse on the image of L is given
by L whiskered with the counit. -/
@[simp]
theorem inv_map_unit {X : C} [IsIso (h.unit.app X)] :
    inv (L.map (h.unit.app X)) = h.counit.app (L.obj X) :=
  IsIso.inv_eq_of_hom_inv_id (h.left_triangle_components X)
#align category_theory.inv_map_unit CategoryTheory.Adjunction.inv_map_unit

/-- If the unit is an isomorphism, bundle one has an isomorphism `L ⋙ R ⋙ L ≅ L`. -/
@[simps!]
noncomputable def whiskerLeftLCounitIsoOfIsIsoUnit [IsIso h.unit] : L ⋙ R ⋙ L ≅ L :=
  (L.associator R L).symm ≪≫ isoWhiskerRight (asIso h.unit).symm L ≪≫ Functor.leftUnitor _
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_left_L_counit_iso_of_is_iso_unit CategoryTheory.Adjunction.whiskerLeftLCounitIsoOfIsIsoUnit

/-- If the counit of an adjunction is an isomorphism, then its inverse on the image of R is given
by R whiskered with the unit. -/
@[simp]
theorem inv_counit_map {X : D} [IsIso (h.counit.app X)] :
    inv (R.map (h.counit.app X)) = h.unit.app (R.obj X) :=
  IsIso.inv_eq_of_inv_hom_id (h.right_triangle_components X)
#align category_theory.inv_counit_map CategoryTheory.Adjunction.inv_counit_map

/-- If the counit of an is an isomorphism, one has an isomorphism `(R ⋙ L ⋙ R) ≅ R`. -/
@[simps!]
noncomputable def whiskerLeftRUnitIsoOfIsIsoCounit [IsIso h.counit] : R ⋙ L ⋙ R ≅ R :=
  (R.associator L R).symm ≪≫ isoWhiskerRight (asIso h.counit) R ≪≫ Functor.leftUnitor _
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_left_R_unit_iso_of_is_iso_counit CategoryTheory.Adjunction.whiskerLeftRUnitIsoOfIsIsoCounit

/-- If each component the unit is a monomorphism, then the left adjoint is faithful. -/
lemma faithful_L_of_mono_unit_app [∀ X, Mono (h.unit.app X)] : L.Faithful where
  map_injective {X Y f g} hfg := by
    apply Mono.right_cancellation (f := h.unit.app Y)
    apply (h.homEquiv X (L.obj Y)).symm.injective
    simpa using hfg

/-- If each component the unit is a split epimorphism, then the left adjoint is full. -/
lemma full_L_of_isSplitEpi_unit_app [∀ X, IsSplitEpi (h.unit.app X)] : L.Full where
  map_surjective {X Y} f := by
    use ((h.homEquiv X (L.obj Y)) f ≫ section_ (h.unit.app Y))
    have h' : L.map (section_ (h.unit.app Y)) ≫ L.map (h.unit.app Y) = 𝟙 _ :=
      by simp [← Functor.map_comp]
    have : L.map (section_ (h.unit.app Y)) = h.counit.app (L.obj Y) := by
      rw [← comp_id (L.map (section_ (h.unit.app Y)))]
      simp only [Functor.comp_obj, Functor.id_obj, comp_id,
        ← h.left_triangle_components Y, ← assoc, h', id_comp]
    simp [this]

/-- If the unit is an isomorphism, then the left adjoint is fully faithful. -/
noncomputable def fullyFaithfulLOfIsIsoUnit [IsIso h.unit] : L.FullyFaithful where
  preimage {X Y} f := h.homEquiv _ (L.obj Y) f ≫ inv (h.unit.app Y)

/-- If each component the counit is an epimorphism, then the right adjoint is faithful. -/
lemma faithful_R_of_epi_counit_app [∀ X, Epi (h.counit.app X)] : R.Faithful where
  map_injective {X Y f g} hfg := by
    apply Epi.left_cancellation (f := h.counit.app X)
    apply (h.homEquiv (R.obj X) Y).injective
    simpa using hfg

/-- If each component the counit is a split monomorphism, then the right adjoint is full. -/
lemma full_R_of_isSplitMono_counit_app [∀ X, IsSplitMono (h.counit.app X)] : R.Full where
  map_surjective {X Y} f := by
    use (retraction (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f)
    have h' : R.map (h.counit.app X) ≫ R.map (retraction (h.counit.app X)) = 𝟙 _ :=
      by simp [← Functor.map_comp]
    have : R.map (retraction (h.counit.app X)) = h.unit.app (R.obj X) := by
      rw [← id_comp (R.map (retraction (h.counit.app X)))]
      simp only [Functor.id_obj, Functor.comp_obj, id_comp,
        ← h.right_triangle_components X, assoc, h', comp_id]
    simp [this]

/-- If the counit is an isomorphism, then the right adjoint is fully faithful. -/
noncomputable def fullyFaithfulROfIsIsoCounit [IsIso h.counit] : R.FullyFaithful where
  preimage {X Y} f := inv (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f

instance whiskerLeft_counit_iso_of_L_fully_faithful [L.Full] [L.Faithful] :
    IsIso (whiskerLeft L h.counit) := by
  have := h.left_triangle
  rw [← IsIso.eq_inv_comp] at this
  rw [this]
  infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_left_counit_iso_of_L_fully_faithful CategoryTheory.Adjunction.whiskerLeft_counit_iso_of_L_fully_faithful

instance whiskerRight_counit_iso_of_L_fully_faithful [L.Full] [L.Faithful] :
    IsIso (whiskerRight h.counit R) := by
  have := h.right_triangle
  rw [← IsIso.eq_inv_comp] at this
  rw [this]
  infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_right_counit_iso_of_L_fully_faithful CategoryTheory.Adjunction.whiskerRight_counit_iso_of_L_fully_faithful

instance whiskerLeft_unit_iso_of_R_fully_faithful [R.Full] [R.Faithful] :
    IsIso (whiskerLeft R h.unit) := by
  have := h.right_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_left_unit_iso_of_R_fully_faithful CategoryTheory.Adjunction.whiskerLeft_unit_iso_of_R_fully_faithful

instance whiskerRight_unit_iso_of_R_fully_faithful [R.Full] [R.Faithful] :
    IsIso (whiskerRight h.unit L) := by
  have := h.left_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.whisker_right_unit_iso_of_R_fully_faithful CategoryTheory.Adjunction.whiskerRight_unit_iso_of_R_fully_faithful

instance [L.Faithful] [L.Full] {Y : C} : IsIso (h.counit.app (L.obj Y)) :=
  isIso_of_hom_comp_eq_id _ (h.left_triangle_components Y)

instance [L.Faithful] [L.Full] {Y : D} : IsIso (R.map (h.counit.app Y)) :=
  isIso_of_hom_comp_eq_id _ (h.right_triangle_components Y)

lemma isIso_counit_app_iff_mem_essImage [L.Faithful] [L.Full] {X : D} :
    IsIso (h.counit.app X) ↔ X ∈ L.essImage := by
  constructor
  · intro
    exact ⟨R.obj X, ⟨asIso (h.counit.app X)⟩⟩
  · rintro ⟨_, ⟨i⟩⟩
    rw [NatTrans.isIso_app_iff_of_iso _ i.symm]
    infer_instance

lemma mem_essImage_of_counit_isIso (A : D)
    [IsIso (h.counit.app A)] : A ∈ L.essImage :=
  ⟨R.obj A, ⟨asIso (h.counit.app A)⟩⟩

lemma isIso_counit_app_of_iso [L.Faithful] [L.Full] {X : D} {Y : C} (e : X ≅ L.obj Y) :
    IsIso (h.counit.app X) :=
  (isIso_counit_app_iff_mem_essImage h).mpr ⟨Y, ⟨e.symm⟩⟩

instance [R.Faithful] [R.Full] {Y : D} : IsIso (h.unit.app (R.obj Y)) :=
  isIso_of_comp_hom_eq_id _ (h.right_triangle_components Y)

instance [R.Faithful] [R.Full] {X : C} : IsIso (L.map (h.unit.app X)) :=
  isIso_of_comp_hom_eq_id _ (h.left_triangle_components X)

lemma isIso_unit_app_iff_mem_essImage [R.Faithful] [R.Full] {Y : C} :
    IsIso (h.unit.app Y) ↔ Y ∈ R.essImage := by
  constructor
  · intro
    exact ⟨L.obj Y, ⟨(asIso (h.unit.app Y)).symm⟩⟩
  · rintro ⟨_, ⟨i⟩⟩
    rw [NatTrans.isIso_app_iff_of_iso _ i.symm]
    infer_instance

/-- If `η_A` is an isomorphism, then `A` is in the essential image of `i`. -/
theorem mem_essImage_of_unit_isIso (A : C)
    [IsIso (h.unit.app A)] : A ∈ R.essImage :=
  ⟨L.obj A, ⟨(asIso (h.unit.app A)).symm⟩⟩
#align category_theory.mem_ess_image_of_unit_is_iso CategoryTheory.Adjunction.mem_essImage_of_unit_isIso

@[deprecated (since := "2024-06-19")] alias _root_.CategoryTheory.mem_essImage_of_unit_isIso :=
  mem_essImage_of_unit_isIso

lemma isIso_unit_app_of_iso [R.Faithful] [R.Full] {X : D} {Y : C} (e : Y ≅ R.obj X) :
    IsIso (h.unit.app Y) :=
  (isIso_unit_app_iff_mem_essImage h).mpr ⟨X, ⟨e.symm⟩⟩

instance [R.IsEquivalence] : IsIso h.unit := by
  have := fun Y => isIso_unit_app_of_iso h (R.objObjPreimageIso Y).symm
  apply NatIso.isIso_of_isIso_app

instance [L.IsEquivalence] : IsIso h.counit := by
  have := fun X => isIso_counit_app_of_iso h (L.objObjPreimageIso X).symm
  apply NatIso.isIso_of_isIso_app

lemma isEquivalence_left_of_isEquivalence_right [R.IsEquivalence] : L.IsEquivalence :=
  h.toEquivalence.isEquivalence_functor

lemma isEquivalence_right_of_isEquivalence_left [L.IsEquivalence] : R.IsEquivalence :=
  h.toEquivalence.isEquivalence_inverse

instance [L.IsEquivalence] : IsIso h.unit := by
  have := h.isEquivalence_right_of_isEquivalence_left
  infer_instance

instance [R.IsEquivalence] : IsIso h.counit := by
  have := h.isEquivalence_left_of_isEquivalence_right
  infer_instance

end CategoryTheory.Adjunction
