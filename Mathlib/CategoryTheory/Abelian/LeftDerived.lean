/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Adam Topaz

! This file was ported from Lean 3 source module category_theory.abelian.left_derived
! leanprover-community/mathlib commit 8001ea54ece3bd5c0d0932f1e4f6d0f142ea20d9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Abelian.Homology
import Mathlib.CategoryTheory.Functor.LeftDerived
import Mathlib.CategoryTheory.Abelian.Projective
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Zeroth left derived functors

If `F : C ⥤ D` is an additive right exact functor between abelian categories, where `C` has enough
projectives, we provide the natural isomorphism `F.left_derived 0 ≅ F`.

## Main definitions

* `category_theory.abelian.functor.left_derived_zero_iso_self`: the natural isomorphism
  `(F.left_derived 0) ≅ F`.

## Main results
* `preserves_exact_of_preserves_finite_colimits_of_epi`: if `preserves_finite_colimits F` and
  `epi g`, then `exact (F.map f) (F.map g)` if `exact f g`.

-/


noncomputable section

universe w v u

open CategoryTheory.Limits CategoryTheory CategoryTheory.Functor

variable {C : Type u} [Category.{w} C] {D : Type u} [Category.{w} D]

variable (F : C ⥤ D) {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}

namespace CategoryTheory.Abelian.Functor

open CategoryTheory.Preadditive

variable [Abelian C] [Abelian D] [Additive F]

/-- If `preserves_finite_colimits F` and `epi g`, then `exact (F.map f) (F.map g)` if
`exact f g`. -/
theorem preserves_exact_of_preservesFiniteColimits_of_epi [PreservesFiniteColimits F] [Epi g]
    (ex : Exact f g) : Exact (F.map f) (F.map g) :=
  Abelian.exact_of_is_cokernel _ _ (by simp [← functor.map_comp, ex.w]) <|
    Limits.isColimitCoforkMapOfIsColimit' _ ex.w (Abelian.isColimitOfExactOfEpi _ _ ex)
#align category_theory.abelian.functor.preserves_exact_of_preserves_finite_colimits_of_epi CategoryTheory.Abelian.Functor.preserves_exact_of_preservesFiniteColimits_of_epi

theorem exact_of_map_projective_resolution (P : ProjectiveResolution X)
    [PreservesFiniteColimits F] :
    Exact (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).dTo 0)
      (F.map (P.π.f 0)) :=
  Preadditive.exact_of_iso_of_exact' (F.map (P.complex.d 1 0)) (F.map (P.π.f 0)) _ _
    (HomologicalComplex.xPrevIso ((F.mapHomologicalComplex _).obj P.complex) rfl).symm (Iso.refl _)
    (Iso.refl _) (by simp) (by simp) (preserves_exact_of_preservesFiniteColimits_of_epi _ P.exact₀)
#align category_theory.abelian.functor.exact_of_map_projective_resolution CategoryTheory.Abelian.Functor.exact_of_map_projective_resolution

/-- Given `P : ProjectiveResolution X`, a morphism `(F.left_derived 0).obj X ⟶ F.obj X`. -/
@[nolint unused_arguments]
def leftDerivedZeroToSelfApp [EnoughProjectives C] {X : C} (P : ProjectiveResolution X) :
    (F.leftDerived 0).obj X ⟶ F.obj X :=
  (leftDerivedObjIso F 0 P).Hom ≫
    homology.desc' _ _ _ (kernel.ι _ ≫ F.map (P.π.f 0))
      (by
        rw [kernel.lift_ι_assoc,
          HomologicalComplex.dTo_eq _ (by simp : (ComplexShape.down ℕ).Rel 1 0),
          map_homological_complex_obj_d, category.assoc, ← functor.map_comp]
        simp)
#align category_theory.abelian.functor.left_derived_zero_to_self_app CategoryTheory.Abelian.Functor.leftDerivedZeroToSelfApp

/-- Given `P : ProjectiveResolution X`, a morphism `F.obj X ⟶ (F.left_derived 0).obj X` given
`preserves_finite_colimits F`. -/
def leftDerivedZeroToSelfAppInv [EnoughProjectives C] [PreservesFiniteColimits F] {X : C}
    (P : ProjectiveResolution X) : F.obj X ⟶ (F.leftDerived 0).obj X := by
  refine'
    (as_iso (cokernel.desc _ _ (exact_of_map_projective_resolution F P).w)).inv ≫
      _ ≫ (homologyIsoCokernelLift _ _ _).inv ≫ (left_derived_obj_iso F 0 P).inv
  exact cokernel.map _ _ (𝟙 _) (kernel.lift _ (𝟙 _) (by simp)) (by ext; simp)
#align category_theory.abelian.functor.left_derived_zero_to_self_app_inv CategoryTheory.Abelian.Functor.leftDerivedZeroToSelfAppInv

theorem leftDerivedZeroToSelfApp_comp_inv [EnoughProjectives C] [PreservesFiniteColimits F] {X : C}
    (P : ProjectiveResolution X) :
    leftDerivedZeroToSelfApp F P ≫ leftDerivedZeroToSelfAppInv F P = 𝟙 _ := by
  dsimp [left_derived_zero_to_self_app, left_derived_zero_to_self_app_inv]
  rw [← category.assoc, ← category.assoc, ← category.assoc, iso.comp_inv_eq, category.id_comp,
    category.assoc, category.assoc, category.assoc]
  convert category.comp_id _
  rw [← category.assoc, ← category.assoc, iso.comp_inv_eq, category.id_comp]
  ext
  rw [← category.assoc, ← category.assoc, homology.π'_desc', category.assoc, category.assoc, ←
    category.assoc (F.map _), abelian.cokernel.desc.inv, cokernel.π_desc, homology.π',
    category.assoc, iso.inv_hom_id, category.comp_id, ← category.assoc]
  convert category.id_comp _ using 2
  ext
  rw [category.id_comp, category.assoc, equalizer_as_kernel, kernel.lift_ι, category.comp_id]
#align category_theory.abelian.functor.left_derived_zero_to_self_app_comp_inv CategoryTheory.Abelian.Functor.leftDerivedZeroToSelfApp_comp_inv

theorem leftDerivedZeroToSelfAppInv_comp [EnoughProjectives C] [PreservesFiniteColimits F] {X : C}
    (P : ProjectiveResolution X) :
    leftDerivedZeroToSelfAppInv F P ≫ leftDerivedZeroToSelfApp F P = 𝟙 _ := by
  dsimp [left_derived_zero_to_self_app, left_derived_zero_to_self_app_inv]
  rw [category.assoc, category.assoc, category.assoc, ←
    category.assoc (F.left_derived_obj_iso 0 P).inv, iso.inv_hom_id, category.id_comp,
    is_iso.inv_comp_eq, category.comp_id]
  ext
  simp only [cokernel.π_desc_assoc, category.assoc, cokernel.π_desc, homology.desc']
  rw [← category.assoc, ← category.assoc (homologyIsoCokernelLift _ _ _).inv, iso.inv_hom_id,
    category.id_comp]
  simp only [category.assoc, cokernel.π_desc, kernel.lift_ι_assoc, category.id_comp]
#align category_theory.abelian.functor.left_derived_zero_to_self_app_inv_comp CategoryTheory.Abelian.Functor.leftDerivedZeroToSelfAppInv_comp

/-- Given `P : ProjectiveResolution X`, the isomorphism `(F.left_derived 0).obj X ≅ F.obj X` if
`preserves_finite_colimits F`. -/
def leftDerivedZeroToSelfAppIso [EnoughProjectives C] [PreservesFiniteColimits F] {X : C}
    (P : ProjectiveResolution X) : (F.leftDerived 0).obj X ≅ F.obj X where
  Hom := leftDerivedZeroToSelfApp _ P
  inv := leftDerivedZeroToSelfAppInv _ P
  hom_inv_id' := leftDerivedZeroToSelfApp_comp_inv _ P
  inv_hom_id' := leftDerivedZeroToSelfAppInv_comp _ P
#align category_theory.abelian.functor.left_derived_zero_to_self_app_iso CategoryTheory.Abelian.Functor.leftDerivedZeroToSelfAppIso

/-- Given `P : ProjectiveResolution X` and `Q : ProjectiveResolution Y` and a morphism `f : X ⟶ Y`,
naturality of the square given by `left_derived_zero_to_self_obj_hom. -/
theorem leftDerived_zero_to_self_natural [EnoughProjectives C] {X : C} {Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
    (F.leftDerived 0).map f ≫ leftDerivedZeroToSelfApp F Q =
      leftDerivedZeroToSelfApp F P ≫ F.map f := by
  dsimp only [left_derived_zero_to_self_app]
  rw [functor.left_derived_map_eq F 0 f (ProjectiveResolution.lift f P Q) (by simp), category.assoc,
    category.assoc, ← category.assoc _ (F.left_derived_obj_iso 0 Q).Hom, iso.inv_hom_id,
    category.id_comp, category.assoc, whisker_eq]
  dsimp only [homologyFunctor_map]
  ext
  simp only [HomologicalComplex.Hom.sqTo_right, map_homological_complex_map_f,
    homology.π'_map_assoc, homology.π'_desc', kernel.lift_ι_assoc, category.assoc,
    homology.π'_desc'_assoc, ← map_comp,
    show (ProjectiveResolution.lift f P Q).f 0 ≫ _ = _ ≫ f from
      HomologicalComplex.congr_hom (ProjectiveResolution.lift_commutes f P Q) 0]
#align category_theory.abelian.functor.left_derived_zero_to_self_natural CategoryTheory.Abelian.Functor.leftDerived_zero_to_self_natural

/-- Given `preserves_finite_colimits F`, the natural isomorphism `(F.left_derived 0) ≅ F`. -/
def leftDerivedZeroIsoSelf [EnoughProjectives C] [PreservesFiniteColimits F] :
    F.leftDerived 0 ≅ F :=
  NatIso.ofComponents (fun X => leftDerivedZeroToSelfAppIso _ (ProjectiveResolution.of X))
    fun X Y f => leftDerived_zero_to_self_natural _ _ _ _
#align category_theory.abelian.functor.left_derived_zero_iso_self CategoryTheory.Abelian.Functor.leftDerivedZeroIsoSelf

end CategoryTheory.Abelian.Functor

