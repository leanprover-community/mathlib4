/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Adam Topaz
-/
import Mathlib.CategoryTheory.Abelian.Homology
import Mathlib.CategoryTheory.Functor.LeftDerived
import Mathlib.CategoryTheory.Abelian.Projective
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

#align_import category_theory.abelian.left_derived from "leanprover-community/mathlib"@"8001ea54ece3bd5c0d0932f1e4f6d0f142ea20d9"

/-!
# Zeroth left derived functors

If `F : C ⥤ D` is an additive right exact functor between abelian categories, where `C` has enough
projectives, we provide the natural isomorphism `F.leftDerived 0 ≅ F`.

## Main definitions

* `CategoryTheory.Abelian.Functor.leftDerivedZeroIsoSelf`: the natural isomorphism
  `(F.leftDerived 0) ≅ F`.

## Main results
* `preserves_exact_of_PreservesFiniteColimits_of_epi`: if `PreservesFiniteColimits F` and
  `Epi g`, then `Exact (F.map f) (F.map g)` if `exact f g`.

-/


noncomputable section

universe w v u

open CategoryTheory.Limits CategoryTheory CategoryTheory.Functor

variable {C : Type u} [Category.{w} C] {D : Type u} [Category.{w} D]

variable (F : C ⥤ D) {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}

namespace CategoryTheory.Abelian.Functor

open CategoryTheory.Preadditive

variable [Abelian C] [Abelian D] [Additive F]

/-- If `PreservesFiniteColimits F` and `Epi g`, then `Exact (F.map f) (F.map g)` if
`Exact f g`. -/
theorem preserves_exact_of_PreservesFiniteColimits_of_epi [PreservesFiniteColimits F] [Epi g]
    (ex : Exact f g) : Exact (F.map f) (F.map g) :=
  Abelian.exact_of_is_cokernel _ _ (by simp [← Functor.map_comp, ex.w]) <|
    Limits.isColimitCoforkMapOfIsColimit' _ ex.w (Abelian.isColimitOfExactOfEpi _ _ ex)
#align category_theory.abelian.functor.preserves_exact_of_preserves_finite_colimits_of_epi CategoryTheory.Abelian.Functor.preserves_exact_of_PreservesFiniteColimits_of_epi

theorem exact_of_map_projectiveResolution (P : ProjectiveResolution X)
    [PreservesFiniteColimits F] :
    Exact (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).dTo 0)
      (F.map (P.π.f 0)) :=
  Preadditive.exact_of_iso_of_exact' (F.map (P.complex.d 1 0)) (F.map (P.π.f 0)) _ _
    (HomologicalComplex.xPrevIso ((F.mapHomologicalComplex _).obj P.complex) rfl).symm (Iso.refl _)
    (Iso.refl _) (by
      -- Porting note: simp used to be able to do this
      simp only [Iso.symm_hom, HomologicalComplex.xPrevIso_comp_dTo]
      simp only [mapHomologicalComplex_obj_d, Iso.refl_hom, Category.comp_id]
      rfl) (by simp) (preserves_exact_of_PreservesFiniteColimits_of_epi _ P.exact₀)
#align category_theory.abelian.functor.exact_of_map_projective_resolution CategoryTheory.Abelian.Functor.exact_of_map_projectiveResolution

/-- Given `P : ProjectiveResolution X`, a morphism `(F.leftDerived 0).obj X ⟶ F.obj X`. -/
def leftDerivedZeroToSelfApp [EnoughProjectives C] {X : C} (P : ProjectiveResolution X) :
    (F.leftDerived 0).obj X ⟶ F.obj X :=
  (leftDerivedObjIso F 0 P).hom ≫
    homology'.desc' _ _ _ (kernel.ι _ ≫ F.map (P.π.f 0))
      (by
        rw [kernel.lift_ι_assoc,
          HomologicalComplex.dTo_eq _ (by simp : (ComplexShape.down ℕ).Rel 1 0),
          mapHomologicalComplex_obj_d, Category.assoc, ← Functor.map_comp]
        simp)
#align category_theory.abelian.functor.left_derived_zero_to_self_app CategoryTheory.Abelian.Functor.leftDerivedZeroToSelfApp

/-- Given `P : ProjectiveResolution X`, a morphism `F.obj X ⟶ (F.leftDerived 0).obj X` given
`PreservesFiniteColimits F`. -/
def leftDerivedZeroToSelfAppInv [EnoughProjectives C] [PreservesFiniteColimits F] {X : C}
    (P : ProjectiveResolution X) : F.obj X ⟶ (F.leftDerived 0).obj X := by
  -- Porting note: this is no longer an instance
  have := isIso_cokernel_desc_of_exact_of_epi _ _ (exact_of_map_projectiveResolution F P)
  refine'
    (asIso (cokernel.desc _ _ (exact_of_map_projectiveResolution F P).w)).inv ≫
      _ ≫ (homology'IsoCokernelLift _ _ _).inv ≫ (leftDerivedObjIso F 0 P).inv
  refine' cokernel.map _ _ (𝟙 _) (kernel.lift _ (𝟙 _) (by simp)) _
  ext
  -- Porting note: this used to just be `simp`
  simp only [Category.assoc, kernel.lift_ι, Category.comp_id, Category.id_comp]
#align category_theory.abelian.functor.left_derived_zero_to_self_app_inv CategoryTheory.Abelian.Functor.leftDerivedZeroToSelfAppInv

theorem leftDerivedZeroToSelfApp_comp_inv [EnoughProjectives C] [PreservesFiniteColimits F] {X : C}
    (P : ProjectiveResolution X) :
    leftDerivedZeroToSelfApp F P ≫ leftDerivedZeroToSelfAppInv F P = 𝟙 _ := by
  dsimp [leftDerivedZeroToSelfApp, leftDerivedZeroToSelfAppInv]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, Iso.comp_inv_eq]
  -- Porting note: working around 'motive is not type correct'
  simp only [Category.id_comp]
  rw [Category.assoc, Category.assoc, Category.assoc]
  convert Category.comp_id (leftDerivedObjIso F 0 P).hom
  rw [← Category.assoc, ← Category.assoc, Iso.comp_inv_eq]
  -- Porting note: broken ext
  apply homology'.hom_from_ext
  simp only [← Category.assoc]
  erw [homology'.π'_desc', Category.assoc, Category.assoc, ←
    Category.assoc (F.map _), Abelian.cokernel.desc.inv _ _ (exact_of_map_projectiveResolution F P),
    cokernel.π_desc, homology'.π', Category.comp_id, Category.assoc (cokernel.π _), Iso.inv_hom_id,
    Category.comp_id, ← Category.assoc]
  -- Porting note: restructured proof to avoid `convert`
  conv_rhs => rw [← Category.id_comp (cokernel.π _)]
  congr
  ext
  -- Porting note: working around 'motive is not type correct'
  simp only [Category.id_comp]
  rw [Category.assoc, equalizer_as_kernel, kernel.lift_ι]
  simp only [Category.comp_id]
#align category_theory.abelian.functor.left_derived_zero_to_self_app_comp_inv CategoryTheory.Abelian.Functor.leftDerivedZeroToSelfApp_comp_inv

-- Porting note: linter thinks the `have` below is unused, but removing it makes a typeclass
-- search fail
@[nolint unusedHavesSuffices]
theorem leftDerivedZeroToSelfAppInv_comp [EnoughProjectives C] [PreservesFiniteColimits F] {X : C}
    (P : ProjectiveResolution X) :
    leftDerivedZeroToSelfAppInv F P ≫ leftDerivedZeroToSelfApp F P = 𝟙 _ := by
  dsimp [leftDerivedZeroToSelfApp, leftDerivedZeroToSelfAppInv]
  rw [Category.assoc, Category.assoc]
  -- Porting note: working around 'motive is not type correct'
  simp only [Category.assoc]
  rw [← Category.assoc (F.leftDerivedObjIso 0 P).inv, Iso.inv_hom_id]
  -- Porting note: working around 'motive is not type correct'
  simp only [Category.id_comp]
  -- Porting note: instance not found even though it is present in the goal
  have : IsIso (cokernel.desc (F.map
    (HomologicalComplex.d P.complex (ComplexShape.prev (ComplexShape.down ℕ) 0) 0))
      (F.map (HomologicalComplex.Hom.f P.π 0)) (exact_of_map_projectiveResolution F P).w) :=
    isIso_cokernel_desc_of_exact_of_epi _ _ (exact_of_map_projectiveResolution F P)
  rw [IsIso.inv_comp_eq]
  -- Porting note: working around 'motive is not type correct'
  simp only [Category.comp_id]
  ext
  simp only [cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc, homology'.desc']
  rw [← Category.assoc, ← Category.assoc (homology'IsoCokernelLift _ _ _).inv, Iso.inv_hom_id]
  simp only [Category.assoc, cokernel.π_desc, kernel.lift_ι_assoc, Category.id_comp]
#align category_theory.abelian.functor.left_derived_zero_to_self_app_inv_comp CategoryTheory.Abelian.Functor.leftDerivedZeroToSelfAppInv_comp

/-- Given `P : ProjectiveResolution X`, the isomorphism `(F.leftDerived 0).obj X ≅ F.obj X` if
`PreservesFiniteColimits F`. -/
def leftDerivedZeroToSelfAppIso [EnoughProjectives C] [PreservesFiniteColimits F] {X : C}
    (P : ProjectiveResolution X) : (F.leftDerived 0).obj X ≅ F.obj X where
  hom := leftDerivedZeroToSelfApp _ P
  inv := leftDerivedZeroToSelfAppInv _ P
  hom_inv_id := leftDerivedZeroToSelfApp_comp_inv _ P
  inv_hom_id := leftDerivedZeroToSelfAppInv_comp _ P
#align category_theory.abelian.functor.left_derived_zero_to_self_app_iso CategoryTheory.Abelian.Functor.leftDerivedZeroToSelfAppIso

/-- Given `P : ProjectiveResolution X` and `Q : ProjectiveResolution Y` and a morphism `f : X ⟶ Y`,
naturality of the square given by `leftDerived_zero_to_self_obj_hom`. -/
theorem leftDerived_zero_to_self_natural [EnoughProjectives C] {X : C} {Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
    (F.leftDerived 0).map f ≫ leftDerivedZeroToSelfApp F Q =
      leftDerivedZeroToSelfApp F P ≫ F.map f := by
  dsimp only [leftDerivedZeroToSelfApp]
  rw [Functor.leftDerived_map_eq F 0 f (ProjectiveResolution.lift f P Q) (by simp), Category.assoc,
    Category.assoc, ← Category.assoc _ (F.leftDerivedObjIso 0 Q).hom, Iso.inv_hom_id,
    Category.id_comp, Category.assoc, whisker_eq]
  dsimp only [homology'Functor_map]
  -- Porting note: broken ext
  apply homology'.hom_from_ext
  simp only [HomologicalComplex.Hom.sqTo_right, mapHomologicalComplex_map_f,
    homology'.π'_map_assoc, homology'.π'_desc', kernel.lift_ι_assoc, Category.assoc,
    homology'.π'_desc'_assoc, ← map_comp,
    ProjectiveResolution.lift_commutes_zero f P Q]
#align category_theory.abelian.functor.left_derived_zero_to_self_natural CategoryTheory.Abelian.Functor.leftDerived_zero_to_self_natural

/-- Given `PreservesFiniteColimits F`, the natural isomorphism `(F.leftDerived 0) ≅ F`. -/
def leftDerivedZeroIsoSelf [EnoughProjectives C] [PreservesFiniteColimits F] :
    F.leftDerived 0 ≅ F :=
  NatIso.ofComponents (fun X => leftDerivedZeroToSelfAppIso _ (ProjectiveResolution.of X))
    fun {_ _} _ => leftDerived_zero_to_self_natural _ _ _ _
#align category_theory.abelian.functor.left_derived_zero_iso_self CategoryTheory.Abelian.Functor.leftDerivedZeroIsoSelf

end CategoryTheory.Abelian.Functor
