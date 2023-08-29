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
                                       -- 🎉 no goals
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
      -- ⊢ HomologicalComplex.d ((mapHomologicalComplex F (ComplexShape.down ℕ)).obj P. …
      simp only [mapHomologicalComplex_obj_d, Iso.refl_hom, Category.comp_id]
      -- ⊢ F.map (HomologicalComplex.d P.complex (0 + 1) 0) = F.map (HomologicalComplex …
      rfl) (by simp) (preserves_exact_of_PreservesFiniteColimits_of_epi _ P.exact₀)
      -- 🎉 no goals
               -- 🎉 no goals
#align category_theory.abelian.functor.exact_of_map_projective_resolution CategoryTheory.Abelian.Functor.exact_of_map_projectiveResolution

/-- Given `P : ProjectiveResolution X`, a morphism `(F.leftDerived 0).obj X ⟶ F.obj X`. -/
def leftDerivedZeroToSelfApp [EnoughProjectives C] {X : C} (P : ProjectiveResolution X) :
    (F.leftDerived 0).obj X ⟶ F.obj X :=
  (leftDerivedObjIso F 0 P).hom ≫
    homology.desc' _ _ _ (kernel.ι _ ≫ F.map (P.π.f 0))
      (by
        rw [kernel.lift_ι_assoc,
          HomologicalComplex.dTo_eq _ (by simp : (ComplexShape.down ℕ).Rel 1 0),
          mapHomologicalComplex_obj_d, Category.assoc, ← Functor.map_comp]
        simp)
        -- 🎉 no goals
#align category_theory.abelian.functor.left_derived_zero_to_self_app CategoryTheory.Abelian.Functor.leftDerivedZeroToSelfApp

/-- Given `P : ProjectiveResolution X`, a morphism `F.obj X ⟶ (F.leftDerived 0).obj X` given
`PreservesFiniteColimits F`. -/
def leftDerivedZeroToSelfAppInv [EnoughProjectives C] [PreservesFiniteColimits F] {X : C}
    (P : ProjectiveResolution X) : F.obj X ⟶ (F.leftDerived 0).obj X := by
  -- Porting note: this is no longer an instance
  have := isIso_cokernel_desc_of_exact_of_epi _ _ (exact_of_map_projectiveResolution F P)
  -- ⊢ F.obj X ⟶ (leftDerived F 0).obj X
  refine'
    (asIso (cokernel.desc _ _ (exact_of_map_projectiveResolution F P).w)).inv ≫
      _ ≫ (homologyIsoCokernelLift _ _ _).inv ≫ (leftDerivedObjIso F 0 P).inv
  refine' cokernel.map _ _ (𝟙 _) (kernel.lift _ (𝟙 _) (by simp)) _
  -- ⊢ HomologicalComplex.dTo ((mapHomologicalComplex F (ComplexShape.down ℕ)).obj  …
  ext
  -- ⊢ (HomologicalComplex.dTo ((mapHomologicalComplex F (ComplexShape.down ℕ)).obj …
  -- Porting note: this used to just be `simp`
  simp only [Category.assoc, kernel.lift_ι, Category.comp_id, Category.id_comp]
  -- 🎉 no goals
#align category_theory.abelian.functor.left_derived_zero_to_self_app_inv CategoryTheory.Abelian.Functor.leftDerivedZeroToSelfAppInv

theorem leftDerivedZeroToSelfApp_comp_inv [EnoughProjectives C] [PreservesFiniteColimits F] {X : C}
    (P : ProjectiveResolution X) :
    leftDerivedZeroToSelfApp F P ≫ leftDerivedZeroToSelfAppInv F P = 𝟙 _ := by
  dsimp [leftDerivedZeroToSelfApp, leftDerivedZeroToSelfAppInv]
  -- ⊢ ((leftDerivedObjIso F 0 P).hom ≫ homology.desc' (F.map (HomologicalComplex.d …
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, Iso.comp_inv_eq]
  -- ⊢ ((((leftDerivedObjIso F 0 P).hom ≫ homology.desc' (F.map (HomologicalComplex …
  -- Porting note: working around 'motive is not type correct'
  simp only [Category.id_comp]
  -- ⊢ ((((leftDerivedObjIso F 0 P).hom ≫ homology.desc' (F.map (HomologicalComplex …
  rw [Category.assoc, Category.assoc, Category.assoc]
  -- ⊢ (leftDerivedObjIso F 0 P).hom ≫ homology.desc' (F.map (HomologicalComplex.d  …
  convert Category.comp_id (leftDerivedObjIso F 0 P).hom
  -- ⊢ homology.desc' (F.map (HomologicalComplex.d P.complex (ComplexShape.prev (Co …
  rw [← Category.assoc, ← Category.assoc, Iso.comp_inv_eq]
  -- ⊢ (homology.desc' (F.map (HomologicalComplex.d P.complex (ComplexShape.prev (C …
  -- Porting note: broken ext
  apply homology.hom_from_ext
  -- ⊢ homology.π' (HomologicalComplex.dTo ((mapHomologicalComplex F (ComplexShape. …
  simp only [← Category.assoc]
  -- ⊢ ((homology.π' (HomologicalComplex.dTo ((mapHomologicalComplex F (ComplexShap …
  erw [homology.π'_desc', Category.assoc, Category.assoc, ←
    Category.assoc (F.map _), Abelian.cokernel.desc.inv _ _ (exact_of_map_projectiveResolution F P),
    cokernel.π_desc, homology.π', Category.comp_id, Category.assoc (cokernel.π _), Iso.inv_hom_id,
    Category.comp_id, ← Category.assoc]
  -- Porting note: restructured proof to avoid `convert`
  conv_rhs => rw [← Category.id_comp (cokernel.π _)]
  -- ⊢ (kernel.ι (F.map (HomologicalComplex.d P.complex 0 (ComplexShape.next (Compl …
  congr
  -- ⊢ kernel.ι (F.map (HomologicalComplex.d P.complex 0 (ComplexShape.next (Comple …
  ext
  -- ⊢ (kernel.ι (F.map (HomologicalComplex.d P.complex 0 (ComplexShape.next (Compl …
  -- Porting note: working around 'motive is not type correct'
  simp only [Category.id_comp]
  -- ⊢ (kernel.ι (F.map (HomologicalComplex.d P.complex 0 (ComplexShape.next (Compl …
  rw [Category.assoc, equalizer_as_kernel, kernel.lift_ι]
  -- ⊢ kernel.ι (F.map (HomologicalComplex.d P.complex 0 (ComplexShape.next (Comple …
  simp only [Category.comp_id]
  -- 🎉 no goals
#align category_theory.abelian.functor.left_derived_zero_to_self_app_comp_inv CategoryTheory.Abelian.Functor.leftDerivedZeroToSelfApp_comp_inv

-- Porting note: linter thinks the `have` below is unused, but removing it makes a typeclass
-- search fail
@[nolint unusedHavesSuffices]
theorem leftDerivedZeroToSelfAppInv_comp [EnoughProjectives C] [PreservesFiniteColimits F] {X : C}
    (P : ProjectiveResolution X) :
    leftDerivedZeroToSelfAppInv F P ≫ leftDerivedZeroToSelfApp F P = 𝟙 _ := by
  dsimp [leftDerivedZeroToSelfApp, leftDerivedZeroToSelfAppInv]
  -- ⊢ (inv (cokernel.desc (F.map (HomologicalComplex.d P.complex (ComplexShape.pre …
  rw [Category.assoc, Category.assoc]
  -- ⊢ inv (cokernel.desc (F.map (HomologicalComplex.d P.complex (ComplexShape.prev …
  -- Porting note: working around 'motive is not type correct'
  simp only [Category.assoc]
  -- ⊢ inv (cokernel.desc (F.map (HomologicalComplex.d P.complex (ComplexShape.prev …
  rw [← Category.assoc (F.leftDerivedObjIso 0 P).inv, Iso.inv_hom_id]
  -- ⊢ inv (cokernel.desc (F.map (HomologicalComplex.d P.complex (ComplexShape.prev …
  -- Porting note: working around 'motive is not type correct'
  simp only [Category.id_comp]
  -- ⊢ inv (cokernel.desc (F.map (HomologicalComplex.d P.complex (ComplexShape.prev …
  -- Porting note: instance not found even though it is present in the goal
  have : IsIso (cokernel.desc (F.map
    (HomologicalComplex.d P.complex (ComplexShape.prev (ComplexShape.down ℕ) 0) 0))
      (F.map (HomologicalComplex.Hom.f P.π 0)) (exact_of_map_projectiveResolution F P).w) :=
    isIso_cokernel_desc_of_exact_of_epi _ _ (exact_of_map_projectiveResolution F P)
  rw [IsIso.inv_comp_eq]
  -- ⊢ cokernel.map (F.map (HomologicalComplex.d P.complex (ComplexShape.prev (Comp …
  -- Porting note: working around 'motive is not type correct'
  simp only [Category.comp_id]
  -- ⊢ cokernel.map (F.map (HomologicalComplex.d P.complex (ComplexShape.prev (Comp …
  ext
  -- ⊢ coequalizer.π (F.map (HomologicalComplex.d P.complex (ComplexShape.prev (Com …
  simp only [cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc, homology.desc']
  -- ⊢ kernel.lift (F.map (HomologicalComplex.d P.complex 0 (ComplexShape.next (Com …
  rw [← Category.assoc, ← Category.assoc (homologyIsoCokernelLift _ _ _).inv, Iso.inv_hom_id]
  -- ⊢ (kernel.lift (F.map (HomologicalComplex.d P.complex 0 (ComplexShape.next (Co …
  simp only [Category.assoc, cokernel.π_desc, kernel.lift_ι_assoc, Category.id_comp]
  -- 🎉 no goals
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
  -- ⊢ (leftDerived F 0).map f ≫ (leftDerivedObjIso F 0 Q).hom ≫ homology.desc' (Ho …
  rw [Functor.leftDerived_map_eq F 0 f (ProjectiveResolution.lift f P Q) (by simp), Category.assoc,
    Category.assoc, ← Category.assoc _ (F.leftDerivedObjIso 0 Q).hom, Iso.inv_hom_id,
    Category.id_comp, Category.assoc, whisker_eq]
  dsimp only [homologyFunctor_map]
  -- ⊢ homology.map (_ : HomologicalComplex.dTo ((mapHomologicalComplex F (ComplexS …
  -- Porting note: broken ext
  apply homology.hom_from_ext
  -- ⊢ homology.π' (HomologicalComplex.dTo ((mapHomologicalComplex F (ComplexShape. …
  simp only [HomologicalComplex.Hom.sqTo_right, mapHomologicalComplex_map_f,
    homology.π'_map_assoc, homology.π'_desc', kernel.lift_ι_assoc, Category.assoc,
    homology.π'_desc'_assoc, ← map_comp,
    show (ProjectiveResolution.lift f P Q).f 0 ≫ _ = _ ≫ f from
      HomologicalComplex.congr_hom (ProjectiveResolution.lift_commutes f P Q) 0]
#align category_theory.abelian.functor.left_derived_zero_to_self_natural CategoryTheory.Abelian.Functor.leftDerived_zero_to_self_natural

/-- Given `PreservesFiniteColimits F`, the natural isomorphism `(F.leftDerived 0) ≅ F`. -/
def leftDerivedZeroIsoSelf [EnoughProjectives C] [PreservesFiniteColimits F] :
    F.leftDerived 0 ≅ F :=
  NatIso.ofComponents (fun X => leftDerivedZeroToSelfAppIso _ (ProjectiveResolution.of X))
    fun {_ _} _ => leftDerived_zero_to_self_natural _ _ _ _
#align category_theory.abelian.functor.left_derived_zero_iso_self CategoryTheory.Abelian.Functor.leftDerivedZeroIsoSelf

end CategoryTheory.Abelian.Functor
