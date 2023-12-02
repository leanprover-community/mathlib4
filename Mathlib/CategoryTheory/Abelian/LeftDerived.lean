/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Riccardo Brasca, Adam Topaz, Jujian Zhang, Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.Homology
import Mathlib.CategoryTheory.Abelian.ProjectiveResolution
import Mathlib.Algebra.Homology.Additive

#align_import category_theory.abelian.left_derived from "leanprover-community/mathlib"@"8001ea54ece3bd5c0d0932f1e4f6d0f142ea20d9"

/-!
# Left-derived functors

We define the left-derived functors `F.leftDerived n : C ⥤ D` for any additive functor `F`
out of a category with projective resolutions.

We first define a functor
`F.leftDerivedToHomotopyCategory : C ⥤ HomotopyCategory D (ComplexShape.down ℕ)` which is
`projectiveResolutions C ⋙ F.mapHomotopyCategory _`. We show that if `X : C` and
`P : ProjectiveResolution X`, then `F.leftDerivedToHomotopyCategory.obj X` identifies
to the image in the homotopy category of the functor `F` applied objectwise to `P.complex`
(this isomorphism is `P.isoLeftDerivedToHomotopyCategoryObj F`).

Then, the left-derived functors `F.leftDerived n : C ⥤ D` are obtained by composing
`F.leftDerivedToHomotopyCategory` with the homology functors on the homotopy category.

Similarly we define natural transformations between left-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Main results
* `Functor.isZero_leftDerived_obj_projective_succ`: projective objects have no higher
  left derived functor.
* `NatTrans.leftDerived`: the natural isomorphism between left derived functors
  induced by natural transformation.
* `Functor.fromLeftDerivedZero`: the natural transformation `F.leftDerived 0 ⟶ F`,
  which is an isomorphism when `F` is right exact (i.e. preserves finite colimits),
  see also `Functor.leftDerivedZeroIsoSelf`.
-/

<<<<<<< HEAD
-- this is already in `CategoryTheory.Functor.LeftDerived`

/-noncomputable section
=======
universe v u

namespace CategoryTheory
>>>>>>> origin/homology-sequence-computation

open Category Limits

variable {C : Type u} [Category.{v} C] {D : Type*} [Category D]
  [Abelian C] [HasProjectiveResolutions C] [Abelian D]

/-- When `F : C ⥤ D` is an additive functor, this is
the functor `C ⥤ HomotopyCategory D (ComplexShape.down ℕ)` which
sends `X : C` to `F` applied to a projective resolution of `X`. -/
noncomputable def Functor.leftDerivedToHomotopyCategory (F : C ⥤ D) [F.Additive] :
    C ⥤ HomotopyCategory D (ComplexShape.down ℕ) :=
  projectiveResolutions C ⋙ F.mapHomotopyCategory _

/-- If `P : ProjectiveResolution Z` and `F : C ⥤ D` is an additive functor, this is
an isomorphism between `F.leftDerivedToHomotopyCategory.obj X` and the complex
obtained by applying `F` to `P.complex`. -/
noncomputable def ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.leftDerivedToHomotopyCategory.obj X ≅
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).obj P.complex :=
  (F.mapHomotopyCategory _).mapIso P.iso ≪≫
    (F.mapHomotopyCategoryFactors _).app P.complex

@[reassoc]
lemma ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_inv_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] :
    (P.isoLeftDerivedToHomotopyCategoryObj F).inv ≫ F.leftDerivedToHomotopyCategory.map f =
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map φ ≫
        (Q.isoLeftDerivedToHomotopyCategoryObj F).inv := by
  dsimp [Functor.leftDerivedToHomotopyCategory, isoLeftDerivedToHomotopyCategoryObj]
  rw [assoc, ← Functor.map_comp, iso_inv_naturality f P Q φ comm, Functor.map_comp]
  erw [(F.mapHomotopyCategoryFactors (ComplexShape.down ℕ)).inv.naturality_assoc]
  rfl

@[reassoc]
lemma ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] :
    F.leftDerivedToHomotopyCategory.map f ≫ (Q.isoLeftDerivedToHomotopyCategoryObj F).hom =
      (P.isoLeftDerivedToHomotopyCategoryObj F).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map φ := by
    dsimp
    rw [← cancel_epi (P.isoLeftDerivedToHomotopyCategoryObj F).inv, Iso.inv_hom_id_assoc,
      isoLeftDerivedToHomotopyCategoryObj_inv_naturality_assoc f P Q φ comm F,
      Iso.inv_hom_id, comp_id]

/-- The left derived functors of an additive functor. -/
noncomputable def Functor.leftDerived (F : C ⥤ D) [F.Additive] (n : ℕ) : C ⥤ D :=
  F.leftDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n
#align category_theory.functor.left_derived CategoryTheory.Functor.leftDerived

/-- We can compute a left derived functor using a chosen projective resolution. -/
noncomputable def ProjectiveResolution.isoLeftDerivedObj {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.leftDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj P.complex) :=
  (HomotopyCategory.homologyFunctor D _ n).mapIso
    (P.isoLeftDerivedToHomotopyCategoryObj F) ≪≫
    (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down ℕ) n).app _

@[reassoc]
lemma ProjectiveResolution.isoLeftDerivedObj_hom_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.leftDerived n).map f ≫ (Q.isoLeftDerivedObj F n).hom =
      (P.isoLeftDerivedObj F n).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ := by
  dsimp [isoLeftDerivedObj, Functor.leftDerived]
  rw [assoc, ← Functor.map_comp_assoc,
    ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality f P Q φ comm F,
    Functor.map_comp, assoc]
  erw [(HomotopyCategory.homologyFunctorFactors D (ComplexShape.down ℕ) n).hom.naturality]
  rfl

<<<<<<< HEAD
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
=======
@[reassoc]
lemma ProjectiveResolution.isoLeftDerivedObj_inv_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (P.isoLeftDerivedObj F n).inv ≫ (F.leftDerived n).map f =
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ ≫
          (Q.isoLeftDerivedObj F n).inv := by
  rw [← cancel_mono (Q.isoLeftDerivedObj F n).hom, assoc, assoc,
    ProjectiveResolution.isoLeftDerivedObj_hom_naturality f P Q φ comm F n,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, comp_id]

/-- The higher derived functors vanish on projective objects. -/
lemma Functor.isZero_leftDerived_obj_projective_succ
    (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) [Projective X] :
    IsZero ((F.leftDerived (n + 1)).obj X) := by
  refine IsZero.of_iso ?_ ((ProjectiveResolution.self X).isoLeftDerivedObj F (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero (by apply isZero_zero))

/-- We can compute a left derived functor on a morphism using a descent of that morphism
to a chain map between chosen projective resolutions.
-/
theorem Functor.leftDerived_map_eq (F : C ⥤ D) [F.Additive] (n : ℕ) {X Y : C} (f : X ⟶ Y)
    {P : ProjectiveResolution X} {Q : ProjectiveResolution Y} (g : P.complex ⟶ Q.complex)
    (w : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) :
    (F.leftDerived n).map f =
      (P.isoLeftDerivedObj F n).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map g ≫
          (Q.isoLeftDerivedObj F n).inv := by
  rw [← cancel_mono (Q.isoLeftDerivedObj F n).hom,
    ProjectiveResolution.isoLeftDerivedObj_hom_naturality f P Q g _ F n,
    assoc, assoc, Iso.inv_hom_id, comp_id]
  rw [← HomologicalComplex.comp_f, w, HomologicalComplex.comp_f,
    ChainComplex.single₀_map_f_zero]
#align category_theory.functor.left_derived_map_eq CategoryTheory.Functor.leftDerived_map_eq

/-- The natural transformation
`F.leftDerivedToHomotopyCategory ⟶ G.leftDerivedToHomotopyCategory` induced by
a natural transformation `F ⟶ G` between additive functors. -/
noncomputable def NatTrans.leftDerivedToHomotopyCategory
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    F.leftDerivedToHomotopyCategory ⟶ G.leftDerivedToHomotopyCategory :=
  whiskerLeft _ (NatTrans.mapHomotopyCategory α (ComplexShape.down ℕ))
>>>>>>> origin/homology-sequence-computation

lemma ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : ProjectiveResolution X) :
    (NatTrans.leftDerivedToHomotopyCategory α).app X =
      (P.isoLeftDerivedToHomotopyCategoryObj F).hom ≫
        (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex α _).app P.complex) ≫
          (P.isoLeftDerivedToHomotopyCategoryObj G).inv := by
  rw [← cancel_mono (P.isoLeftDerivedToHomotopyCategoryObj G).hom, assoc, assoc,
      Iso.inv_hom_id, comp_id]
  dsimp [isoLeftDerivedToHomotopyCategoryObj, Functor.mapHomotopyCategoryFactors,
    NatTrans.leftDerivedToHomotopyCategory]
  rw [assoc]
  erw [id_comp, comp_id]
  obtain ⟨β, hβ⟩ := (HomotopyCategory.quotient _ _).map_surjective (iso P).hom
  rw [← hβ]
  dsimp
  simp only [← Functor.map_comp, NatTrans.mapHomologicalComplex_naturality]
  rfl

<<<<<<< HEAD
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
    show (ProjectiveResolution.lift f P Q).f 0 ≫ _ = _ ≫ f from
      HomologicalComplex.congr_hom (ProjectiveResolution.lift_commutes f P Q) 0]
#align category_theory.abelian.functor.left_derived_zero_to_self_natural CategoryTheory.Abelian.Functor.leftDerived_zero_to_self_natural
=======
@[simp]
lemma NatTrans.leftDerivedToHomotopyCategory_id (F : C ⥤ D) [F.Additive] :
    NatTrans.leftDerivedToHomotopyCategory (𝟙 F) = 𝟙 _ := rfl
>>>>>>> origin/homology-sequence-computation

@[simp, reassoc]
lemma NatTrans.leftDerivedToHomotopyCategory_comp {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)
    [F.Additive] [G.Additive] [H.Additive] :
    NatTrans.leftDerivedToHomotopyCategory (α ≫ β) =
      NatTrans.leftDerivedToHomotopyCategory α ≫
        NatTrans.leftDerivedToHomotopyCategory β := rfl

<<<<<<< HEAD
end CategoryTheory.Abelian.Functor-/
=======
/-- The natural transformation between left-derived functors induced by a natural transformation.-/
noncomputable def NatTrans.leftDerived
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) :
    F.leftDerived n ⟶ G.leftDerived n :=
  whiskerRight (NatTrans.leftDerivedToHomotopyCategory α) _
#align category_theory.nat_trans.left_derived CategoryTheory.NatTrans.leftDerived

@[simp]
theorem NatTrans.leftDerived_id (F : C ⥤ D) [F.Additive] (n : ℕ) :
    NatTrans.leftDerived (𝟙 F) n = 𝟙 (F.leftDerived n) := by
  dsimp only [leftDerived]
  simp only [leftDerivedToHomotopyCategory_id, whiskerRight_id']
  rfl
#align category_theory.nat_trans.left_derived_id CategoryTheory.NatTrans.leftDerived_id

@[simp, reassoc]
theorem NatTrans.leftDerived_comp {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (α : F ⟶ G) (β : G ⟶ H) (n : ℕ) :
    NatTrans.leftDerived (α ≫ β) n = NatTrans.leftDerived α n ≫ NatTrans.leftDerived β n := by
  simp [NatTrans.leftDerived]
#align category_theory.nat_trans.left_derived_comp CategoryTheory.NatTrans.leftDerived_comp

namespace ProjectiveResolution

/-- A component of the natural transformation between left-derived functors can be computed
using a chosen projective resolution. -/
lemma leftDerived_app_eq
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : ProjectiveResolution X)
    (n : ℕ) : (NatTrans.leftDerived α n).app X =
      (P.isoLeftDerivedObj F n).hom ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map
        ((NatTrans.mapHomologicalComplex α _).app P.complex) ≫
        (P.isoLeftDerivedObj G n).inv := by
  dsimp [NatTrans.leftDerived, isoLeftDerivedObj]
  rw [ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq α P,
    Functor.map_comp, Functor.map_comp, assoc]
  erw [← (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down ℕ) n).hom.naturality_assoc
    ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex)]
  simp only [Functor.comp_map, Iso.hom_inv_id_app_assoc]

/-- If `P : ProjectiveResolution X` and `F` is an additive functor, this is
the canonical morphism from the opcycles in degree `0` of
`(F.mapHomologicalComplex _).obj P.complex` to `F.obj X`. -/
noncomputable def fromLeftDerivedZero' {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    ((F.mapHomologicalComplex _).obj P.complex).opcycles 0 ⟶ F.obj X :=
  HomologicalComplex.descOpcycles _ (F.map (P.π.f 0)) 1 (by simp) (by
    dsimp
    rw [← F.map_comp, complex_d_comp_π_f_zero, F.map_zero])

@[reassoc (attr := simp)]
lemma pOpcycles_comp_fromLeftDerivedZero' {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    HomologicalComplex.pOpcycles _ _ ≫ P.fromLeftDerivedZero' F = F.map (P.π.f 0) := by
  simp [fromLeftDerivedZero']

@[reassoc]
lemma fromLeftDerivedZero'_naturality {X Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] :
    HomologicalComplex.opcyclesMap ((F.mapHomologicalComplex _).map φ) 0 ≫
        Q.fromLeftDerivedZero' F = P.fromLeftDerivedZero' F ≫ F.map f := by
  simp only [← cancel_epi (HomologicalComplex.pOpcycles _ _), ← F.map_comp, comm,
    HomologicalComplex.p_opcyclesMap_assoc, Functor.mapHomologicalComplex_map_f,
    pOpcycles_comp_fromLeftDerivedZero', pOpcycles_comp_fromLeftDerivedZero'_assoc]

instance (F : C ⥤ D) [F.Additive] (X : C) [Projective X] :
    IsIso ((ProjectiveResolution.self X).fromLeftDerivedZero' F) := by
  dsimp [ProjectiveResolution.fromLeftDerivedZero']
  rw [ChainComplex.isIso_descOpcycles_iff]
  refine' ⟨ShortComplex.Splitting.exact _, inferInstance⟩
  exact
    { r := 0
      s := 𝟙 _
      f_r := (F.map_isZero (isZero_zero _)).eq_of_src _ _ }

end ProjectiveResolution

/-- The natural transformation `F.leftDerived 0 ⟶ F`. -/
noncomputable def Functor.fromLeftDerivedZero (F : C ⥤ D) [F.Additive] :
    F.leftDerived 0 ⟶ F where
  app X := (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down ℕ) 0).hom.app _ ≫
      (ChainComplex.isoHomologyι₀ _).hom ≫ (projectiveResolution X).fromLeftDerivedZero' F
  naturality {X Y} f := by
    dsimp [leftDerived]
    rw [assoc, assoc, ← ProjectiveResolution.fromLeftDerivedZero'_naturality f
      (projectiveResolution X) (projectiveResolution Y)
      (ProjectiveResolution.lift f _ _) (by simp),
      ← HomologicalComplex.homologyι_naturality_assoc]
    erw [← NatTrans.naturality_assoc]
    rfl

lemma ProjectiveResolution.fromLeftDerivedZero_eq
    {X : C} (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.fromLeftDerivedZero.app X = (P.isoLeftDerivedObj F 0).hom ≫
      (ChainComplex.isoHomologyι₀ _).hom ≫
        P.fromLeftDerivedZero' F := by
  dsimp [Functor.fromLeftDerivedZero, isoLeftDerivedObj]
  have h₁ := ProjectiveResolution.fromLeftDerivedZero'_naturality
    (𝟙 X) P (projectiveResolution X) (lift (𝟙 X) _ _) (by simp) F
  have h₂ : (P.isoLeftDerivedToHomotopyCategoryObj F).inv =
    (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map (lift (𝟙 X) _ _) :=
      id_comp _
  simp only [Functor.map_id, comp_id] at h₁
  rw [assoc, ← cancel_epi ((HomotopyCategory.homologyFunctor _ _ 0).map
      (P.isoLeftDerivedToHomotopyCategoryObj F).inv), ← Functor.map_comp_assoc,
      Iso.inv_hom_id, Functor.map_id, id_comp, ← h₁, h₂,
      ← HomologicalComplex.homologyι_naturality_assoc]
  erw [← NatTrans.naturality_assoc]
  rfl

instance (F : C ⥤ D) [F.Additive] (X : C) [Projective X] :
    IsIso (F.fromLeftDerivedZero.app X) := by
  rw [(ProjectiveResolution.self X).fromLeftDerivedZero_eq F]
  infer_instance

section

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]

instance {X : C} (P : ProjectiveResolution X) :
    IsIso (P.fromLeftDerivedZero' F) := by
  dsimp [ProjectiveResolution.fromLeftDerivedZero']
  rw [ChainComplex.isIso_descOpcycles_iff, ShortComplex.exact_and_epi_g_iff_g_is_cokernel]
  exact ⟨CokernelCofork.mapIsColimit _ (P.isColimitCokernelCofork) F⟩

instance (X : C) : IsIso (F.fromLeftDerivedZero.app X) := by
  dsimp [Functor.fromLeftDerivedZero]
  infer_instance

instance : IsIso F.fromLeftDerivedZero :=
  NatIso.isIso_of_isIso_app _

namespace Functor

/-- The canonical isomorphism `F.leftDerived 0 ≅ F` when `F` is right exact
(i.e. preserves finite colimits). -/
@[simps! hom]
noncomputable def leftDerivedZeroIsoSelf : F.leftDerived 0 ≅ F :=
  (asIso F.fromLeftDerivedZero)

@[reassoc (attr := simp)]
lemma leftDerivedZeroIsoSelf_hom_inv_id :
    F.fromLeftDerivedZero ≫ F.leftDerivedZeroIsoSelf.inv = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.hom_inv_id

@[reassoc (attr := simp)]
lemma leftDerivedZeroIsoSelf_inv_hom_id :
    F.leftDerivedZeroIsoSelf.inv ≫ F.fromLeftDerivedZero =  𝟙 _ :=
  F.leftDerivedZeroIsoSelf.inv_hom_id

@[reassoc (attr := simp)]
lemma leftDerivedZeroIsoSelf_hom_inv_id_app (X : C) :
    F.fromLeftDerivedZero.app X ≫ F.leftDerivedZeroIsoSelf.inv.app X = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.hom_inv_id_app X

@[reassoc (attr := simp)]
lemma leftDerivedZeroIsoSelf_inv_hom_id_app (X : C) :
    F.leftDerivedZeroIsoSelf.inv.app X ≫ F.fromLeftDerivedZero.app X = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.inv_hom_id_app X

end Functor

end

end CategoryTheory
>>>>>>> origin/homology-sequence-computation
