/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Preadditive.ProjectiveResolution

#align_import category_theory.functor.left_derived from "leanprover-community/mathlib"@"13ff898b0eee75d3cc75d1c06a491720eaaf911d"

/-!
# Left-derived functors

We define the left-derived functors `F.leftDerived n : C ⥤ D` for any additive functor `F`
out of a category with projective resolutions.

The definition is
```
projectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙ HomotopyCategory.homologyFunctor D _ n
```
that is, we pick a projective resolution (thought of as an object of the homotopy category),
we apply `F` objectwise, and compute `n`-th homology.

We show that these left-derived functors can be calculated
on objects using any choice of projective resolution,
and on morphisms by any choice of lift to a chain map between chosen projective resolutions.

Similarly we define natural transformations between left-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Implementation

We don't assume the categories involved are abelian
(just preadditive, and have equalizers, cokernels, and image maps),
or that the functors are right exact.
None of these assumptions are needed yet.

It is often convenient, of course, to work with `[Abelian C] [EnoughProjectives C] [Abelian D]`
which (assuming the results from `CategoryTheory.Abelian.Projective`) are enough to
provide all the typeclass hypotheses assumed here.
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type*} [Category D]

-- Importing `CategoryTheory.Abelian.Projective` and assuming
-- `[Abelian C] [EnoughProjectives C] [Abelian D]` suffices to acquire all the following:
variable [Abelian C] [HasProjectiveResolutions C] [Abelian D]

def Functor.leftDerivedToHomotopyCategory (F : C ⥤ D) [F.Additive] :
    C ⥤ HomotopyCategory D (ComplexShape.down ℕ) :=
  projectiveResolutions C ⋙ F.mapHomotopyCategory _

def ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.leftDerivedToHomotopyCategory.obj X ≅
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).obj P.complex :=
  (F.mapHomotopyCategory _).mapIso P.iso ≪≫
    (F.mapHomotopyCategoryFactors _).app P.complex

@[reassoc]
def ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] :
    F.leftDerivedToHomotopyCategory.map f ≫ (Q.isoLeftDerivedToHomotopyCategoryObj F).hom =
      (P.isoLeftDerivedToHomotopyCategoryObj F).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map φ := by
  dsimp [Functor.leftDerivedToHomotopyCategory, isoLeftDerivedToHomotopyCategoryObj]
  rw [← Functor.map_comp_assoc, iso_hom_naturality f P Q φ comm, Functor.map_comp,
    Category.assoc, Category.assoc]
  erw [(F.mapHomotopyCategoryFactors (ComplexShape.down ℕ)).hom.naturality]
  rfl

@[reassoc]
def ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_inv_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] :
    (P.isoLeftDerivedToHomotopyCategoryObj F).inv ≫
      F.leftDerivedToHomotopyCategory.map f =
        (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map φ ≫
          (Q.isoLeftDerivedToHomotopyCategoryObj F).inv := by
  rw [← cancel_mono (Q.isoLeftDerivedToHomotopyCategoryObj F).hom,
    Category.assoc, Category.assoc, Iso.inv_hom_id,
    isoLeftDerivedToHomotopyCategoryObj_hom_naturality f P Q φ comm,
    Iso.inv_hom_id_assoc, Category.comp_id]

/-- The left derived functors of an additive functor. -/
def Functor.leftDerived (F : C ⥤ D) [F.Additive] (n : ℕ) : C ⥤ D :=
  F.leftDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n
#align category_theory.functor.left_derived CategoryTheory.Functor.leftDerived

/-- We can compute a left derived functor using a chosen projective resolution. -/
def ProjectiveResolution.isoLeftDerivedObj {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.leftDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj P.complex) :=
  (HomotopyCategory.homologyFunctor D _ n).mapIso (P.isoLeftDerivedToHomotopyCategoryObj F) ≪≫
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
  rw [Category.assoc, ← Functor.map_comp_assoc,
    ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality f P Q φ comm F,
    Functor.map_comp, Category.assoc]
  erw [(HomotopyCategory.homologyFunctorFactors D (ComplexShape.down ℕ) n).hom.naturality]
  rfl

@[reassoc]
lemma ProjectiveResolution.isoLeftDerivedObj_inv_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (P.isoLeftDerivedObj F n).inv ≫ (F.leftDerived n).map f =
      (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ ≫
        (Q.isoLeftDerivedObj F n).inv := by
  rw [← cancel_mono (Q.isoLeftDerivedObj F n).hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, isoLeftDerivedObj_hom_naturality f P Q φ comm,
    Iso.inv_hom_id_assoc]

open ZeroObject

lemma Functor.isZero_leftDerived_obj_projective_succ
    (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) [Projective X] :
    IsZero ((F.leftDerived (n+1)).obj X) := by
  refine' IsZero.of_iso _ ((ProjectiveResolution.self X).isoLeftDerivedObj F (n+1))
  erw [HomologicalComplex.isZero_homology_iff]
  apply ShortComplex.exact_of_isZero_X₂
  dsimp [ProjectiveResolution.self]
  exact IsZero.of_iso (isZero_zero _) F.mapZeroObject

/-- The higher derived functors vanish on projective objects. -/
def Functor.leftDerivedObjProjectiveSucc (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) [Projective X] :
    (F.leftDerived (n + 1)).obj X ≅ 0 :=
  (F.isZero_leftDerived_obj_projective_succ n X).isoZero
#align category_theory.functor.left_derived_obj_projective_succ CategoryTheory.Functor.leftDerivedObjProjectiveSucc

/-- We can compute a left derived functor on a morphism using a lift of that morphism
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
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← HomologicalComplex.comp_f, w, HomologicalComplex.comp_f,
    ChainComplex.single₀_map_f_0]
#align category_theory.functor.left_derived_map_eq CategoryTheory.Functor.leftDerived_map_eq

def NatTrans.leftDerivedToHomotopyCategory {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    F.leftDerivedToHomotopyCategory ⟶ G.leftDerivedToHomotopyCategory :=
  whiskerLeft _ (NatTrans.mapHomotopyCategory α (ComplexShape.down ℕ))

lemma ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : ProjectiveResolution X) :
    (NatTrans.leftDerivedToHomotopyCategory α).app X =
      (P.isoLeftDerivedToHomotopyCategoryObj F).hom ≫
        (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex α _).app P.complex) ≫
          (P.isoLeftDerivedToHomotopyCategoryObj G).inv := by
  rw [← cancel_mono (P.isoLeftDerivedToHomotopyCategoryObj G).hom, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp [isoLeftDerivedToHomotopyCategoryObj, Functor.mapHomotopyCategoryFactors,
    NatTrans.leftDerivedToHomotopyCategory]
  rw [Category.assoc]
  erw [Category.id_comp, Category.comp_id]
  obtain ⟨β, hβ⟩ := (HomotopyCategory.quotient _ _).map_surjective (iso P).hom
  rw [← hβ]
  dsimp
  simp only [← Functor.map_comp, NatTrans.mapHomologicalComplex_naturality]
  rfl

@[simp]
lemma NatTrans.leftDerivedToHomotopyCategory_id (F : C ⥤ D) [F.Additive] :
    NatTrans.leftDerivedToHomotopyCategory (𝟙 F) = 𝟙 _ := rfl

@[simp]
lemma NatTrans.leftDerivedToHomotopyCategory_comp {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)
    [F.Additive] [G.Additive] [H.Additive] :
    NatTrans.leftDerivedToHomotopyCategory (α ≫ β) =
      NatTrans.leftDerivedToHomotopyCategory α ≫
        NatTrans.leftDerivedToHomotopyCategory β := rfl

/-- The natural transformation between left-derived functors induced by a natural transformation.-/
def NatTrans.leftDerived {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) :
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

@[simp, nolint simpNF]
theorem NatTrans.leftDerived_comp {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (α : F ⟶ G) (β : G ⟶ H) (n : ℕ) :
    NatTrans.leftDerived (α ≫ β) n = NatTrans.leftDerived α n ≫ NatTrans.leftDerived β n := by
  simp [NatTrans.leftDerived]
#align category_theory.nat_trans.left_derived_comp CategoryTheory.NatTrans.leftDerived_comp


/-- A component of the natural transformation between left-derived functors can be computed
using a chosen projective resolution.
-/
lemma ProjectiveResolution.leftDerived_app_eq
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : ProjectiveResolution X)
    (n : ℕ) : (NatTrans.leftDerived α n).app X =
      (P.isoLeftDerivedObj F n).hom ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map
        ((NatTrans.mapHomologicalComplex α _).app P.complex) ≫
        (P.isoLeftDerivedObj G n).inv := by
  dsimp [NatTrans.leftDerived, isoLeftDerivedObj]
  rw [ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq α P,
    Functor.map_comp, Functor.map_comp, Category.assoc]
  erw [← (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down ℕ) n).hom.naturality_assoc
    ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex)]
  simp only [Functor.comp_map, Iso.hom_inv_id_app_assoc]


-- TODO:
-- lemma nat_trans.left_derived_projective_zero {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G)
--   (X : C) [projective X] :
--   (nat_trans.left_derived α 0).app X =
--     (F.left_derived_obj_projective_zero X).hom ≫
--       α.app X ≫
--         (G.left_derived_obj_projective_zero X).inv := sorry
-- TODO:
-- lemma nat_trans.left_derived_projective_succ {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G)
--   (n : ℕ) (X : C) [projective X] :
--   (nat_trans.left_derived α (n+1)).app X = 0 := sorry
-- TODO left-derived functors of the identity functor are the identity
-- (requires we assume `abelian`?)
-- PROJECT left-derived functors of a composition (Grothendieck sequence)

def ProjectiveResolution.fromLeftDerivedZero' {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    ((F.mapHomologicalComplex _).obj P.complex).homology 0 ⟶ F.obj X :=
  (ChainComplex.isoHomologyι₀ _).hom ≫
    HomologicalComplex.descOpcycles _ (F.map (P.π.f 0)) 1 (by simp) (by
      dsimp
      rw [← F.map_comp, ← HomologicalComplex.Hom.comm, ChainComplex.single₀_obj_X_d,
        comp_zero, F.map_zero])

@[reassoc (attr := simp)]
lemma ProjectiveResolution.pOpcycles_comp_isoHomology₀_inv_fromLeftDerivedZero' {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    HomologicalComplex.pOpcycles _ _ ≫ (ChainComplex.isoHomologyι₀ _).inv ≫
      P.fromLeftDerivedZero' F = F.map (P.π.f 0) := by
  dsimp only [fromLeftDerivedZero']
  simp

@[reassoc]
def ProjectiveResolution.fromLeftDerivedZero'_naturality {X Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] :
    P.fromLeftDerivedZero' F ≫ F.map f =
      (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ 0).map φ ≫
        Q.fromLeftDerivedZero' F := by
  simp only [← cancel_epi (ChainComplex.isoHomologyι₀ _).inv,
    ← cancel_epi (HomologicalComplex.pOpcycles _ _),
    pOpcycles_comp_isoHomology₀_inv_fromLeftDerivedZero'_assoc, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map,
    ChainComplex.isoHomologyι₀_inv_naturality_assoc,
    HomologicalComplex.p_opcyclesMap_assoc,
    pOpcycles_comp_isoHomology₀_inv_fromLeftDerivedZero',
    Functor.mapHomologicalComplex_map_f, ← F.map_comp, comm]

instance (F : C ⥤ D) [F.Additive] (X : C) [Projective X] :
    IsIso ((ProjectiveResolution.self X).fromLeftDerivedZero' F) := by
  dsimp [ProjectiveResolution.fromLeftDerivedZero',
    ProjectiveResolution.self]
  refine @IsIso.comp_isIso  _ _ _ _ _ _ _ inferInstance ?_
  rw [ChainComplex.isIso_descOpcycles_iff]
  constructor
  · infer_instance
  · rw [ShortComplex.exact_iff_mono]
    · dsimp
      simp only [Functor.map_id]
      infer_instance
    · simp

def Functor.fromLeftDerivedZero (F : C ⥤ D) [F.Additive] :
    F.leftDerived 0 ⟶ F where
  app X := (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down ℕ) 0).hom.app _ ≫
    (projectiveResolution X).fromLeftDerivedZero' F
  naturality {X Y} f := by
    rw [Category.assoc, ProjectiveResolution.fromLeftDerivedZero'_naturality f
      (projectiveResolution X) (projectiveResolution Y) (projectiveResolution.lift f) (by simp) F]
    erw [← NatTrans.naturality_assoc]
    rfl

lemma ProjectiveResolution.fromLeftDerivedZero_eq
    {X : C} (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.fromLeftDerivedZero.app X =
      (P.isoLeftDerivedObj F 0).hom ≫ P.fromLeftDerivedZero' F := by
  dsimp [Functor.fromLeftDerivedZero, isoLeftDerivedObj]
  have h₁ : (P.isoLeftDerivedToHomotopyCategoryObj F).inv =
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map (lift (𝟙 X) _ _) :=
    Category.id_comp _
  have h₂ := ProjectiveResolution.fromLeftDerivedZero'_naturality (𝟙 X)
    P (projectiveResolution X) (lift (𝟙 X) _ _ ) (by
      dsimp
      rw [← HomologicalComplex.comp_f, lift_commutes, Functor.map_id,
        Category.comp_id, Category.comp_id]) F
  rw [F.map_id, Category.comp_id] at h₂
  rw [← cancel_epi ((HomotopyCategory.homologyFunctor _ _ 0).map
    (P.isoLeftDerivedToHomotopyCategoryObj F).inv), Category.assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
  rw [h₂, h₁]
  erw [← NatTrans.naturality_assoc]
  rfl

-- this replaces the previous `Functor.leftDerivedObjProjectiveZero` which
-- is generalized as `Functor.leftDerivedZeroIsoSelf` for all `X` when
-- `F` preserves finite colimits
instance (F : C ⥤ D) [F.Additive] (X : C) [Projective X] :
    IsIso (F.fromLeftDerivedZero.app X) := by
  rw [(ProjectiveResolution.self X).fromLeftDerivedZero_eq F]
  infer_instance

section

variable (F : C ⥤ D) [F.Additive]

instance [PreservesFiniteColimits F] {X : C} (P : ProjectiveResolution X) :
    IsIso (P.fromLeftDerivedZero' F) := by
  dsimp [ProjectiveResolution.fromLeftDerivedZero']
  refine @IsIso.comp_isIso  _ _ _ _ _ _ _ inferInstance ?_
  rw [ChainComplex.isIso_descOpcycles_iff]
  constructor
  · infer_instance
  · let S : ShortComplex C := ShortComplex.mk (P.complex.d 1 0) (P.π.f 0) (by simp)
    -- this exactness property should be moved to Abelian/ProjectiveResolution.lean
    have hS : S.Exact := by
      have : QuasiIsoAt P.π 0 := inferInstance
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros'] at this
      rotate_left
      · simp
      · rfl
      · rfl
      exact this.2
    exact hS.map_of_epi_of_preservesCokernel F
      (by dsimp; infer_instance) inferInstance

instance [PreservesFiniteColimits F] : IsIso F.fromLeftDerivedZero := by
  have : ∀ X, IsIso (F.fromLeftDerivedZero.app X) := fun X => by
    dsimp [Functor.fromLeftDerivedZero]
    infer_instance
  apply NatIso.isIso_of_isIso_app

variable [PreservesFiniteColimits F]

@[simps! inv]
def Functor.leftDerivedZeroIsoSelf : F.leftDerived 0 ≅ F :=
  asIso F.fromLeftDerivedZero

@[reassoc (attr := simp)]
lemma Functor.leftDerivedZeroIsoSelf_inv_hom_id :
    F.leftDerivedZeroIsoSelf.inv ≫ F.fromLeftDerivedZero = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.inv_hom_id

@[reassoc (attr := simp)]
lemma Functor.leftDerivedZeroIsoSelf_hom_inv_id :
    F.fromLeftDerivedZero ≫ F.leftDerivedZeroIsoSelf.inv = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.hom_inv_id

@[reassoc (attr := simp)]
lemma Functor.leftDerivedZeroIsoSelf_inv_hom_id_app (X : C) :
    F.leftDerivedZeroIsoSelf.inv.app X ≫ F.fromLeftDerivedZero.app X = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.inv_hom_id_app X

@[reassoc (attr := simp)]
lemma Functor.leftDerivedZeroIsoSelf_hom_inv_id_app (X : C) :
    F.fromLeftDerivedZero.app X ≫ F.leftDerivedZeroIsoSelf.inv.app X = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.hom_inv_id_app X

end

end CategoryTheory
