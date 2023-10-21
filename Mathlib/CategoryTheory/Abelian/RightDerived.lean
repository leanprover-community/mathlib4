/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Morrison, Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.InjectiveResolution
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Abelian.Homology
import Mathlib.CategoryTheory.Abelian.Exact

#align_import category_theory.abelian.right_derived from "leanprover-community/mathlib"@"024a4231815538ac739f52d08dd20a55da0d6b23"

/-!
# Right-derived functors

We define the right-derived functors `F.rightDerived n : C ⥤ D` for any additive functor `F`
out of a category with injective resolutions.

The definition is
```
injectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙ HomotopyCategory.homologyFunctor D _ n
```
that is, we pick an injective resolution (thought of as an object of the homotopy category),
we apply `F` objectwise, and compute `n`-th homology.

We show that these right-derived functors can be calculated
on objects using any choice of injective resolution,
and on morphisms by any choice of lift to a cochain map between chosen injective resolutions.

Similarly we define natural transformations between right-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Main results
* `CategoryTheory.Functor.rightDerivedObj_injective_zero`: the `0`-th derived functor of `F` on
  an injective object `X` is isomorphic to `F.obj X`.
* `CategoryTheory.Functor.rightDerivedObj_injective_succ`: injective objects have no higher
  right derived functor.
* `CategoryTheory.NatTrans.rightDerived`: the natural isomorphism between right derived functors
  induced by natural transformation.

Now, we assume `PreservesFiniteLimits F`, then
* `CategoryTheory.Abelian.Functor.preserves_exact_of_preservesFiniteLimits_of_mono`: if `f` is
  mono and `Exact f g`, then `Exact (F.map f) (F.map g)`.
* `CategoryTheory.Abelian.Functor.rightDerivedZeroIsoSelf`: if there are enough injectives,
  then there is a natural isomorphism `(F.rightDerived 0) ≅ F`.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {D : Type*} [Category D]

variable [Abelian C] [HasInjectiveResolutions C] [Abelian D]

def Functor.rightDerivedToHomotopyCategory (F : C ⥤ D) [F.Additive] :
    C ⥤ HomotopyCategory D (ComplexShape.up ℕ) :=
  injectiveResolutions C ⋙ F.mapHomotopyCategory _

def InjectiveResolution.isoRightDerivedToHomotopyCategoryObj {X : C}
    (I : InjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.rightDerivedToHomotopyCategory.obj X ≅
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).obj I.cocomplex :=
  (F.mapHomotopyCategory _).mapIso I.iso ≪≫
    (F.mapHomotopyCategoryFactors _).app I.cocomplex

@[reassoc]
def InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_naturality
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] :
    F.rightDerivedToHomotopyCategory.map f ≫ (J.isoRightDerivedToHomotopyCategoryObj F).hom =
      (I.isoRightDerivedToHomotopyCategoryObj F).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map φ := by
  dsimp [Functor.rightDerivedToHomotopyCategory, isoRightDerivedToHomotopyCategoryObj]
  rw [← Functor.map_comp_assoc, iso_hom_naturality f I J φ comm, Functor.map_comp,
    Category.assoc, Category.assoc]
  erw [(F.mapHomotopyCategoryFactors (ComplexShape.up ℕ)).hom.naturality]
  rfl

@[reassoc]
def InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_inv_naturality
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] :
    (I.isoRightDerivedToHomotopyCategoryObj F).inv ≫ F.rightDerivedToHomotopyCategory.map f =
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map φ ≫
        (J.isoRightDerivedToHomotopyCategoryObj F).inv := by
    rw [← cancel_epi (I.isoRightDerivedToHomotopyCategoryObj F).hom, Iso.hom_inv_id_assoc]
    dsimp
    rw [← isoRightDerivedToHomotopyCategoryObj_hom_naturality_assoc f I J φ comm F,
      Iso.hom_inv_id, Category.comp_id]

/-- The right derived functors of an additive functor. -/
def Functor.rightDerived (F : C ⥤ D) [F.Additive] (n : ℕ) : C ⥤ D :=
  F.rightDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n
#align category_theory.functor.right_derived CategoryTheory.Functor.rightDerived

/-- We can compute a right derived functor using a chosen injective resolution. -/
def InjectiveResolution.isoRightDerivedObj {X : C} (I : InjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj I.cocomplex) :=
  (HomotopyCategory.homologyFunctor D _ n).mapIso (I.isoRightDerivedToHomotopyCategoryObj F) ≪≫ (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).app _

@[reassoc]
lemma InjectiveResolution.isoRightDerivedObj_hom_naturality
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).map f ≫ (J.isoRightDerivedObj F n).hom =
      (I.isoRightDerivedObj F n).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ := by
  dsimp [isoRightDerivedObj, Functor.rightDerived]
  rw [Category.assoc, ← Functor.map_comp_assoc,
    InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_naturality f I J φ comm F,
    Functor.map_comp, Category.assoc]
  erw [(HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).hom.naturality]
  rfl

@[reassoc]
lemma InjectiveResolution.isoRightDerivedObj_inv_naturality
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (I.isoRightDerivedObj F n).inv ≫ (F.rightDerived n).map f =
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ ≫
          (J.isoRightDerivedObj F n).inv := by
  rw [← cancel_mono (J.isoRightDerivedObj F n).hom, Category.assoc, Category.assoc,
    InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ comm F n,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

open ZeroObject

lemma Functor.isZero_rightDerived_obj_injective_succ
    (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) [Injective X] :
    IsZero ((F.rightDerived (n+1)).obj X) := by
  refine' IsZero.of_iso _ ((InjectiveResolution.self X).isoRightDerivedObj F (n+1))
  erw [HomologicalComplex.isZero_homology_iff]
  apply ShortComplex.exact_of_isZero_X₂
  dsimp [InjectiveResolution.self]
  exact IsZero.of_iso (isZero_zero _) F.mapZeroObject

/-- The higher derived functors vanish on injective objects. -/
def Functor.rightDerivedObjInjectiveSucc (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) [Injective X] :
    (F.rightDerived (n + 1)).obj X ≅ 0 :=
  (F.isZero_rightDerived_obj_injective_succ n X).isoZero
#align category_theory.functor.right_derived_obj_injective_succ CategoryTheory.Functor.rightDerivedObjInjectiveSucc

/-- We can compute a right derived functor on a morphism using a descent of that morphism
to a cochain map between chosen injective resolutions.
-/
theorem Functor.rightDerived_map_eq (F : C ⥤ D) [F.Additive] (n : ℕ) {X Y : C} (f : X ⟶ Y)
    {P : InjectiveResolution X} {Q : InjectiveResolution Y} (g : P.cocomplex ⟶ Q.cocomplex)
    (w : P.ι ≫ g = (CochainComplex.single₀ C).map f ≫ Q.ι) :
    (F.rightDerived n).map f =
      (P.isoRightDerivedObj F n).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map g ≫
          (Q.isoRightDerivedObj F n).inv := by
  rw [← cancel_mono (Q.isoRightDerivedObj F n).hom,
    InjectiveResolution.isoRightDerivedObj_hom_naturality f P Q g _ F n,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← HomologicalComplex.comp_f, w, HomologicalComplex.comp_f,
    CochainComplex.single₀_map_f_0]
#align category_theory.functor.right_derived_map_eq CategoryTheory.Functor.rightDerived_map_eq

def NatTrans.rightDerivedToHomotopyCategory {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    F.rightDerivedToHomotopyCategory ⟶ G.rightDerivedToHomotopyCategory :=
  whiskerLeft _ (NatTrans.mapHomotopyCategory α (ComplexShape.up ℕ))

lemma InjectiveResolution.rightDerivedToHomotopyCategory_app_eq
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : InjectiveResolution X) :
    (NatTrans.rightDerivedToHomotopyCategory α).app X =
      (P.isoRightDerivedToHomotopyCategoryObj F).hom ≫
        (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex α _).app P.cocomplex) ≫
          (P.isoRightDerivedToHomotopyCategoryObj G).inv := by
  rw [← cancel_mono (P.isoRightDerivedToHomotopyCategoryObj G).hom, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp [isoRightDerivedToHomotopyCategoryObj, Functor.mapHomotopyCategoryFactors,
    NatTrans.rightDerivedToHomotopyCategory]
  rw [Category.assoc]
  erw [Category.id_comp, Category.comp_id]
  obtain ⟨β, hβ⟩ := (HomotopyCategory.quotient _ _).map_surjective (iso P).hom
  rw [← hβ]
  dsimp
  simp only [← Functor.map_comp, NatTrans.mapHomologicalComplex_naturality]
  rfl

@[simp]
lemma NatTrans.rightDerivedToHomotopyCategory_id (F : C ⥤ D) [F.Additive] :
    NatTrans.rightDerivedToHomotopyCategory (𝟙 F) = 𝟙 _ := rfl

@[simp]
lemma NatTrans.rightDerivedToHomotopyCategory_comp {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)
    [F.Additive] [G.Additive] [H.Additive] :
    NatTrans.rightDerivedToHomotopyCategory (α ≫ β) =
      NatTrans.rightDerivedToHomotopyCategory α ≫
        NatTrans.rightDerivedToHomotopyCategory β := rfl

/-- The natural transformation between right-derived functors induced by a natural transformation.-/
def NatTrans.rightDerived {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) :
    F.rightDerived n ⟶ G.rightDerived n :=
  whiskerRight (NatTrans.rightDerivedToHomotopyCategory α) _
#align category_theory.nat_trans.right_derived CategoryTheory.NatTrans.rightDerived

@[simp]
theorem NatTrans.rightDerived_id (F : C ⥤ D) [F.Additive] (n : ℕ) :
    NatTrans.rightDerived (𝟙 F) n = 𝟙 (F.rightDerived n) := by
  dsimp only [rightDerived]
  simp only [rightDerivedToHomotopyCategory_id, whiskerRight_id']
  rfl
#align category_theory.nat_trans.right_derived_id CategoryTheory.NatTrans.rightDerived_id

@[simp, nolint simpNF]
theorem NatTrans.rightDerived_comp {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (α : F ⟶ G) (β : G ⟶ H) (n : ℕ) :
    NatTrans.rightDerived (α ≫ β) n = NatTrans.rightDerived α n ≫ NatTrans.rightDerived β n := by
  simp [NatTrans.rightDerived]
#align category_theory.nat_trans.right_derived_comp CategoryTheory.NatTrans.rightDerived_comp

/-- A component of the natural transformation between right-derived functors can be computed
using a chosen injective resolution. -/
lemma InjectiveResolution.rightDerived_app_eq
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : InjectiveResolution X)
    (n : ℕ) : (NatTrans.rightDerived α n).app X =
      (P.isoRightDerivedObj F n).hom ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map
        ((NatTrans.mapHomologicalComplex α _).app P.cocomplex) ≫
        (P.isoRightDerivedObj G n).inv := by
  dsimp [NatTrans.rightDerived, isoRightDerivedObj]
  rw [InjectiveResolution.rightDerivedToHomotopyCategory_app_eq α P,
    Functor.map_comp, Functor.map_comp, Category.assoc]
  erw [← (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).hom.naturality_assoc
    ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app P.cocomplex)]
  simp only [Functor.comp_map, Iso.hom_inv_id_app_assoc]

def InjectiveResolution.toRightDerivedZero' {X : C}
    (P : InjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.obj X ⟶ ((F.mapHomologicalComplex _).obj P.cocomplex).homology 0 := by
  refine' _ ≫ (CochainComplex.isoHomologyπ₀ _).hom
  exact HomologicalComplex.liftCycles _ (F.map (P.ι.f 0)) 1 (by simp) (by
    dsimp
    rw [← F.map_comp, HomologicalComplex.Hom.comm, CochainComplex.single₀_obj_X_d, zero_comp,
      F.map_zero])

@[reassoc (attr := simp)]
lemma InjectiveResolution.toRightDerivedZero'_comp_isoHomology₀_inv_comp_iCycles {X : C}
    (P : InjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    P.toRightDerivedZero' F ≫ (CochainComplex.isoHomologyπ₀ _).inv ≫
      HomologicalComplex.iCycles _ _ = F.map (P.ι.f 0) := by
  dsimp only [toRightDerivedZero' ]
  simp

@[reassoc]
def InjectiveResolution.toRightDerivedZero'_naturality {X Y : C} (f : X ⟶ Y)
    (P : InjectiveResolution X) (Q : InjectiveResolution Y)
    (φ : P.cocomplex ⟶ Q.cocomplex) (comm : P.ι.f 0 ≫ φ.f 0 = f ≫ Q.ι.f 0)
    (F : C ⥤ D) [F.Additive] :
    F.map f ≫ Q.toRightDerivedZero' F =
      P.toRightDerivedZero' F ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ 0).map φ := by
  simp only [← cancel_mono (CochainComplex.isoHomologyπ₀ _).inv,
    ← cancel_mono (HomologicalComplex.iCycles _ _), Category.assoc,
    toRightDerivedZero'_comp_isoHomology₀_inv_comp_iCycles, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map, CochainComplex.isoHomologyπ₀_inv_naturality,
    HomologicalComplex.cyclesMap_i, Functor.mapHomologicalComplex_map_f,
    toRightDerivedZero'_comp_isoHomology₀_inv_comp_iCycles_assoc, ← F.map_comp, comm]

instance (F : C ⥤ D) [F.Additive] (X : C) [Injective X] :
    IsIso ((InjectiveResolution.self X).toRightDerivedZero' F) := by
  dsimp [InjectiveResolution.toRightDerivedZero',
    InjectiveResolution.self]
  refine @IsIso.comp_isIso  _ _ _ _ _ _ _ ?_ inferInstance
  rw [CochainComplex.isIso_liftCycles_iff]
  constructor
  · infer_instance
  · rw [ShortComplex.exact_iff_epi]
    · dsimp
      simp only [Functor.map_id]
      infer_instance
    · simp

def Functor.toRightDerivedZero (F : C ⥤ D) [F.Additive] :
    F ⟶ F.rightDerived 0 where
  app X := (injectiveResolution' X).toRightDerivedZero' F ≫
    (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) 0).inv.app _
  naturality {X Y} f := by
    rw [InjectiveResolution.toRightDerivedZero'_naturality_assoc f
      (injectiveResolution' X) (injectiveResolution' Y)
      (injectiveResolution.desc f) (by simp) F, Category.assoc,
      NatTrans.naturality]
    rfl

lemma InjectiveResolution.toRightDerivedZero_eq
    {X : C} (I : InjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.toRightDerivedZero.app X =
      I.toRightDerivedZero' F ≫ (I.isoRightDerivedObj F 0).inv := by
  dsimp [Functor.toRightDerivedZero, isoRightDerivedObj]
  have h₁ : (I.isoRightDerivedToHomotopyCategoryObj F).hom =
    (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map (desc (𝟙 X) _ _) :=
    Category.comp_id _
  have h₂ := InjectiveResolution.toRightDerivedZero'_naturality
    (𝟙 X) (injectiveResolution' X) I (desc (𝟙 X) _ _) (by
      rw [← HomologicalComplex.comp_f, desc_commutes, Functor.map_id,
        Category.id_comp, Category.id_comp]) F
  rw [F.map_id, Category.id_comp] at h₂
  rw [← cancel_mono ((HomotopyCategory.homologyFunctor _ _ 0).map (I.isoRightDerivedToHomotopyCategoryObj F).hom),
    Category.assoc, Category.assoc, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    Functor.map_id, Category.comp_id, h₂, h₁, Category.assoc]
  erw [← NatTrans.naturality]
  rfl

-- this replaced the previous `Functor.rightDerivedObjInjectiveZero` which
-- is generalized as `Functor.rightDerivedZeroIsoSelf` for all `X` when
-- `F` preserves finite limits
instance (F : C ⥤ D) [F.Additive] (X : C) [Injective X] :
    IsIso (F.toRightDerivedZero.app X) := by
  rw [(InjectiveResolution.self X).toRightDerivedZero_eq F]
  infer_instance

section

variable (F : C ⥤ D) [F.Additive]

instance [PreservesFiniteLimits F] {X : C} (P : InjectiveResolution X) :
    IsIso (P.toRightDerivedZero' F) := by
  dsimp [InjectiveResolution.toRightDerivedZero']
  refine @IsIso.comp_isIso  _ _ _ _ _ _ _ ?_ inferInstance
  rw [CochainComplex.isIso_liftCycles_iff]
  constructor
  · infer_instance
  · let S : ShortComplex C := ShortComplex.mk (P.ι.f 0) (P.cocomplex.d 0 1) (by simp)
    -- this exactness property should be moved to Abelian/InjectiveResolution.lean
    have hS : S.Exact := by
      have : QuasiIsoAt P.ι 0 := inferInstance
      rw [CochainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros] at this
      rotate_left
      · rfl
      · rfl
      · simp
      exact this.2
    exact hS.map_of_mono_of_preservesKernel F
      (by dsimp; infer_instance) inferInstance

instance [PreservesFiniteLimits F] : IsIso F.toRightDerivedZero := by
  have : ∀ X, IsIso (F.toRightDerivedZero.app X) := fun X => by
    dsimp [Functor.toRightDerivedZero]
    infer_instance
  apply NatIso.isIso_of_isIso_app

variable [PreservesFiniteLimits F]

@[simps! inv]
def Functor.rightDerivedZeroIsoSelf : F.rightDerived 0 ≅ F :=
  (asIso F.toRightDerivedZero).symm

@[reassoc (attr := simp)]
lemma Functor.rightDerivedZeroIsoSelf_hom_inv_id :
    F.rightDerivedZeroIsoSelf.hom ≫ F.toRightDerivedZero = 𝟙 _ :=
  F.rightDerivedZeroIsoSelf.hom_inv_id

@[reassoc (attr := simp)]
lemma Functor.rightDerivedZeroIsoSelf_inv_hom_id :
    F.toRightDerivedZero ≫ F.rightDerivedZeroIsoSelf.hom = 𝟙 _ :=
  F.rightDerivedZeroIsoSelf.inv_hom_id

@[reassoc (attr := simp)]
lemma Functor.rightDerivedZeroIsoSelf_hom_inv_id_app (X : C) :
    F.rightDerivedZeroIsoSelf.hom.app X ≫ F.toRightDerivedZero.app X = 𝟙 _ :=
  F.rightDerivedZeroIsoSelf.hom_inv_id_app X

@[reassoc (attr := simp)]
lemma Functor.rightDerivedZeroIsoSelf_inv_hom_id_app (X : C) :
    F.toRightDerivedZero.app X ≫ F.rightDerivedZeroIsoSelf.hom.app X = 𝟙 _ :=
  F.rightDerivedZeroIsoSelf.inv_hom_id_app X

end

end CategoryTheory
