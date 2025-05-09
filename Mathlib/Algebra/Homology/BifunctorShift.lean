/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.TotalComplexShift

/-!
# Behavior of the action of a bifunctor on cochain complexes with respect to shifts

In this file, given cochain complexes `K₁ : CochainComplex C₁ ℤ`, `K₂ : CochainComplex C₂ ℤ` and
a functor `F : C₁ ⥤ C₂ ⥤ D`, we define an isomorphism of cochain complexes in `D`:
- `CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F x` of type
`mapBifunctor (K₁⟦x⟧) K₂ F ≅ (mapBifunctor K₁ K₂ F)⟦x⟧` for `x : ℤ`.
- `CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F y` of type
`mapBifunctor K₁ (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦y⟧` for `y : ℤ`.

In the lemma `CochainComplex.mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso`, we obtain
that the two ways to deduce an isomorphism
`mapBifunctor (K₁⟦x⟧) (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦x + y⟧` differ by the sign
`(x * y).negOnePow`.

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]

namespace CochainComplex

section

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂]
  (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]

/-- The condition that `((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂` has
a total cochain complex. -/
abbrev HasMapBifunctor := HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)

/-- Given `K₁ : CochainComplex C₁ ℤ`, `K₂ : CochainComplex C₂ ℤ`,
a bifunctor `F : C₁ ⥤ C₂ ⥤ D`, this `mapBifunctor K₁ K₂ F : CochainComplex D ℤ`
is the total complex of the bicomplex obtained by applying `F` to `K₁` and `K₂`. -/
noncomputable abbrev mapBifunctor [HasMapBifunctor K₁ K₂ F] : CochainComplex D ℤ :=
  HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up ℤ)

/-- The inclusion of a summand `(F.obj (K₁.X n₁)).obj (K₂.X n₂) ⟶ (mapBifunctor K₁ K₂ F).X n`
of the total cochain complex when `n₁ + n₂ = n`. -/
noncomputable abbrev ιMapBifunctor [HasMapBifunctor K₁ K₂ F] (n₁ n₂ n : ℤ) (h : n₁ + n₂ = n) :
    (F.obj (K₁.X n₁)).obj (K₂.X n₂) ⟶ (mapBifunctor K₁ K₂ F).X n :=
  HomologicalComplex.ιMapBifunctor K₁ K₂ F _ _ _ _ h

end

section

variable [Preadditive C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ : CochainComplex C₁ ℤ) (K₂ K₂' : CochainComplex C₂ ℤ) (φ : K₂ ⟶ K₂')
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms] (x : ℤ)
  [HasMapBifunctor K₁ K₂ F] [HasMapBifunctor K₁ K₂' F]

/-- Auxiliary definition for `mapBifunctorShift₁Iso`. -/
@[simps! hom_f_f inv_f_f]
def mapBifunctorHomologicalComplexShift₁Iso :
    ((F.mapBifunctorHomologicalComplex _ _).obj (K₁⟦x⟧)).obj K₂ ≅
    (HomologicalComplex₂.shiftFunctor₁ D x).obj
      (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intros
    ext
    dsimp
    simp only [Linear.comp_units_smul, id_comp, Functor.map_units_smul,
      NatTrans.app_units_zsmul, comp_id])

instance : HasMapBifunctor (K₁⟦x⟧) K₂ F :=
  HomologicalComplex₂.hasTotal_of_iso (mapBifunctorHomologicalComplexShift₁Iso K₁ K₂ F x).symm _

/-- The canonical isomorphism `mapBifunctor (K₁⟦x⟧) K₂ F ≅ (mapBifunctor K₁ K₂ F)⟦x⟧`.
This isomorphism does not involve signs. -/
noncomputable def mapBifunctorShift₁Iso :
    mapBifunctor (K₁⟦x⟧) K₂ F ≅ (mapBifunctor K₁ K₂ F)⟦x⟧ :=
  HomologicalComplex₂.total.mapIso (mapBifunctorHomologicalComplexShift₁Iso K₁ K₂ F x) _ ≪≫
    (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂).totalShift₁Iso x

open HomologicalComplex

-- naturality with respect to `K₂`
variable {K₂ K₂'} in
@[reassoc (attr := simp)]
lemma mapBifunctorShift₁Iso_hom_naturality₂ :
    mapBifunctorMap (𝟙 (K₁⟦x⟧)) φ F _ ≫ (mapBifunctorShift₁Iso K₁ K₂' F x).hom =
    (mapBifunctorShift₁Iso K₁ K₂ F x).hom ≫ (mapBifunctorMap (𝟙 K₁) φ F _)⟦x⟧' := by
  ext n p q h
  simp [mapBifunctorShift₁Iso, HomologicalComplex₂.ι_totalShift₁Iso_hom_f _ _ _ _ _ _ _ rfl _ rfl,
   HomologicalComplex₂.ι_totalShift₁Iso_hom_f_assoc _ _ _ _ _ _ _ rfl _ rfl]

end

section

variable [HasZeroMorphisms C₁] [Preadditive C₂] [Preadditive D]
  (K₁ K₁' : CochainComplex C₁ ℤ) (φ : K₁ ⟶ K₁') (K₂ : CochainComplex C₂ ℤ)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F.obj X₁).Additive] (y : ℤ)
  [HasMapBifunctor K₁ K₂ F] [HasMapBifunctor K₁' K₂ F]

/-- Auxiliary definition for `mapBifunctorShift₂Iso`. -/
@[simps! hom_f_f inv_f_f]
def mapBifunctorHomologicalComplexShift₂Iso :
    ((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj (K₂⟦y⟧) ≅
    (HomologicalComplex₂.shiftFunctor₂ D y).obj
      (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i₁ => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)) (by
      intros
      ext
      dsimp
      simp only [id_comp, comp_id])

instance : HasMapBifunctor K₁ (K₂⟦y⟧) F :=
  HomologicalComplex₂.hasTotal_of_iso (mapBifunctorHomologicalComplexShift₂Iso K₁ K₂ F y).symm _

/-- The canonical isomorphism `mapBifunctor K₁ (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦y⟧`.
This isomorphism involves signs: on the summand `(F.obj (K₁.X p)).obj (K₂.X q)`, it is given
by the multiplication by `(p * y).negOnePow`. -/
noncomputable def mapBifunctorShift₂Iso :
    mapBifunctor K₁ (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦y⟧ :=
  HomologicalComplex₂.total.mapIso
    (mapBifunctorHomologicalComplexShift₂Iso K₁ K₂ F y) (ComplexShape.up ℤ) ≪≫
    (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂).totalShift₂Iso y

open HomologicalComplex in
variable {K₁ K₁'} in
@[reassoc (attr := simp)]
lemma mapBifunctorShift₂Iso_hom_naturality₁ :
    mapBifunctorMap φ (𝟙 (K₂⟦y⟧)) F _ ≫ (mapBifunctorShift₂Iso K₁' K₂ F y).hom =
      (mapBifunctorShift₂Iso K₁ K₂ F y).hom ≫ (mapBifunctorMap φ (𝟙 (K₂)) F _)⟦y⟧' := by
  ext n p q h
  simp [mapBifunctorShift₂Iso, HomologicalComplex₂.ι_totalShift₂Iso_hom_f _ _ _ _ _ _ _ rfl _ rfl,
    HomologicalComplex₂.ι_totalShift₂Iso_hom_f_assoc _ _ _ _ _ _ _ rfl _ rfl]

end

section

variable [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).Additive] (x y : ℤ)
  [HasMapBifunctor K₁ K₂ F]

lemma mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso :
    mapBifunctorShift₁Iso K₁ (K₂⟦y⟧) F x ≪≫
      (CategoryTheory.shiftFunctor _ x).mapIso (mapBifunctorShift₂Iso K₁ K₂ F y) =
      (x * y).negOnePow • (mapBifunctorShift₂Iso (K₁⟦x⟧) K₂ F y ≪≫
        (CategoryTheory.shiftFunctor _ y).mapIso (mapBifunctorShift₁Iso K₁ K₂ F x) ≪≫
          (shiftFunctorComm (CochainComplex D ℤ) x y).app _) := by
  ext1
  dsimp [mapBifunctorShift₁Iso, mapBifunctorShift₂Iso]
  rw [Functor.map_comp, Functor.map_comp, assoc, assoc, assoc,
    ← HomologicalComplex₂.totalShift₁Iso_hom_naturality_assoc,
    HomologicalComplex₂.totalShift₁Iso_hom_totalShift₂Iso_hom,
    ← HomologicalComplex₂.totalShift₂Iso_hom_naturality_assoc,
    Linear.comp_units_smul, Linear.comp_units_smul,
    smul_left_cancel_iff,
    ← HomologicalComplex₂.total.map_comp_assoc,
    ← HomologicalComplex₂.total.map_comp_assoc,
    ← HomologicalComplex₂.total.map_comp_assoc]
  congr 2
  ext a b
  dsimp [HomologicalComplex₂.shiftFunctor₁₂CommIso]
  simp only [id_comp]

end

section

noncomputable def bifunctorMapHomologicalComplexObjShiftIso
    [Preadditive C₁] [HasZeroMorphisms C₂] [Preadditive D]
    (F : C₁ ⥤ C₂ ⥤ D)
    [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]
      [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]
    (K₁ : CochainComplex C₁ ℤ) (n : ℤ) :
    (F.bifunctorMapHomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj (K₁⟦n⟧) ≅
      (F.bifunctorMapHomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj K₁ ⋙
        shiftFunctor _ n :=
  NatIso.ofComponents (fun K₂ ↦ mapBifunctorShift₁Iso K₁ K₂ F n)

noncomputable def bifunctorMapHomologicalComplexFlipObjShiftIso
    [HasZeroMorphisms C₁] [Preadditive C₂] [Preadditive D]
    (F : C₁ ⥤ C₂ ⥤ D)
    [F.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F.obj X₁).Additive]
      [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]
    (K₂ : CochainComplex C₂ ℤ) (n : ℤ) :
    (F.bifunctorMapHomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj (K₂⟦n⟧) ≅
      (F.bifunctorMapHomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj K₂ ⋙
        shiftFunctor _ n :=
  NatIso.ofComponents (fun K₁ ↦ mapBifunctorShift₂Iso K₁ K₂ F n)

end

end CochainComplex
