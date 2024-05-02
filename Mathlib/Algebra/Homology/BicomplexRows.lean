import Mathlib.Algebra.Homology.BicomplexColumns

open CategoryTheory Limits ComplexShape

namespace HomologicalComplex₂

section

variable (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι₁ ι₂ : Type*} [DecidableEq ι₂] (c₁ : ComplexShape ι₁) (c₂ : ComplexShape ι₂)

noncomputable abbrev singleRow (i₂ : ι₂) :
    HomologicalComplex C c₁ ⥤ HomologicalComplex₂ C c₁ c₂ :=
  (HomologicalComplex.single C c₂ i₂).mapHomologicalComplex c₁

variable {C c₁}

lemma isZero_singleRow_X_X (K : HomologicalComplex C c₁)
    (i₁ : ι₁) (i₂ i₂' : ι₂) (h : i₂' ≠ i₂) :
    IsZero ((((singleRow C c₁ c₂ i₂).obj K).X i₁).X i₂') :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ h

noncomputable def singleRowXXIso (K : HomologicalComplex C c₁) (i₁ : ι₁) (i₂ : ι₂) :
    (((singleRow C c₁ c₂ i₂).obj K).X i₁).X i₂ ≅ K.X i₁ :=
  HomologicalComplex.singleObjXSelf _ _ _

@[reassoc]
lemma singleRow_obj_d_f (K : HomologicalComplex C c₁) (i₁ i₁' : ι₁) (i₂ : ι₂) :
    (((singleRow C c₁ c₂ i₂).obj K).d i₁ i₁').f i₂ =
      (singleRowXXIso c₂ K i₁ i₂).hom ≫ K.d i₁ i₁' ≫
        (singleRowXXIso c₂ K i₁' i₂).inv := by
    apply HomologicalComplex.single_map_f_self

end

section

variable (C : Type*) [Category C] [Preadditive C] [HasZeroObject C]
  {ι₁ ι₂ ι : Type*} [DecidableEq ι₂] [DecidableEq ι] (c₁ : ComplexShape ι₁) (c₂ : ComplexShape ι₂)
  (K : HomologicalComplex C c₁) (i₂ : ι₂) (c : ComplexShape ι)
  [TotalComplexShape c₁ c₂ c]
  [((singleRow C c₁ c₂ i₂).obj K).HasTotal c]

@[simp]
lemma singleRow_d₁ (x x' : ι₁) (hx : c₁.Rel x x') (n : ι)
    (hn : π c₁ c₂ c (x', i₂) = n) :
    ((singleRow C c₁ c₂ i₂).obj K).d₁ c x i₂ n =
      ε₁ c₁ c₂ c (x, i₂) • (singleRowXXIso c₂ K x i₂).hom ≫ K.d x x' ≫
        (singleRowXXIso c₂ K x' i₂).inv ≫
        ((singleRow C c₁ c₂ i₂).obj K).ιTotal c x' i₂ n hn := by
  simp [d₁_eq _ _ hx _ _ hn, ← singleRow_obj_d_f_assoc]

@[simp]
lemma singleRow_d₂ (x : ι₁) (y : ι₂) (n : ι) :
    ((singleRow C c₁ c₂ i₂).obj K).d₂ c x y n = 0 := by
  by_cases hy : c₂.Rel y (c₂.next y)
  · by_cases hx' : π c₁ c₂ c (x, c₂.next y) = n
    · rw [d₂_eq _ _ _ hy _ hx']
      simp
    · rw [d₂_eq_zero' _ _ _ hy _ hx']
  · rw [d₂_eq_zero _ _ _ _ _ hy]

end

end HomologicalComplex₂
