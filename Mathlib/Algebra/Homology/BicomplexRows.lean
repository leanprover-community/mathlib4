import Mathlib.Algebra.Homology.BicomplexColumns

open CategoryTheory Limits ComplexShape Category

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

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

@[simp]
noncomputable def cofanSingleRowObjTotal (K : CochainComplex C ℤ) (x y n : ℤ) (h : x + y = n):
  GradedObject.CofanMapObjFun (((singleRow C (up ℤ) (up ℤ) y).obj K).toGradedObject)
    (π (up ℤ) (up ℤ) (up ℤ)) n :=
  cofanOfIsZeroButOne  _ ⟨⟨x, y⟩, h⟩ (by
    rintro ⟨⟨x', y'⟩, hxy⟩ h'
    apply isZero_singleRow_X_X
    simp at hxy h'
    omega)

noncomputable def isColimitCofanSingleRowObjTotal
    (K : CochainComplex C ℤ) (x y n : ℤ) (h : x + y = n) :
    IsColimit (cofanSingleRowObjTotal K x y n h) := by
  apply isColimitCofanOfIsZeroButOne

instance (K : CochainComplex C ℤ) (y : ℤ) :
    ((singleRow C (up ℤ) (up ℤ) y).obj K).HasTotal (up ℤ) := fun n =>
  ⟨_, isColimitCofanSingleRowObjTotal K (n - y) y n (by omega)⟩

noncomputable def singleRowObjTotalXIso
    (K : CochainComplex C ℤ) (x y n : ℤ) (h : x + y = n) :
    (((singleRow C (up ℤ) (up ℤ) y).obj K).total (up ℤ)).X n ≅ K.X x :=
  ((cofanSingleRowObjTotal K x y n h).iso
    (isColimitCofanSingleRowObjTotal K x y n h)).symm ≪≫ singleRowXXIso (up ℤ) K x y

lemma singleRowObjTotalXIso_inv
    (K : CochainComplex C ℤ) (x y n : ℤ) (h : x + y = n) :
    (singleRowObjTotalXIso K x y n h).inv =
      (singleRowXXIso (up ℤ) K x y).inv ≫
        ((singleRow C (up ℤ) (up ℤ) y).obj K).ιTotal (up ℤ) x y n h := by
  rfl

@[reassoc]
lemma singleRow_ιTotal
    (L : CochainComplex C ℤ) (x y n : ℤ) (h : x + y = n) :
    ((singleRow C (up ℤ) (up ℤ) y).obj L).ιTotal (up ℤ) x y n h =
      (singleRowXXIso (up ℤ) L x y).hom ≫(singleRowObjTotalXIso L x y n h).inv := by
  rw [singleRowObjTotalXIso_inv, Iso.hom_inv_id_assoc]

noncomputable def singleRowObjTotal (L : CochainComplex C ℤ) (y y' : ℤ) (h : y + y' = 0) :
    ((singleRow C (up ℤ) (up ℤ) y).obj L).total (up ℤ) ≅ L⟦y'⟧ :=
  Iso.symm (HomologicalComplex.Hom.isoOfComponents
    (fun n => (Int.negOnePow (n • y) • singleRowObjTotalXIso L _ _ _ (by dsimp; omega)).symm) (by
      intro x x' h'
      dsimp at h' ⊢
      simp [singleRowObjTotalXIso_inv]
      rw [singleRow_d₁ _ _ _ _ _ _ _ (x' + y') (by dsimp; omega) _ (by dsimp; omega)]
      dsimp
      obtain rfl : y = -y' := by omega
      simp only [mul_neg, Int.negOnePow_neg, one_smul, Iso.inv_hom_id_assoc, smul_smul]
      subst h'
      congr 1
      rw [add_mul, Int.negOnePow_add, one_mul, mul_assoc, Int.units_mul_self, mul_one]))

@[reassoc (attr := simp)]
noncomputable def singleRowObjTotal_inv_naturality {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (y y' : ℤ) (h : y + y' = 0) :
    (singleRowObjTotal K y y' h).inv ≫ total.map ((singleRow C (up ℤ) (up ℤ) y).map φ) (up ℤ) =
      φ⟦y'⟧' ≫ (singleRowObjTotal L y y' h).inv := by
  ext n
  dsimp [singleRowObjTotal]
  rw [Int.units_inv_eq_self, Linear.units_smul_comp, Linear.comp_units_smul,
    smul_left_cancel_iff]
  rw [singleRowObjTotalXIso_inv, singleRowObjTotalXIso_inv, assoc, ιTotal_map]
  simp [HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, singleRowXXIso]

@[reassoc (attr := simp)]
noncomputable def singleRowObjTotal_hom_naturality {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (y y' : ℤ) (h : y + y' = 0) :
    total.map ((singleRow C (up ℤ) (up ℤ) y).map φ) (up ℤ) ≫
      (singleRowObjTotal L y y' h).hom =
      (singleRowObjTotal K y y' h).hom ≫ φ⟦y'⟧' := by
  rw [← cancel_epi (singleRowObjTotal K y y' h).inv,
    singleRowObjTotal_inv_naturality_assoc, Iso.inv_hom_id, comp_id, Iso.inv_hom_id_assoc]

noncomputable def singleRow₀ObjTotal (L : CochainComplex C ℤ) :
    ((singleRow C (up ℤ) (up ℤ) 0).obj L).total (up ℤ) ≅ L :=
  singleRowObjTotal L 0 0 (add_zero 0) ≪≫ (shiftFunctorZero _ _).app L

end HomologicalComplex₂
