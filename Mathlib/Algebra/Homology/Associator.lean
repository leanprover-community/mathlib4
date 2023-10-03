import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.CategoryTheory.GradedObject.Trifunctor

open CategoryTheory Limits Category Preadditive

variable (C C₁ C₂ C₃ C₁₂ C₂₃ : Type*) [Category C] [Category C₁] [Category C₂] [Category C₃]
  [Category C₁₂] [Category C₂₃]
  {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}

abbrev HomologicalComplex₃ [HasZeroMorphisms C] (c₁ : ComplexShape I₁)
  (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃) :=
  HomologicalComplex (HomologicalComplex (HomologicalComplex C c₃) c₂) c₁

namespace HomologicalComplex₃

variable {C} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₃ : ComplexShape I₃}

-- `[HasZeroMorphisms C]` is sufficient, but we use `Functor.mapHomologicalComplex` which has a `Preadditive C` assumption
set_option maxHeartbeats 400000 in
@[simps]
def rotate [Preadditive C] (K : HomologicalComplex₃ C c₁ c₂ c₃) :
    HomologicalComplex₃ C c₃ c₁ c₂ where
  X i₃ :=
    { X := fun i₁ => ((HomologicalComplex.eval C c₃ i₃).mapHomologicalComplex c₂).obj (K.X i₁)
      d := fun i₁ i₁' => ((HomologicalComplex.eval C c₃ i₃).mapHomologicalComplex c₂).map (K.d i₁ i₁')
      shape := fun i₁ i₁' h => by
        dsimp
        rw [K.shape _ _ h, Functor.map_zero]
      d_comp_d' := fun i₁ i₁' i₁'' _ _ => by
        dsimp
        rw [← Functor.map_comp, K.d_comp_d, Functor.map_zero] }
  d i₃ i₃' :=
    { f := fun i₁ => { f := fun i₂ => ((K.X i₁).X i₂).d i₃ i₃' } }
  shape i₃ i₃' h := by
    ext i₁ i₂
    exact ((K.X i₁).X i₂).shape _ _ h
  d_comp_d' i₃ i₃' i₃'' _ _ := by
    ext i₁ i₂
    apply ((K.X i₁).X i₂).d_comp_d

end HomologicalComplex₃

section

variable [Preadditive C] {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₃ : ComplexShape I₃}
  (K : HomologicalComplex₃ C c₁ c₂ c₃)
  (c₁₂ : ComplexShape I₁₂) [DecidableEq I₁₂]
  (c₂₃ : ComplexShape I₂₃) [DecidableEq I₂₃]
  (c : ComplexShape J) [DecidableEq J]

namespace HomologicalComplex₃

variable {C}

section

variable [TotalComplexShape c₂ c₃ c₂₃]

abbrev HasTotal₂₃ := ∀ (i₁ : I₁), HomologicalComplex₂.HasTotal (K.X i₁) c₂₃

variable [K.HasTotal₂₃ c₂₃]

noncomputable def total₂₃ : HomologicalComplex₂ C c₁ c₂₃ where
  X i₁ := HomologicalComplex₂.total (K.X i₁) c₂₃
  d i₁ i₁' := HomologicalComplex₂.totalMap (K.d i₁ i₁') c₂₃
  shape i₁ i₁' h := by
    dsimp
    rw [K.shape _ _ h, HomologicalComplex₂.totalMap_zero]
  d_comp_d' i₁ i₁' i₁'' _ _ := by
    dsimp
    rw [← HomologicalComplex₂.totalMap_comp, K.d_comp_d, HomologicalComplex₂.totalMap_zero]

end

section

variable [TotalComplexShape c₁ c₂ c₁₂]

abbrev HasTotal₁₂ := ∀ (i₃ : I₃), HomologicalComplex₂.HasTotal (K.rotate.X i₃) c₁₂

variable [HasTotal₁₂ K c₁₂]

noncomputable def total₁₂ : HomologicalComplex₂ C c₁₂ c₃ := (K.rotate.total₂₃ c₁₂).flip

end

section

variable
  [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₁₂ c₃ c]
  [TotalComplexShape c₂ c₃ c₂₃] [TotalComplexShape c₁ c₂₃ c]
  [HasTotal₂₃ K c₂₃] [(K.total₂₃ c₂₃).HasTotal c]
  [HasTotal₁₂ K c₁₂] [(K.total₁₂ c₁₂).HasTotal c]
  [ComplexShape.Associator c₁ c₂ c₃ c₁₂ c₂₃ c]

noncomputable def ιTotal' (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    ((K.X i₁).X i₂).X i₃ ⟶ ((K.total₁₂ c₁₂).total c).X j :=
  HomologicalComplex₂.ιTotal ((K.rotate).X i₃) c₁₂ i₁ i₂ _ rfl ≫ (K.total₁₂ c₁₂).ιTotal c (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) i₃ j h

@[reassoc]
lemma ιTotal'_eq (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j)
    (i₁₂ : I₁₂) (h' : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) : K.ιTotal' c₁₂ c i₁ i₂ i₃ j h =
    HomologicalComplex₂.ιTotal ((K.rotate).X i₃) c₁₂ i₁ i₂ i₁₂ h' ≫ (K.total₁₂ c₁₂).ιTotal c i₁₂ i₃ j (by rw [← h, ← h']) := by
  subst h'
  rfl

noncomputable def ιTotal (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j) :
    ((K.X i₁).X i₂).X i₃ ⟶ ((K.total₂₃ c₂₃).total c).X j :=
  HomologicalComplex₂.ιTotal (K.X i₁) c₂₃ i₂ i₃ _ rfl ≫ (K.total₂₃ c₂₃).ιTotal c i₁ (ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩) j h

@[reassoc]
lemma ιTotal_eq (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j)
    (i₂₃ : I₂₃) (h' : ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩ = i₂₃) :
    K.ιTotal c₂₃ c i₁ i₂ i₃ j h =
      HomologicalComplex₂.ιTotal (K.X i₁) c₂₃ i₂ i₃ i₂₃ h' ≫ (K.total₂₃ c₂₃).ιTotal c i₁ i₂₃ j (by rw [← h, ←h']) := by
  subst h'
  rfl

noncomputable def totalXAssociator (j : J) :
    ((K.total₁₂ c₁₂).total c).X j ≅ ((K.total₂₃ c₂₃).total c).X j where
  hom := HomologicalComplex₂.descTotal _ _
    (fun i₁₂ i₃ h => HomologicalComplex₂.descTotal _ _
      (fun i₁ i₂ h' => K.ιTotal c₂₃ c i₁ i₂ i₃ j (by rw [← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c, h', h])))
  inv := HomologicalComplex₂.descTotal _ _
    (fun i₁ i₂₃ h => HomologicalComplex₂.descTotal _ _
      (fun i₂ i₃ h' => K.ιTotal' c₁₂ c i₁ i₂ i₃ j (by rw [ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c, h', h])))
  hom_inv_id := by
    ext i₁₂ i₃ h
    apply HomologicalComplex₂.total_ext
    rintro i₁ i₂ h'
    rw [HomologicalComplex₂.ι_descTotal_assoc, HomologicalComplex₂.ι_descTotal_assoc, comp_id,
      K.ιTotal_eq c₂₃ c i₁ i₂ i₃ j (by rw [← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c, h', h]) _ rfl,
      assoc, HomologicalComplex₂.ι_descTotal, HomologicalComplex₂.ι_descTotal,
      K.ιTotal'_eq c₁₂ c i₁ i₂ i₃ j (by rw [h', h]) i₁₂ h']
  inv_hom_id := by
    ext i₁ i₂₃ h
    apply HomologicalComplex₂.total_ext
    rintro i₂ i₃ h'
    rw [HomologicalComplex₂.ι_descTotal_assoc, HomologicalComplex₂.ι_descTotal_assoc, comp_id,
      K.ιTotal'_eq c₁₂ c i₁ i₂ i₃ j (by rw [ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c, h',h]) _ rfl,
      assoc, HomologicalComplex₂.ι_descTotal, HomologicalComplex₂.ι_descTotal,
      K.ιTotal_eq c₂₃ c i₁ i₂ i₃ j (by rw [h', h]) i₂₃]

@[reassoc]
lemma ιTotal_total₁₂_d₃ (i₁ : I₁) (i₂ : I₂) (i₃ i₃' : I₃) (i₁₂ : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    HomologicalComplex₂.ιTotal ((rotate K).X i₃) c₁₂ i₁ i₂ i₁₂ h ≫ ((K.total₁₂ c₁₂).X i₁₂).d i₃ i₃' =
      (((rotate K).d i₃ i₃').f i₁).f i₂ ≫ HomologicalComplex₂.ιTotal ((rotate K).X i₃') c₁₂ i₁ i₂ i₁₂ h := by
  apply GradedObject.ι_mapMap

noncomputable def totalAssociator : (K.total₁₂ c₁₂).total c ≅ (K.total₂₃ c₂₃).total c :=
  HomologicalComplex.Hom.isoOfComponents (K.totalXAssociator c₁₂ c₂₃ c) (fun j j' _ => by
    ext i₁₂ i₃ h
    apply HomologicalComplex₂.total_ext
    intro i₁ i₂ h'
    dsimp [totalXAssociator]
    conv_lhs =>
      rw [HomologicalComplex₂.ι_descTotal_assoc, HomologicalComplex₂.ι_descTotal_assoc,
        K.ιTotal_eq c₂₃ c i₁ i₂ i₃ j _ _ rfl, assoc,
        HomologicalComplex₂.ιTotal_d, comp_add, comp_zsmul, comp_zsmul]
      dsimp
      erw [HomologicalComplex₂.ιTotal_d_assoc]
      rw [add_comp, zsmul_comp, zsmul_comp, zsmul_add, smul_smul, smul_smul, assoc, assoc]
    conv_rhs =>
      rw [HomologicalComplex₂.ιTotal_d_assoc, add_comp, comp_add, zsmul_comp, zsmul_comp,
        comp_zsmul, comp_zsmul, assoc, assoc]
      dsimp
      erw [HomologicalComplex₂.ιTotal_d_assoc]
      rw [add_comp, zsmul_comp, zsmul_comp, assoc, assoc, zsmul_add, smul_smul, smul_smul,
        add_assoc]
    congr 1
    · congr 1
      · rw [← h', ComplexShape.associator_ε₁_eq_mul c₁ c₂ c₃ c₁₂ c₂₃ c]
      · by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
        · dsimp
          erw [GradedObject.ι_mapMap_assoc]
          by_cases h₂ : ComplexShape.π c₁ c₂₃ c (ComplexShape.next c₁ i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j'
          · have h₃ : ComplexShape.π c₁₂ c₃ c ⟨c₁₂.next i₁₂, i₃⟩ = j' := by
              rw [← h', ComplexShape.next_π₁ c₂ c₁₂ h₁ i₂,
                ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c, h₂]
            have h₄ : ComplexShape.π c₁ c₂ c₁₂ (c₁.next i₁, i₂) = c₁₂.next i₁₂ := by
              rw [← ComplexShape.next_π₁ c₂ c₁₂ h₁ i₂, h']
            rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h₂,
              HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h₃,
              HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h₄,
              HomologicalComplex₂.ι_descTotal, HomologicalComplex₂.ι_descTotal]
            rfl
          · have h₃ : ComplexShape.π c₁₂ c₃ c ⟨c₁₂.next i₁₂, i₃⟩ ≠ j' := fun h₄ => h₂ (by
              rw [← h₄, ← h', ← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c,
                ComplexShape.next_π₁ c₂ c₁₂ h₁ i₂])
            rw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h₂, comp_zero, comp_zero,
              HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h₃, zero_comp, comp_zero, comp_zero]
        · rw [HomologicalComplex.shape _ _ _ h₁, HomologicalComplex.shape _ _ _ h₁,
            HomologicalComplex.zero_f, HomologicalComplex.zero_f, zero_comp, comp_zero,
            zero_comp]
    · congr 1
      · congr 1
        · rw [ComplexShape.associator_ε₂_ε₁ c₁ c₂ c₃ c₁₂ c₂₃ c, h']
        · by_cases h₁ : c₂.Rel i₂ (c₂.next i₂)
          · dsimp
            by_cases h₂ : ComplexShape.π c₁₂ c₃ c (c₁₂.next i₁₂, i₃) = j'
            · have h₃ : ComplexShape.π c₁ c₂₃ c (i₁, c₂₃.next (ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃))) = j' := by
                rw [ComplexShape.next_π₁ c₃ c₂₃ h₁ i₃, ← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c,
                  ← h₂, ← h', ComplexShape.next_π₂ c₁ c₁₂ i₁ h₁]
              have h₄ : ComplexShape.π c₁ c₂ c₁₂ (i₁, c₂.next i₂) = c₁₂.next i₁₂ := by
                rw [← h', ComplexShape.next_π₂ c₁ c₁₂ i₁ h₁]
              rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h₂,
                HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h₃,
                HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h₄,
                HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (ComplexShape.next_π₁ c₃ c₂₃ h₁ i₃).symm,
                HomologicalComplex₂.ι_descTotal, HomologicalComplex₂.ι_descTotal,
                ← K.ιTotal_eq c₂₃ c]
            · have h₃ : ComplexShape.π c₁ c₂₃ c (i₁, c₂₃.next (ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃))) ≠ j' := fun h₄ => h₂ (by
                rw [← h', ← h₄, ComplexShape.next_π₂ c₁ c₁₂ i₁ h₁,
                  ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c, ComplexShape.next_π₁ c₃ c₂₃ h₁ i₃])
              rw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h₂, zero_comp, comp_zero,
                HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h₃, comp_zero]
          · rw [HomologicalComplex.shape _ _ _ h₁, HomologicalComplex.shape _ _ _ h₁,
              HomologicalComplex.zero_f, zero_comp, zero_comp]
      · congr 1
        · rw [← h', ComplexShape.associator_ε₂_eq_mul c₁ c₂ c₃ c₁₂ c₂₃ c]
        · by_cases h₁ : c₃.Rel i₃ (c₃.next i₃)
          · dsimp
            by_cases h₂ : ComplexShape.π c₁ c₂₃ c (i₁, c₂₃.next (ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃))) = j'
            · have h₃ : ComplexShape.π c₁₂ c₃ c (i₁₂, c₃.next i₃) = j' := by
                rw [← h₂, ← h', ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c,
                  ComplexShape.next_π₂ c₂ c₂₃ i₂ h₁]
              rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h₂,
                HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h₃,
                HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (ComplexShape.next_π₂ c₂ c₂₃ i₂ h₁).symm,
                HomologicalComplex₂.ι_descTotal, ιTotal_total₁₂_d₃_assoc,
                HomologicalComplex₂.ι_descTotal, ← K.ιTotal_eq c₂₃ c]
              rfl
            · have h₃ : ComplexShape.π c₁₂ c₃ c (i₁₂, c₃.next i₃) ≠ j' := fun h₃ => h₂ (by
                rw [ComplexShape.next_π₂ c₂ c₂₃ i₂ h₁, ← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c,
                  ← h₃, h'])
              rw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h₂, comp_zero, comp_zero,
                HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h₃, zero_comp,
                comp_zero, comp_zero]
          · rw [HomologicalComplex.shape _ _ _ h₁, HomologicalComplex.shape _ _ _ h₁,
              zero_comp, zero_comp, comp_zero])

@[reassoc (attr := simp)]
def ι_totalAssociator_hom_f (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    K.ιTotal' c₁₂ c i₁ i₂ i₃ j h ≫ (K.totalAssociator c₁₂ c₂₃ c).hom.f j =
      K.ιTotal c₂₃ c i₁ i₂ i₃ j (by rw [← h, ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c]) := by
  dsimp [totalAssociator, totalXAssociator]
  rw [K.ιTotal'_eq c₁₂ c i₁ i₂ i₃ j h _ rfl, assoc,
    HomologicalComplex₂.ι_descTotal, HomologicalComplex₂.ι_descTotal]

@[reassoc (attr := simp)]
def ι_totalAssociator_inv_f (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j):
    K.ιTotal c₂₃ c i₁ i₂ i₃ j h ≫ (K.totalAssociator c₁₂ c₂₃ c).inv.f j =
      K.ιTotal' c₁₂ c i₁ i₂ i₃ j (by rw [← h, ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c]) := by
  dsimp [totalAssociator, totalXAssociator]
  rw [K.ιTotal_eq c₂₃ c i₁ i₂ i₃ j h _ rfl, assoc,
    HomologicalComplex₂.ι_descTotal, HomologicalComplex₂.ι_descTotal]

end

end HomologicalComplex₃

end

namespace CategoryTheory

namespace Functor

variable {C C₁ C₂ C₃}
variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms C₃] [HasZeroMorphisms C]
  (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C) (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃)
  [F.PreservesZeroMorphisms]
  [∀ (X₁ : C₁), PreservesZeroMorphisms (F.obj X₁)]
  [∀ (X₁ : C₁) (X₂ : C₂), PreservesZeroMorphisms ((F.obj X₁).obj X₂)]

@[simps]
def mapHomologicalComplex₃ObjObj (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂) :
      HomologicalComplex C₃ c₃ ⥤ HomologicalComplex₃ C c₁ c₂ c₃ where
  obj K₃ :=
    { X := fun i₁ => ((mapHomologicalComplex₂ (F.obj (K₁.X i₁)) c₂ c₃).obj K₂).obj K₃
      d := fun i₁ i₁' => ((NatTrans.mapHomologicalComplex₂ (F.map (K₁.d i₁ i₁')) c₂ c₃).app K₂).app K₃
      shape := fun i₁ i₁' h => by
        ext i₂ i₃
        dsimp [NatTrans.mapHomologicalComplex₂]
        rw [K₁.shape _ _ h, F.map_zero]
        rfl
      d_comp_d' := fun i₁ i₁' i₁'' _ _ => by
        ext i₂ i₃
        dsimp
        rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← F.map_comp, K₁.d_comp_d, F.map_zero]
        rfl }
  map {K₃ K₃'} φ :=
    { f := fun i₁ => ((mapHomologicalComplex₂ (F.obj (K₁.X i₁)) c₂ c₃).obj K₂).map φ
      comm' := fun i₁ i₁' _ => by
        ext i₂ i₃
        dsimp
        rw [NatTrans.naturality] }
  map_id K₃ := by
    ext1 i₁
    dsimp
    rw [Functor.map_id]
    rfl
  map_comp {K₃ K₃' K₃''} φ φ' := by
    ext1 i₁
    dsimp
    rw [Functor.map_comp]

@[simps]
def mapHomologicalComplex₃ObjMap (K₁ : HomologicalComplex C₁ c₁)
    {K₂ K₂' : HomologicalComplex C₂ c₂} (φ : K₂ ⟶ K₂') :
    mapHomologicalComplex₃ObjObj F c₁ c₂ c₃ K₁ K₂ ⟶
    mapHomologicalComplex₃ObjObj F c₁ c₂ c₃ K₁ K₂' :=
  { app := fun K₃ =>
      { f := fun i₁ =>
          { f := fun i₂ =>
              { f := fun i₃ => ((F.obj (K₁.X i₁)).map (φ.f i₂)).app (K₃.X i₃)
                comm' := fun i₃ i₃' _ => by
                  dsimp
                  rw [NatTrans.naturality] }
            comm' := fun i₂ i₂' _ => by
              ext i₃
              dsimp
              rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp,
                ← Functor.map_comp, φ.comm] }
        comm' := fun i₁ i₁' _ => by
          ext i₂ i₃
          dsimp
          rw [← NatTrans.comp_app, ← NatTrans.comp_app, NatTrans.naturality] } }

@[simps]
def mapHomologicalComplex₃Obj (K₁ : HomologicalComplex C₁ c₁) :
    HomologicalComplex C₂ c₂ ⥤
      HomologicalComplex C₃ c₃ ⥤ HomologicalComplex₃ C c₁ c₂ c₃ where
  obj := mapHomologicalComplex₃ObjObj F c₁ c₂ c₃ K₁
  map {K₂ K₂'} φ := mapHomologicalComplex₃ObjMap F c₁ c₂ c₃ K₁ φ

@[simps]
def mapHomologicalComplex₃MapApp {K₁ K₁' : HomologicalComplex C₁ c₁} (φ : K₁ ⟶ K₁')
    (K₂ : HomologicalComplex C₂ c₂) :
    (mapHomologicalComplex₃Obj F c₁ c₂ c₃ K₁).obj K₂ ⟶
      (mapHomologicalComplex₃Obj F c₁ c₂ c₃ K₁').obj K₂ where
  app K₃ :=
    { f := fun i₁ =>
        { f := fun i₂ =>
            { f := fun i₃ => ((F.map (φ.f i₁)).app _).app _ }
          comm' := fun i₃ i₃' _ => by
            ext i₃
            dsimp
            rw [← NatTrans.comp_app, ← NatTrans.comp_app, NatTrans.naturality] }
      comm' := fun i₂ i₂' _ => by
        ext i₂ i₃
        dsimp
        rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← NatTrans.comp_app,
          ← NatTrans.comp_app, ← F.map_comp, ← F.map_comp, φ.comm] }

@[simps]
def mapHomologicalComplex₃Map {K₁ K₁' : HomologicalComplex C₁ c₁} (φ : K₁ ⟶ K₁') :
    mapHomologicalComplex₃Obj F c₁ c₂ c₃ K₁ ⟶ mapHomologicalComplex₃Obj F c₁ c₂ c₃ K₁' where
  app := mapHomologicalComplex₃MapApp F c₁ c₂ c₃ φ
  naturality := fun K₂ K₂' φ => by
    ext
    dsimp
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, NatTrans.naturality]

@[simps]
def mapHomologicalComplex₃ : HomologicalComplex C₁ c₁ ⥤ HomologicalComplex C₂ c₂ ⥤
    HomologicalComplex C₃ c₃ ⥤ HomologicalComplex₃ C c₁ c₂ c₃ where
  obj K₁ := mapHomologicalComplex₃Obj F c₁ c₂ c₃ K₁
  map {K₁ K₁'} φ := mapHomologicalComplex₃Map F c₁ c₂ c₃ φ

end Functor

end CategoryTheory

namespace ComplexShape

variable (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃)
  (c₁₂ : ComplexShape I₁₂) (c : ComplexShape J) [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₁₂ c₃ c]

def π₃ : I₁ × I₂ × I₃ → J := fun ⟨i₁, i₂, i₃⟩ =>
  ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃)

end ComplexShape

namespace HomologicalComplex

section

variable {C C₁ C₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} [Preadditive C₁] [Preadditive C₂]
  [Preadditive C]
  (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
  (F : C₁ ⥤ C₂ ⥤ C)
  [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).Additive]
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]

abbrev HasBifunctorObj : Prop :=
  (((F.mapHomologicalComplex₂ c₁ c₂).obj K₁).obj K₂).HasTotal c₁₂

noncomputable def bifunctorObj [HasBifunctorObj K₁ K₂ F c₁₂] : HomologicalComplex C c₁₂ :=
  (((F.mapHomologicalComplex₂ c₁ c₂).obj K₁).obj K₂).total c₁₂

noncomputable def ιBifunctorObj [HasBifunctorObj K₁ K₂ F c₁₂] (i₁ : I₁) (i₂ : I₂) (j : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = j) :
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ (bifunctorObj K₁ K₂ F c₁₂).X j :=
  (((F.mapHomologicalComplex₂ c₁ c₂).obj K₁).obj K₂).ιTotal c₁₂ i₁ i₂ j h

noncomputable def ιBifunctorObjOrZero [HasBifunctorObj K₁ K₂ F c₁₂] (i₁ : I₁) (i₂ : I₂) (j : I₁₂) :
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ (bifunctorObj K₁ K₂ F c₁₂).X j :=
  if h : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = j
    then ιBifunctorObj K₁ K₂ F c₁₂ i₁ i₂ j h
    else 0

noncomputable def ιBifunctorObjOrZero_eq [HasBifunctorObj K₁ K₂ F c₁₂] (i₁ : I₁) (i₂ : I₂) (j : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = j) :
    ιBifunctorObjOrZero K₁ K₂ F c₁₂ i₁ i₂ j = ιBifunctorObj K₁ K₂ F c₁₂ i₁ i₂ j h := dif_pos h

noncomputable def ιBifunctorObjOrZero_eq_zero [HasBifunctorObj K₁ K₂ F c₁₂] (i₁ : I₁) (i₂ : I₂) (j : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ ≠ j) :
    ιBifunctorObjOrZero K₁ K₂ F c₁₂ i₁ i₂ j = 0 := dif_neg h

lemma ιBifunctorObj_d [HasBifunctorObj K₁ K₂ F c₁₂] (i₁ : I₁) (i₂ : I₂) (j j' : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = j) :
    ιBifunctorObj K₁ K₂ F c₁₂ i₁ i₂ j h ≫ (bifunctorObj K₁ K₂ F c₁₂).d j j' =
      ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂) • (F.map (K₁.d i₁ (c₁.next i₁))).app (K₂.X i₂) ≫ ιBifunctorObjOrZero _ _ _ _ _ _ _ +
      ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂) • (F.obj (K₁.X i₁)).map (K₂.d i₂ (c₂.next i₂)) ≫ ιBifunctorObjOrZero _ _ _ _ _ _ _ := by
  apply HomologicalComplex₂.ιTotal_d

end

variable {C C₁ C₂ C₃ C₁₂ C₂₃}
variable
  [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
  [Preadditive C₁₂] [Preadditive C₂₃] [Preadditive C]
  {F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂} {G : C₁₂ ⥤ C₃ ⥤ C}
  {F : C₁ ⥤ C₂₃ ⥤ C} {G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃}
  [F₁₂.Additive] [∀ (X₁ : C₁), (F₁₂.obj X₁).Additive]
  [G.Additive] [∀ (X₁₂ : C₁₂), (G.obj X₁₂).Additive]
  [G₂₃.Additive] [∀ (X₂ : C₂), (G₂₃.obj X₂).Additive]
  [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).Additive]
  (associator : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃)
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₃ : ComplexShape I₃}
  (K₁ : HomologicalComplex C₁ c₁)
  (K₂ : HomologicalComplex C₂ c₂)
  (K₃ : HomologicalComplex C₃ c₃)
  (c₁₂ : ComplexShape I₁₂) (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J)
  [DecidableEq I₁₂] [DecidableEq I₂₃] [DecidableEq J]
  [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₁₂ c₃ c]
  [TotalComplexShape c₂ c₃ c₂₃] [TotalComplexShape c₁ c₂₃ c]
  [ComplexShape.Associator c₁ c₂ c₃ c₁₂ c₂₃ c]
  [HasBifunctorObj K₁ K₂ F₁₂ c₁₂] [HasBifunctorObj (bifunctorObj K₁ K₂ F₁₂ c₁₂) K₃ G c]
  [HasBifunctorObj K₂ K₃ G₂₃ c₂₃] [HasBifunctorObj K₁ (bifunctorObj K₂ K₃ G₂₃ c₂₃) F c]

instance : (bifunctorComp₁₂ F₁₂ G).Additive where
instance (X₁ : C₁) : ((bifunctorComp₁₂ F₁₂ G).obj X₁).Additive where
instance (X₁ : C₁) (X₂ : C₂) : (((bifunctorComp₁₂ F₁₂ G).obj X₁).obj X₂).Additive where
instance : (bifunctorComp₂₃ F G₂₃).Additive where
instance (X₁ : C₁) : ((bifunctorComp₂₃ F G₂₃).obj X₁).Additive where
instance (X₁ : C₁) (X₂ : C₂) : (((bifunctorComp₂₃ F G₂₃).obj X₁).obj X₂).Additive where

variable (c₁ c₂ c₃)

@[simps]
def ρ₁₂ : GradedObject.Bifunctor₁₂BifunctorIndexData (ComplexShape.π₃ c₁ c₂ c₃ c₁₂ c) where
  I₁₂ := I₁₂
  p := ComplexShape.π c₁ c₂ c₁₂
  q := ComplexShape.π c₁₂ c₃ c
  hpq _ := rfl

@[simps]
def ρ₂₃ : GradedObject.BifunctorBifunctor₂₃IndexData (ComplexShape.π₃ c₁ c₂ c₃ c₁₂ c) where
  I₂₃ := I₂₃
  p := ComplexShape.π c₂ c₃ c₂₃
  q := ComplexShape.π c₁ c₂₃ c
  hpq := fun ⟨i₁, i₂, i₃⟩ => ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c i₁ i₂ i₃

variable {c₁ c₂ c₃}

variable
  [H₁₂ : GradedObject.HasGoodBifunctor₁₂BifunctorObj F₁₂ G (ρ₁₂ c₁ c₂ c₃ c₁₂ c) K₁.X K₂.X K₃.X]
  [H₂₃ : GradedObject.HasGoodBifunctorBifunctor₂₃Obj F G₂₃ (ρ₂₃ c₁ c₂ c₃ c₁₂ c₂₃ c) K₁.X K₂.X K₃.X]

instance : (((GradedObject.mapBifunctor F₁₂ I₁ I₂).obj K₁.X).obj K₂.X).HasMap (ρ₁₂ c₁ c₂ c₃ c₁₂ c).p := by
  change HasBifunctorObj K₁ K₂ F₁₂ c₁₂
  infer_instance

instance : (((GradedObject.mapBifunctor G (ρ₁₂ c₁ c₂ c₃ c₁₂ c).I₁₂ I₃).obj
    (GradedObject.mapBifunctorMapObj F₁₂ (ρ₁₂ c₁ c₂ c₃ c₁₂ c).p K₁.X K₂.X)).obj K₃.X).HasMap (ρ₁₂ c₁ c₂ c₃ c₁₂ c).q :=
  (inferInstance : HasBifunctorObj (bifunctorObj K₁ K₂ F₁₂ c₁₂) K₃ G c)

instance : (((GradedObject.mapBifunctor G₂₃ I₂ I₃).obj K₂.X).obj K₃.X).HasMap (ρ₂₃ c₁ c₂ c₃ c₁₂ c₂₃ c).p :=
  (inferInstance : HasBifunctorObj K₂ K₃ G₂₃ c₂₃)

instance : (((GradedObject.mapBifunctor F I₁ (ρ₂₃ c₁ c₂ c₃ c₁₂ c₂₃ c).I₂₃).obj K₁.X).obj
    (GradedObject.mapBifunctorMapObj G₂₃ (ρ₂₃ c₁ c₂ c₃ c₁₂ c₂₃ c).p K₂.X K₃.X)).HasMap
  (ρ₂₃ c₁ c₂ c₃ c₁₂ c₂₃ c).q := (inferInstance : HasBifunctorObj K₁ (bifunctorObj K₂ K₃ G₂₃ c₂₃) F c)

@[reassoc]
lemma ιMapBifunctorBifunctor₂₃MapObj_d (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j j' : J) (h : ComplexShape.π₃ c₁ c₂ c₃ c₁₂ c (i₁, i₂, i₃) = j) :
    GradedObject.ιMapBifunctorBifunctor₂₃MapObj F G₂₃ (ρ₂₃ c₁ c₂ c₃ c₁₂ c₂₃ c) K₁.X K₂.X K₃.X i₁ i₂ i₃ j h ≫
      d (bifunctorObj K₁ (bifunctorObj K₂ K₃ G₂₃ c₂₃) F c) j j' =
        ComplexShape.ε₁ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) •
          (F.map (K₁.d i₁ (c₁.next i₁))).app ((G₂₃.obj (K₂.X i₂)).obj (K₃.X i₃)) ≫
          GradedObject.ιMapBifunctorBifunctor₂₃MapObjOrZero _ _ (ρ₂₃ c₁ c₂ c₃ c₁₂ c₂₃ c) _ _ _ _ _ _ _ +
        (ComplexShape.ε₂ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) * ComplexShape.ε₁ c₂ c₃ c₂₃ (i₂, i₃)) •
          (F.obj (K₁.X i₁)).map ((G₂₃.map (K₂.d i₂ (c₂.next i₂))).app (K₃.X i₃)) ≫
          GradedObject.ιMapBifunctorBifunctor₂₃MapObjOrZero _ _ _ _ _ _ _ _ _ _ +
        (ComplexShape.ε₂ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) * ComplexShape.ε₂ c₂ c₃ c₂₃ (i₂, i₃)) •
          (F.obj (K₁.X i₁)).map ((G₂₃.obj (K₂.X i₂)).map (K₃.d i₃ (c₃.next i₃))) ≫
          GradedObject.ιMapBifunctorBifunctor₂₃MapObjOrZero _ _ _ _ _ _ _ _ _ _ := by
  dsimp [GradedObject.ιMapBifunctorBifunctor₂₃MapObj]
  rw [assoc]
  erw [ιBifunctorObj_d K₁ (bifunctorObj K₂ K₃ G₂₃ c₂₃) F c i₁ (ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩) j j'
    (by simpa only [← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c] using h)]
  rw [comp_add, comp_zsmul, comp_zsmul, ← Functor.map_comp_assoc]
  erw [NatTrans.naturality_assoc, ιBifunctorObj_d]
  rw [Functor.map_add, Functor.map_zsmul, add_comp, smul_add, zsmul_comp, smul_smul,
    Functor.map_zsmul, zsmul_comp, smul_smul, add_assoc]
  congr 1
  · congr 1
    by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
    · by_cases h₂ : ComplexShape.π c₁ c₂₃ c (c₁.next i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j'
      · rw [ιBifunctorObjOrZero_eq _ _ _ _ _ _ _ h₂]
        erw [GradedObject.ιMapBifunctorBifunctor₂₃MapObjOrZero_eq]; swap
        · dsimp [ComplexShape.π₃]
          rw [ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c, h₂]
        rfl
      · rw [ιBifunctorObjOrZero_eq_zero _ _ _ _ _ _ _ h₂, comp_zero, comp_zero]
        erw [GradedObject.ιMapBifunctorBifunctor₂₃MapObjOrZero_eq_zero, comp_zero]
        intro h₃
        apply h₂
        rw [← h₃, ← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c]
        rfl
    · rw [shape _ _ _ h₁, F.map_zero, zero_app, zero_comp, zero_comp]
  · congr 1
    · congr 1
      by_cases h₁ : c₂.Rel i₂ (c₂.next i₂)
      · by_cases h₂ : ComplexShape.π c₁ c₂₃ c (i₁, c₂₃.next (ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃))) = j'
        · have h₃ : ComplexShape.π₃ c₁ c₂ c₃ c₁₂ c (i₁, c₂.next i₂, i₃) = j' := by
            rw [← h₂, ComplexShape.next_π₁ c₃ c₂₃ h₁ i₃,
              ← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c]
            rfl
          rw [Functor.map_comp, assoc, ιBifunctorObjOrZero_eq _ _ _ _ _ _ _ h₂,
            ιBifunctorObjOrZero_eq _ _ _ _ _ _ _ (ComplexShape.next_π₁ c₃ c₂₃ h₁ i₃).symm]
          erw [GradedObject.ιMapBifunctorBifunctor₂₃MapObjOrZero_eq _ _ _ _ _ _ _ _ _ _ h₃]
          congr 1
          symm
          apply GradedObject.ιMapBifunctorBifunctor₂₃MapObj_eq
        · rw [ιBifunctorObjOrZero_eq_zero _ _ _ _ _ _ _ h₂, comp_zero]
          erw [GradedObject.ιMapBifunctorBifunctor₂₃MapObjOrZero_eq_zero, comp_zero]
          intro h₃
          apply h₂
          rw [← h₃, ComplexShape.next_π₁ c₃ c₂₃ h₁ i₃, ← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c]
          rfl
      · rw [shape _ _ _ h₁, Functor.map_zero, zero_app, Functor.map_zero, zero_comp,
          zero_comp, Functor.map_zero, zero_comp]
    · congr 1
      by_cases h₁ : c₃.Rel i₃ (c₃.next i₃)
      · by_cases h₂ : ComplexShape.π c₁ c₂₃ c (i₁, c₂₃.next (ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃))) = j'
        · rw [ιBifunctorObjOrZero_eq _ _ _ _ _ _ _ h₂]
          sorry
        · rw [ιBifunctorObjOrZero_eq_zero _ _ _ _ _ _ _ h₂, comp_zero]
          erw [GradedObject.ιMapBifunctorBifunctor₂₃MapObjOrZero_eq_zero, comp_zero]
          intro h₃
          apply h₂
          rw [← h₃, ComplexShape.next_π₂ c₂ c₂₃ i₂ h₁, ← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c]
          rfl
      · rw [shape _ _ _ h₁, Functor.map_zero, Functor.map_zero, zero_comp, zero_comp,
          Functor.map_zero, zero_comp]

noncomputable def bifunctorObjXAssociator :
    (bifunctorObj (bifunctorObj K₁ K₂ F₁₂ c₁₂) K₃ G c).toGradedObject ≅
      (bifunctorObj K₁ (bifunctorObj K₂ K₃ G₂₃ c₂₃) F c).toGradedObject :=
  GradedObject.mapBifunctorBifunctorAssociator associator (ρ₁₂ c₁ c₂ c₃ c₁₂ c) (ρ₂₃ c₁ c₂ c₃ c₁₂ c₂₃ c) K₁.X K₂.X K₃.X

noncomputable def bifunctorObjAssociator : bifunctorObj (bifunctorObj K₁ K₂ F₁₂ c₁₂) K₃ G c ≅
    bifunctorObj K₁ (bifunctorObj K₂ K₃ G₂₃ c₂₃) F c :=
  Hom.isoOfComponents
    (fun j => (GradedObject.eval j).mapIso (bifunctorObjXAssociator associator K₁ K₂ K₃ c₁₂ c₂₃ c))
      (fun j j' _ => by
        apply GradedObject.mapBifunctor₁₂BifunctorMapObj_ext F₁₂ G (ρ₁₂ c₁ c₂ c₃ c₁₂ c)
        intro i₁ i₂ i₃ h
        dsimp [bifunctorObjXAssociator]
        erw [GradedObject.ι_mapBifunctorBifunctorAssociator_hom_assoc]
        rw [ιMapBifunctorBifunctor₂₃MapObj_d, comp_add, comp_add, comp_zsmul, comp_zsmul, comp_zsmul]
        have h₁ := congr_app (congr_app (associator.hom.naturality (K₁.d i₁ (c₁.next i₁))) (K₂.X i₂)) (K₃.X i₃)
        dsimp at h₁
        rw [← reassoc_of% h₁]
        erw [← GradedObject.ιOrZero_mapBifunctorBifunctorAssociator_hom associator (ρ₁₂ c₁ c₂ c₃ c₁₂ c) (ρ₂₃ c₁ c₂ c₃ c₁₂ c₂₃ c) K₁.X K₂.X K₃.X]
        sorry)

end HomologicalComplex
