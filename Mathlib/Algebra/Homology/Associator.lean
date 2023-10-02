import Mathlib.Algebra.Homology.HomologicalBicomplex

open CategoryTheory Limits Category Preadditive

variable (C : Type*) [Category C]
  {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}
  (c₁ : ComplexShape I₁)
  (c₂ : ComplexShape I₂)
  (c₃ : ComplexShape I₃)

abbrev HomologicalComplex₃ [HasZeroMorphisms C] :=
  HomologicalComplex (HomologicalComplex (HomologicalComplex C c₃) c₂) c₁

namespace HomologicalComplex₃

variable {C c₁ c₂ c₃}

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

variable [Preadditive C] (K : HomologicalComplex₃ C c₁ c₂ c₃)
  (c₁₂ : ComplexShape I₁₂) [DecidableEq I₁₂]
  (c₂₃ : ComplexShape I₂₃) [DecidableEq I₂₃]
  (c : ComplexShape J) [DecidableEq J]

namespace HomologicalComplex₃

variable {C c₁ c₂ c₃}

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
