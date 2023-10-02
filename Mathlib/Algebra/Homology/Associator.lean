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

-- `[HasZeroMorphisms C]` is sufficient, but `Functor.mapHomologicalComplex` has a `Preadditive C` assumption
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

namespace ComplexShape

class Associator [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₁₂ c₃ c]
    [TotalComplexShape c₂ c₃ c₂₃] [TotalComplexShape c₁ c₂₃ c] where
  assoc (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    π c₁₂ c₃ c ⟨π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃⟩ = π c₁ c₂₃ c ⟨i₁, π c₂ c₃ c₂₃ ⟨i₂, i₃⟩⟩
  compatibility₁ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ComplexShape.ε₁ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) =
      ComplexShape.ε₁ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂)

section

variable [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₁₂ c₃ c]
  [TotalComplexShape c₂ c₃ c₂₃] [TotalComplexShape c₁ c₂₃ c] [Associator c₁ c₂ c₃ c₁₂ c₂₃ c]

lemma assoc (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
      π c₁₂ c₃ c ⟨π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃⟩ = π c₁ c₂₃ c ⟨i₁, π c₂ c₃ c₂₃ ⟨i₂, i₃⟩⟩ := by
  apply Associator.assoc

lemma associator_ε₁_eq_mul (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ComplexShape.ε₁ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) =
      ComplexShape.ε₁ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂) := by
  apply Associator.compatibility₁

end

end ComplexShape

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

noncomputable def totalAssociatorX (j : J) :
    ((K.total₁₂ c₁₂).total c).X j ≅ ((K.total₂₃ c₂₃).total c).X j where
  hom := HomologicalComplex₂.descTotal _ _
    (fun i₁₂ i₃ h => HomologicalComplex₂.descTotal _ _
      (fun i₁ i₂ h' => HomologicalComplex₂.ιTotal (K.X i₁) c₂₃ i₂ i₃ _ rfl ≫
        (K.total₂₃ c₂₃).ιTotal c i₁ (ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩) j
          (by rw [← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c, h', h])))
  inv := HomologicalComplex₂.descTotal _ _
    (fun i₁ i₂₃ h => HomologicalComplex₂.descTotal _ _
      (fun i₂ i₃ h' => HomologicalComplex₂.ιTotal (K.rotate.X i₃) c₁₂ i₁ i₂ _ rfl ≫
        (K.total₁₂ c₁₂).ιTotal c (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) i₃ j
          (by rw [ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c, h', h])))
  hom_inv_id := by
    ext i₁₂ i₃ h
    apply HomologicalComplex₂.total_ext
    rintro i₁ i₂ h'
    rw [← h'] at h
    subst h'
    dsimp
    simp
  inv_hom_id := by
    ext i₁ i₂₃ h
    apply HomologicalComplex₂.total_ext
    rintro i₂ i₃ h'
    rw [← h'] at h
    subst h'
    dsimp
    simp

/-
noncomputable def totalAssociator : (K.total₁₂ c₁₂).total c ≅ (K.total₂₃ c₂₃).total c :=
  HomologicalComplex.Hom.isoOfComponents (K.totalAssociatorX c₁₂ c₂₃ c) (fun j j' _ => by
    ext i₁₂ i₃ h
    apply HomologicalComplex₂.total_ext
    intro i₁ i₂ h'
    dsimp [totalAssociatorX]
    conv_lhs =>
      rw [HomologicalComplex₂.ι_descTotal_assoc, HomologicalComplex₂.ι_descTotal_assoc, assoc,
        HomologicalComplex₂.ιTotal_d, comp_add, comp_zsmul, comp_zsmul]
      dsimp
      erw [HomologicalComplex₂.ιTotal_d_assoc]
      rw [add_comp, zsmul_comp, zsmul_comp, zsmul_add, smul_smul, smul_smul, assoc, assoc]
    conv_rhs =>
      rw [HomologicalComplex₂.ιTotal_d_assoc, add_comp, comp_add, zsmul_comp, zsmul_comp,
        comp_zsmul, comp_zsmul, assoc, assoc]
      dsimp
      erw [HomologicalComplex₂.ιTotal_d_assoc]
      rw [add_comp, zsmul_comp, zsmul_comp, assoc, assoc, zsmul_add, smul_smul, smul_smul]
    rw [add_assoc]
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
      · sorry
      · sorry
    )-/

end


end HomologicalComplex₃
