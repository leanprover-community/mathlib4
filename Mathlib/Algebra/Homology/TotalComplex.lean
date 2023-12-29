/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Homology.ComplexShapeSigns
import Mathlib.Algebra.Homology.HomologicalBicomplex

/-!
# The total complex of a bicomplex

Given a preadditive `C`, two complex shapes `c₁ : ComplexShape I₁`, `c₂ : ComplexShape I₂`,
a bicomplex `K : HomologicalComplex₂ C c₁ c₂`, and a third complex shape `c₁₂ : ComplexShape I₁₂`
equipped with `[TotalComplexShape c₁ c₂ c₁₂]`, we construct the total complex
`K.total c₁₂ : HomologicalComplex C c₁₂`.

-/


open CategoryTheory Category Limits Preadditive

namespace HomologicalComplex₂

variable {C : Type*} [Category C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K : HomologicalComplex₂ C c₁ c₂)
  (c₁₂ : ComplexShape I₁₂) [DecidableEq I₁₂]
  [TotalComplexShape c₁ c₂ c₁₂]

/-- A bicomplex has a total bicomplex if for any `i₁₂ : I₁₂`, the coproduct
of the objects `(K.X i₁).X i₂` such that `ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂` exists. -/
abbrev HasTotal := K.toGradedObject.HasMap (ComplexShape.π c₁ c₂ c₁₂)

variable [K.HasTotal c₁₂]

section

variable (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)

/-- The horizontal differential in the total complex. -/
noncomputable def d₁ :
    (K.X i₁).X i₂ ⟶ (K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)) i₁₂ :=
  ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ (c₁.next i₁)).f i₂ ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨_, i₂⟩ i₁₂)

/-- The vertical differential in the total complex. -/
noncomputable def d₂ :
    (K.X i₁).X i₂ ⟶ (K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)) i₁₂ :=
  ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ (c₂.next i₂) ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, _⟩ i₁₂)

lemma d₁_eq_zero (h : ¬ c₁.Rel i₁ (c₁.next i₁)) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = 0 := by
  dsimp [d₁]
  rw [K.shape_f _ _ h, zero_comp, smul_zero]

lemma d₂_eq_zero (h : ¬ c₂.Rel i₂ (c₂.next i₂)) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = 0 := by
  dsimp [d₂]
  rw [HomologicalComplex.shape _ _ _ h, zero_comp, smul_zero]

end

lemma d₁_eq' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ i₁').f i₂ ≫
      K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁', i₂⟩ i₁₂) := by
  obtain rfl := c₁.next_eq' h
  rfl

lemma d₁_eq_zero' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ ≠ i₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = 0 := by
  rw [K.d₁_eq' c₁₂ h i₂ i₁₂, K.toGradedObject.ιMapObjOrZero_eq_zero, comp_zero, smul_zero]
  exact h'

lemma d₁_eq {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ = i₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ i₁').f i₂ ≫
      K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁', i₂⟩ i₁₂ h') := by
  rw [K.d₁_eq' c₁₂ h i₂ i₁₂, K.toGradedObject.ιMapObjOrZero_eq]

lemma d₂_eq' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ i₂' ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂'⟩ i₁₂) := by
  obtain rfl := c₂.next_eq' h
  rfl

lemma d₂_eq_zero' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ ≠ i₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = 0 := by
  rw [K.d₂_eq' c₁₂ i₁ h i₁₂, K.toGradedObject.ιMapObjOrZero_eq_zero, comp_zero, smul_zero]
  exact h'

lemma d₂_eq (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ = i₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ i₂' ≫
    K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂'⟩ i₁₂ h') := by
  rw [K.d₂_eq' c₁₂ i₁ h i₁₂, K.toGradedObject.ιMapObjOrZero_eq]

/-- The total complex of a bicomplex. -/
noncomputable def total : HomologicalComplex C c₁₂ where
  X := K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)
  d i₁₂ i₁₂' := GradedObject.descMapObj _ (ComplexShape.π c₁ c₂ c₁₂)
    (fun ⟨i₁, i₂⟩ _ => K.d₁ c₁₂ i₁ i₂ i₁₂' + K.d₂ c₁₂ i₁ i₂ i₁₂')
  shape i₁₂ i₁₂' h₁₂ := by
    ext ⟨i₁, i₂⟩ h
    have w₁ : K.d₁ c₁₂ i₁ i₂ i₁₂' = 0 := by
      by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
      · rw [K.d₁_eq_zero' c₁₂ h₁ i₂ i₁₂']
        intro h₂
        exact h₁₂ (by simpa only [← h, ← h₂] using ComplexShape.rel_π₁ c₂ c₁₂ h₁ i₂)
      · exact d₁_eq_zero _ _ _ _ _ h₁
    have w₂ : K.d₂ c₁₂ i₁ i₂ i₁₂' = 0 := by
      by_cases h₁ : c₂.Rel i₂ (c₂.next i₂)
      · rw [K.d₂_eq_zero' c₁₂ i₁ h₁ i₁₂']
        intro h₂
        exact h₁₂ (by simpa only [← h, ← h₂] using ComplexShape.rel_π₂ c₁ c₁₂ i₁ h₁)
      · exact d₂_eq_zero _ _ _ _ _ h₁
    simp only [GradedObject.ι_descMapObj, comp_zero, w₁, w₂, add_zero]
  d_comp_d' i₁₂ i₁₂' i₁₂'' h₁ h₂ := by
    ext ⟨i₁, i₂⟩ h₁₂
    simp only [GradedObject.ι_descMapObj_assoc, add_comp, comp_zero]
    by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
    · rw [K.d₁_eq c₁₂ h₃ i₂ i₁₂']; swap
      · rw [← ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂, ← c₁₂.next_eq' h₁, h₁₂]
      simp only [Linear.units_smul_comp, assoc, GradedObject.ι_descMapObj,
        comp_add, smul_add]
      rw [add_assoc]
      conv_rhs => rw [← add_zero 0]
      congr 1
      · by_cases h₄ : c₁.Rel (c₁.next i₁) (c₁.next (c₁.next i₁))
        · rw [K.d₁_eq c₁₂ h₄ i₂ i₁₂'', Linear.comp_units_smul,
            d_f_comp_d_f_assoc, zero_comp, smul_zero, smul_zero]
          rw [← ComplexShape.next_π₁ c₂ c₁₂ h₄, ← ComplexShape.next_π₁ c₂ c₁₂ h₃,
            h₁₂, c₁₂.next_eq' h₁, c₁₂.next_eq' h₂]
        · rw [K.d₁_eq_zero _ _ _ _ h₄, comp_zero, smul_zero]
      · by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
        · have h₅ : ComplexShape.π c₁ c₂ c₁₂ (i₁, c₂.next i₂) = i₁₂' := by
            rw [← c₁₂.next_eq' h₁, ← h₁₂, ComplexShape.next_π₂ c₁ c₁₂ i₁ h₄]
          have h₆ : ComplexShape.π c₁ c₂ c₁₂ (c₁.next i₁, c₂.next i₂) = i₁₂'' := by
            rw [← c₁₂.next_eq' h₂, ← ComplexShape.next_π₁ c₂ c₁₂ h₃, h₅]
          rw [K.d₂_eq c₁₂ i₁ h₄ i₁₂' h₅, K.d₂_eq c₁₂ (c₁.next i₁) h₄ i₁₂'' h₆,
            Linear.comp_units_smul, Linear.units_smul_comp, assoc, GradedObject.ι_descMapObj,
            comp_add, smul_add, ← add_assoc]
          conv_rhs => rw [← zero_add 0]
          congr 1
          · dsimp
            rw [K.d₁_eq c₁₂ h₃ (c₂.next i₂) i₁₂'' h₆, Linear.comp_units_smul, smul_smul,
              smul_smul, HomologicalComplex.Hom.comm_assoc, ComplexShape.ε₂ε₁ c₁₂ h₃ h₄,
              neg_mul, Units.neg_smul, add_right_neg]
          · by_cases h₈ : c₂.Rel (c₂.next i₂) (c₂.next (c₂.next i₂))
            · have h₉ : ComplexShape.π c₁ c₂ c₁₂ (i₁, c₂.next (c₂.next i₂)) = i₁₂'' := by
                rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₈, h₅, c₁₂.next_eq' h₂]
              rw [K.d₂_eq c₁₂ i₁ h₈ i₁₂'' h₉, Linear.comp_units_smul,
                HomologicalComplex.d_comp_d_assoc, zero_comp, smul_zero, smul_zero]
            · rw [K.d₂_eq_zero _ _ _ _ h₈, comp_zero, smul_zero]
        · rw [K.d₂_eq_zero _ _ _ _ h₄, K.d₂_eq_zero _ _ _ _ h₄, comp_zero, zero_comp,
            smul_zero, add_zero]
    · rw [K.d₁_eq_zero _ _ _ _ h₃, zero_comp, zero_add]
      by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
      · by_cases h₅ : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, c₂.next i₂⟩ = i₁₂'
        · simp only [K.d₂_eq c₁₂ i₁ h₄ _ h₅, Linear.units_smul_comp, assoc,
            GradedObject.ι_descMapObj, comp_add, smul_add, zero_add,
            K.d₁_eq_zero c₁₂ i₁ (c₂.next i₂) i₁₂'' h₃, comp_zero, smul_zero]
          by_cases h₆ : c₂.Rel (c₂.next i₂) (c₂.next (c₂.next i₂))
          · rw [K.d₂_eq c₁₂ i₁ h₆ _]; swap
            · rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₆,
                ← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₄,
                ← c₁₂.next_eq' h₂, ← c₁₂.next_eq' h₁, h₁₂]
            rw [Linear.comp_units_smul, HomologicalComplex.d_comp_d_assoc,
              zero_comp, smul_zero, smul_zero]
          · rw [K.d₂_eq_zero _ _ _ _ h₆, comp_zero, smul_zero]
        · rw [K.d₂_eq_zero' c₁₂ i₁ h₄ _ h₅, zero_comp]
      · rw [K.d₂_eq_zero _ _ _ _ h₄, zero_comp]

end HomologicalComplex₂
