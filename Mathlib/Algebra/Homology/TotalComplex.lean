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

Given a preadditive category `C`, two complex shapes `c₁ : ComplexShape I₁`,
`c₂ : ComplexShape I₂`, a bicomplex `K : HomologicalComplex₂ C c₁ c₂`,
and a third complex shape `c₁₂ : ComplexShape I₁₂` equipped
with `[TotalComplexShape c₁ c₂ c₁₂]`, we construct the total complex
`K.total c₁₂ : HomologicalComplex C c₁₂`.

In particular, if `c := ComplexShape.up ℤ` and `K : HomologicalComplex₂ c c`, then for any
`n : ℤ`, `(K.total c).X n` identifies to the coproduct of the `(K.X p).X q` such that
`p + q = n`, and the differential on `(K.total c).X n` is induced by the sum of horizontal
differentials `(K.X p).X q ⟶ (K.X (p + 1)).X q` and `(-1) ^ p` times the vertical
differentials `(K.X p).X q ⟶ (K.X p).X (q + 1)`.

-/

open CategoryTheory Category Limits Preadditive

namespace HomologicalComplex₂

variable {C : Type*} [Category C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [DecidableEq I₁₂]
  [TotalComplexShape c₁ c₂ c₁₂]

/-- A bicomplex has a total bicomplex if for any `i₁₂ : I₁₂`, the coproduct
of the objects `(K.X i₁).X i₂` such that `ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂` exists. -/
abbrev HasTotal := K.toGradedObject.HasMap (ComplexShape.π c₁ c₂ c₁₂)

variable [K.HasTotal c₁₂]

section

variable (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)

/-- The horizontal differential in the total complex on a given summand. -/
noncomputable def d₁ :
    (K.X i₁).X i₂ ⟶ (K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)) i₁₂ :=
  ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ (c₁.next i₁)).f i₂ ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨_, i₂⟩ i₁₂)

/-- The vertical differential in the total complex on a given summand. -/
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

namespace totalAux
/-! Lemmas in the `totalAux` namespace should be used only in the internals of
the construction of the total complex `HomologicalComplex₂.total`. Once that
definition is done, similar lemmas shall be restated, but with
terms like `K.toGradedObject.ιMapObj` replaced by `K.ιTotal`. This is done in order
to prevent API leakage from definitions involving graded objects. -/

lemma d₁_eq' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ i₁').f i₂ ≫
      K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁', i₂⟩ i₁₂) := by
  obtain rfl := c₁.next_eq' h
  rfl

lemma d₁_eq {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ = i₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ i₁').f i₂ ≫
      K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁', i₂⟩ i₁₂ h') := by
  rw [d₁_eq' K c₁₂ h i₂ i₁₂, K.toGradedObject.ιMapObjOrZero_eq]

lemma d₂_eq' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ i₂' ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂'⟩ i₁₂) := by
  obtain rfl := c₂.next_eq' h
  rfl

lemma d₂_eq (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ = i₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ i₂' ≫
    K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂'⟩ i₁₂ h') := by
  rw [d₂_eq' K c₁₂ i₁ h i₁₂, K.toGradedObject.ιMapObjOrZero_eq]

end totalAux

lemma d₁_eq_zero' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ ≠ i₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = 0 := by
  rw [totalAux.d₁_eq' K c₁₂ h i₂ i₁₂, K.toGradedObject.ιMapObjOrZero_eq_zero, comp_zero, smul_zero]
  exact h'

lemma d₂_eq_zero' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ ≠ i₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = 0 := by
  rw [totalAux.d₂_eq' K c₁₂ i₁ h i₁₂, K.toGradedObject.ιMapObjOrZero_eq_zero, comp_zero, smul_zero]
  exact h'

/-- The horizontal differential in the total complex. -/
noncomputable def D₁ (i₁₂ i₁₂' : I₁₂) :
    K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂) i₁₂ ⟶
      K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂) i₁₂' :=
  GradedObject.descMapObj _ (ComplexShape.π c₁ c₂ c₁₂)
    (fun ⟨i₁, i₂⟩ _ => K.d₁ c₁₂ i₁ i₂ i₁₂')

/-- The vertical differential in the total complex. -/
noncomputable def D₂ (i₁₂ i₁₂' : I₁₂) :
    K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂) i₁₂ ⟶
      K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂) i₁₂' :=
  GradedObject.descMapObj _ (ComplexShape.π c₁ c₂ c₁₂)
    (fun ⟨i₁, i₂⟩ _ => K.d₂ c₁₂ i₁ i₂ i₁₂')

namespace totalAux

@[reassoc (attr := simp)]
lemma ιMapObj_D₁ (i₁₂ i₁₂' : I₁₂) (i : I₁ × I₂) (h : ComplexShape.π c₁ c₂ c₁₂ i = i₁₂) :
    K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) i i₁₂ h ≫ K.D₁ c₁₂ i₁₂ i₁₂' =
      K.d₁ c₁₂ i.1 i.2 i₁₂' := by
  simp [D₁]

@[reassoc (attr := simp)]
lemma ιMapObj_D₂ (i₁₂ i₁₂' : I₁₂) (i : I₁ × I₂) (h : ComplexShape.π c₁ c₂ c₁₂ i = i₁₂) :
    K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) i i₁₂ h ≫ K.D₂ c₁₂ i₁₂ i₁₂' =
      K.d₂ c₁₂ i.1 i.2 i₁₂' := by
  simp [D₂]

end totalAux

lemma D₁_shape (i₁₂ i₁₂' : I₁₂) (h₁₂ : ¬ c₁₂.Rel i₁₂ i₁₂') : K.D₁ c₁₂ i₁₂ i₁₂' = 0 := by
  ext ⟨i₁, i₂⟩ h
  simp only [totalAux.ιMapObj_D₁, comp_zero]
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · rw [K.d₁_eq_zero' c₁₂ h₁ i₂ i₁₂']
    intro h₂
    exact h₁₂ (by simpa only [← h, ← h₂] using ComplexShape.rel_π₁ c₂ c₁₂ h₁ i₂)
  · exact d₁_eq_zero _ _ _ _ _ h₁

lemma D₂_shape (i₁₂ i₁₂' : I₁₂) (h₁₂ : ¬ c₁₂.Rel i₁₂ i₁₂') : K.D₂ c₁₂ i₁₂ i₁₂' = 0 := by
  ext ⟨i₁, i₂⟩ h
  simp only [totalAux.ιMapObj_D₂, comp_zero]
  by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
  · rw [K.d₂_eq_zero' c₁₂ i₁ h₂ i₁₂']
    intro h₁
    exact h₁₂ (by simpa only [← h, ← h₁] using ComplexShape.rel_π₂ c₁ c₁₂ i₁ h₂)
  · exact d₂_eq_zero _ _ _ _ _ h₂

@[reassoc (attr := simp)]
lemma D₁_D₁ (i₁₂ i₁₂' i₁₂'' : I₁₂) : K.D₁ c₁₂ i₁₂ i₁₂' ≫ K.D₁ c₁₂ i₁₂' i₁₂'' = 0 := by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₁_assoc, comp_zero]
      by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
      · rw [totalAux.d₁_eq K c₁₂ h₃ i₂ i₁₂']; swap
        · rw [← ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂, ← c₁₂.next_eq' h₁, h]
        simp only [Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₁]
        by_cases h₄ : c₁.Rel (c₁.next i₁) (c₁.next (c₁.next i₁))
        · rw [totalAux.d₁_eq K c₁₂ h₄ i₂ i₁₂'', Linear.comp_units_smul,
            d_f_comp_d_f_assoc, zero_comp, smul_zero, smul_zero]
          rw [← ComplexShape.next_π₁ c₂ c₁₂ h₄, ← ComplexShape.next_π₁ c₂ c₁₂ h₃,
            h, c₁₂.next_eq' h₁, c₁₂.next_eq' h₂]
        · rw [K.d₁_eq_zero _ _ _ _ h₄, comp_zero, smul_zero]
      · rw [K.d₁_eq_zero c₁₂ _ _ _ h₃, zero_comp]
    · rw [K.D₁_shape c₁₂ _ _ h₂, comp_zero]
  · rw [K.D₁_shape c₁₂ _ _ h₁, zero_comp]

@[reassoc (attr := simp)]
lemma D₂_D₂ (i₁₂ i₁₂' i₁₂'' : I₁₂) : K.D₂ c₁₂ i₁₂ i₁₂' ≫ K.D₂ c₁₂ i₁₂' i₁₂'' = 0 := by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₂_assoc, comp_zero]
      by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
      · rw [totalAux.d₂_eq K c₁₂ i₁ h₃ i₁₂']; swap
        · rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₃, ← c₁₂.next_eq' h₁, h]
        simp only [Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₂]
        by_cases h₄ : c₂.Rel (c₂.next i₂) (c₂.next (c₂.next i₂))
        · rw [totalAux.d₂_eq K c₁₂ i₁ h₄ i₁₂'', Linear.comp_units_smul,
            HomologicalComplex.d_comp_d_assoc, zero_comp, smul_zero, smul_zero]
          rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₄, ← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₃,
            h, c₁₂.next_eq' h₁, c₁₂.next_eq' h₂]
        · rw [K.d₂_eq_zero c₁₂ _ _ _ h₄, comp_zero, smul_zero]
      · rw [K.d₂_eq_zero c₁₂ _ _ _ h₃, zero_comp]
    · rw [K.D₂_shape c₁₂ _ _ h₂, comp_zero]
  · rw [K.D₂_shape c₁₂ _ _ h₁, zero_comp]

@[reassoc (attr := simp)]
lemma D₂_D₁ (i₁₂ i₁₂' i₁₂'' : I₁₂) :
    K.D₂ c₁₂ i₁₂ i₁₂' ≫ K.D₁ c₁₂ i₁₂' i₁₂'' = - K.D₁ c₁₂ i₁₂ i₁₂' ≫ K.D₂ c₁₂ i₁₂' i₁₂'' := by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₂_assoc, comp_neg, totalAux.ιMapObj_D₁_assoc]
      by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
      · rw [totalAux.d₁_eq K c₁₂ h₃ i₂ i₁₂']; swap
        · rw [← ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂, ← c₁₂.next_eq' h₁, h]
        simp only [Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₂]
        by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
        · have h₅ : ComplexShape.π c₁ c₂ c₁₂ (i₁, c₂.next i₂) = i₁₂' := by
            rw [← c₁₂.next_eq' h₁, ← h, ComplexShape.next_π₂ c₁ c₁₂ i₁ h₄]
          have h₆ : ComplexShape.π c₁ c₂ c₁₂ (c₁.next i₁, c₂.next i₂) = i₁₂'' := by
            rw [← c₁₂.next_eq' h₂, ← ComplexShape.next_π₁ c₂ c₁₂ h₃, h₅]
          simp only [totalAux.d₂_eq K c₁₂ _ h₄ _ h₅, totalAux.d₂_eq K c₁₂ _ h₄ _ h₆,
            Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₁, Linear.comp_units_smul,
            totalAux.d₁_eq K c₁₂ h₃ _ _ h₆, HomologicalComplex.Hom.comm_assoc, smul_smul,
            ComplexShape.ε₂_ε₁ c₁₂ h₃ h₄, neg_mul, Units.neg_smul]
        · simp only [K.d₂_eq_zero c₁₂ _ _ _ h₄, zero_comp, comp_zero, smul_zero, neg_zero]
      · rw [K.d₁_eq_zero c₁₂ _ _ _ h₃, zero_comp, neg_zero]
        by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
        · rw [totalAux.d₂_eq K c₁₂ i₁ h₄ i₁₂']; swap
          · rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₄, ← c₁₂.next_eq' h₁, h]
          simp only [Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₁]
          rw [K.d₁_eq_zero c₁₂ _ _ _ h₃, comp_zero, smul_zero]
        · rw [K.d₂_eq_zero c₁₂ _ _ _ h₄, zero_comp]
    · rw [K.D₁_shape c₁₂ _ _ h₂, K.D₂_shape c₁₂ _ _ h₂, comp_zero, comp_zero, neg_zero]
  · rw [K.D₁_shape c₁₂ _ _ h₁, K.D₂_shape c₁₂ _ _ h₁, zero_comp, zero_comp, neg_zero]

@[reassoc]
lemma D₁_D₂ (i₁₂ i₁₂' i₁₂'' : I₁₂) :
    K.D₁ c₁₂ i₁₂ i₁₂' ≫ K.D₂ c₁₂ i₁₂' i₁₂'' = - K.D₂ c₁₂ i₁₂ i₁₂' ≫ K.D₁ c₁₂ i₁₂' i₁₂'' := by simp

/-- The total complex of a bicomplex. -/
@[simps d]
noncomputable def total : HomologicalComplex C c₁₂ where
  X := K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)
  d i₁₂ i₁₂' := K.D₁ c₁₂ i₁₂ i₁₂' + K.D₂ c₁₂ i₁₂ i₁₂'
  shape i₁₂ i₁₂' h₁₂ := by
    dsimp
    rw [K.D₁_shape c₁₂ _ _ h₁₂, K.D₂_shape c₁₂ _ _ h₁₂, zero_add]

/-- The inclusion of a summand in the total complex. -/
noncomputable def ιTotal (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    (K.X i₁).X i₂ ⟶ (K.total c₁₂).X i₁₂ :=
  K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂⟩ i₁₂ h

@[reassoc (attr := simp)]
lemma XXIsoOfEq_hom_ιTotal {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂)
    (i₁₂ : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ (y₁, y₂) = i₁₂) :
    (K.XXIsoOfEq h₁ h₂).hom ≫ K.ιTotal c₁₂ y₁ y₂ i₁₂ h =
      K.ιTotal c₁₂ x₁ x₂ i₁₂ (by rw [h₁, h₂, h]) := by
  subst h₁ h₂
  simp

@[reassoc (attr := simp)]
lemma XXIsoOfEq_inv_ιTotal {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂)
    (i₁₂ : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ (x₁, x₂) = i₁₂) :
    (K.XXIsoOfEq h₁ h₂).inv ≫ K.ιTotal c₁₂ x₁ x₂ i₁₂ h =
      K.ιTotal c₁₂ y₁ y₂ i₁₂ (by rw [← h, h₁, h₂]) := by
  subst h₁ h₂
  simp

/-- The inclusion of a summand in the total complex, or zero if the degrees do not match. -/
noncomputable def ιTotalOrZero (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    (K.X i₁).X i₂ ⟶ (K.total c₁₂).X i₁₂ :=
  K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂⟩ i₁₂

lemma ιTotalOrZero_eq (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιTotalOrZero c₁₂ i₁ i₂ i₁₂ = K.ιTotal c₁₂ i₁ i₂ i₁₂ h := dif_pos h

lemma ιTotalOrZero_eq_zero (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) ≠ i₁₂) :
    K.ιTotalOrZero c₁₂ i₁ i₂ i₁₂ = 0 := dif_neg h

@[reassoc (attr := simp)]
lemma ι_D₁ (i₁₂ i₁₂' : I₁₂) (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂) :
    K.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ K.D₁ c₁₂ i₁₂ i₁₂' =
      K.d₁ c₁₂ i₁ i₂ i₁₂' := by
  apply totalAux.ιMapObj_D₁

@[reassoc (attr := simp)]
lemma ι_D₂ (i₁₂ i₁₂' : I₁₂) (i₁ : I₁) (i₂ : I₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂) :
    K.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ K.D₂ c₁₂ i₁₂ i₁₂' =
      K.d₂ c₁₂ i₁ i₂ i₁₂' := by
  apply totalAux.ιMapObj_D₂

lemma d₁_eq' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ i₁').f i₂ ≫
      K.ιTotalOrZero c₁₂ i₁' i₂ i₁₂) :=
  totalAux.d₁_eq' _ _ h _ _

lemma d₁_eq {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ = i₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ i₁').f i₂ ≫
      K.ιTotal c₁₂ i₁' i₂ i₁₂ h') :=
  totalAux.d₁_eq _ _ h _ _ _

lemma d₂_eq' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ i₂' ≫
    K.ιTotalOrZero c₁₂ i₁ i₂' i₁₂) :=
  totalAux.d₂_eq' _ _ _ h _

lemma d₂_eq (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ = i₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ i₂' ≫
    K.ιTotal c₁₂ i₁ i₂' i₁₂ h') :=
  totalAux.d₂_eq _ _ _ h _ _

section

variable {c₁₂}
variable {A : C} {i₁₂ : I₁₂}
  (f : ∀ (i₁ : I₁) (i₂ : I₂) (_ : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂), (K.X i₁).X i₂ ⟶ A)

/-- Given a bicomplex `K`, this is a constructor for morphisms from `(K.total c₁₂).X i₁₂`. -/
noncomputable def totalDesc : (K.total c₁₂).X i₁₂ ⟶ A :=
  K.toGradedObject.descMapObj _ (fun ⟨i₁, i₂⟩ hi => f i₁ i₂ hi)

@[reassoc (attr := simp)]
lemma ι_totalDesc (i₁ : I₁) (i₂ : I₂) (hi : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιTotal c₁₂ i₁ i₂ i₁₂ hi ≫ K.totalDesc f = f i₁ i₂ hi := by
  simp [totalDesc, ιTotal]

end

namespace total

variable {K L M}

@[ext]
lemma hom_ext {A : C} {i₁₂ : I₁₂} {f g : (K.total c₁₂).X i₁₂ ⟶ A}
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (hi : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂),
      K.ιTotal c₁₂ i₁ i₂ i₁₂ hi ≫ f = K.ιTotal c₁₂ i₁ i₂ i₁₂ hi ≫ g) : f = g := by
  apply GradedObject.mapObj_ext
  rintro ⟨i₁, i₂⟩ hi
  exact h i₁ i₂ hi

variable [L.HasTotal c₁₂]

namespace mapAux

@[reassoc (attr := simp)]
lemma d₁_mapMap (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ =
    (φ.f i₁).f i₂ ≫ L.d₁ c₁₂ i₁ i₂ i₁₂ := by
  by_cases h : c₁.Rel i₁ (c₁.next i₁)
  · simp [totalAux.d₁_eq' _ c₁₂ h]
  · simp [d₁_eq_zero _ c₁₂ i₁ i₂ i₁₂ h]

@[reassoc (attr := simp)]
lemma d₂_mapMap (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ =
    (φ.f i₁).f i₂ ≫ L.d₂ c₁₂ i₁ i₂ i₁₂ := by
  by_cases h : c₂.Rel i₂ (c₂.next i₂)
  · simp [totalAux.d₂_eq' _ c₁₂ i₁ h]
  · simp [d₂_eq_zero _ c₁₂ i₁ i₂ i₁₂ h]

@[reassoc]
lemma mapMap_D₁ (i₁₂ i₁₂' : I₁₂) :
    GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ ≫ L.D₁ c₁₂ i₁₂ i₁₂' =
      K.D₁ c₁₂ i₁₂ i₁₂' ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂' := by
  aesop_cat

@[reassoc]
lemma mapMap_D₂ (i₁₂ i₁₂' : I₁₂) :
    GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ ≫ L.D₂ c₁₂ i₁₂ i₁₂' =
      K.D₂ c₁₂ i₁₂ i₁₂' ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂' := by
  aesop_cat

end mapAux

/-- The morphism `K.total c₁₂ ⟶ L.total c₁₂` of homological complexes induced
by a morphism of bicomplexes `K ⟶ L`. -/
noncomputable def map : K.total c₁₂ ⟶ L.total c₁₂ where
  f := GradedObject.mapMap (toGradedObjectMap φ) _
  comm' i₁₂ i₁₂' _ := by
    dsimp [total]
    rw [comp_add, add_comp, mapAux.mapMap_D₁, mapAux.mapMap_D₂]

@[simp]
lemma forget_map :
    (HomologicalComplex.forget C c₁₂).map (map φ c₁₂) =
      GradedObject.mapMap (toGradedObjectMap φ) _ := rfl

variable (K) in
@[simp]
lemma map_id : map (𝟙 K) c₁₂ = 𝟙 _ := by
  apply (HomologicalComplex.forget _ _).map_injective
  apply GradedObject.mapMap_id

variable [M.HasTotal c₁₂]

@[simp, reassoc]
lemma map_comp : map (φ ≫ ψ) c₁₂ = map φ c₁₂ ≫ map ψ c₁₂ := by
  apply (HomologicalComplex.forget _ _).map_injective
  exact GradedObject.mapMap_comp (toGradedObjectMap φ) (toGradedObjectMap ψ) _

/-- The isomorphism `K.total c₁₂ ≅ L.total c₁₂` of homological complexes induced
by an isomorphism of bicomplexes `K ≅ L`. -/
@[simps]
noncomputable def mapIso : K.total c₁₂ ≅ L.total c₁₂ where
  hom := map e.hom _
  inv := map e.inv _
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

end total

section

variable [L.HasTotal c₁₂]

@[reassoc (attr := simp)]
lemma ιTotal_map (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ (total.map φ c₁₂).f i₁₂ =
      (φ.f i₁).f i₂ ≫ L.ιTotal c₁₂ i₁ i₂ i₁₂ h := by
  simp [total.map, ιTotal]

@[reassoc (attr := simp)]
lemma ιTotalOrZero_map (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    K.ιTotalOrZero c₁₂ i₁ i₂ i₁₂ ≫ (total.map φ c₁₂).f i₁₂ =
      (φ.f i₁).f i₂ ≫ L.ιTotalOrZero c₁₂ i₁ i₂ i₁₂ := by
  simp [total.map, ιTotalOrZero]

end

variable (C c₁ c₂)
variable [∀ (K : HomologicalComplex₂ C c₁ c₂), K.HasTotal c₁₂]

/-- The functor which sends a bicomplex to its total complex. -/
@[simps]
noncomputable def totalFunctor :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₁₂ where
  obj K := K.total c₁₂
  map φ := total.map φ c₁₂

end HomologicalComplex₂
