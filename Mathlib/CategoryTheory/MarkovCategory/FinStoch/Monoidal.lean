/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.MarkovCategory.FinStoch.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Data.NNReal.Basic

/-!
# Monoidal Structure on FinStoch

Tensor products model independent parallel processes.

## Main definitions

* `associator` - Isomorphism `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`
* `leftUnitor` - Isomorphism `I ⊗ X ≅ X`
* `rightUnitor` - Isomorphism `X ⊗ I ≅ X`

## Implementation notes

Structural morphisms use deterministic functions.
Proofs use functional reasoning instead of matrix calculations.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]

## Tags

Markov category, monoidal category, stochastic matrix
-/

namespace CategoryTheory.MarkovCategory

open FinStoch MonoidalCategory

universe u

open FinStoch

/-! ### Structural isomorphisms using DetMorphism -/

/-- Rearranges `((X ⊗ Y) ⊗ Z)` to `(X ⊗ (Y ⊗ Z))`. -/
def associator (X Y Z : FinStoch) :
    (tensorObj (tensorObj X Y) Z) ≅ (tensorObj X (tensorObj Y Z)) where
  hom := (associatorDet X Y Z).toStochastic
  inv := (associatorInvDet X Y Z).toStochastic
  hom_inv_id := by
    apply StochasticMatrix.ext
    ext ⟨⟨x, y⟩, z⟩ ⟨⟨x', y'⟩, z'⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single ⟨x, ⟨y, z⟩⟩]
    · simp only [associatorDet, associatorInvDet, DetMorphism.ofFunc]
      cat_disch
    · intro b _ hb
      simp only [associatorDet, associatorInvDet, DetMorphism.ofFunc]
      cat_disch
    · intro h; exfalso; exact h (Finset.mem_univ _)
  inv_hom_id := by
    apply StochasticMatrix.ext
    ext ⟨x, ⟨y, z⟩⟩ ⟨x', ⟨y', z'⟩⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single ⟨⟨x, y⟩, z⟩]
    · simp only [associatorInvDet, associatorDet, DetMorphism.ofFunc]
      cat_disch
    · intro b _ hb
      simp only [associatorInvDet, associatorDet, DetMorphism.ofFunc]
      cat_disch
    · intro h; exfalso; exact h (Finset.mem_univ _)

/-- Removes trivial left factor from `I ⊗ X` to get `X`. -/
def leftUnitor (X : FinStoch) : (tensorObj tensorUnit X) ≅ X where
  hom := (leftUnitorDet X).toStochastic
  inv := (leftUnitorInvDet X).toStochastic
  hom_inv_id := by
    apply StochasticMatrix.ext
    ext ⟨⟨⟩, x⟩ ⟨⟨⟩, x'⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single x]
    · simp only [leftUnitorDet, leftUnitorInvDet, DetMorphism.ofFunc]
      cat_disch
    · simp only [leftUnitorDet, leftUnitorInvDet, DetMorphism.ofFunc]
      cat_disch
    · intro h; exfalso; exact h (Finset.mem_univ _)
  inv_hom_id := by
    apply StochasticMatrix.ext
    ext x x'
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single ⟨⟨⟩, x⟩]
    · simp only [leftUnitorInvDet, leftUnitorDet, DetMorphism.ofFunc]
      cat_disch
    · simp only [leftUnitorDet, leftUnitorInvDet, DetMorphism.ofFunc]
      cat_disch
    · intro h; exfalso; exact h (Finset.mem_univ _)

/-- Removes trivial right factor from `X ⊗ I` to get `X`. -/
def rightUnitor (X : FinStoch) : (tensorObj X tensorUnit) ≅ X where
  hom := (rightUnitorDet X).toStochastic
  inv := (rightUnitorInvDet X).toStochastic
  hom_inv_id := by
    apply StochasticMatrix.ext
    ext ⟨x, ⟨⟩⟩ ⟨x', ⟨⟩⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single x]
    · simp only [rightUnitorDet, rightUnitorInvDet, DetMorphism.ofFunc]
      cat_disch
    · simp only [rightUnitorDet, rightUnitorInvDet, DetMorphism.ofFunc]
      cat_disch
    · intro h; exfalso; exact h (Finset.mem_univ _)
  inv_hom_id := by
    apply StochasticMatrix.ext
    ext x x'
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single ⟨x, ⟨⟩⟩]
    · simp only [rightUnitorDet, rightUnitorInvDet, DetMorphism.ofFunc]
      cat_disch
    · simp only [rightUnitorDet, rightUnitorInvDet, DetMorphism.ofFunc]
      cat_disch
    · intro h; exfalso; exact h (Finset.mem_univ _)

/-- Basic monoidal structure on FinStoch using tensor products. -/
instance : MonoidalCategoryStruct FinStoch where
  tensorObj := tensorObj
  tensorUnit := tensorUnit
  tensorHom f g := StochasticMatrix.tensor f g
  whiskerLeft := fun X {_ _} f => StochasticMatrix.tensor (𝟙 X) f
  whiskerRight := fun {_ _} f Y => StochasticMatrix.tensor f (𝟙 Y)
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

/-! ### Simp lemmas for structural morphisms -/

/-- Matrix entry for associator. -/
@[simp]
lemma associator_matrix (X Y Z : FinStoch) (xyz : ((X ⊗ Y) ⊗ Z).carrier)
    (xyz' : (X ⊗ (Y ⊗ Z)).carrier) :
    (MonoidalCategoryStruct.associator X Y Z).hom.toMatrix xyz xyz' =
    if xyz.1.1 = xyz'.1 ∧ xyz.1.2 = xyz'.2.1 ∧ xyz.2 = xyz'.2.2 then 1 else 0 := by
  simp only [MonoidalCategoryStruct.associator, associator, DetMorphism.toMatrix_apply]
  simp only [associatorDet, DetMorphism.ofFunc]
  aesop

/-- Matrix entry for left unitor. -/
@[simp]
lemma leftUnitor_matrix (X : FinStoch) (ux : (FinStoch.tensorUnit ⊗ X).carrier)
    (x : X.carrier) :
    (MonoidalCategoryStruct.leftUnitor X).hom.toMatrix ux x =
    if ux.2 = x then 1 else 0 := by
  simp only [MonoidalCategoryStruct.leftUnitor, leftUnitor, DetMorphism.toMatrix_apply]
  simp only [leftUnitorDet, DetMorphism.ofFunc]
  obtain ⟨⟨⟩, x'⟩ := ux
  simp only

/-- Matrix entry for right unitor. -/
@[simp]
lemma rightUnitor_matrix (X : FinStoch) (xu : (X ⊗ FinStoch.tensorUnit).carrier)
    (x : X.carrier) :
    (MonoidalCategoryStruct.rightUnitor X).hom.toMatrix xu x =
    if xu.1 = x then 1 else 0 := by
  simp only [MonoidalCategoryStruct.rightUnitor, rightUnitor]
  simp only [rightUnitorDet, DetMorphism.ofFunc]
  obtain ⟨x', ⟨⟩⟩ := xu
  simp only

/-! ### Deterministic morphisms -/

section Deterministic

open StochasticMatrix

/-- The associator is deterministic. -/
lemma associator_isDeterministic (X Y Z : FinStoch) :
    (α_ X Y Z).hom.isDeterministic := (associatorDet X Y Z).is_det

/-- The inverse associator is deterministic. -/
lemma associator_inv_isDeterministic (X Y Z : FinStoch) :
    (α_ X Y Z).inv.isDeterministic := (associatorInvDet X Y Z).is_det

/-- The left unitor is deterministic. -/
lemma leftUnitor_isDeterministic (X : FinStoch) :
    (λ_ X).hom.isDeterministic := (leftUnitorDet X).is_det

/-- The inverse left unitor is deterministic. -/
lemma leftUnitor_inv_isDeterministic (X : FinStoch) :
    (λ_ X).inv.isDeterministic := (leftUnitorInvDet X).is_det

/-- The right unitor is deterministic. -/
lemma rightUnitor_isDeterministic (X : FinStoch) :
    (ρ_ X).hom.isDeterministic := (rightUnitorDet X).is_det

/-- The inverse right unitor is deterministic. -/
lemma rightUnitor_inv_isDeterministic (X : FinStoch) :
    (ρ_ X).inv.isDeterministic := (rightUnitorInvDet X).is_det

end Deterministic

/-- FinStoch forms a monoidal category. -/
instance : MonoidalCategory FinStoch where
  tensorHom_def := by
    intros X₁ Y₁ X₂ Y₂ f g
    apply StochasticMatrix.ext
    ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    simp only [MonoidalCategoryStruct.tensorHom, StochasticMatrix.tensor,
               MonoidalCategoryStruct.whiskerRight, MonoidalCategoryStruct.whiskerLeft,
               CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single ⟨y₁, x₂⟩]
    · simp only [StochasticMatrix.id, CategoryStruct.id]
      cat_disch
    · simp only [StochasticMatrix.id, CategoryStruct.id]
      cat_disch
    · intro h; exfalso; exact h (Finset.mem_univ _)
  id_tensorHom_id := by
    intros X Y
    apply StochasticMatrix.ext
    ext ⟨x, y⟩ ⟨x', y'⟩
    simp only [MonoidalCategoryStruct.tensorHom, StochasticMatrix.tensor]
    simp only [CategoryStruct.id, StochasticMatrix.id]
    by_cases hx : x = x'
    · by_cases hy : y = y'
      · simp [hx, hy]
      · simp [hx, hy]
        split_ifs with h
        · exfalso
          obtain ⟨_, h2⟩ := h
          exact hy rfl
        · rfl
    · simp [hx]
      split_ifs with h
      · exfalso
        obtain ⟨h1, _⟩ := h
        exact hx rfl
      · rfl
  tensor_comp := by
    intros X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
    apply StochasticMatrix.ext
    ext ⟨x₁, x₂⟩ ⟨z₁, z₂⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp,
               MonoidalCategoryStruct.tensorHom, StochasticMatrix.tensor]
    rw [Finset.sum_mul_sum]
    simp_rw [← Finset.sum_product']
    ac_rfl
  whiskerLeft_id := by
    intros X Y
    apply StochasticMatrix.ext
    ext ⟨x, y⟩ ⟨x', y'⟩
    simp only [MonoidalCategoryStruct.whiskerLeft, StochasticMatrix.tensor]
    simp only [CategoryStruct.id, StochasticMatrix.id]
    by_cases hx : x = x'
    · by_cases hy : y = y'
      · subst hx hy; simp
      · subst hx
        simp [hy]
        by_cases h : (x, y) = (x, y')
        · exfalso
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, h2⟩ := h
          exact hy h2
        · simp [h]
    · simp [hx]
      by_cases h : (x, y) = (x', y')
      · exfalso
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, _⟩ := h
        exact hx h1
      · simp [h]
  id_whiskerRight := by
    intros X Y
    apply StochasticMatrix.ext
    ext ⟨x, y⟩ ⟨x', y'⟩
    simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor]
    simp only [CategoryStruct.id, StochasticMatrix.id]
    by_cases hx : x = x'
    · by_cases hy : y = y'
      · subst hx hy
        simp
      · subst hx
        simp [hy]
        by_cases h : (x, y) = (x, y')
        · exfalso
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, h2⟩ := h
          exact hy h2
        · simp [h]
    · simp [hx]
      by_cases h : (x, y) = (x', y')
      · exfalso
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, _⟩ := h
        exact hx h1
      · simp [h]
  associator_naturality := by
    intros X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
    apply StochasticMatrix.ext
    ext ⟨⟨x₁, x₂⟩, x₃⟩ ⟨y₁, ⟨y₂, y₃⟩⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp,
               MonoidalCategoryStruct.tensorHom, StochasticMatrix.tensor]
    rw [Finset.sum_eq_single ⟨⟨y₁, y₂⟩, y₃⟩]
    · simp [associator_matrix]
      rw [Finset.sum_eq_single ⟨x₁, ⟨x₂, x₃⟩⟩]
      · norm_num; ring
      · intro ⟨x₁', ⟨x₂', x₃'⟩⟩ _ h_ne
        by_cases h : x₁' = x₁ ∧ x₂' = x₂ ∧ x₃' = x₃
        · exfalso
          apply h_ne
          simp [h]
        · aesop
      · intro; exfalso; apply ‹_›; exact Finset.mem_univ _
    · intro ⟨⟨y₁', y₂'⟩, y₃'⟩ _ h_ne
      by_cases h : y₁' = y₁ ∧ y₂' = y₂ ∧ y₃' = y₃
      · exfalso
        apply h_ne
        simp only [h]
      · have h_assoc_zero : (MonoidalCategoryStruct.associator Y₁ Y₂ Y₃).hom.toMatrix
                              ((y₁', y₂'), y₃') (y₁, y₂, y₃) = 0 := by
          simp [associator_matrix, h]
        rw [h_assoc_zero, mul_zero]
    · intro; exfalso; apply ‹_›; exact Finset.mem_univ _
  leftUnitor_naturality := by
    intros X Y f
    apply StochasticMatrix.ext
    ext ⟨⟨⟩, x⟩ y
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single ⟨⟨⟩, y⟩]
    · simp [MonoidalCategoryStruct.whiskerLeft, StochasticMatrix.tensor,
            CategoryStruct.id, StochasticMatrix.id]
    · intro ⟨⟨⟩, y'⟩ _ h_ne
      have h_neq : y' ≠ y := by
        intro h_eq
        apply h_ne
        simp only [h_eq]
      simp only [MonoidalCategoryStruct.whiskerLeft, StochasticMatrix.tensor,
                 CategoryStruct.id, StochasticMatrix.id]
      have h_unitor_zero : (MonoidalCategoryStruct.leftUnitor Y).hom.toMatrix (⟨⟩, y') y = 0 := by
        simp [leftUnitor_matrix, h_neq]
      simp [h_unitor_zero]
    · intro h; exfalso; exact h (Finset.mem_univ _)
  rightUnitor_naturality := by
    intros X Y f
    apply StochasticMatrix.ext
    ext ⟨x, ⟨⟩⟩ y
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single ⟨y, ⟨⟩⟩]
    · simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor,
                 CategoryStruct.id, StochasticMatrix.id]
      have h_right_unitor : (MonoidalCategoryStruct.rightUnitor Y).hom.toMatrix (y,⟨⟩) y = 1 := by
        simp [rightUnitor_matrix]
      simp only [h_right_unitor, mul_one]
      rw [Finset.sum_eq_single x]
      · have h_right_unitor :
          (MonoidalCategoryStruct.rightUnitor X).hom.toMatrix (x, ⟨⟩) x = 1 := by
          simp [rightUnitor_matrix]
        simp [h_right_unitor]
      · intro x' _ h_ne
        have h_unitor_zero :
          (MonoidalCategoryStruct.rightUnitor X).hom.toMatrix (x, ⟨⟩) x' = 0 := by
          simp only [rightUnitor_matrix]
          rw [if_neg h_ne.symm]
        simp [h_unitor_zero]
      · intro h; exfalso; exact h (Finset.mem_univ _)
    · intro ⟨y', ⟨⟩⟩ _ h_ne
      have h_neq : y' ≠ y := by
        intro h_eq
        apply h_ne
        simp only [h_eq]
      simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor,
                 CategoryStruct.id, StochasticMatrix.id]
      have h_unitor_zero : (MonoidalCategoryStruct.rightUnitor Y).hom.toMatrix (y', ⟨⟩) y = 0 := by
        simp [rightUnitor_matrix, h_neq]
      simp [h_unitor_zero]
    · intro h; exfalso; exact h (Finset.mem_univ _)
  pentagon := by
    intros W X Y Z
    apply StochasticMatrix.ext
    ext ⟨⟨⟨w, x⟩, y⟩, z⟩ ⟨w', ⟨x', ⟨y', z'⟩⟩⟩
    -- Both paths map ((w,x),y,z) to (w,(x,(y,z))) deterministically
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    -- Left path through the pentagon
    rw [Finset.sum_eq_single ⟨⟨w, ⟨x, y⟩⟩, z⟩]
    · rw [Finset.sum_eq_single ⟨w, ⟨⟨x, y⟩, z⟩⟩]
      · -- Right path
        rw [Finset.sum_eq_single ⟨⟨w, x⟩, ⟨y, z⟩⟩]
        · -- Evaluate all morphisms
          simp only [MonoidalCategoryStruct.whiskerRight, MonoidalCategoryStruct.whiskerLeft,
                     StochasticMatrix.tensor, associator_matrix,
                     CategoryStruct.id, StochasticMatrix.id]
          -- Check equality conditions
          by_cases hw : w = w'
          · by_cases hx : x = x'
            · by_cases hy : y = y'
              · by_cases hz : z = z'
                · subst hw hx hy hz; simp
                · simp [hw, hx, hy, hz]
                  subst hw hx hy
                  split
                  · grind only
                  · rfl
              · simp [hw, hx, hy]
                subst hw hx
                split
                · grind only
                · rfl
            · simp [hw, hx]
          · simp [hw]
        · intro b _ hb
          simp only [associator_matrix, mul_eq_zero]
          left
          split_ifs with h
          · exfalso
            obtain ⟨h1, h2, h3⟩ := h
            have : b = ⟨⟨w, x⟩, ⟨y, z⟩⟩ := by
              cases b; simp [h1, h2, h3]
            exact hb this
          · rfl
        · intro h; exfalso; exact h (Finset.mem_univ _)
      · intro a _ ha
        simp only [associator_matrix, mul_eq_zero]
        left
        split_ifs with h
        · exfalso
          obtain ⟨h1, h2, h3⟩ := h
          have : a = ⟨w, ⟨⟨x, y⟩, z⟩⟩ := by
            cases a; simp [h1, h2, h3]
          exact ha this
        · rfl
      · intro h; exfalso; exact h (Finset.mem_univ _)
    · intro b _ hb
      simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor,
                 associator_matrix, CategoryStruct.id, StochasticMatrix.id, mul_eq_zero]
      left
      split_ifs with h
      · exfalso
        obtain ⟨hw, hx, hy⟩ := h
        have : b = ⟨⟨w, ⟨x, y⟩⟩, z⟩ := by
          cases b; simp_all only [Finset.mem_univ, Prod.mk.eta, ne_eq, not_true_eq_false]
        exact hb this
      · right; rfl
      · left; rfl
      · left; rfl
    · intro h; exfalso; exact h (Finset.mem_univ _)
  triangle := by
    intros X Y
    apply StochasticMatrix.ext
    ext ⟨⟨x, ⟨⟩⟩, y⟩ ⟨x', y'⟩
    -- Both sides map ((x,()),y) to (x,y) deterministically
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    -- The unique intermediate is (x,((),y))
    rw [Finset.sum_eq_single ⟨x, ⟨⟨⟩, y⟩⟩]
    · simp only [associator_matrix, MonoidalCategoryStruct.whiskerLeft,
                 MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor,
                 leftUnitor_matrix, rightUnitor_matrix, CategoryStruct.id, StochasticMatrix.id]
      by_cases hx : x = x'
      · by_cases hy : y = y'
        · subst hx hy; simp
        · simp [hx, hy]
      · simp [hx]
    · intro a _ ha
      obtain ⟨x₁, ⟨⟨⟩, y₁⟩⟩ := a
      cat_disch
    · intro h; exfalso; exact h (Finset.mem_univ _)

end CategoryTheory.MarkovCategory
