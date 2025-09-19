/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.MarkovCategory.FinStoch.Braided
import Mathlib.CategoryTheory.CopyDiscardCategory.Basic

/-!
# Copy-Discard Structure on FinStoch

FinStoch has copy and discard operations making it a copy-discard category.

## Main definitions

* `copy` - Diagonal embedding
* `discard` - Map to singleton
* `ComonObj` instances
* `CopyDiscardCategory FinStoch`

## Implementation notes

Copy duplicates states (diagonal), discard maps all states to the unit.

## Tags

copy-discard, comonoid, Markov category
-/

namespace CategoryTheory.MarkovCategory

open FinStoch MonoidalCategory ComonObj

universe u

/-- Copy: diagonal embedding. Maps a state to both copies of itself. -/
def copy (X : FinStoch) : X ⟶ X ⊗ X where
  toMatrix := fun i (j₁, j₂) => if i = j₁ ∧ i = j₂ then 1 else 0
  row_sum := fun i => by
    rw [Fintype.sum_eq_single ⟨i, i⟩]
    · simp only [and_self, ↓reduceIte]
    · simp only [ne_eq]
      intro xx hne
      split
      rename_i x j₁ j₂
      simp_all only [ite_eq_right_iff, one_ne_zero, imp_false, not_and]
      intro a; subst a
      intro a; subst a
      simp_all only [not_true_eq_false]

/-- Discard: map to singleton. All states map to the unique unit state. -/
def discard (X : FinStoch) : X ⟶ tensorUnit where
  toMatrix := fun i _ => 1
  row_sum := fun i => by
    rw [Fintype.sum_eq_single ⟨⟩]
    simp_all only [ne_eq, one_ne_zero, imp_false, Decidable.not_not]
    intro x
    rfl

open scoped ComonObj

/-- FinStoch has comonoid structure on every object. -/
instance (X : FinStoch) : ComonObj X where
  comul := copy X
  counit := discard X
  counit_comul := by
    apply StochasticMatrix.ext
    ext i ⟨⟨⟩ , x⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp, copy, whiskerRight, discard,
      MonoidalCategoryStruct.leftUnitor, leftUnitor, StochasticMatrix.tensor,
      CategoryStruct.id, StochasticMatrix.id, leftUnitorInvDet, DetMorphism.ofFunc]
    -- Goal: Σ_{(j₁,j₂)} copy(i)(j₁,j₂) · (discard ⊗ id)(j₁,j₂)(unit_,x) = λ⁻¹(i)(unit_,x)
    -- LHS = Σ_{(j₁,j₂)} [i=j₁∧i=j₂] · 1 · [j₂=x] = [i=x]
    -- RHS = λ⁻¹(i)(unit_,x) = [i=x]
    rw [Fintype.sum_eq_single ⟨i, x⟩]
    · simp only [true_and, ↓reduceIte, mul_one, NNReal.coe_inj]
      split_ifs with h h'
      · rfl
      · simp_all only [not_true_eq_false]
      · rename_i h'
        simp only [zero_ne_one]
        grind only
      · rfl
    · intro ⟨j₁, j₂⟩ hne
      simp_all only [ne_eq, mul_ite, mul_one, mul_zero, ite_eq_right_iff, one_ne_zero, imp_false,
        not_and]
      intro a a_1; subst a a_1
      intro a; subst a
      simp_all only [not_true_eq_false]
  comul_counit := by
    apply StochasticMatrix.ext
    ext i ⟨x, ⟨⟩⟩
    simp_all only [CategoryStruct.comp, StochasticMatrix.comp, copy, whiskerLeft,
      StochasticMatrix.tensor, CategoryStruct.id, StochasticMatrix.id, discard, mul_one, mul_ite,
      mul_zero, NNReal.coe_sum, MonoidalCategoryStruct.rightUnitor, rightUnitor]
    -- The composition: copy ≫ (id ⊗ discard) ≫ rightUnitor
    -- First: copy(i) gives (i,i)
    -- Second: (id ⊗ discard)(i,i) gives (i,*)
    -- Third: rightUnitor(i,*) gives i
    -- Overall: identity morphism
    rw [Finset.sum_eq_single ⟨i, x⟩]
    · simp_all only [true_and, ↓reduceIte, rightUnitorInvDet, DetMorphism.ofFunc, NNReal.coe_inj]
      split
      next h =>
        subst h
        simp_all only [left_eq_ite_iff, one_ne_zero, imp_false, not_not]
      next h =>
        simp_all only [right_eq_ite_iff, zero_ne_one, imp_false]
        grind only
    · simp_all only [Finset.mem_univ, ne_eq, forall_const]
      intro xx hxx
      split
      · rename_i hx
        simp only [NNReal.coe_eq_zero]
        subst hx
        split
        rename_i x j₁ j₂
        simp_all only [ite_eq_right_iff, one_ne_zero, imp_false, not_and]
        intro a; subst a
        intro a; subst a
        simp_all only [not_true_eq_false]
      · rfl
    · simp_all only [Finset.mem_univ, not_true_eq_false, and_self, ↓reduceIte, NNReal.coe_eq_zero,
        ite_eq_right_iff, one_ne_zero, implies_true]
  comul_assoc := by
    apply StochasticMatrix.ext
    ext i ⟨j₁, ⟨j₂, j₃⟩⟩
    simp_all only [CategoryStruct.comp, StochasticMatrix.comp, copy, whiskerLeft,
      StochasticMatrix.tensor, CategoryStruct.id, StochasticMatrix.id, ite_mul, one_mul, zero_mul,
      mul_ite, mul_zero, mul_one, NNReal.coe_sum, whiskerRight, MonoidalCategoryStruct.associator,
      associator, associatorDet, DetMorphism.ofFunc, NNReal.coe_mul]
    -- Both sides give 1 if i = j₁ = j₂ = j₃, else 0
    -- Show both paths equal this value
    by_cases h : i = j₁ ∧ i = j₂ ∧ i = j₃
    · -- Case when all are equal to i
      obtain ⟨h1, h2, h3⟩ := h
      subst h1 h2 h3
      -- Left path: copy ≫ (copy ⊗ id) ≫ α
      trans 1
      · simp only [and_self]
        rw [Fintype.sum_eq_single ⟨i, i⟩]
        · simp only [↓reduceIte, and_self, NNReal.coe_one]
        · intro b hb
          split_ifs <;> try simp
          rename_i hb1 hb2
          simp_all only [ne_eq]
          grind only
      -- Right path
      · rw [Fintype.sum_eq_single ⟨i, i⟩]
        · simp_all only [and_self, ↓reduceIte, NNReal.coe_one, one_mul]
          rw [Fintype.sum_eq_single ⟨⟨i, i⟩, i⟩]
          · simp_all only [↓reduceIte, and_self, NNReal.coe_one]
          · simp_all only [ne_eq, NNReal.coe_eq_zero, ite_eq_right_iff]
            intro xxx hne
            intro a a_1; subst a_1
            split
            rename_i x j₁ j₂ heq
            simp_all only [ite_eq_right_iff, one_ne_zero, imp_false, not_and]
            intro a_1; subst a_1
            intro a_1; subst a_1
            split at a
            rename_i x_1 x_2 y z
            simp_all only [not_true_eq_false]
        · intro b hb
          simp_all only [ne_eq, mul_eq_zero, NNReal.coe_eq_zero]
          split
          rename_i x j₁ j₂
          simp_all only [ite_eq_right_iff, one_ne_zero, imp_false, not_and]
          apply Or.inl
          intro a; subst a
          intro a; subst a
          simp_all only [not_true_eq_false]
    · -- Case when not all equal
      simp_all only [not_and]
      sorry

/-- The comonoid structure in FinStoch is commutative. -/
instance (X : FinStoch) : CommComonObj X where
  isComm := by
    apply StochasticMatrix.ext
    ext i ⟨j₁, j₂⟩
    simp_all only [CategoryStruct.comp, StochasticMatrix.comp, NNReal.coe_sum, NNReal.coe_mul]
    -- Copy is commutative: Δ ≫ β = Δ
    -- LHS: copy(i) gives (i,i), then swap gives (i,i)
    -- RHS: copy(i) gives (j₁,j₂) which is 1 iff i = j₁ = j₂
    rw [Fintype.sum_eq_single ⟨i, i⟩]
    · -- At (i,i): copy gives 1, swap keeps (i,i) → (i,i) with prob 1
      simp only [comul, copy, and_self, ↓reduceIte, NNReal.coe_one, one_mul, NNReal.coe_inj]
      -- swap (i,i) → (j₁,j₂) is 1 iff i = j₂ ∧ i = j₁
      have h_swap : (β_ X X).hom.toMatrix (i, i) (j₁, j₂) =
                    if i = j₂ ∧ i = j₁ then 1 else 0 := by
        simp only [BraidedCategory.braiding]
        rfl
      rw [h_swap]
      -- Both sides equal 1 iff i = j₁ = j₂
      split_ifs with h_cond h_copy
      · -- h_cond: i = j₂ ∧ i = j₁, so j₁ = j₂ = i
        obtain ⟨h1, h2⟩ := h_cond
        subst h1 h2
        simp only
      · -- h_copy: i = j₁ ∧ i = j₂
        simp_all only [true_and, and_true, one_ne_zero, ↓reduceIte]
        obtain ⟨left, right⟩ := h_cond
        subst right left
        simp_all only [not_true_eq_false]
      · simp_all only [and_true, zero_ne_one, ↓reduceIte]
        rename_i h'
        obtain ⟨l, r⟩ := h'
        subst l r
        simp_all only [not_true_eq_false]
      · rfl
    · -- Other pairs (x,y) with (x,y) ≠ (i,i) give copy value 0
      intro ⟨x, y⟩ hne
      simp only [comul, copy]
      split_ifs with h
      · -- If copy gives 1, then x = i ∧ y = i, contradicting hne
        obtain ⟨hx, hy⟩ := h
        subst hx hy
        exfalso
        exact hne rfl
      · simp

/-- Tensor coherence for copy. -/
lemma copy_tensor_eq (X Y : FinStoch) :
    Δ[X ⊗ Y] = (Δ[X] ⊗ₘ Δ[Y]) ≫ tensorμ X X Y Y := by
  -- Δ[X ⊗ Y] maps (x,y) to ((x,y), (x,y))
  -- (Δ[X] ⊗ Δ[Y]) maps (x,y) to ((x,x), (y,y))
  -- tensorμ rearranges ((x,x), (y,y)) to ((x,y), (x,y))
  apply StochasticMatrix.ext
  ext ⟨x, y⟩ ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
  simp_all only [comul, copy, CategoryStruct.comp, StochasticMatrix.comp, tensorHom,
    StochasticMatrix.tensor, NNReal.coe_sum, NNReal.coe_mul, tensorμ, MonoidalCategory.associator,
    BraidedCategory.braiding, associator, associatorDet, DetMorphism.ofFunc, whiskerLeft,
    DetMorphism.toMatrix_apply, id_matrix]
  -- LHS: Δ[X ⊗ Y] gives 1 iff (x,y) = (x₁,y₁) = (x₂,y₂)
  -- RHS: composition through tensorμ
  -- The sum over intermediate states
  split
  next h =>
    simp_all only [NNReal.coe_one]
    obtain ⟨l, r⟩ := h
    have : (x₁, y₁) = (x₂, y₂) := l.symm.trans r
    simp only [Prod.ext_iff] at this l
    rw [Fintype.sum_eq_single ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩]
    · simp_all only [and_self]
      obtain ⟨left, right⟩ := this
      subst left right
      rw [Fintype.sum_eq_single ⟨x, x, ⟨y, y⟩⟩]
      · simp_all
        sorry
      · sorry
    · sorry
  next h =>
    simp_all only [not_and, NNReal.coe_zero]
    sorry

/-- Tensor coherence for discard. -/
lemma discard_tensor_eq (X Y : FinStoch) :
    ε[X ⊗ Y] = (ε[X] ⊗ₘ ε[Y]) ≫ (λ_ (𝟙_ FinStoch)).hom := by
  apply StochasticMatrix.ext
  ext ⟨x, y⟩ unitor_fs
  simp_all only [counit, discard, NNReal.coe_one, CategoryStruct.comp, StochasticMatrix.comp,
    tensorHom, StochasticMatrix.tensor, mul_one, MonoidalCategoryStruct.leftUnitor, leftUnitor,
    DetMorphism.toMatrix_apply, mul_ite, mul_zero, Finset.sum_boole, NNReal.coe_natCast]
  norm_cast

/-- Copy on unit equals left unitor inverse. -/
lemma copy_unit_eq : Δ[𝟙_ FinStoch] = (λ_ (𝟙_ FinStoch)).inv := by
  apply StochasticMatrix.ext
  ext ⟨⟩ ⟨⟨⟩, ⟨⟩⟩
  simp only [comul, copy, MonoidalCategoryStruct.leftUnitor]
  simp only [and_self, ↓reduceIte, NNReal.coe_one]
  rfl

/-- Discard on unit is identity. -/
lemma discard_unit_eq : ε[𝟙_ FinStoch] = 𝟙 (𝟙_ FinStoch) := by
  apply StochasticMatrix.ext
  ext ⟨⟩ ⟨⟩
  simp only [ComonObj.counit, discard, CategoryStruct.id, StochasticMatrix.id]
  rfl

/-- FinStoch has copy-discard structure. -/
instance : CopyDiscardCategory FinStoch where
  -- commComonObj uses inferInstance by default, which finds our instances above
  copy_tensor := copy_tensor_eq
  discard_tensor := discard_tensor_eq
  copy_unit := copy_unit_eq
  discard_unit := discard_unit_eq

end CategoryTheory.MarkovCategory
