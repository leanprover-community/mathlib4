/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.MarkovCategory.FinStoch.Monoidal
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braided Structure on FinStoch

FinStoch is symmetric monoidal with swap as the braiding.

## Main definitions

* `swap` - Swaps components of tensor products
* `BraidedCategory FinStoch` - Braiding structure
* `SymmetricCategory FinStoch` - Symmetric structure

## Tags

Markov category, braided category, symmetric category
-/

namespace CategoryTheory.MarkovCategory

open FinStoch MonoidalCategory

universe u

/-- Composition of morphisms with single non-zero path. -/
lemma comp_single_path {X Y Z : FinStoch} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X.carrier) (y : Y.carrier) (z : Z.carrier)
    (hf : ∀ y', y' ≠ y → f.toMatrix x y' = 0) :
    (f ≫ g).toMatrix x z = f.toMatrix x y * g.toMatrix y z := by
  simp only [CategoryStruct.comp, StochasticMatrix.comp]
  rw [Finset.sum_eq_single y]
  · intro y' _ hy'
    simp [hf y' hy']
  · intro h; exfalso; exact h (Finset.mem_univ _)

/-- The identity matrix has 1 on the diagonal and 0 elsewhere. -/
@[simp]
lemma id_matrix {X : FinStoch} (x x' : X.carrier) :
    (𝟙 X : X ⟶ X).toMatrix x x' = if x = x' then 1 else 0 := by
  simp only [CategoryStruct.id, StochasticMatrix.id]

/-- The associator morphism applied to matrix elements. -/
lemma associator_toMatrix {X Y Z : FinStoch} (xyz : ((X ⊗ Y) ⊗ Z).carrier)
    (xyz' : (X ⊗ (Y ⊗ Z)).carrier) :
    (α_ X Y Z).hom.toMatrix xyz xyz' =
    if xyz.1.1 = xyz'.1 ∧ xyz.1.2 = xyz'.2.1 ∧ xyz.2 = xyz'.2.2 then 1 else 0 := by
  cases xyz with | mk xy z =>
  cases xy with | mk x y =>
  cases xyz' with | mk x' yz' =>
  cases yz' with | mk y' z' =>
  simp only [MonoidalCategoryStruct.associator, associator, associatorDet, DetMorphism.ofFunc]
  grind only [cases Or]

/-- Inverse associator applied to matrix elements. -/
@[simp]
lemma associator_inv_toMatrix {X Y Z : FinStoch} (xyz : (X ⊗ (Y ⊗ Z)).carrier)
    (xyz' : ((X ⊗ Y) ⊗ Z).carrier) :
    (α_ X Y Z).inv.toMatrix xyz xyz' =
    if xyz.1 = xyz'.1.1 ∧ xyz.2.1 = xyz'.1.2 ∧ xyz.2.2 = xyz'.2 then 1 else 0 := by
  cases xyz with | mk x yz =>
  cases yz with | mk y z =>
  cases xyz' with | mk xy' z' =>
  cases xy' with | mk x' y' =>
  simp only [MonoidalCategoryStruct.associator, associator, associatorInvDet, DetMorphism.ofFunc]
  grind only [cases Or]

/-- Special case: the associator maps ((x,y),z) to (x,(y,z)). -/
lemma associator_apply {X Y Z : FinStoch} (x : X.carrier) (y : Y.carrier) (z : Z.carrier) :
    (α_ X Y Z).hom.toMatrix ((x, y), z) (x, (y, z)) = 1 := by
    simp

/-- Special case: the associator is 0 when the x-component doesn't match. -/
lemma associator_apply_ne_fst {X Y Z : FinStoch} (x x' : X.carrier) (y : Y.carrier)
    (z : Z.carrier) (yz : (Y ⊗ Z).carrier) (h : x ≠ x') :
    (α_ X Y Z).hom.toMatrix ((x, y), z) (x', yz) = 0 := by
  cases yz with | mk y' z' =>
  simp [h]

/-- The inverse associator maps (x,(y,z)) to ((x,y),z). -/
lemma associator_inv_apply {X Y Z : FinStoch} (x : X.carrier) (y : Y.carrier) (z : Z.carrier) :
    (α_ X Y Z).inv.toMatrix (x, (y, z)) ((x, y), z) = 1 := by
  simp [associator_inv_toMatrix]

/-- Inverse associator is 0 when x-components don't match. -/
lemma associator_inv_apply_ne_fst {X Y Z : FinStoch} (x x' : X.carrier) (y : Y.carrier)
    (z : Z.carrier) (y' : Y.carrier) (z' : Z.carrier) (h : x ≠ x') :
    (α_ X Y Z).inv.toMatrix (x, (y, z)) ((x', y'), z') = 0 := by
  simp [associator_inv_toMatrix, h]

/-- Swaps components of tensor products. -/
def swap (X Y : FinStoch) : X ⊗ Y ⟶ Y ⊗ X where
  toMatrix := fun (x, y) (y', x') => if x = x' ∧ y = y' then 1 else 0
  row_sum := fun (x, y) => by
    -- We need to show: ∑_{(y',x')} swap((x,y), (y',x')) = 1
    -- The matrix has a 1 at position (y,x) and 0 elsewhere
    convert Finset.sum_eq_single (y, x) _ _ using 1
    · -- At (y, x): we get 1
      simp only [and_self, if_true]
    · -- For any other point: we get 0
      intro b _ hb
      obtain ⟨y', x'⟩ := b
      simp only
      -- If x = x' and y = y', then b = (y,x), contradiction
      by_cases hx : x = x'
      · by_cases hy : y = y'
        · -- Both match, so b = (y,x)
          subst hx hy
          exfalso
          exact hb rfl
        · -- y ≠ y', so condition fails
          simp [hx, hy]
      · -- x ≠ x', so condition fails
        simp [hx]
    · -- (y,x) is in the set
      intro h
      exfalso
      exact h (Finset.mem_univ _)

/-- The swap morphism applied to matrix elements. -/
@[simp]
lemma swap_toMatrix {X Y : FinStoch} (xy : (X ⊗ Y).carrier) (yx : (Y ⊗ X).carrier) :
    (swap X Y).toMatrix xy yx = if xy.1 = yx.2 ∧ xy.2 = yx.1 then 1 else 0 := by
  cases xy with | mk x y =>
  cases yx with | mk y' x' =>
  simp [swap]

/-- Special case: swap preserves components when they match. -/
lemma swap_apply {X Y : FinStoch} (x : X.carrier) (y : Y.carrier) :
    (swap X Y).toMatrix (x, y) (y, x) = 1 := by
  simp [swap_toMatrix]

/-- Special case: swap is 0 when x-components don't match. -/
lemma swap_apply_ne_fst {X Y : FinStoch} (x : X.carrier) (y : Y.carrier)
    (x' : X.carrier) (y' : Y.carrier) (h : x ≠ x') :
    (swap X Y).toMatrix (x, y) (y', x') = 0 := by
  simp [swap_toMatrix, h]

/-- Special case: swap is 0 when y-components don't match. -/
lemma swap_apply_ne_snd {X Y : FinStoch} (x : X.carrier) (y : Y.carrier)
    (x' : X.carrier) (y' : Y.carrier) (h : y ≠ y') :
    (swap X Y).toMatrix (x, y) (y', x') = 0 := by
  simp [swap_toMatrix, h]

/-- FinStoch is braided. -/
instance : BraidedCategory FinStoch where
  braiding X Y := ⟨swap X Y, swap Y X, by
    apply StochasticMatrix.ext
    ext ⟨x, y⟩ ⟨x', y'⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp, CategoryStruct.id,
               swap, StochasticMatrix.id]
    -- swap ∘ swap = id because swap is involutive
    -- First simplify the sum to make pattern matching explicit
    have h_sum : (∑ ab : Y.carrier × X.carrier,
          (if x = ab.2 ∧ y = ab.1 then (1 : NNReal) else 0) *
          (if ab.1 = y' ∧ ab.2 = x' then 1 else 0)) =
        if x = x' ∧ y = y' then 1 else 0 := by
      -- The sum has exactly one non-zero term when ab = (y, x)
      rw [Finset.sum_eq_single (y, x)]
      · -- At (y, x): the first condition is true, second depends on y=y' and x=x'
        simp only [and_self]
        simp only [if_true, one_mul]
        -- Now we have: if y = y' ∧ x = x' then 1 else 0
        -- We need: if x = x' ∧ y = y' then 1 else 0
        simp only [and_comm]
      · -- For any other (a, b) ≠ (y, x): show product is 0
        intro ⟨a, b⟩ _ h_ne
        simp only
        split_ifs with h₁ h₂
        · -- If x = b ∧ y = a, then (a, b) = (y, x), contradiction
          exfalso
          apply h_ne
          ext <;> simp only [h₁]
        · simp only [mul_zero]
        · simp only [mul_one]
        · simp only [mul_zero]
      · -- (y, x) is in Finset.univ
        intro h_not_mem
        exfalso
        exact h_not_mem (Finset.mem_univ _)
    -- Now convert and apply our result
    convert congr_arg NNReal.toReal h_sum
    constructor
    · intro h
      cases h
      constructor <;> rfl
    · intro ⟨h1, h2⟩
      cases h1
      cases h2
      rfl
  , by
    apply StochasticMatrix.ext
    ext ⟨y, x⟩ ⟨y', x'⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp, id_matrix, swap]
    -- swap ∘ swap = id
    -- First simplify the sum
    have h_sum : (∑ ab : X.carrier × Y.carrier,
          (if y = ab.2 ∧ x = ab.1 then (1 : NNReal) else 0) *
          (if ab.1 = x' ∧ ab.2 = y' then 1 else 0)) =
        if y = y' ∧ x = x' then 1 else 0 := by
      -- The sum has exactly one non-zero term when ab = (x, y)
      rw [Finset.sum_eq_single (x, y)]
      · -- At (x, y): the first condition is true, second depends on x=x' and y=y'
        simp only [and_self]
        simp only [if_true, one_mul]
        -- Now we have: if x = x' ∧ y = y' then 1 else 0
        -- We need: if y = y' ∧ x = x' then 1 else 0
        simp only [and_comm]
      · -- For any other (a, b) ≠ (x, y): show product is 0
        intro ⟨a, b⟩ _ h_ne
        simp only
        split_ifs with h₁ h₂
        · -- If y = b ∧ x = a, then (a, b) = (x, y), contradiction
          exfalso
          apply h_ne
          ext <;> simp only [h₁]
        · simp only [mul_zero]
        · simp only [mul_one]
        · simp only [mul_zero]
      · -- (x, y) is in Finset.univ
        intro h_not_mem
        exfalso
        exact h_not_mem (Finset.mem_univ _)
    -- Now convert and apply our result
    convert congr_arg NNReal.toReal h_sum
    constructor
    · intro h
      cases h
      constructor <;> rfl
    · intro ⟨h1, h2⟩
      cases h1
      cases h2
      rfl⟩
  braiding_naturality_left := by
    intros X Y f Z
    apply StochasticMatrix.ext
    ext ⟨x, z⟩ ⟨z', y'⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp, MonoidalCategoryStruct.whiskerRight,
               StochasticMatrix.tensor, swap, CategoryStruct.id, StochasticMatrix.id,
               MonoidalCategoryStruct.whiskerLeft]
    -- (f ▷ Z) ≫ β_{Y,Z} = β_{X,Z} ≫ (Z ◁ f)
    -- Both sides compute to: if z = z' then f(x,y') else 0

    -- Compute both sides to the same intermediate value
    trans (if z = z' then f.toMatrix x y' else 0 : NNReal).toReal
    · congr 1
      -- LHS = ∑_{(y₁,z₁)} (f ⊗ id_Z)_{(x,z),(y₁,z₁)} * swap_{y₁,z₁,z',y'}
      convert Finset.sum_eq_single (y', z) _ _ using 1
      · -- At (y', z): we get f(x,y') * (if z = z then 1 else 0) *
        -- (if y' = y' ∧ z = z' then 1 else 0)
        simp only [if_true]
        by_cases hz : z = z'
        · simp [hz]
        · simp [hz]
      · -- For other points: show the sum term is 0
        intro ⟨y₁, z₁⟩ _ h_ne
        -- We have f(x,y₁) * (if z = z₁ then 1 else 0) * (if y₁ = y' ∧ z₁ = z' then 1 else 0)
        by_cases hz₁ : z = z₁
        · subst hz₁
          by_cases hyz : y₁ = y' ∧ z = z'
          · obtain ⟨hy₁, _⟩ := hyz
            subst hy₁
            exfalso; exact h_ne rfl
          · simp [hyz]
        · simp [hz₁]
      · intro h; exfalso; exact h (Finset.mem_univ _)

    -- Compute the RHS sum
    · congr 1
      symm
      -- RHS = ∑_{(z₁,x₁)} swap_{x,z,z₁,x₁} * (id_Z ⊗ f)_{(z₁,x₁),(z',y')}
      convert Finset.sum_eq_single (z, x) _ _ using 1
      · -- At (z, x): we get (if x = x ∧ z = z then 1 else 0) *
        -- ((if z = z' then 1 else 0) * f(x,y'))
        simp only [and_self, if_true]
        by_cases hz : z = z'
        · simp [hz]
        · simp [hz]
      · -- For other points: show the sum term is 0
        intro ⟨z₁, x₁⟩ _ h_ne
        -- We have (if x = x₁ ∧ z = z₁ then 1 else 0) * ((if z₁ = z' then 1 else 0) * f(x₁,y'))
        by_cases hxz : x = x₁ ∧ z = z₁
        · obtain ⟨hx₁, hz₁⟩ := hxz
          subst hx₁ hz₁
          exfalso; exact h_ne rfl
        · simp [hxz]
      · intro h; exfalso; exact h (Finset.mem_univ _)
  braiding_naturality_right := by
    intros X Y Z f
    apply StochasticMatrix.ext
    ext ⟨x, y⟩ ⟨z', x'⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp, MonoidalCategoryStruct.whiskerLeft,
               StochasticMatrix.tensor, swap, CategoryStruct.id, StochasticMatrix.id,
               MonoidalCategoryStruct.whiskerRight]
    -- (X ◁ f) ≫ β_{X,Z} = β_{X,Y} ≫ (f ▷ X)
    -- Both sides compute to: if x = x' then f(y,z') else 0

    -- Compute the LHS sum
    trans (if x = x' then f.toMatrix y z' else 0 : NNReal).toReal
    · congr 1
      -- LHS = ∑_{(x₁,z₁)} (id_X ⊗ f)_{(x,y),(x₁,z₁)} * swap_{x₁,z₁,x',z'}
      convert Finset.sum_eq_single (x, z') _ _ using 1
      · -- We get (if x = x then 1 else 0) * f(y,z') * (if x = x' ∧ z' = z' then 1 else 0)
        simp only [if_true, one_mul]
        by_cases hx : x = x'
        · simp [hx]
        · simp [hx]
      · -- For other points: show the sum term is 0
        intro ⟨x₁, z₁⟩ _ h_ne
        -- We have (if x = x₁ then 1 else 0) * f(y,z₁) * (if x₁ = x' ∧ z₁ = z' then 1 else 0)
        by_cases hx₁ : x = x₁
        · subst hx₁
          by_cases hxz : x = x' ∧ z₁ = z'
          · obtain ⟨_, hz₁⟩ := hxz
            subst hz₁
            exfalso; exact h_ne rfl
          · simp [hxz]
        · simp [hx₁]
      · intro h; exfalso; exact h (Finset.mem_univ _)

    -- Compute the RHS sum
    · congr 1
      symm
      -- RHS = ∑_{(y₁,x₁)} swap_{x,y,x₁,y₁} * (f ⊗ id_X)_{(y₁,x₁),(z',x')}
      convert Finset.sum_eq_single (y, x) _ _ using 1
      · -- At (y, x): we get (if x = x ∧ y = y then 1 else 0) *
        -- (f(y,z') * (if x = x' then 1 else 0))
        simp only [and_self, if_true]
        by_cases hx : x = x'
        · simp [hx]
        · simp [hx]
      · -- For other points: show the sum term is 0
        intro ⟨y₁, x₁⟩ _ h_ne
        -- We have (if x = x₁ ∧ y = y₁ then 1 else 0) * (f(y₁,z') * (if x₁ = x' then 1 else 0))
        by_cases hxy : x = x₁ ∧ y = y₁
        · obtain ⟨hx₁, hy₁⟩ := hxy
          subst hx₁ hy₁
          exfalso; exact h_ne rfl
        · simp [hxy]
      · intro h; exfalso; exact h (Finset.mem_univ _)
  hexagon_forward := by
    intros X Y Z
    -- Show: α ≫ β_{X,Y⊗Z} ≫ α = (β_{X,Y} ▷ Z) ≫ α ≫ (Y ◁ β_{X,Z})
    -- Both map ((x,y),z) to (y,(z,x))
    apply StochasticMatrix.ext
    ext ⟨⟨x, y⟩, z⟩ ⟨y', ⟨z', x'⟩⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp,
               MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor,
               swap, MonoidalCategoryStruct.whiskerLeft]

    -- Both sides equal 1 iff x = x' ∧ y = y' ∧ z = z'
    trans (if x = x' ∧ y = y' ∧ z = z' then (1:NNReal) else 0).toReal
    · -- LHS computation: should equal if x = x' ∧ y = y' ∧ z = z' then 1 else 0
      -- The path is: ((x,y),z) → (x,(y,z)) → ((y,z),x) → (y,(z,x))
      -- Each step has probability 1 when the path is followed correctly
      congr 1
      by_cases h : x = x' ∧ y = y' ∧ z = z'
      · -- Case: the variables match, so we expect 1
        obtain ⟨hx, hy, hz⟩ := h
        subst hx hy hz
        simp only [and_true, if_true]
        -- Now we need to show the sum equals 1
        -- The sum should collapse to a single term
        convert Finset.sum_eq_single (x, (y, z)) _ _ using 1
        · -- At the unique non-zero term
          -- The associator at ((x,y),z) -> (x,(y,z)) is 1
          have h_assoc : (α_ X Y Z).hom.toMatrix ((x, y), z) (x, (y, z)) = 1 := by
            -- The associator in FinStoch is defined as: if x = x' ∧ y = y' ∧ z = z' then 1 else 0
            -- At ((x,y),z) -> (x,(y,z)), all components match, so we get 1
            simp [MonoidalCategoryStruct.associator, associator, DetMorphism.toMatrix_apply]
            rfl
          simp only [h_assoc, one_mul]
          rw [eq_comm]
          -- The sum has a single non-zero term at ((y,z), x)
          have h_sum : ∑ x_1, (match x_1 with | (y', x') => if x = x' ∧ (y, z) = y' then 1 else 0) *
              (α_ Y Z X).hom.toMatrix x_1 (y, z, x) =
                 ∑ x_1, (if x_1 = ((y, z), x) then 1 else 0) *
              (α_ Y Z X).hom.toMatrix x_1 (y, z, x) := by
                congr 1
                ext x_1
                cases x_1 with | mk y' x' =>
                simp only
                -- Show the match expression equals the if condition
                by_cases h : x = x' ∧ (y, z) = y'
                · simp [h]
                · simp [h]
                  have : ¬(y' = (y, z) ∧ x' = x) := by
                    rw [and_comm]
                    grind only
                  simp [this]
          -- Use h_sum to transform the match expression
          trans (∑ x_1, (if x_1 = ((y, z), x) then 1 else 0) *
                        (α_ Y Z X).hom.toMatrix x_1 (y, z, x))
          · exact h_sum
          -- Now we have a sum with a single non-zero term at ((y,z), x)
          rw [Finset.sum_eq_single ((y, z), x)]
          · simp only [if_true, one_mul]
            -- The associator at ((y,z), x) -> (y,(z,x)) gives 1
            have h_assoc2 : (α_ Y Z X).hom.toMatrix ((y, z), x) (y, (z, x)) = 1 := by
              simp [MonoidalCategoryStruct.associator, associator, DetMorphism.toMatrix_apply]
              rfl
            simp only [h_assoc2]
          · intro b _ hb
            simp [hb]
          · intro h_mem; exfalso; exact h_mem (Finset.mem_univ _)
        · -- Other x₁ terms are 0
          intro x₁ _ hx₁
          -- The associator gives 0 for x₁ ≠ (x, (y, z))
          have h_zero : (α_ X Y Z).hom.toMatrix ((x, y), z) x₁ = 0 := by
            simp [MonoidalCategoryStruct.associator, associator, DetMorphism.toMatrix_apply]
            tauto
          simp [h_zero]
        · intro h_mem; exfalso; exact h_mem (Finset.mem_univ _)
      · -- Case: variables don't match, so we expect 0
        simp only [h, if_false]
        -- Show the entire sum is 0
        rw [Finset.sum_eq_zero]
        intro x₁ _
        -- We need to show this product is 0
        -- Either the associator gives 0, or the inner sum is 0
        by_cases h_assoc : (α_ X Y Z).hom.toMatrix ((x, y), z) x₁ = 0
        · -- Associator is 0, so product is 0
          simp [h_assoc]
        · -- Associator is non-zero, so x₁ = (x, (y, z))
          push_neg at h_assoc
          have hx₁ : x₁ = (x, (y, z)) := by
            simp_all [MonoidalCategoryStruct.associator, associator, DetMorphism.toMatrix_apply]
            tauto
          subst hx₁
          simp only [MonoidalCategory.associator, associator]
          -- Now show the inner sum is 0
          rw [Finset.sum_eq_zero]
          · simp
          · intro x_inner _
            -- Need to show swap * final_assoc = 0
            cases x_inner with | mk y_inner x_inner =>
            simp only
            -- Check if swap condition holds
            by_cases h_swap : x = x_inner ∧ (y, z) = y_inner
            · -- Swap gives 1, check final associator
              obtain ⟨hx_eq, hy_eq⟩ := h_swap
              subst hx_eq hy_eq
              simp_all [associator_matrix, associatorDet, DetMorphism.ofFunc]
              grind only
            · -- Swap gives 0
              simp [h_swap]

    -- RHS computation
    · congr 1
      symm
      -- RHS: ((x,y),z) → ((y,x),z) → (y,(x,z)) → (y,(z,x))
      -- First swap ⊗ id maps ((x,y),z) ↦ ((y,x),z) with prob 1
      -- Then associator maps ((y,x),z) ↦ (y,(x,z)) with prob 1
      -- Then id ⊗ swap maps (y,(x,z)) ↦ (y,(z,x)) with prob 1

      -- Sum over final state before last operation
      -- The RHS path: swap ⊗ id, then associator, then id ⊗ swap
      simp [id_matrix, associator_matrix]
      -- We need to show the sum equals the indicator function
      by_cases h_match : x = x' ∧ y = y' ∧ z = z'
      · -- Case: all match, result should be 1
        obtain ⟨hx, hy, hz⟩ := h_match
        subst hx hy hz
        simp
        -- The sum should collapse to a single non-zero term
        convert Finset.sum_eq_single ((y, x), z) _ _ using 1
        · -- At ((y,x),z): show it produces 1
          simp
          -- The sum equals 1 as only (y, (x, z)) contributes
          -- Simplify to show the sum has exactly one non-zero term
          have h_sum_eq : (∑ x_1 : Y.carrier × (X.carrier × Z.carrier),
                if x_1.1 = y then
                  if y = x_1.1 ∧ x = x_1.2.1 ∧ z = x_1.2.2 then
                    match x_1.2 with | (x_2, z_2) => if x_2 = x ∧ z_2 = z then 1 else 0
                  else 0
                else 0) = (1 : NNReal) := by
            rw [Finset.sum_eq_single (y, (x, z))]
            · simp
            · intro ⟨y₁, x₁, z₁⟩ _ hne
              by_cases hy : y₁ = y
              · simp [hy]
                by_cases hxz : x = x₁ ∧ z = z₁
                · obtain ⟨hx, hz⟩ := hxz
                  subst hy hx hz
                  exfalso; exact hne rfl
                · push_neg at hxz
                  by_cases hx : x = x₁
                  · simp [hx, hxz hx]
                  · simp [hx]
              · simp [hy]
            · intro h; exfalso; exact h (Finset.mem_univ _)
          grind only [cases eager Prod, cases Or]
        · -- Other x₁ values give 0
          grind only [cases eager Prod]
        · intro h; exfalso; exact h (Finset.mem_univ _)
      · -- Case: not all match, result should be 0
        simp only [h_match, if_false]
        -- Show the sum is 0
        rw [Finset.sum_eq_zero]
        intro x₁ _
        -- We analyze based on whether x₁ = ((y,x),z)
        by_cases hx₁ : x₁ = ((y, x), z)
        · subst hx₁
          simp only [and_self, if_true, one_mul, one_mul]
          -- Sum over associator output
          rw [Finset.sum_eq_zero]
          intro c _
          split_ifs with h_assoc
          · -- Associator gives 1, so c = (y,(x,z))
            -- The conditions mean c.1 = y' and c.2.1 = x and c.2.2 = z
            -- So c = (y', (x, z))
            -- Now check the swap condition
            grind only [Finset.mem_univ, cases Or]
          · rfl
          · rfl
        · -- x₁ ≠ ((y,x),z): first swap gives 0
          simp_all
          -- Grind out the rest of the proof
          grind only [cases Or]

  hexagon_reverse := by
    intros X Y Z
    -- Show: α^{-1} ≫ β_{X⊗Y,Z} ≫ α^{-1} = (X ◁ β_{Y,Z}) ≫ α^{-1} ≫ (β_{X,Z} ▷ Y)
    -- Both map (x,(y,z)) to ((z,x),y)
    apply StochasticMatrix.ext
    ext ⟨x, ⟨y, z⟩⟩ ⟨⟨z', x'⟩, y'⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp,
               MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor,
               swap, MonoidalCategoryStruct.whiskerLeft]

    -- Both sides equal 1 iff x = x' ∧ y = y' ∧ z = z'
    trans (if x = x' ∧ y = y' ∧ z = z' then (1:NNReal) else 0).toReal
    · -- LHS: (x,(y,z)) → ((x,y),z) → (z,(x,y)) → ((z,x),y)
      congr 1
      by_cases h : x = x' ∧ y = y' ∧ z = z'
      · -- Case: all match, expect 1
        obtain ⟨hx, hy, hz⟩ := h
        subst hx hy hz
        simp only [and_true, if_true]
        -- Sum collapses to single term
        convert Finset.sum_eq_single ((x, y), z) _ _ using 1
        · -- At ((x,y),z): α_inv gives 1
          have h1 : (α_ X Y Z).inv.toMatrix (x, (y, z)) ((x, y), z) = 1 :=
            associator_inv_apply x y z
          symm
          simp [associator_inv_toMatrix]
          -- Now compute swap and final α_inv
          convert Finset.sum_eq_single (z, (x, y)) _ _ using 1
          · -- swap gives 1, then α_inv gives 1
            simp
          · intro b _ hb
            -- swap is deterministic, only maps to (z,(x,y))
            cases b with | mk b1 b2 =>
            simp only
            by_cases h_swap : (x, y) = b2 ∧ z = b1
            · obtain ⟨h_xy, h_z⟩ := h_swap
              subst h_xy h_z
              exfalso; exact hb rfl
            · simp
              tauto
          · intro habs; exfalso; exact habs (Finset.mem_univ _)
        · -- Other terms are 0
          intro b _ hb
          -- α_inv is deterministic, only maps to ((x,y),z)
          have h_inv : (α_ X Y Z).inv.toMatrix (x, (y, z)) b =
            if b = ((x, y), z) then 1 else 0 := by
            cases b with | mk b1 b2 =>
            cases b1 with | mk b11 b12 =>
            simp only [associator_inv_toMatrix]
            by_cases h_eq : x = b11 ∧ y = b12 ∧ z = b2
            · obtain ⟨h1, h2, h3⟩ := h_eq
              subst h1 h2 h3
              simp
            · simp only [h_eq, if_false]
              split_ifs with h_contra
              · exfalso
                cases h_contra
                exact h_eq ⟨rfl, rfl, rfl⟩
              · rfl
          simp [h_inv, hb]
        · intro habs; exfalso; exact habs (Finset.mem_univ _)
      · -- Case: not all match, expect 0
        simp only [h, if_false]
        rw [Finset.sum_eq_zero]
        intro b _
        -- Either α_inv gives 0, or rest gives 0
        by_cases h_inv : (α_ X Y Z).inv.toMatrix (x, (y, z)) b = 0
        · simp [h_inv]
        · -- α_inv is non-zero, so b = ((x,y),z)
          push_neg at h_inv
          have hb : b = ((x, y), z) := by
            cases b with | mk b1 b2 =>
            cases b1 with | mk b11 b12 =>
            simp [associator_inv_toMatrix] at h_inv
            obtain ⟨h1, h2, h3⟩ := h_inv
            simp only [h1, h2, h3]
          subst hb
          -- Now show inner sum is 0
          rw [Finset.sum_eq_zero]
          · rw [mul_zero]
          · simp_all
            grind only [cases Or]

    -- RHS: (x,(y,z)) → (x,(z,y)) → ((x,z),y) → ((z,x),y)
    · simp_all only [id_matrix, ite_mul, one_mul, zero_mul, associator_inv_toMatrix, mul_ite,
        mul_one, mul_zero, NNReal.coe_sum]
      by_cases h_match : x = x' ∧ y = y' ∧ z = z'
      · -- All match, expect 1
        obtain ⟨hx, hy, hz⟩ := h_match
        subst hx hy hz
        simp
        -- First: X ◁ swap Y Z
        rw [Fintype.sum_eq_single ⟨x ,⟨z, y⟩⟩]
        · -- At (x,(z,y)): whisker gives 1 when x matches
          simp
          rw [Fintype.sum_eq_single ⟨⟨x, z⟩, y⟩]
          · simp
          · aesop
        · -- Other terms in first sum are 0
          simp
          -- X ◁ swap is only non-zero at (x,(z,y))
          intro xzy h_neg h1_x; subst h1_x
          right
          intro xzy' hy hxz1 hxz2 hxzy22; subst hxzy22
          simp_all
          aesop
      · -- Not all match, expect 0
        simp [h_match]
        rw [Fintype.sum_eq_single ⟨x, ⟨z, y⟩⟩]
        · simp_all
          rw [Fintype.sum_eq_single ⟨⟨x, z⟩, y⟩] <;> aesop
        · simp_all
          intro xzy hxzy_neg hx; subst hx
          left
          cases xzy with | mk x_val zy_val =>
          cases zy_val with | mk z_val y_val =>
          simp only
          split_ifs with h_cond
          · -- If condition holds: y = y_val ∧ z = z_val
            exfalso
            obtain ⟨hy_eq, hz_eq⟩ := h_cond
            subst hy_eq hz_eq
            exact hxzy_neg rfl
          · -- Condition doesn't hold, so result is 0
            rfl

/-- FinStoch is symmetric. -/
instance : SymmetricCategory FinStoch where
  symmetry X Y := by
    apply StochasticMatrix.ext
    ext ⟨x, y⟩ ⟨x', y'⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp,
               CategoryStruct.id, StochasticMatrix.id]
    -- We need to show swap ∘ swap = id
    -- The composition should give δ_{(x,y), (x',y')}

    -- The sum is over intermediate states
    -- The sum ∑_{(y₁,x₁)} swap_{(x,y),(y₁,x₁)} * swap_{(y₁,x₁),(x',y')}
    -- has exactly one non-zero term when (y₁,x₁) = (y,x)
    have h_sum : (∑ ab : Y.carrier × X.carrier,
          (if x = ab.2 ∧ y = ab.1 then (1 : NNReal) else 0) *
          (if ab.1 = y' ∧ ab.2 = x' then 1 else 0)) =
        if x = x' ∧ y = y' then 1 else 0 := by
      convert Finset.sum_eq_single (y, x) _ _ using 1
      · -- At (y, x): first condition gives 1, second gives 1 iff y = y' ∧ x = x'
        simp [and_self, and_comm]
      · -- For other points: product is 0
        intro ⟨y₁, x₁⟩ _ h_ne
        by_cases h : x = x₁ ∧ y = y₁
        · obtain ⟨hx, hy⟩ := h
          subst hx hy
          exfalso; exact h_ne rfl
        · simp [h]
      · -- (y, x) is in univ
        intro h; exfalso; exact h (Finset.mem_univ _)

    -- Now show the composition equals the identity
    simp only [BraidedCategory.braiding, swap]
    convert congr_arg NNReal.toReal h_sum
    constructor
    · intro h
      cases h
      constructor <;> rfl
    · intro ⟨h1, h2⟩
      cases h1
      cases h2
      rfl

end CategoryTheory.MarkovCategory
