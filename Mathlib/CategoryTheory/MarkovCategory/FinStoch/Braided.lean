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

/-! ### Helper lemmas for stochastic matrices -/

/-- Sum of delta function equals 1 at the unique non-zero point. -/
lemma sum_delta {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    ∑ x : α, (if x = a then (1 : NNReal) else 0) = 1 := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp only [hb, ↓reduceIte]
  · intro h; exfalso; exact h (Finset.mem_univ _)

/-- Product of delta functions. -/
lemma delta_mul_delta {α β : Type*} [DecidableEq α] [DecidableEq β] (a a' : α) (b b' : β) :
    (if a = a' then (1 : NNReal) else 0) * (if b = b' then 1 else 0) =
    if a = a' ∧ b = b' then 1 else 0 := by
  by_cases ha : a = a'
  · by_cases hb : b = b'
    · simp only [ha, ↓reduceIte, hb, mul_one, and_self]
    · simp only [ha, ↓reduceIte, hb, mul_zero, and_false]
  · simp only [ha, ↓reduceIte, mul_ite, mul_one, mul_zero, ite_self, false_and]

/-- Sum over product space with unique non-zero term. -/
lemma sum_prod_delta {α β : Type*} [Fintype α] [Fintype β] (a : α) (b : β) (f : α × β → NNReal)
    (hf : ∀ x : α × β, x ≠ (a, b) → f x = 0) :
    ∑ x : α × β, f x = f (a, b) := by
  rw [Finset.sum_eq_single (a, b)]
  · intro b _ hb
    exact hf b hb
  · intro h; exfalso; exact h (Finset.mem_univ _)

/-- Composition of morphisms with single non-zero path. -/
lemma comp_single_path {X Y Z : FinStoch} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X.carrier) (y : Y.carrier) (z : Z.carrier)
    (hf : ∀ y', y' ≠ y → f.toMatrix x y' = 0) :
    (f ≫ g).toMatrix x z = f.toMatrix x y * g.toMatrix y z := by
  simp only [CategoryStruct.comp, StochasticMatrix.comp]
  rw [Finset.sum_eq_single y]
  · intro y' _ hy'
    simp only [hf y' hy', zero_mul]
  · intro h; exfalso; exact h (Finset.mem_univ _)

/-- The identity matrix has 1 on the diagonal and 0 elsewhere. -/
@[simp]
lemma id_matrix {X : FinStoch} (x x' : X.carrier) :
    (𝟙 X : X ⟶ X).toMatrix x x' = if x = x' then 1 else 0 := by
  simp only [CategoryStruct.id, StochasticMatrix.id]

/-- The associator morphism applied to matrix elements. -/
@[simp]
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
  simp only [associator_toMatrix, and_self, if_true]

/-- Special case: the associator is 0 when the x-component doesn't match. -/
lemma associator_apply_ne_fst {X Y Z : FinStoch} (x x' : X.carrier) (y : Y.carrier)
    (z : Z.carrier) (yz : (Y ⊗ Z).carrier) (h : x ≠ x') :
    (α_ X Y Z).hom.toMatrix ((x, y), z) (x', yz) = 0 := by
  cases yz with | mk y' z' =>
  simp only [associator_toMatrix, h, false_and, if_false]

/-- The inverse associator maps (x,(y,z)) to ((x,y),z). -/
lemma associator_inv_apply {X Y Z : FinStoch} (x : X.carrier) (y : Y.carrier) (z : Z.carrier) :
    (α_ X Y Z).inv.toMatrix (x, (y, z)) ((x, y), z) = 1 := by
  simp only [associator_inv_toMatrix, and_self, if_true]

/-- Inverse associator is 0 when x-components don't match. -/
lemma associator_inv_apply_ne_fst {X Y Z : FinStoch} (x x' : X.carrier) (y : Y.carrier)
    (z : Z.carrier) (y' : Y.carrier) (z' : Z.carrier) (h : x ≠ x') :
    (α_ X Y Z).inv.toMatrix (x, (y, z)) ((x', y'), z') = 0 := by
  simp only [associator_inv_toMatrix, h, false_and, if_false]

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
          simp only [hx, hy, and_false, ↓reduceIte]
      · -- x ≠ x', so condition fails
        simp only [hx, false_and, ↓reduceIte]
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
  simp only [swap]

/-- Special case: swap preserves components when they match. -/
lemma swap_apply {X Y : FinStoch} (x : X.carrier) (y : Y.carrier) :
    (swap X Y).toMatrix (x, y) (y, x) = 1 := by
  simp only [swap_toMatrix, and_self, if_true]

/-- Special case: swap is 0 when x-components don't match. -/
lemma swap_apply_ne_fst {X Y : FinStoch} (x : X.carrier) (y : Y.carrier)
    (x' : X.carrier) (y' : Y.carrier) (h : x ≠ x') :
    (swap X Y).toMatrix (x, y) (y', x') = 0 := by
  simp only [swap_toMatrix, h, false_and, if_false]

/-- Special case: swap is 0 when y-components don't match. -/
lemma swap_apply_ne_snd {X Y : FinStoch} (x : X.carrier) (y : Y.carrier)
    (x' : X.carrier) (y' : Y.carrier) (h : y ≠ y') :
    (swap X Y).toMatrix (x, y) (y', x') = 0 := by
  simp only [swap_toMatrix, h, and_false, if_false]

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
        simp only []
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
        simp only []
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
        · simp only [hz, ↓reduceIte, mul_one, and_self]
        · simp only [hz, ↓reduceIte, mul_one, and_false, mul_zero]
      · -- For other points: show the sum term is 0
        intro ⟨y₁, z₁⟩ _ h_ne
        -- We have f(x,y₁) * (if z = z₁ then 1 else 0) * (if y₁ = y' ∧ z₁ = z' then 1 else 0)
        by_cases hz₁ : z = z₁
        · subst hz₁
          by_cases hyz : y₁ = y' ∧ z = z'
          · obtain ⟨hy₁, _⟩ := hyz
            subst hy₁
            exfalso; exact h_ne rfl
          · simp only [↓reduceIte, mul_one, hyz, mul_zero]
        · simp only [hz₁, ↓reduceIte, mul_zero, mul_ite, mul_one, ite_self]
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
        · simp only [hz, ↓reduceIte, one_mul]
        · simp only [hz, ↓reduceIte, zero_mul, mul_zero]
      · -- For other points: show the sum term is 0
        intro ⟨z₁, x₁⟩ _ h_ne
        -- We have (if x = x₁ ∧ z = z₁ then 1 else 0) * ((if z₁ = z' then 1 else 0) * f(x₁,y'))
        by_cases hxz : x = x₁ ∧ z = z₁
        · obtain ⟨hx₁, hz₁⟩ := hxz
          subst hx₁ hz₁
          exfalso; exact h_ne rfl
        · simp only [hxz, ↓reduceIte, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, ite_self]
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
        · simp only [hx, ↓reduceIte, and_self, mul_one]
        · simp only [hx, ↓reduceIte, and_true, mul_zero]
      · -- For other points: show the sum term is 0
        intro ⟨x₁, z₁⟩ _ h_ne
        -- We have (if x = x₁ then 1 else 0) * f(y,z₁) * (if x₁ = x' ∧ z₁ = z' then 1 else 0)
        by_cases hx₁ : x = x₁
        · subst hx₁
          by_cases hxz : x = x' ∧ z₁ = z'
          · obtain ⟨_, hz₁⟩ := hxz
            subst hz₁
            exfalso; exact h_ne rfl
          · simp only [↓reduceIte, one_mul, hxz, mul_zero]
        · simp only [hx₁, ↓reduceIte, zero_mul, mul_ite, mul_one, mul_zero, ite_self]
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
        · simp only [hx, ↓reduceIte, mul_one, one_mul]
        · simp only [hx, ↓reduceIte, mul_zero]
      · -- For other points: show the sum term is 0
        intro ⟨y₁, x₁⟩ _ h_ne
        -- We have (if x = x₁ ∧ y = y₁ then 1 else 0) * (f(y₁,z') * (if x₁ = x' then 1 else 0))
        by_cases hxy : x = x₁ ∧ y = y₁
        · obtain ⟨hx₁, hy₁⟩ := hxy
          subst hx₁ hy₁
          exfalso; exact h_ne rfl
        · simp only [hxy, ↓reduceIte, mul_ite, mul_one, mul_zero, zero_mul, ite_self]
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
            simp only [MonoidalCategoryStruct.associator, associator, DetMorphism.toMatrix_apply,
              ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
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
                · simp only [h, and_self, ↓reduceIte, one_mul]
                · simp only [h]
                  have : ¬(y' = (y, z) ∧ x' = x) := by
                    rw [and_comm]
                    grind only
                  simp only [↓reduceIte, zero_mul, NNReal.coe_zero, Prod.mk.injEq, this]
          -- Use h_sum to transform the match expression
          trans (∑ x_1, (if x_1 = ((y, z), x) then 1 else 0) *
                        (α_ Y Z X).hom.toMatrix x_1 (y, z, x))
          · exact h_sum
          -- Now we have a sum with a single non-zero term at ((y,z), x)
          rw [Finset.sum_eq_single ((y, z), x)]
          · simp only [if_true, one_mul]
            -- The associator at ((y,z), x) -> (y,(z,x)) gives 1
            have h_assoc2 : (α_ Y Z X).hom.toMatrix ((y, z), x) (y, (z, x)) = 1 := by
              simp only [MonoidalCategoryStruct.associator, associator, DetMorphism.toMatrix_apply,
                ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
              rfl
            simp only [h_assoc2]
          · intro b _ hb
            simp only [hb, if_false, zero_mul]
          · intro h_mem; exfalso; exact h_mem (Finset.mem_univ _)
        · -- Other x₁ terms are 0
          intro x₁ _ hx₁
          -- The associator gives 0 for x₁ ≠ (x, (y, z))
          have h_zero : (α_ X Y Z).hom.toMatrix ((x, y), z) x₁ = 0 := by
            simp only [MonoidalCategoryStruct.associator, associator, DetMorphism.toMatrix_apply,
              ite_eq_right_iff, one_ne_zero, imp_false]
            tauto
          simp only [h_zero, zero_mul]
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
          simp only [h_assoc, associator_matrix, mul_ite, mul_one, mul_zero, zero_mul]
        · -- Associator is non-zero, so x₁ = (x, (y, z))
          push_neg at h_assoc
          have hx₁ : x₁ = (x, (y, z)) := by
            simp_all only [not_and, Finset.mem_univ, MonoidalCategoryStruct.associator, associator,
              DetMorphism.toMatrix_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
              Decidable.not_not]
            tauto
          subst hx₁
          simp only [MonoidalCategory.associator, associator]
          -- Now show the inner sum is 0
          rw [Finset.sum_eq_zero]
          · simp only [mul_zero]
          · intro x_inner _
            -- Need to show swap * final_assoc = 0
            cases x_inner with | mk y_inner x_inner =>
            simp only
            -- Check if swap condition holds
            by_cases h_swap : x = x_inner ∧ (y, z) = y_inner
            · -- Swap gives 1, check final associator
              obtain ⟨hx_eq, hy_eq⟩ := h_swap
              subst hx_eq hy_eq
              simp_all only [not_and, Finset.mem_univ, associator_matrix, and_self, ↓reduceIte,
                ne_eq, one_ne_zero, not_false_eq_true, mul_ite, mul_one,
                mul_zero, ite_eq_right_iff, imp_false, associatorDet, DetMorphism.ofFunc]
              grind only
            · -- Swap gives 0
              simp only [h_swap, if_false, zero_mul]

    -- RHS computation
    · congr 1
      symm
      -- RHS: ((x,y),z) → ((y,x),z) → (y,(x,z)) → (y,(z,x))
      -- First swap ⊗ id maps ((x,y),z) ↦ ((y,x),z) with prob 1
      -- Then associator maps ((y,x),z) ↦ (y,(x,z)) with prob 1
      -- Then id ⊗ swap maps (y,(x,z)) ↦ (y,(z,x)) with prob 1

      -- Sum over final state before last operation
      -- The RHS path: swap ⊗ id, then associator, then id ⊗ swap
      simp only [id_matrix, mul_ite, mul_one, mul_zero, associator_matrix, ite_mul, one_mul,
        zero_mul]
      -- We need to show the sum equals the indicator function
      by_cases h_match : x = x' ∧ y = y' ∧ z = z'
      · -- Case: all match, result should be 1
        obtain ⟨hx, hy, hz⟩ := h_match
        subst hx hy hz
        simp only [and_true, if_true]
        -- The sum should collapse to a single non-zero term
        convert Finset.sum_eq_single ((y, x), z) _ _ using 1
        · -- At ((y,x),z): show it produces 1
          simp only [and_self, ↓reduceIte, one_mul]
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
              · simp only [hy, ↓reduceIte, true_and, ite_eq_right_iff, one_ne_zero, imp_false,
                  not_and, and_imp]
                by_cases hxz : x = x₁ ∧ z = z₁
                · obtain ⟨hx, hz⟩ := hxz
                  subst hy hx hz
                  exfalso; exact hne rfl
                · push_neg at hxz
                  by_cases hx : x = x₁
                  · simp only [hx, hxz hx, forall_const, IsEmpty.forall_iff]
                  · simp only [hx, IsEmpty.forall_iff]
              · simp only [hy, ↓reduceIte]
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
          simp_all only [not_and, Finset.mem_univ, ite_eq_right_iff, mul_eq_zero,
            Finset.sum_eq_zero_iff, and_imp, forall_const]
          -- Grind out the rest of the proof
          intro a; subst a
          push_neg at hx₁
          split
          · split_ifs
            · simp_all only [ne_eq, one_ne_zero, false_or]
              rename_i h
              intro i a a_1 a_2 a_3
              subst a a_1 a_2
              simp_all only [forall_const]
              obtain ⟨left, right⟩ := h
              subst left right
              split
              rename_i x x_2 y heq_1
              simp_all only [ite_eq_right_iff, one_ne_zero, imp_false, not_and, not_false_eq_true,
                implies_true]
            · simp_all only [ne_eq, not_and, true_or]

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
          simp only [associator_inv_toMatrix, mul_ite, mul_one, mul_zero, and_self, ↓reduceIte,
            one_mul]
          -- Now compute swap and final α_inv
          convert Finset.sum_eq_single (z, (x, y)) _ _ using 1
          · -- swap gives 1, then α_inv gives 1
            simp only [and_self, ↓reduceIte]
          · intro b _ hb
            -- swap is deterministic, only maps to (z,(x,y))
            cases b with | mk b1 b2 =>
            simp only
            by_cases h_swap : (x, y) = b2 ∧ z = b1
            · obtain ⟨h_xy, h_z⟩ := h_swap
              subst h_xy h_z
              exfalso; exact hb rfl
            · simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_and, and_imp]
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
              simp only [and_self, if_true]
            · simp only [h_eq, if_false]
              split_ifs with h_contra
              · exfalso
                cases h_contra
                exact h_eq ⟨rfl, rfl, rfl⟩
              · rfl
          simp only [h_inv, hb, if_false, zero_mul]
        · intro habs; exfalso; exact habs (Finset.mem_univ _)
      · -- Case: not all match, expect 0
        simp only [h, if_false]
        rw [Finset.sum_eq_zero]
        intro b _
        -- Either α_inv gives 0, or rest gives 0
        by_cases h_inv : (α_ X Y Z).inv.toMatrix (x, (y, z)) b = 0
        · simp only [h_inv, zero_mul]
        · -- α_inv is non-zero, so b = ((x,y),z)
          push_neg at h_inv
          have hb : b = ((x, y), z) := by
            cases b with | mk b1 b2 =>
            cases b1 with | mk b11 b12 =>
            simp only [associator_inv_toMatrix, ne_eq, ite_eq_right_iff,
                       one_ne_zero, imp_false, Decidable.not_not] at h_inv
            obtain ⟨h1, h2, h3⟩ := h_inv
            simp only [h1, h2, h3]
          subst hb
          -- Now show inner sum is 0
          rw [Finset.sum_eq_zero]
          · rw [mul_zero]
          · simp_all only [not_and, Finset.mem_univ, associator_inv_toMatrix, and_self, ↓reduceIte,
              ne_eq, one_ne_zero, not_false_eq_true, mul_ite, mul_one, mul_zero, ite_eq_right_iff,
              and_imp, forall_const]
            intro x_1 a a_1 a_2; subst a_1 a a_2
            split
            rename_i x_1 y' x'
            simp_all only [ite_eq_right_iff, one_ne_zero, imp_false, not_and]
            intro a; subst a
            simp_all only [forall_const, not_false_eq_true]

    -- RHS: (x,(y,z)) → (x,(z,y)) → ((x,z),y) → ((z,x),y)
    · simp_all only [id_matrix, ite_mul, one_mul, zero_mul, associator_inv_toMatrix, mul_ite,
        mul_one, mul_zero, NNReal.coe_sum]
      by_cases h_match : x = x' ∧ y = y' ∧ z = z'
      · -- All match, expect 1
        obtain ⟨hx, hy, hz⟩ := h_match
        subst hx hy hz
        simp only [and_self, ↓reduceIte, NNReal.coe_one]
        -- First: X ◁ swap Y Z
        rw [Fintype.sum_eq_single ⟨x ,⟨z, y⟩⟩]
        · -- At (x,(z,y)): whisker gives 1 when x matches
          simp only [↓reduceIte, and_self, and_true, one_mul, NNReal.coe_sum]
          rw [Fintype.sum_eq_single ⟨⟨x, z⟩, y⟩]
          · simp only [↓reduceIte, and_self, NNReal.coe_one]
          · simp only [ne_eq, NNReal.coe_eq_zero, ite_eq_right_iff, and_imp]
            intro x_1 a a_1 a_2 a_3; subst a_3 a_2 a_1
            simp_all only [Prod.mk.eta, not_true_eq_false]
        · -- Other terms in first sum are 0
          simp_all only [ne_eq, NNReal.coe_eq_zero, ite_eq_right_iff, mul_eq_zero,
            Finset.sum_eq_zero_iff, Finset.mem_univ, and_imp, forall_const]
          -- X ◁ swap is only non-zero at (x,(z,y))
          intro xzy h_neg h1_x
          subst h1_x
          right
          intro xzy' hy hxz1 hxz2 hxzy22
          subst hxzy22
          simp_all only
          split
          · rename_i x x_1 y heq
            simp_all only [true_and, ite_eq_right_iff, one_ne_zero, imp_false]
            subst hxz2 hxz1
            intro a; subst a
            simp_all only [Prod.mk.eta, not_true_eq_false]
      · -- Not all match, expect 0
        simp only [h_match, ↓reduceIte, NNReal.coe_zero]
        rw [Fintype.sum_eq_single ⟨x, ⟨z, y⟩⟩]
        · simp_all only [not_and, ↓reduceIte, and_self, one_mul, NNReal.coe_sum]
          rw [Fintype.sum_eq_single ⟨⟨x, z⟩, y⟩] <;> aesop
        · simp_all only [not_and, ne_eq, NNReal.coe_eq_zero, ite_eq_right_iff, mul_eq_zero,
            Finset.sum_eq_zero_iff, Finset.mem_univ, and_imp, forall_const]
          intro xzy hxzy_neg hx
          subst hx
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
        simp only [and_self, if_true, one_mul]
        simp only [and_comm]
      · -- For other points: product is 0
        intro ⟨y₁, x₁⟩ _ h_ne
        by_cases h : x = x₁ ∧ y = y₁
        · obtain ⟨hx, hy⟩ := h
          subst hx hy
          exfalso; exact h_ne rfl
        · simp only [h, ↓reduceIte, mul_ite, mul_one, mul_zero, ite_self]
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
