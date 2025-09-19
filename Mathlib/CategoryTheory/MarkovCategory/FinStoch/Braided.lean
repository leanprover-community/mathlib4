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
  · intro b _ hb; simp [hb]
  · intro h; exfalso; exact h (Finset.mem_univ _)

/-- Product of delta functions. -/
lemma delta_mul_delta {α β : Type*} [DecidableEq α] [DecidableEq β] (a a' : α) (b b' : β) :
    (if a = a' then (1 : NNReal) else 0) * (if b = b' then 1 else 0) =
    if a = a' ∧ b = b' then 1 else 0 := by
  by_cases ha : a = a'
  · by_cases hb : b = b'
    · simp [ha, hb]
    · simp [ha, hb]
  · simp [ha]

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
    simp [hf y' hy']
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
  simp only [MonoidalCategory.associator, associator]

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
          ext <;> simp [h₁]
        · simp
        · simp
        · simp
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
    simp only [CategoryStruct.comp, StochasticMatrix.comp, CategoryStruct.id,
               swap, StochasticMatrix.id]
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
          ext <;> simp [h₁]
        · simp
        · simp
        · simp
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
        · simp [hz, mul_one]
        · simp [hz, mul_zero]
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
        · simp [hz, one_mul]
        · simp [hz, zero_mul]
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
        · simp [hx, mul_one]
        · simp [hx, mul_zero]
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
            simp only [MonoidalCategory.associator, associator]
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
              simp only [MonoidalCategory.associator, associator]
              rfl
            simp only [h_assoc2]
          · intro b _ hb
            simp only [hb, if_false, zero_mul]
          · intro h_mem; exfalso; exact h_mem (Finset.mem_univ _)
        · -- Other x₁ terms are 0
          intro x₁ _ hx₁
          -- The associator gives 0 for x₁ ≠ (x, (y, z))
          have h_zero : (α_ X Y Z).hom.toMatrix ((x, y), z) x₁ = 0 := by
            simp only [MonoidalCategory.associator, associator]
            -- Since x₁ ≠ (x, (y, z)), the condition fails
            split_ifs with h_cond
            · -- If the condition holds, contradiction
              obtain ⟨h1, h2, h3⟩ := h_cond
              subst h1 h2 h3
              exact absurd rfl hx₁
            · rfl
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
          simp [h_assoc]
        · -- Associator is non-zero, so x₁ = (x, (y, z))
          push_neg at h_assoc
          have hx₁ : x₁ = (x, (y, z)) := by
            simp only [MonoidalCategory.associator, associator] at h_assoc ⊢
            grind only [Finset.mem_univ, cases Or]
          subst hx₁
          simp only [MonoidalCategory.associator, associator]
          -- Now show the inner sum is 0
          rw [Finset.sum_eq_zero]
          · simp only [and_self, ↓reduceIte, mul_zero]
          · intro x_inner _
            -- Need to show swap * final_assoc = 0
            cases x_inner with | mk y_inner x_inner =>
            simp only
            -- Check if swap condition holds
            by_cases h_swap : x = x_inner ∧ (y, z) = y_inner
            · -- Swap gives 1, check final associator
              obtain ⟨hx_eq, hy_eq⟩ := h_swap
              subst hx_eq hy_eq
              simp only [and_self, ↓reduceIte, mul_ite, mul_one, mul_zero, ite_eq_right_iff,
                         one_ne_zero, imp_false, not_and]
              intro a_2 a_3
              subst a_3 a_2
              simp_all only [Finset.mem_univ, associator_matrix, and_self, ↓reduceIte, ne_eq,
                             one_ne_zero, not_false_eq_true, and_true]
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
      simp only [StochasticMatrix.id, CategoryStruct.id]
      -- We need to show the sum equals the indicator function
      by_cases h_match : x = x' ∧ y = y' ∧ z = z'
      · -- Case: all match, result should be 1
        obtain ⟨hx, hy, hz⟩ := h_match
        subst hx hy hz
        simp only [and_true, if_true]
        -- The sum should collapse to a single non-zero term
        convert Finset.sum_eq_single ((y, x), z) _ _ using 1
        · -- At ((y,x),z): show it produces 1
          simp only [and_self, ↓reduceIte, mul_one, associator_toMatrix, ite_mul, one_mul, zero_mul,
                     mul_ite, mul_zero]
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
          simp only [and_self, if_true, one_mul, associator_toMatrix, ite_mul, one_mul, zero_mul,
                     mul_ite, mul_zero]
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
          simp_all only [not_and, Finset.mem_univ, mul_ite, mul_one, mul_zero, associator_toMatrix,
                         ite_mul, one_mul, zero_mul, ite_eq_right_iff, mul_eq_zero,
                         Finset.sum_eq_zero_iff, and_imp, forall_const]
          sorry


  hexagon_reverse := by
    intros X Y Z
    -- The reverse hexagon identity
    -- Similar proof strategy as hexagon_forward
    sorry

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
