/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.MarkovCategory.FinStoch.Basic
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Monoidal Structure on FinStoch

Tensor products model independent parallel processes.

## Main definitions

* `associator` - Isomorphism `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`
* `leftUnitor` - Isomorphism `I ⊗ X ≅ X`
* `rightUnitor` - Isomorphism `X ⊗ I ≅ X`

## Implementation notes

Structural isomorphisms are deterministic.
Use computational lemmas to simplify proofs.

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

/-! ### Helper lemmas for structural morphisms -/

/-- Rearranges `((X ⊗ Y) ⊗ Z)` to `(X ⊗ (Y ⊗ Z))`.

Maps `((x,y),z) ↦ (x,(y,z))` deterministically. -/
def associator (X Y Z : FinStoch) :
    (tensorObj (tensorObj X Y) Z) ≅ (tensorObj X (tensorObj Y Z)) where
  hom := ⟨fun ⟨⟨x, y⟩, z⟩ ⟨x', ⟨y', z'⟩⟩ =>
    if x = x' ∧ y = y' ∧ z = z' then 1 else 0, fun ⟨⟨x, y⟩, z⟩ => by
    rw [Finset.sum_eq_single ⟨x, ⟨y, z⟩⟩]
    · simp only [and_self, if_true]
    · intro b _ hb
      obtain ⟨x', ⟨y', z'⟩⟩ := b
      simp only
      split_ifs with h
      · obtain ⟨h1, h2, h3⟩ := h
        exfalso
        apply hb
        congr 1
        · exact h1.symm
        · congr 1
          · exact h2.symm
          · exact h3.symm
      · rfl
    · intro h; exfalso; exact h (Finset.mem_univ _)⟩
  inv := ⟨fun ⟨x, ⟨y, z⟩⟩ ⟨⟨x', y'⟩, z'⟩ =>
    if x = x' ∧ y = y' ∧ z = z' then 1 else 0, fun ⟨x, ⟨y, z⟩⟩ => by
    rw [Finset.sum_eq_single ⟨⟨x, y⟩, z⟩]
    · simp only [and_self, if_true]
    · intro b _ hb
      obtain ⟨⟨x', y'⟩, z'⟩ := b
      simp only
      split_ifs with h
      · exfalso
        obtain ⟨h1, h2, h3⟩ := h
        apply hb
        congr 1
        · congr 1
          · exact h1.symm
          · exact h2.symm
        · exact h3.symm
      · rfl
    · intro h; exfalso; exact h (Finset.mem_univ _)⟩
  hom_inv_id := by
    apply StochasticMatrix.ext
    ext ⟨⟨x, y⟩, z⟩ ⟨⟨x', y'⟩, z'⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    -- Round trip: ((x,y),z) → (x,(y,z)) → ((x,y),z)
    rw [Finset.sum_eq_single ⟨x, ⟨y, z⟩⟩]
    · simp only [and_self, if_true, one_mul]
      simp only [StochasticMatrix.id, CategoryStruct.id]
      by_cases h : ((x, y), z) = ((x', y'), z')
      · simp only [h, ↓reduceIte, NNReal.coe_one, NNReal.coe_eq_one, ite_eq_left_iff, not_and,
                   zero_ne_one, imp_false, Classical.not_imp, Decidable.not_not]
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        simp only [and_self]
      · simp only [h, ↓reduceIte, NNReal.coe_zero, NNReal.coe_eq_zero, ite_eq_right_iff,
                   one_ne_zero, imp_false, not_and]
        push_neg at h
        simp only [ne_eq, Prod.mk.injEq, not_and, and_imp] at h
        exact h
    · intro b _ hb
      obtain ⟨x₁, ⟨y₁, z₁⟩⟩ := b
      simp only
      split_ifs with h h2
      · obtain ⟨rfl, rfl, rfl⟩ := h
        exfalso
        exact hb rfl
      · obtain ⟨rfl, rfl, rfl⟩ := h
        exfalso
        exact hb rfl
      · simp only [zero_mul]
      · simp only [zero_mul]
    · intro h
      exfalso
      exact h (Finset.mem_univ _)
  inv_hom_id := by
    apply StochasticMatrix.ext
    ext ⟨x, ⟨y, z⟩⟩ ⟨x', ⟨y', z'⟩⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    -- Round trip: (x,(y,z)) → ((x,y),z) → (x,(y,z))
    rw [Finset.sum_eq_single ⟨⟨x, y⟩, z⟩]
    · simp only [and_self, if_true, one_mul]
      simp only [StochasticMatrix.id, CategoryStruct.id]
      grind only [cases Or]
    · intro b _ hb
      obtain ⟨⟨x₁, y₁⟩, z₁⟩ := b
      simp only
      split_ifs with h h2
      · obtain ⟨rfl, rfl, rfl⟩ := h
        exfalso
        exact hb rfl
      · obtain ⟨rfl, rfl, rfl⟩ := h
        exfalso
        exact hb rfl
      · simp only [zero_mul]
      · simp only [zero_mul]
    · intro h; exfalso; exact h (Finset.mem_univ _)

/-- The left unitor removes the trivial left factor from `I ⊗ X` to get `X`.

This maps `((),x) ↦ x` with probability 1. The unit carries no information,
so removing it doesn't change the data. The monoidal unit is singleton
because it cannot hold information. -/
def leftUnitor (X : FinStoch) : (tensorObj tensorUnit X) ≅ X where
  hom := ⟨fun ⟨⟨⟩, x⟩ x' => if x = x' then 1 else 0, fun ⟨⟨⟩, x⟩ => by
    rw [Finset.sum_eq_single x]
    · simp only [if_true]
    · intro x' _ hx'
      simp only
      split_ifs with h
      · exfalso
        exact hx' h.symm
      · rfl
    · intro h
      exfalso
      apply h
      exact Finset.mem_univ _⟩
  inv := ⟨fun x ⟨⟨⟩, x'⟩ => if x = x' then 1 else 0, fun x => by
    rw [Finset.sum_eq_single ⟨⟨⟩, x⟩]
    · simp only [if_true]
    · intro b _ hb
      obtain ⟨⟨⟩, x'⟩ := b
      simp only
      split_ifs with h
      · exfalso
        apply hb
        congr 1
        exact h.symm
      · rfl
    · intro h
      exfalso
      apply h
      exact Finset.mem_univ _⟩
  hom_inv_id := by
    apply StochasticMatrix.ext
    ext ⟨⟨⟩, x⟩ ⟨⟨⟩, x'⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    -- Round trip: ((),x) → x → ((),x)
    rw [Finset.sum_eq_single x]
    · simp only [if_true, one_mul]
      simp only [StochasticMatrix.id, CategoryStruct.id]
      -- Align equality conditions: x = x' ↔ ((),x) = ((),x')
      have h : (x = x') = (((), x) = ((), x')) := by
        simp only [Prod.mk.injEq, true_and]
      rw [ite_cond_congr h]
    · intro x' _ hx'
      split_ifs with h
      · exfalso
        exact hx' (h.symm)
      · rw [mul_zero]
      · rw [zero_mul]
      · rw [mul_zero]
    · intro h
      exfalso
      apply h
      exact Finset.mem_univ _
  inv_hom_id := by
    apply StochasticMatrix.ext
    ext x
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single ⟨⟨⟩, x⟩]
    · simp only [if_true, one_mul]
      simp only [StochasticMatrix.id, CategoryStruct.id]
    · intro b _ hb
      obtain ⟨⟨⟩, x'⟩ := b
      by_cases h : ((), x) = ((), x')
      · -- Case: ((), x) = ((), x')
        simp only [Prod.mk.injEq, true_and] at h
        subst h
        simp only [if_true, one_mul]
        exfalso
        apply hb
        rfl
      · -- Case: ((), x) ≠ ((), x')
        simp only [Prod.mk.injEq, true_and] at h
        push_neg at h
        -- Zero when x ≠ x'
        simp only [h, if_false, zero_mul]
    · intro h
      exfalso
      apply h
      exact Finset.mem_univ _

/-- The right unitor removes the trivial right factor from `X ⊗ I` to get `X`.

This maps `(x,()) ↦ x` with probability 1. The unit carries no information,
so removing it doesn't change the data. The symmetry with the left unitor shows
tensor products have no preferred order. -/
def rightUnitor (X : FinStoch) : (tensorObj X tensorUnit) ≅ X where
  hom := ⟨fun ⟨x, ⟨⟩⟩ x' => if x = x' then 1 else 0, fun ⟨x, ⟨⟩⟩ => by
    rw [Finset.sum_eq_single x]
    · simp only [if_true]
    · intro x' _ hx'
      simp only
      split_ifs with h
      · exfalso
        exact hx' h.symm
      · rfl
    · intro h
      exfalso
      apply h
      exact Finset.mem_univ _⟩
  inv := ⟨fun x ⟨x', ⟨⟩⟩ => if x = x' then 1 else 0, fun x => by
    rw [Finset.sum_eq_single ⟨x, ⟨⟩⟩]
    · simp only [if_true]
    · intro b _ hb
      obtain ⟨x', ⟨⟩⟩ := b
      simp only
      split_ifs with h
      · exfalso
        apply hb
        congr 1
        exact h.symm
      · rfl
    · intro h
      exfalso
      apply h
      exact Finset.mem_univ _⟩
  hom_inv_id := by
    apply StochasticMatrix.ext
    ext ⟨x, ⟨⟩⟩ ⟨x', ⟨⟩⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    -- Round trip: (x,()) → x → (x,())
    rw [Finset.sum_eq_single x]
    · simp only [if_true, one_mul]
      simp only [StochasticMatrix.id, CategoryStruct.id]
      -- Align equality conditions: x = x' ↔ (x,()) = (x',())
      have h : (x = x') = ((x, ()) = (x', ())) := by
        simp only [Prod.mk.injEq, and_true]
      rw [ite_cond_congr h]
    · intro x' _ hx'
      split_ifs with h
      · exfalso
        exact hx' (h.symm)
      · rw [mul_zero]
      · rw [zero_mul]
      · rw [zero_mul]
    · intro h
      exfalso
      apply h
      exact Finset.mem_univ _
  inv_hom_id := by
    apply StochasticMatrix.ext
    ext x
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single ⟨x, ⟨⟩⟩]
    · simp only [if_true, one_mul]
      simp only [StochasticMatrix.id, CategoryStruct.id]
    · intro b _ hb
      obtain ⟨x', ⟨⟩⟩ := b
      by_cases h : (x, ()) = (x', ())
      · -- Case: (x, ()) = (x', ())
        simp only [Prod.mk.injEq, and_true] at h
        subst h
        simp only [if_true, one_mul]
        exfalso
        apply hb
        rfl
      · -- Case: (x, ()) ≠ (x', ())
        simp only [Prod.mk.injEq, and_true] at h
        push_neg at h
        -- Zero when x ≠ x'
        simp only [h, if_false, zero_mul]
    · intro h
      exfalso
      apply h
      exact Finset.mem_univ _

/-- The basic monoidal structure on FinStoch using tensor products of finite types
and explicit structural isomorphisms. -/
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
  change (associator X Y Z).hom.toMatrix xyz xyz' = _
  obtain ⟨⟨x, y⟩, z⟩ := xyz
  obtain ⟨x', ⟨y', z'⟩⟩ := xyz'
  simp only [associator]

/-- Matrix entry for inverse associator. -/
@[simp]
lemma associator_inv_matrix (X Y Z : FinStoch) (xyz : (X ⊗ (Y ⊗ Z)).carrier)
    (xyz' : ((X ⊗ Y) ⊗ Z).carrier) :
    (MonoidalCategoryStruct.associator X Y Z).inv.toMatrix xyz xyz' =
    if xyz.1 = xyz'.1.1 ∧ xyz.2.1 = xyz'.1.2 ∧ xyz.2.2 = xyz'.2 then 1 else 0 := by
  change (associator X Y Z).inv.toMatrix xyz xyz' = _
  obtain ⟨x, ⟨y, z⟩⟩ := xyz
  obtain ⟨⟨x', y'⟩, z'⟩ := xyz'
  simp only [associator]

/-- Matrix entry for left unitor. -/
@[simp]
lemma leftUnitor_matrix (X : FinStoch) (ux : (FinStoch.tensorUnit ⊗ X).carrier) (x : X.carrier) :
    (MonoidalCategoryStruct.leftUnitor X).hom.toMatrix ux x =
    if ux.2 = x then 1 else 0 := by
  change (leftUnitor X).hom.toMatrix ux x = _
  obtain ⟨⟨⟩, x'⟩ := ux
  simp only [leftUnitor]

/-- Matrix entry for inverse left unitor. -/
@[simp]
lemma leftUnitor_inv_matrix (X : FinStoch) (x : X.carrier)
    (ux : (FinStoch.tensorUnit ⊗ X).carrier) :
    (MonoidalCategoryStruct.leftUnitor X).inv.toMatrix x ux =
    if x = ux.2 then 1 else 0 := by
  change (leftUnitor X).inv.toMatrix x ux = _
  obtain ⟨⟨⟩, x'⟩ := ux
  simp only [leftUnitor]

/-- Matrix entry for right unitor. -/
@[simp]
lemma rightUnitor_matrix (X : FinStoch) (xu : (X ⊗ FinStoch.tensorUnit).carrier) (x : X.carrier) :
    (MonoidalCategoryStruct.rightUnitor X).hom.toMatrix xu x =
    if xu.1 = x then 1 else 0 := by
  change (rightUnitor X).hom.toMatrix xu x = _
  obtain ⟨x', ⟨⟩⟩ := xu
  simp only [rightUnitor]

/-- Matrix entry for inverse right unitor. -/
@[simp]
lemma rightUnitor_inv_matrix (X : FinStoch) (x : X.carrier)
    (xu : (X ⊗ FinStoch.tensorUnit).carrier) :
    (MonoidalCategoryStruct.rightUnitor X).inv.toMatrix x xu =
    if x = xu.1 then 1 else 0 := by
  change (rightUnitor X).inv.toMatrix x xu = _
  obtain ⟨x', ⟨⟩⟩ := xu
  simp only [rightUnitor]

/-- FinStoch forms a monoidal category with all coherence conditions satisfied.
This proves Mac Lane's pentagon and triangle identities hold for stochastic matrices. -/
instance : MonoidalCategory FinStoch where
  tensorHom_def := by
    -- Tensor product via whiskering: f ⊗ g = (f ▷ X₂) ≫ (Y₁ ◁ g)
    intros X₁ Y₁ X₂ Y₂ f g
    apply StochasticMatrix.ext
    ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    simp only [MonoidalCategoryStruct.tensorHom, StochasticMatrix.tensor,
               MonoidalCategoryStruct.whiskerRight, MonoidalCategoryStruct.whiskerLeft,
               CategoryStruct.comp, StochasticMatrix.comp]
    -- (f ▷ X₂) ≫ (Y₁ ◁ g) expands to sum over intermediate states
    rw [Finset.sum_eq_single ⟨y₁, x₂⟩]
    · simp only [StochasticMatrix.id, CategoryStruct.id]
      by_cases h₁ : y₁ = y₁
      · by_cases h₂ : x₂ = x₂
        · simp only [NNReal.coe_mul, ↓reduceIte, mul_one, one_mul]
        · -- Impossible: x₂ ≠ x₂
          exfalso
          exact h₂ rfl
      · -- Impossible: y₁ ≠ y₁
        exfalso
        exact h₁ rfl
    · intro ⟨y₁', x₂'⟩ _ h_ne
      simp only [StochasticMatrix.id, CategoryStruct.id]
      -- At least one identity matrix is off-diagonal, contributing 0
      by_cases h₁ : y₁' = y₁
      · by_cases h₂ : x₂ = x₂'
        · exfalso
          apply h_ne
          congr 1
          · exact h₂.symm
        · simp only [h₂, ↓reduceIte, mul_zero, ite_mul, one_mul, zero_mul, mul_ite, ite_self]
      · simp only [mul_ite, mul_one, mul_zero, h₁, ↓reduceIte, zero_mul]
    · intro h
      exfalso
      exact h (Finset.mem_univ _)
  id_tensorHom_id := by
    intros X Y
    apply StochasticMatrix.ext
    ext ⟨x, y⟩ ⟨x', y'⟩
    simp only [MonoidalCategoryStruct.tensorHom, StochasticMatrix.tensor]
    simp only [CategoryStruct.id, StochasticMatrix.id]
    -- id ⊗ id = id: only (x,y) = (x',y') gets probability 1
    by_cases hx : x = x'
    · by_cases hy : y = y'
      · -- Both match: prob 1 * 1 = 1
        simp only [hx, ↓reduceIte, hy, mul_one, NNReal.coe_one]
      · -- x matches, y doesn't: prob 1 * 0 = 0
        simp only [hx, ↓reduceIte, hy, mul_zero, NNReal.coe_zero]
        split_ifs with h
        · exfalso
          obtain ⟨_, h2⟩ := h
          exact hy rfl
        · rfl
    · -- x doesn't match: prob 0 * _ = 0
      simp only [hx, ↓reduceIte, mul_ite, mul_one, mul_zero, ite_self, NNReal.coe_zero]
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
    -- Interchange law: (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂)
    -- LHS: tensor of compositions = (∑ y₁, f₁[x₁,y₁]*g₁[y₁,z₁]) * (∑ y₂, f₂[x₂,y₂]*g₂[y₂,z₂])
    -- RHS: composition of tensors = ∑ (y₁,y₂), (f₁[x₁,y₁]*f₂[x₂,y₂]) * (g₁[y₁,z₁]*g₂[y₂,z₂])

    -- Use distributivity: product of sums = sum of products
    rw [Finset.sum_mul_sum]
    -- Convert double sum to sum over product
    simp_rw [← Finset.sum_product']
    -- Reflexivity handles associativity and commutativity
    ac_rfl
  whiskerLeft_id := by
    intros X Y
    apply StochasticMatrix.ext
    ext ⟨x, y⟩ ⟨x', y'⟩
    simp only [MonoidalCategoryStruct.whiskerLeft, StochasticMatrix.tensor]
    simp only [CategoryStruct.id, StochasticMatrix.id]
    -- X ◁ id_Y = id_(X⊗Y): whiskering preserves identities
    by_cases hx : x = x'
    · by_cases hy : y = y'
      · -- Both match: 1 * 1 = 1
        subst hx hy
        simp
      · -- x matches, y doesn't: 1 * 0 = 0
        subst hx
        simp only [hy, if_false, mul_zero]
        by_cases h : (x, y) = (x, y')
        · exfalso
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, h2⟩ := h
          exact hy h2
        · simp only [NNReal.coe_zero, h, ↓reduceIte]
    · -- x doesn't match: 0 * _ = 0
      simp only [hx, if_false, zero_mul]
      by_cases h : (x, y) = (x', y')
      · exfalso
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, _⟩ := h
        exact hx h1
      · simp only [NNReal.coe_zero, h, ↓reduceIte]
  id_whiskerRight := by
    intros X Y
    apply StochasticMatrix.ext
    ext ⟨x, y⟩ ⟨x', y'⟩
    simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor]
    simp only [CategoryStruct.id, StochasticMatrix.id]
    -- id_X ▷ Y = id_(X⊗Y): symmetric to whiskerLeft_id
    by_cases hx : x = x'
    · by_cases hy : y = y'
      · -- Both match: 1 * 1 = 1
        subst hx hy
        simp only [↓reduceIte, mul_one, NNReal.coe_one]
      · -- x matches, y doesn't: 1 * 0 = 0
        subst hx
        simp only [hy, if_false, mul_zero]
        by_cases h : (x, y) = (x, y')
        · exfalso
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, h2⟩ := h
          exact hy h2
        · simp only [NNReal.coe_zero, h, ↓reduceIte]
    · -- x doesn't match: 0 * _ = 0
      simp only [hx, if_false, zero_mul]
      by_cases h : (x, y) = (x', y')
      · exfalso
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, _⟩ := h
        exact hx h1
      · simp only [NNReal.coe_zero, h, ↓reduceIte]
  associator_naturality := by
    -- Naturality follows from deterministic associator
    intros X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
    apply StochasticMatrix.ext
    ext ⟨⟨x₁, x₂⟩, x₃⟩ ⟨y₁, ⟨y₂, y₃⟩⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp,
               MonoidalCategoryStruct.tensorHom, StochasticMatrix.tensor]

    -- Both sides are sums that isolate the same unique term
    -- LHS: sum over intermediate ((y₁', y₂'), y₃')
    rw [Finset.sum_eq_single ⟨⟨y₁, y₂⟩, y₃⟩]
    · -- Main term: associator gives 1 for correct rearrangement
      simp only [associator_matrix, and_self, ↓reduceIte, mul_one, NNReal.coe_mul, ite_mul, one_mul,
                 zero_mul, NNReal.coe_sum]
      -- RHS: sum over intermediate (x₁', (x₂', x₃'))
      rw [Finset.sum_eq_single ⟨x₁, ⟨x₂, x₃⟩⟩]
      · -- Main term: both associators give 1 for the deterministic rearrangement
        -- Directly evaluate both sides
        norm_num
        ring
      · -- Other terms: associator gives 0
        intro ⟨x₁', ⟨x₂', x₃'⟩⟩ _ h_ne
        -- Associator is 0 unless coordinates match exactly
        by_cases h : x₁' = x₁ ∧ x₂' = x₂ ∧ x₃' = x₃
        · -- This contradicts h_ne
          exfalso
          apply h_ne
          simp [h]
        · simp only [NNReal.coe_eq_zero, ite_eq_right_iff, mul_eq_zero, and_imp]
          intro a_1 a_2 a_3
          subst a_3 a_2 a_1
          simp_all only [Finset.mem_univ, ne_eq, not_true_eq_false]
      · intro
        exfalso
        apply ‹_›
        exact Finset.mem_univ _
    · -- Other terms: wrong intermediate state gives 0
      intro ⟨⟨y₁', y₂'⟩, y₃'⟩ _ h_ne
      -- Associator is 0 unless coordinates match exactly
      by_cases h : y₁' = y₁ ∧ y₂' = y₂ ∧ y₃' = y₃
      · -- This contradicts h_ne
        exfalso
        apply h_ne
        simp [h]
      · -- Show associator matrix entry is 0
        have h_assoc_zero : (MonoidalCategoryStruct.associator Y₁ Y₂ Y₃).hom.toMatrix
                              ((y₁', y₂'), y₃') (y₁, y₂, y₃) = 0 := by
          change (associator Y₁ Y₂ Y₃).hom.toMatrix ((y₁', y₂'), y₃') (y₁, y₂, y₃) = 0
          simp only [associator]
          -- The condition y₁' = y₁ ∧ y₂' = y₂ ∧ y₃' = y₃ contradicts h
          simp only [h, if_false]
        rw [h_assoc_zero, mul_zero]
    · intro
      exfalso
      apply ‹_›
      exact Finset.mem_univ _
  leftUnitor_naturality := by
    intros X Y f
    apply StochasticMatrix.ext
    ext ⟨⟨⟩, x⟩ y
    -- LHS: (𝟙 ⊗ f) ≫ λ_Y, RHS: λ_X ≫ f
    simp only [CategoryStruct.comp, StochasticMatrix.comp]

    -- LHS: Sum over intermediate ((), y') in tensorUnit × Y
    rw [Finset.sum_eq_single ⟨⟨⟩, y⟩]
    · -- Main case: show LHS = RHS = f.toMatrix x y
      -- First simplify LHS tensor operation
      simp only [MonoidalCategoryStruct.whiskerLeft, StochasticMatrix.tensor, CategoryStruct.id,
                 StochasticMatrix.id, ↓reduceIte, one_mul, leftUnitor_matrix, mul_one, ite_mul,
                 zero_mul, Finset.sum_ite_eq, Finset.mem_univ]

    · -- Other intermediate states contribute 0 to LHS
      intro ⟨⟨⟩, y'⟩ _ h_ne
      have h_neq : y' ≠ y := by
        intro h_eq
        apply h_ne
        simp only [h_eq]
      simp only [MonoidalCategoryStruct.whiskerLeft, StochasticMatrix.tensor]
      simp only [CategoryStruct.id, StochasticMatrix.id]
      have h_unitor_zero : (MonoidalCategoryStruct.leftUnitor Y).hom.toMatrix (⟨⟩, y') y = 0 := by
        change (leftUnitor Y).hom.toMatrix (⟨⟩, y') y = 0
        simp only [leftUnitor, h_neq, if_false]
      simp only [h_unitor_zero, mul_zero]

    · -- Membership
      intro h
      exfalso
      exact h (Finset.mem_univ _)
  rightUnitor_naturality := by
    intros X Y f
    apply StochasticMatrix.ext
    ext ⟨x, ⟨⟩⟩ y
    -- LHS: (f ⊗ 𝟙 tensorUnit) ≫ (rightUnitor Y).hom
    -- RHS: (rightUnitor X).hom ≫ f
    simp only [CategoryStruct.comp, StochasticMatrix.comp]

    -- LHS: Sum over intermediate (y', ()) in Y × tensorUnit
    rw [Finset.sum_eq_single ⟨y, ⟨⟩⟩]
    · -- Main case: show LHS = RHS = f.toMatrix x y
      -- First simplify LHS tensor operation
      simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor]
      simp only [CategoryStruct.id, StochasticMatrix.id]
      -- LHS: f[x,y] * 1 * rightUnitor_Y[(y,()), y] = f[x,y] * 1 = f[x,y]
      have h_right_unitor : (MonoidalCategoryStruct.rightUnitor Y).hom.toMatrix (y,⟨⟩) y = 1 := by
        change (rightUnitor Y).hom.toMatrix (y, ⟨⟩) y = 1
        simp only [rightUnitor, if_true]
      simp only [h_right_unitor, mul_one]

      -- Now show RHS = f.toMatrix x y
      -- RHS: Sum over intermediate x' in X
      rw [Finset.sum_eq_single x]
      · -- Main term: rightUnitor_X[(x,()), x] * f[x,y] = 1 * f[x,y] = f[x,y]
        have h_right_unitor :
          (MonoidalCategoryStruct.rightUnitor X).hom.toMatrix (x, ⟨⟩) x = 1 := by
          change (rightUnitor X).hom.toMatrix (x, ⟨⟩) x = 1
          simp only [rightUnitor, if_true]
        simp only [↓reduceIte, mul_one, h_right_unitor, one_mul]
      · -- Other terms: rightUnitor gives 0 for x' ≠ x
        intro x' _ h_ne
        have h_unitor_zero :
          (MonoidalCategoryStruct.rightUnitor X).hom.toMatrix (x, ⟨⟩) x' = 0 := by
          change (rightUnitor X).hom.toMatrix (x, ⟨⟩) x' = 0
          simp only [rightUnitor]
          rw [if_neg h_ne.symm]
        simp only [h_unitor_zero, zero_mul]
      · -- Membership
        intro h
        exfalso
        exact h (Finset.mem_univ _)

    · -- Other intermediate states contribute 0 to LHS
      intro ⟨y', ⟨⟩⟩ _ h_ne
      have h_neq : y' ≠ y := by
        intro h_eq
        apply h_ne
        simp only [h_eq]
      simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor]
      simp only [CategoryStruct.id, StochasticMatrix.id]
      have h_unitor_zero : (MonoidalCategoryStruct.rightUnitor Y).hom.toMatrix (y', ⟨⟩) y = 0 := by
        change (rightUnitor Y).hom.toMatrix (y', ⟨⟩) y = 0
        simp only [rightUnitor, h_neq, if_false]
      simp only [h_unitor_zero, mul_zero]

    · -- Membership
      intro h
      exfalso
      exact h (Finset.mem_univ _)
  pentagon := by
    intros W X Y Z
    apply StochasticMatrix.ext
    ext ⟨⟨⟨w, x⟩, y⟩, z⟩ ⟨w', ⟨x', ⟨y', z'⟩⟩⟩
    -- Pentagon: two paths from (((W ⊗ X) ⊗ Y) ⊗ Z) to (W ⊗ (X ⊗ (Y ⊗ Z)))

    simp only [CategoryStruct.comp, StochasticMatrix.comp]

    -- Both sides sum over intermediate states
    -- LHS path: (((w,x),y),z) → ((w,(x,y)),z) → (w,((x,y),z)) → (w,(x,(y,z)))
    -- RHS path: (((w,x),y),z) → ((w,x),(y,z)) → (w,(x,(y,z)))

    -- LHS: First composition
    rw [Finset.sum_eq_single ⟨⟨w, ⟨x, y⟩⟩, z⟩]
    · -- Second composition
      rw [Finset.sum_eq_single ⟨w, ⟨⟨x, y⟩, z⟩⟩]
      · -- Evaluate all three morphisms in the LHS composition
        -- (α_ W X Y).hom ▷ Z
        simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor]
        simp only [CategoryStruct.id, StochasticMatrix.id]
        -- Evaluate associator W X Y at ((w, x), y) → (w, (x, y))
        have h_assoc1 : (MonoidalCategoryStruct.associator W X Y).hom.toMatrix
                        ((w, x), y) (w, (x, y)) = 1 := by
          change (associator W X Y).hom.toMatrix ((w, x), y) (w, (x, y)) = 1
          simp only [associator, and_self, ↓reduceIte]
        simp only [h_assoc1, one_mul]

        -- (α_ W (X ⊗ Y) Z).hom
        -- Evaluate at ((w, (x, y)), z) → (w, ((x, y), z))
        have h_assoc2 : (MonoidalCategoryStruct.associator W
                         (MonoidalCategoryStruct.tensorObj X Y) Z).hom.toMatrix
                        ((w, (x, y)), z) (w, ((x, y), z)) = 1 := by
          change (associator W (FinStoch.tensorObj X Y) Z).hom.toMatrix
                 ((w, (x, y)), z) (w, ((x, y), z)) = 1
          simp only [associator, and_self, ↓reduceIte]
        simp only [h_assoc2, one_mul]

        -- W ◁ (α_ X Y Z).hom
        simp only [MonoidalCategoryStruct.whiskerLeft, StochasticMatrix.tensor]
        simp only [CategoryStruct.id, StochasticMatrix.id]

        -- Now evaluate the LHS fully
        -- We have: 1 * 1 * (id_W ⊗ associator X Y Z)[(w, ((x,y),z)), (w', (x',(y',z')))]
        -- This equals: (if w = w' then 1 else 0) * associator[((x,y),z), (x',(y',z'))]
        -- The associator gives: if x = x' ∧ y = y' ∧ z = z' then 1 else 0
        simp only [if_true, one_mul]

        -- Manually expand the associator
        have h_assoc3_eval : (MonoidalCategoryStruct.associator X Y Z).hom.toMatrix
                             ((x, y), z) (x', y', z') =
                             if x = x' ∧ y = y' ∧ z = z' then 1 else 0 := by
          change (associator X Y Z).hom.toMatrix ((x, y), z) (x', y', z') = _
          simp only [associator]
        simp only [h_assoc3_eval]

        -- RHS: First composition
        rw [Finset.sum_eq_single ⟨⟨w, x⟩, ⟨y, z⟩⟩]
        · -- Evaluate both morphisms in the RHS composition
          -- (α_ (W ⊗ X) Y Z).hom - this is always 1 since we picked the exact intermediate state
          have h_assoc4 : (MonoidalCategoryStruct.associator
                           (MonoidalCategoryStruct.tensorObj W X) Y Z).hom.toMatrix
                          (((w, x), y), z) ((w, x), (y, z)) = 1 := by
            change (associator (FinStoch.tensorObj W X) Y Z).hom.toMatrix
                   (((w, x), y), z) ((w, x), (y, z)) = 1
            simp only [associator]
            simp [and_self]
          simp only [h_assoc4, one_mul]

          -- (α_ W X (Y ⊗ Z)).hom - need to evaluate at general output
          have h_assoc5_eval : (MonoidalCategoryStruct.associator W X
                               (MonoidalCategoryStruct.tensorObj Y Z)).hom.toMatrix
                              ((w, x), (y, z)) (w', (x', (y', z'))) =
                              if w = w' ∧ x = x' ∧ (y, z) = (y', z') then 1 else 0 := by
            change (associator W X (FinStoch.tensorObj Y Z)).hom.toMatrix
                   ((w, x), (y, z)) (w', (x', (y', z'))) = _
            simp only [associator]
          simp only [h_assoc5_eval]

          -- Both sides equal 1 if all coordinates match, 0 otherwise
          by_cases h : w = w' ∧ x = x' ∧ y = y' ∧ z = z'
          · obtain ⟨hw, hx, hy, hz⟩ := h
            simp only [hw, ↓reduceIte, hx, hy, hz, and_self, mul_one, NNReal.coe_one]
          · push_neg at h
            -- At least one coordinate doesn't match, so result is 0
            by_cases hw : w = w'
            · by_cases hx : x = x'
              · by_cases hy : y = y'
                · -- w, x, y match but z doesn't
                  have hz : ¬(z = z') := by
                    intro hz'
                    apply h
                    exact hw
                    exact hx
                    exact hy
                    exact hz'
                  simp only [hw, ↓reduceIte, hx, hy, hz, and_false, mul_zero, NNReal.coe_zero,
                    Prod.mk.injEq]
                · -- w, x match but y doesn't
                  simp only [hw, ↓reduceIte, hx, hy, false_and, and_false, mul_zero,
                    NNReal.coe_zero, Prod.mk.injEq]
              · -- w matches but x doesn't
                simp only [hw, ↓reduceIte, hx, false_and, mul_zero, NNReal.coe_zero, Prod.mk.injEq,
                  and_false]
            · -- w doesn't match
              simp only [hw, ↓reduceIte, mul_ite, mul_one, mul_zero, ite_self, NNReal.coe_zero,
                Prod.mk.injEq, false_and]

        · -- Other RHS intermediate states give 0
          intro ⟨⟨w₁, x₁⟩, ⟨y₁, z₁⟩⟩ _ h_ne
          -- First associator is 0 unless all match
          have h_assoc_zero : (MonoidalCategoryStruct.associator
                               (MonoidalCategoryStruct.tensorObj W X) Y Z).hom.toMatrix
                              (((w, x), y), z) ((w₁, x₁), (y₁, z₁)) = 0 := by
            change (associator (FinStoch.tensorObj W X) Y Z).hom.toMatrix
                   (((w, x), y), z) ((w₁, x₁), (y₁, z₁)) = 0
            simp only [associator]
            by_cases h : (w, x) = (w₁, x₁) ∧ y = y₁ ∧ z = z₁
            · -- This would contradict h_ne
              obtain ⟨⟨hw, hx⟩, hy, hz⟩ := h
              exfalso
              apply h_ne
              simp only [hy, hz]
            · push_neg at h
              simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_and]
              exact h
          simp only [h_assoc_zero, associator_matrix, mul_ite, mul_one, mul_zero, ite_self]

        · intro h; exfalso; exact h (Finset.mem_univ _)

      · -- Other LHS second intermediate states give 0
        intro ⟨w₁, ⟨⟨x₁, y₁⟩, z₁⟩⟩ _ h_ne
        -- Second associator is 0 unless all match
        have h_assoc_zero : (MonoidalCategoryStruct.associator W
                             (MonoidalCategoryStruct.tensorObj X Y) Z).hom.toMatrix
                            ((w, (x, y)), z) (w₁, ((x₁, y₁), z₁)) = 0 := by
          change (associator W (FinStoch.tensorObj X Y) Z).hom.toMatrix
                 ((w, (x, y)), z) (w₁, ((x₁, y₁), z₁)) = 0
          simp only [associator]
          by_cases h : w = w₁ ∧ (x, y) = (x₁, y₁) ∧ z = z₁
          · -- This would contradict h_ne
            obtain ⟨hw, ⟨hx, hy⟩, hz⟩ := h
            exfalso
            apply h_ne
            simp only [hw, hz]
          · push_neg at h
            rw [if_neg]
            simp only [not_and]
            exact h
        simp only [h_assoc_zero, zero_mul]

      · -- Membership
        intro h; exfalso; exact h (Finset.mem_univ _)

    · -- Other LHS first intermediate states give 0
      intro ⟨⟨w₁, ⟨x₁, y₁⟩⟩, z₁⟩ _ h_ne
      -- First whiskerRight is 0 unless all match
      simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor]
      simp only [CategoryStruct.id, StochasticMatrix.id]
      -- The whiskerRight (associator ⊗ id_Z) gives 0 when
      -- ((w₁, (x₁, y₁)), z₁) ≠ ((w, (x, y)), z)
      -- This happens when either part is 0
      by_cases h_match : (w₁, (x₁, y₁)) = (w, (x, y)) ∧ z₁ = z
      · -- If both parts match, we'd have ((w₁, (x₁, y₁)), z₁) = ((w, (x, y)), z)
        -- But this contradicts h_ne
        obtain ⟨h_assoc, h_z⟩ := h_match
        exfalso
        apply h_ne
        congr 1
      · -- At least one part doesn't match, so the tensor product gives 0
        push_neg at h_match
        -- The product (associator W X Y)[((w,x),y), (w₁,(x₁,y₁))] * id_Z[z, z₁]
        -- is 0 if either factor is 0
        by_cases h_assoc : (w₁, (x₁, y₁)) = (w, (x, y))
        · -- Associator part matches, so identity part must not match
          have h_z : z₁ ≠ z := h_match h_assoc
          -- The product is associator * id_Z = 1 * 0 = 0
          simp only [associator_matrix, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
            ite_eq_right_iff, Finset.sum_eq_zero_iff, Finset.mem_univ, and_imp, forall_const]
          intro a_1 a_2 a_3 a_4 i a_5 a_6 a_7
          subst a_1 a_4 a_3 a_2 a_5 a_7
          simp_all only [ne_eq, not_true_eq_false]
        · -- Associator part doesn't match, so it gives 0
          -- Show the associator gives 0
          · -- Associator part doesn't match, so it gives 0
            have h_assoc_zero : (MonoidalCategoryStruct.associator W X Y).hom.toMatrix
                                ((w, x), y) (w₁, (x₁, y₁)) = 0 := by
              simp only [MonoidalCategoryStruct.associator, associator]
              rw [if_neg]
              -- Associator gives 1 iff (w₁, (x₁, y₁)) = (w, (x, y))
              -- But h_assoc says they differ
              intro h_components
              obtain ⟨hw, hx, hy⟩ := h_components
              apply h_assoc
              simp only [hw, hx, hy]
            simp only [h_assoc_zero, zero_mul]

    · -- Membership
      intro h; exfalso; exact h (Finset.mem_univ _)

  triangle := by
    intros X Y
    apply StochasticMatrix.ext
    ext ⟨⟨x, ⟨⟩⟩, y⟩ ⟨x', y'⟩
    -- Triangle: (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y
    -- Both sides map ((x, ()), y) ↦ (x, y) deterministically

    simp only [CategoryStruct.comp, StochasticMatrix.comp]

    -- LHS: composition of associator and whiskerLeft
    -- Sum over intermediate states (x₁, ((), y₁))
    rw [Finset.sum_eq_single ⟨x, ⟨⟨⟩, y⟩⟩]
    · -- Main term: intermediate state (x, ((), y))
      -- Evaluate associator at ((x, ()), y) → (x, ((), y))
      have h_assoc : (MonoidalCategoryStruct.associator X
                       (MonoidalCategoryStruct.tensorUnit FinStoch) Y).hom.toMatrix
                       ((x, PUnit.unit), y) (x, PUnit.unit, y) = 1 := by
        change (associator X tensorUnit Y).hom.toMatrix ((x, ()), y) (x, ((), y)) = 1
        simp only [associator, and_self, ↓reduceIte]

      -- Evaluate whiskerLeft = id_X ⊗ λ_Y at (x, ((), y)) → (x', y')
      simp only [MonoidalCategoryStruct.whiskerLeft, StochasticMatrix.tensor]
      simp only [CategoryStruct.id, StochasticMatrix.id]

      -- Simplify tuple projections
      simp only [h_assoc, leftUnitor_matrix, mul_ite, mul_one, mul_zero, NNReal.coe_inj]

      -- Evaluate leftUnitor
      have h_left : (MonoidalCategoryStruct.leftUnitor Y).hom.toMatrix (PUnit.unit, y) y' =
                    if y = y' then 1 else 0 := by
        change (leftUnitor Y).hom.toMatrix ((), y) y' = if y = y' then 1 else 0
        simp only [leftUnitor]

      simp_all only [associator_matrix, and_self, ↓reduceIte, leftUnitor_matrix]

      -- Evaluate RHS: rightUnitor ⊗ id_Y
      simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor]
      simp only [CategoryStruct.id, StochasticMatrix.id]
      simp_all only [rightUnitor_matrix, mul_ite, mul_one, mul_zero]

    · -- Other intermediate states: associator gives 0
      intro ⟨x₁, ⟨⟨⟩, y₁⟩⟩ _ h_ne
      -- The associator is 0 unless (x₁, y₁) = (x, y)
      have h_assoc_zero : (MonoidalCategoryStruct.associator X
                           (MonoidalCategoryStruct.tensorUnit FinStoch) Y).hom.toMatrix
                           ((x, PUnit.unit), y) (x₁, PUnit.unit, y₁) = 0 := by
        change (associator X tensorUnit Y).hom.toMatrix ((x, ()), y) (x₁, ((), y₁)) = 0
        simp only [associator]
        simp_all only [Finset.mem_univ, ne_eq, true_and, ite_eq_right_iff, one_ne_zero, imp_false,
                       not_and]
        intro a
        subst a
        apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [not_true_eq_false]

      simp only [h_assoc_zero, zero_mul]

    · -- Membership: all states exist in finite type
      intro h; exfalso; exact h (Finset.mem_univ _)

end CategoryTheory.MarkovCategory
