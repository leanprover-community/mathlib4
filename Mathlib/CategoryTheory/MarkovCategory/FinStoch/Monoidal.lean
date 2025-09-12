/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.MarkovCategory.FinStoch.Basic
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Monoidal Structure on FinStoch

This file defines the monoidal category structure on `FinStoch`, showing that
finite stochastic matrices form a symmetric monoidal category.

## Mathematical perspective

The monoidal structure on FinStoch models parallel composition of random processes.
The tensor product runs two random processes independently. The structural
isomorphisms (associator, unitors) preserve outcomes regardless of grouping.

All structural isomorphisms are deterministic; they rearrange data without
adding randomness. Thus the categorical structure preserves information;
only morphisms within the category add randomness.

## Main definitions

* `associator` - The associativity isomorphism `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`
* `leftUnitor` - The left unit isomorphism `I ⊗ X ≅ X`
* `rightUnitor` - The right unit isomorphism `X ⊗ I ≅ X`
* `MonoidalCategoryStruct FinStoch` - The basic monoidal structure
* `MonoidalCategory FinStoch` - Full monoidal category with coherence conditions

## Implementation notes

### Deterministic structural maps

We build structural isomorphisms using explicit stochastic matrices that
give probability 1 to the right rearrangement and 0 elsewhere. This
makes them deterministic in the Markov category sense (preserve copying).

### Proof strategy

The proofs follow this pattern:
1. Use `Finset.sum_eq_single` to isolate the unique non-zero contribution
2. Handle the exceptional cases (which contribute 0)
3. For inverse proofs, use `ite_cond_congr` to align tuple equality conditions

The `ite_cond_congr` technique works around Lean distinguishing between
`x = x'` and `((), x) = ((), x')` as propositions, though they're logically
the same. This rewriting makes the if-then-else conditions match.

### Coherence proofs

All naturality and coherence conditions are proven:
- Naturality: Structural maps commute with arbitrary morphisms
- Pentagon/triangle: Mac Lane's coherence conditions hold

The proofs track composition using sums.

## Design rationale

We build structural isomorphisms explicitly rather than deriving them
from a product structure because:
1. It shows they're deterministic
2. It matches actual computation
3. It provides concrete foundations for the Markov category instance

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]

## Tags

Markov category, monoidal category, stochastic matrix, tensor product
-/

namespace CategoryTheory.MarkovCategory

open FinStoch

universe u

/-- The associator isomorphism rearranges `((X ⊗ Y) ⊗ Z)` to `(X ⊗ (Y ⊗ Z))`.

This map sends `((x,y),z) ↦ (x,(y,z))` with probability 1. It only changes
the tuple structure, not the data. This proves that grouping doesn't affect
the outcome when we compose three processes in parallel. -/
def associator (X Y Z : FinStoch) :
    (tensorObj (tensorObj X Y) Z) ≅ (tensorObj X (tensorObj Y Z)) where
  hom := ⟨fun ⟨⟨x, y⟩, z⟩ ⟨x', ⟨y', z'⟩⟩ =>
    if x = x' ∧ y = y' ∧ z = z' then 1 else 0, fun ⟨⟨x, y⟩, z⟩ => by
    -- The output (x,(y,z)) has probability 1, all others have 0
    rw [Finset.sum_eq_single ⟨x, ⟨y, z⟩⟩]
    · simp only [and_self, if_true]
    · -- Other outputs have probability 0
      intro b _ hb
      obtain ⟨x', ⟨y', z'⟩⟩ := b
      simp only
      split_ifs with h
      · -- Can't match if b ≠ target
        obtain ⟨h1, h2, h3⟩ := h
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
    -- Inverse map: (x,(y,z)) ↦ ((x,y),z)
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
      · simp [h]
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        simp [and_self]
      · simp [h]
        push_neg at h
        simp [Prod.mk.injEq] at h
        exact h
    · -- Other intermediate states contribute 0
      intro b _ hb
      obtain ⟨x₁, ⟨y₁, z₁⟩⟩ := b
      simp only
      split_ifs with h h2
      · -- Would contradict hb
        obtain ⟨rfl, rfl, rfl⟩ := h
        exfalso
        exact hb rfl
      · -- Would contradict hb
        obtain ⟨rfl, rfl, rfl⟩ := h
        exfalso
        exact hb rfl
      · -- Zero probability path
        simp only [zero_mul]
      · -- Zero probability path
        simp only [zero_mul]
    · -- State must exist in finite type
      intro h
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
      by_cases h : (x, (y, z)) = (x', (y', z'))
      · simp [h]
        obtain ⟨rfl, ⟨rfl, rfl⟩⟩ := h
        simp [and_self]
      · simp [h]
        push_neg at h
        simp [Prod.mk.injEq] at h
        exact h
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
        -- First match gives 0 because x ≠ x'
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
        -- First match gives 0 because x ≠ x'
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
    · -- The unique non-zero term when y₁' = y₁ and x₂' = x₂
      simp only [StochasticMatrix.id, CategoryStruct.id]
      by_cases h₁ : y₁ = y₁
      · by_cases h₂ : x₂ = x₂
        · simp [one_mul, mul_one]
        · -- Impossible: x₂ ≠ x₂
          exfalso
          exact h₂ rfl
      · -- Impossible: y₁ ≠ y₁
        exfalso
        exact h₁ rfl
    · -- Other terms: show (y₁', x₂') ≠ (y₁, x₂) gives zero contribution
      intro ⟨y₁', x₂'⟩ _ h_ne
      simp only [StochasticMatrix.id, CategoryStruct.id]
      -- At least one identity matrix is off-diagonal, contributing 0
      by_cases h₁ : y₁' = y₁
      · by_cases h₂ : x₂ = x₂'
        · -- Would contradict h_ne: both coordinates match
          exfalso
          apply h_ne
          congr 1
          · exact h₂.symm
        · -- x₂ ≠ x₂': right identity gives 0
          simp [h₂, zero_mul]
      · -- y₁' ≠ y₁: left identity gives 0
        simp [h₁, mul_zero]
    · -- Membership: (y₁, x₂) is in the finite set Y₁ × X₂
      intro h
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
        simp [hx, hy]
      · -- x matches, y doesn't: prob 1 * 0 = 0
        simp [hx, hy]
        split_ifs with h
        · exfalso
          obtain ⟨_, h2⟩ := h
          exact hy rfl
        · rfl
    · -- x doesn't match: prob 0 * _ = 0
      simp [hx]
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
        · simp [h]
    · -- x doesn't match: 0 * _ = 0
      simp only [hx, if_false, zero_mul]
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
    -- id_X ▷ Y = id_(X⊗Y): symmetric to whiskerLeft_id
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
        · simp [h]
    · -- x doesn't match: 0 * _ = 0
      simp only [hx, if_false, zero_mul]
      by_cases h : (x, y) = (x', y')
      · exfalso
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, _⟩ := h
        exact hx h1
      · simp [h]
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
      simp
      -- RHS: sum over intermediate (x₁', (x₂', x₃'))
      rw [Finset.sum_eq_single ⟨x₁, ⟨x₂, x₃⟩⟩]
      · -- Main term: both associators give 1 for the deterministic rearrangement
        -- Show both associator evaluations are 1
        have h1 : (MonoidalCategoryStruct.associator Y₁ Y₂ Y₃).hom.toMatrix
                    ((y₁, y₂), y₃) (y₁, y₂, y₃) = 1 := by
          change (associator Y₁ Y₂ Y₃).hom.toMatrix ((y₁, y₂), y₃) (y₁, y₂, y₃) = 1
          simp only [associator]
          simp
        have h2 : (MonoidalCategoryStruct.associator X₁ X₂ X₃).hom.toMatrix
                    ((x₁, x₂), x₃) (x₁, x₂, x₃) = 1 := by
          change (associator X₁ X₂ X₃).hom.toMatrix ((x₁, x₂), x₃) (x₁, x₂, x₃) = 1
          simp only [associator]
          simp
        simp only [h1, h2]
        ring
      · -- Other terms: associator gives 0
        intro ⟨x₁', ⟨x₂', x₃'⟩⟩ _ h_ne
        -- Associator is 0 unless coordinates match exactly
        by_cases h : x₁' = x₁ ∧ x₂' = x₂ ∧ x₃' = x₃
        · -- This contradicts h_ne
          exfalso
          apply h_ne
          simp [h]
        · -- Associator gives 0, making the entire product 0
          -- Show associator matrix entry is 0
          have h_assoc_zero : (MonoidalCategoryStruct.associator X₁ X₂ X₃).hom.toMatrix
                                ((x₁, x₂), x₃) (x₁', x₂', x₃') = 0 := by
            change (associator X₁ X₂ X₃).hom.toMatrix ((x₁, x₂), x₃) (x₁', x₂', x₃') = 0
            simp only [associator]
            -- The condition x₁ = x₁' ∧ x₂ = x₂' ∧ x₃ = x₃' equals our h
            have h' : ¬(x₁ = x₁' ∧ x₂ = x₂' ∧ x₃ = x₃') := by
              intro h_eq
              apply h
              exact ⟨h_eq.1.symm, h_eq.2.1.symm, h_eq.2.2.symm⟩
            simp only [h', if_false]
          rw [h_assoc_zero]
          simp [zero_mul]
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
      simp only [MonoidalCategoryStruct.whiskerLeft, StochasticMatrix.tensor]
      simp only [CategoryStruct.id, StochasticMatrix.id]
      -- LHS: 1 * f[x,y] * leftUnitor_Y[((),y), y] = f[x,y] * 1 = f[x,y]
      have h_left_unitor : (MonoidalCategoryStruct.leftUnitor Y).hom.toMatrix (⟨⟩, y) y = 1 := by
        change (leftUnitor Y).hom.toMatrix (⟨⟩, y) y = 1
        simp only [leftUnitor, if_true]
      simp only [h_left_unitor, mul_one]
      simp

      -- Now show RHS = f.toMatrix x y
      -- RHS: Sum over intermediate x' in X
      rw [Finset.sum_eq_single x]
      · -- Main term: leftUnitor_X[((),x), x] * f[x,y] = 1 * f[x,y] = f[x,y]
        have h_right_unitor : (MonoidalCategoryStruct.leftUnitor X).hom.toMatrix (⟨⟩, x) x = 1 := by
          change (leftUnitor X).hom.toMatrix (⟨⟩, x) x = 1
          simp only [leftUnitor, if_true]
        simp only [h_right_unitor]
        simp
      · -- Other terms: leftUnitor gives 0 for x' ≠ x
        intro x' _ h_ne
        have h_unitor_zero : (MonoidalCategoryStruct.leftUnitor X).hom.toMatrix (⟨⟩, x) x' = 0 := by
          change (leftUnitor X).hom.toMatrix (⟨⟩, x) x' = 0
          simp only [leftUnitor]
          rw [if_neg h_ne.symm]
        simp only [h_unitor_zero]
        simp
      · -- Membership
        intro h
        exfalso
        exact h (Finset.mem_univ _)

    · -- Other intermediate states contribute 0 to LHS
      intro ⟨⟨⟩, y'⟩ _ h_ne
      have h_neq : y' ≠ y := by
        intro h_eq
        apply h_ne
        simp [h_eq]
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
      simp

      -- Now show RHS = f.toMatrix x y
      -- RHS: Sum over intermediate x' in X
      rw [Finset.sum_eq_single x]
      · -- Main term: rightUnitor_X[(x,()), x] * f[x,y] = 1 * f[x,y] = f[x,y]
        have h_right_unitor :
          (MonoidalCategoryStruct.rightUnitor X).hom.toMatrix (x, ⟨⟩) x = 1 := by
          change (rightUnitor X).hom.toMatrix (x, ⟨⟩) x = 1
          simp only [rightUnitor, if_true]
        simp only [h_right_unitor]
        simp
      · -- Other terms: rightUnitor gives 0 for x' ≠ x
        intro x' _ h_ne
        have h_unitor_zero :
          (MonoidalCategoryStruct.rightUnitor X).hom.toMatrix (x, ⟨⟩) x' = 0 := by
          change (rightUnitor X).hom.toMatrix (x, ⟨⟩) x' = 0
          simp only [rightUnitor]
          rw [if_neg h_ne.symm]
        simp only [h_unitor_zero]
        simp
      · -- Membership
        intro h
        exfalso
        exact h (Finset.mem_univ _)

    · -- Other intermediate states contribute 0 to LHS
      intro ⟨y', ⟨⟩⟩ _ h_ne
      have h_neq : y' ≠ y := by
        intro h_eq
        apply h_ne
        simp [h_eq]
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
          simp only [associator]
          simp [and_self]
        simp only [h_assoc1, one_mul]

        -- (α_ W (X ⊗ Y) Z).hom
        -- Evaluate at ((w, (x, y)), z) → (w, ((x, y), z))
        have h_assoc2 : (MonoidalCategoryStruct.associator W
                         (MonoidalCategoryStruct.tensorObj X Y) Z).hom.toMatrix
                        ((w, (x, y)), z) (w, ((x, y), z)) = 1 := by
          change (associator W (tensorObj X Y) Z).hom.toMatrix
                 ((w, (x, y)), z) (w, ((x, y), z)) = 1
          simp only [associator]
          simp [and_self]
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
            change (associator (tensorObj W X) Y Z).hom.toMatrix
                   (((w, x), y), z) ((w, x), (y, z)) = 1
            simp only [associator]
            simp [and_self]
          simp only [h_assoc4, one_mul]

          -- (α_ W X (Y ⊗ Z)).hom - need to evaluate at general output
          have h_assoc5_eval : (MonoidalCategoryStruct.associator W X
                               (MonoidalCategoryStruct.tensorObj Y Z)).hom.toMatrix
                              ((w, x), (y, z)) (w', (x', (y', z'))) =
                              if w = w' ∧ x = x' ∧ (y, z) = (y', z') then 1 else 0 := by
            change (associator W X (tensorObj Y Z)).hom.toMatrix
                   ((w, x), (y, z)) (w', (x', (y', z'))) = _
            simp only [associator]
          simp only [h_assoc5_eval]

          -- Both sides equal 1 if all coordinates match, 0 otherwise
          by_cases h : w = w' ∧ x = x' ∧ y = y' ∧ z = z'
          · obtain ⟨hw, hx, hy, hz⟩ := h
            simp [hw, hx, hy, hz]
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
                  simp [hw, hx, hy, hz]
                · -- w, x match but y doesn't
                  simp [hw, hx, hy]
              · -- w matches but x doesn't
                simp [hw, hx]
            · -- w doesn't match
              simp [hw]

        · -- Other RHS intermediate states give 0
          intro ⟨⟨w₁, x₁⟩, ⟨y₁, z₁⟩⟩ _ h_ne
          -- First associator is 0 unless all match
          have h_assoc_zero : (MonoidalCategoryStruct.associator
                               (MonoidalCategoryStruct.tensorObj W X) Y Z).hom.toMatrix
                              (((w, x), y), z) ((w₁, x₁), (y₁, z₁)) = 0 := by
            change (associator (tensorObj W X) Y Z).hom.toMatrix
                   (((w, x), y), z) ((w₁, x₁), (y₁, z₁)) = 0
            simp only [associator]
            by_cases h : (w, x) = (w₁, x₁) ∧ y = y₁ ∧ z = z₁
            · -- This would contradict h_ne
              obtain ⟨⟨hw, hx⟩, hy, hz⟩ := h
              exfalso
              apply h_ne
              simp [hy, hz]
            · push_neg at h
              simp
              exact h
          simp only [h_assoc_zero]
          simp [zero_mul]

        · intro h; exfalso; exact h (Finset.mem_univ _)

      · -- Other LHS second intermediate states give 0
        intro ⟨w₁, ⟨⟨x₁, y₁⟩, z₁⟩⟩ _ h_ne
        -- Second associator is 0 unless all match
        have h_assoc_zero : (MonoidalCategoryStruct.associator W
                             (MonoidalCategoryStruct.tensorObj X Y) Z).hom.toMatrix
                            ((w, (x, y)), z) (w₁, ((x₁, y₁), z₁)) = 0 := by
          change (associator W (tensorObj X Y) Z).hom.toMatrix
                 ((w, (x, y)), z) (w₁, ((x₁, y₁), z₁)) = 0
          simp only [associator]
          by_cases h : w = w₁ ∧ (x, y) = (x₁, y₁) ∧ z = z₁
          · -- This would contradict h_ne
            obtain ⟨hw, ⟨hx, hy⟩, hz⟩ := h
            exfalso
            apply h_ne
            simp [hw, hz]
          · push_neg at h
            rw [if_neg]
            simp
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
          simp [mul_zero]
          grind
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
              simp [hw, hx, hy]
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
        simp only [associator]
        simp [and_self]

      -- Evaluate whiskerLeft = id_X ⊗ λ_Y at (x, ((), y)) → (x', y')
      simp only [MonoidalCategoryStruct.whiskerLeft, StochasticMatrix.tensor]
      simp only [CategoryStruct.id, StochasticMatrix.id]

      -- Simplify tuple projections
      simp only [h_assoc]
      simp

      -- Evaluate leftUnitor
      have h_left : (MonoidalCategoryStruct.leftUnitor Y).hom.toMatrix (PUnit.unit, y) y' =
                    if y = y' then 1 else 0 := by
        change (leftUnitor Y).hom.toMatrix ((), y) y' = if y = y' then 1 else 0
        simp only [leftUnitor]

      simp only [h_left]

      -- Evaluate RHS: rightUnitor ⊗ id_Y
      simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor]
      simp only [CategoryStruct.id, StochasticMatrix.id]

      -- Evaluate rightUnitor
      have h_right : (MonoidalCategoryStruct.rightUnitor X).hom.toMatrix (x, PUnit.unit) x' =
                     if x = x' then 1 else 0 := by
        change (rightUnitor X).hom.toMatrix (x, ()) x' = if x = x' then 1 else 0
        simp only [rightUnitor]

      simp only [h_right]

      -- Both sides equal (if x = x' then 1 else 0) * (if y = y' then 1 else 0)
      by_cases hx : x = x'
      · by_cases hy : y = y'
        · -- Both match: 1 * 1 = 1
          simp [hx, hy]
        · -- x matches, y doesn't: 1 * 0 = 0
          simp [hx, hy]
      · -- x doesn't match: 0 * _ = 0
        simp [hx]

    · -- Other intermediate states: associator gives 0
      intro ⟨x₁, ⟨⟨⟩, y₁⟩⟩ _ h_ne
      -- The associator is 0 unless (x₁, y₁) = (x, y)
      have h_assoc_zero : (MonoidalCategoryStruct.associator X
                           (MonoidalCategoryStruct.tensorUnit FinStoch) Y).hom.toMatrix
                           ((x, PUnit.unit), y) (x₁, PUnit.unit, y₁) = 0 := by
        change (associator X tensorUnit Y).hom.toMatrix ((x, ()), y) (x₁, ((), y₁)) = 0
        simp only [associator]
        -- Need to show ¬(x = x₁ ∧ () = () ∧ y = y₁)
        by_cases h : x = x₁ ∧ y = y₁
        · -- This would contradict h_ne
          exfalso
          obtain ⟨hx, hy⟩ := h
          apply h_ne
          simp [hx, hy]
        · -- At least one doesn't match
          push_neg at h
          by_cases hx : x = x₁
          · -- x matches but y doesn't
            have hy : ¬(y = y₁) := h hx
            simp [hx, hy]
          · -- x doesn't match
            simp [hx]

      simp only [h_assoc_zero, zero_mul]

    · -- Membership: all states exist in finite type
      intro h; exfalso; exact h (Finset.mem_univ _)

end CategoryTheory.MarkovCategory
