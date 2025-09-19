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
    · simp only [DetMorphism.toMatrix_apply, associatorDet, associatorInvDet]
      simp only [DetMorphism.ofFunc]
      simp only [StochasticMatrix.id, CategoryStruct.id]
      by_cases h : ((x, y), z) = ((x', y'), z')
      · simp only [↓reduceIte, h, mul_one, NNReal.coe_one]
      · simp only [↓reduceIte, h, mul_zero, NNReal.coe_zero]
    · intro b _ hb
      simp only [associatorDet, associatorInvDet, DetMorphism.ofFunc]
      split_ifs with h1 h2
      · simp only [one_mul]
        exfalso
        rw [h1] at hb
        exact hb rfl
      · simp only [mul_zero]
      · simp only [mul_one]
      · simp only [mul_zero]
    · intro h; exfalso; exact h (Finset.mem_univ _)
  inv_hom_id := by
    apply StochasticMatrix.ext
    ext ⟨x, ⟨y, z⟩⟩ ⟨x', ⟨y', z'⟩⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single ⟨⟨x, y⟩, z⟩]
    · simp only [DetMorphism.toMatrix_apply, associatorInvDet, associatorDet]
      simp only [DetMorphism.ofFunc]
      simp only [StochasticMatrix.id, CategoryStruct.id]
      by_cases h : (x, (y, z)) = (x', (y', z'))
      · simp only [↓reduceIte, h, mul_one, NNReal.coe_one]
      · simp only [↓reduceIte, h, mul_zero, NNReal.coe_zero]
    · intro b _ hb
      simp only [associatorInvDet, associatorDet, DetMorphism.ofFunc]
      split_ifs with h1 h2
      · simp only [one_mul]
        exfalso
        rw [h1] at hb
        exact hb rfl
      · simp only [mul_zero]
      · simp only [mul_one]
      · simp only [zero_mul]
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
    · simp only [DetMorphism.toMatrix_apply, leftUnitorDet, leftUnitorInvDet]
      simp only [DetMorphism.ofFunc]
      simp only [StochasticMatrix.id, CategoryStruct.id]
      by_cases h : ((), x) = ((), x')
      · simp only [↓reduceIte, h, mul_one, NNReal.coe_one]
      · simp only [↓reduceIte, h, mul_zero, NNReal.coe_zero]
    · intro x'' _ hx''
      simp only [DetMorphism.toMatrix_apply]
      split_ifs with h
      · have : x'' = x := by
          simp only [leftUnitorDet, DetMorphism.ofFunc] at h
          exact h.symm
        rw [this] at hx''
        exfalso; exact hx'' rfl
      · simp only [mul_zero]
      · simp only [mul_one]
      · simp only [mul_zero]
    · intro h; exfalso; exact h (Finset.mem_univ _)
  inv_hom_id := by
    apply StochasticMatrix.ext
    ext x x'
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single ⟨⟨⟩, x⟩]
    · simp only [DetMorphism.toMatrix_apply, leftUnitorInvDet, leftUnitorDet]
      simp only [DetMorphism.ofFunc]
      simp only [StochasticMatrix.id, CategoryStruct.id]
      by_cases h : x = x'
      · simp only [↓reduceIte, h, mul_one, NNReal.coe_one]
      · simp only [↓reduceIte, h, mul_zero, NNReal.coe_zero]
    · intro b _ hb
      simp only [DetMorphism.toMatrix_apply]
      split_ifs with h
      · have : b = (⟨⟩, x) := by
          simp only [leftUnitorInvDet, DetMorphism.ofFunc] at h
          exact h.symm
        rw [this] at hb
        exfalso; exact hb rfl
      · simp only [mul_zero]
      · simp only [mul_one]
      · simp only [mul_zero]
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
    · simp only [DetMorphism.toMatrix_apply, rightUnitorDet, rightUnitorInvDet]
      simp only [DetMorphism.ofFunc]
      simp only [StochasticMatrix.id, CategoryStruct.id]
      by_cases h : (x, ()) = (x', ())
      · simp only [↓reduceIte, h, mul_one, NNReal.coe_one]
      · simp only [↓reduceIte, h, mul_zero, NNReal.coe_zero]
    · intro x'' _ hx''
      simp only [DetMorphism.toMatrix_apply]
      split_ifs with h
      · have : x'' = x := by
          simp only [rightUnitorDet, DetMorphism.ofFunc] at h
          exact h.symm
        rw [this] at hx''
        exfalso; exact hx'' rfl
      · simp only [mul_zero]
      · simp only [mul_one]
      · simp only [mul_zero]
    · intro h; exfalso; exact h (Finset.mem_univ _)
  inv_hom_id := by
    apply StochasticMatrix.ext
    ext x x'
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single ⟨x, ⟨⟩⟩]
    · simp only [DetMorphism.toMatrix_apply, rightUnitorInvDet, rightUnitorDet]
      simp only [DetMorphism.ofFunc]
      simp only [StochasticMatrix.id, CategoryStruct.id]
      by_cases h : x = x'
      · simp only [↓reduceIte, h, mul_one, NNReal.coe_one]
      · simp_all only [↓reduceIte, mul_zero, NNReal.coe_zero]
    · intro b _ hb
      simp only [DetMorphism.toMatrix_apply]
      split_ifs with h
      · have : b = (x, ⟨⟩) := by
          simp only [rightUnitorInvDet, DetMorphism.ofFunc] at h
          exact h.symm
        rw [this] at hb
        exfalso; exact hb rfl
      · simp only [mul_zero]
      · simp only [mul_one]
      · simp only [mul_zero]
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
  obtain ⟨⟨x, y⟩, z⟩ := xyz
  obtain ⟨x', ⟨y', z'⟩⟩ := xyz'
  simp only
  split
  next
    h =>
    simp_all only [left_eq_ite_iff, not_and, one_ne_zero, imp_false, Classical.not_imp,
      Decidable.not_not]
    constructor
    · cases h; rfl
    constructor
    · cases h; rfl
    · cases h; rfl
  next h =>
    simp_all only [right_eq_ite_iff, zero_ne_one, imp_false, not_and]
    intro hx hy
    by_contra h_eq
    -- Now we have z = z', and we want to contradict h
    have : (x, y, z) = (x', y', z') := by simp only [hx, hy, h_eq]
    exact h this

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

/-! ### Helper lemmas for pentagon identity -/

section PentagonHelpers

/-- Whisker right of associator with identity -/
lemma pentagon_whisker_right (W X Y Z : FinStoch)
    (wwxyz : (((W ⊗ X) ⊗ Y) ⊗ Z).carrier)
    (wxyyz : ((W ⊗ (X ⊗ Y)) ⊗ Z).carrier) :
    ((α_ W X Y).hom ▷ Z).toMatrix wwxyz wxyyz =
    if wwxyz.1.1.1 = wxyyz.1.1 ∧ wwxyz.1.1.2 = wxyyz.1.2.1 ∧
       wwxyz.1.2 = wxyyz.1.2.2 ∧ wwxyz.2 = wxyyz.2 then 1 else 0 := by
  simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor]
  simp only [associator_matrix, StochasticMatrix.id, CategoryStruct.id]
  obtain ⟨⟨⟨w, x⟩, y⟩, z⟩ := wwxyz
  obtain ⟨⟨w', ⟨x', y'⟩⟩, z'⟩ := wxyyz
  simp only
  by_cases h : w = w' ∧ x = x' ∧ y = y'
  · obtain ⟨hw, hx, hy⟩ := h
    subst hw hx hy
    by_cases hz : z = z'
    · subst hz
      simp only [if_true, mul_one, and_self]
    · simp only [and_self, ↓reduceIte, hz, mul_zero, and_false]
  · push_neg at h
    simp only [mul_ite, mul_one, mul_zero]
    by_cases hz : z = z'
    · simp only [hz, ↓reduceIte, and_true]
    · simp only [hz, ↓reduceIte, and_false]

/-- Middle associator in left path -/
lemma pentagon_middle_assoc (W X Y Z : FinStoch)
    (wxyyz : ((W ⊗ (X ⊗ Y)) ⊗ Z).carrier)
    (wxyz : (W ⊗ ((X ⊗ Y) ⊗ Z)).carrier) :
    (α_ W (X ⊗ Y) Z).hom.toMatrix wxyyz wxyz =
    if wxyyz.1.1 = wxyz.1 ∧ wxyyz.1.2 = wxyz.2.1 ∧
       wxyyz.2 = wxyz.2.2 then 1 else 0 := by
  simp only [associator_matrix]

/-- Whisker left of associator with identity -/
lemma pentagon_whisker_left (W X Y Z : FinStoch)
    (wxyyz : (W ⊗ ((X ⊗ Y) ⊗ Z)).carrier)
    (wxyz : (W ⊗ (X ⊗ (Y ⊗ Z))).carrier) :
    (W ◁ (α_ X Y Z).hom).toMatrix wxyyz wxyz =
    if wxyyz.1 = wxyz.1 ∧ wxyyz.2.1.1 = wxyz.2.1 ∧
       wxyyz.2.1.2 = wxyz.2.2.1 ∧ wxyyz.2.2 = wxyz.2.2.2 then 1 else 0 := by
  simp only [MonoidalCategoryStruct.whiskerLeft, StochasticMatrix.tensor]
  simp only [StochasticMatrix.id, CategoryStruct.id, associator_matrix]
  obtain ⟨w, ⟨⟨x, y⟩, z⟩⟩ := wxyyz
  obtain ⟨w', ⟨x', ⟨y', z'⟩⟩⟩ := wxyz
  simp only
  by_cases hw : w = w'
  · subst hw
    by_cases h : x = x' ∧ y = y' ∧ z = z'
    · simp only [↓reduceIte, h, and_self, mul_one]
    · push_neg at h
      simp only [↓reduceIte, mul_ite, mul_one, mul_zero, true_and]
  · simp only [hw, ↓reduceIte, mul_ite, mul_one, mul_zero, ite_self, false_and]

/-- First associator in right path -/
lemma pentagon_right_first (W X Y Z : FinStoch)
    (wwxyz : (((W ⊗ X) ⊗ Y) ⊗ Z).carrier)
    (wxyz : ((W ⊗ X) ⊗ (Y ⊗ Z)).carrier) :
    (α_ (W ⊗ X) Y Z).hom.toMatrix wwxyz wxyz =
    if wwxyz.1.1 = wxyz.1 ∧ wwxyz.1.2 = wxyz.2.1 ∧
       wwxyz.2 = wxyz.2.2 then 1 else 0 := by
  simp only [associator_matrix]

/-- Second associator in right path -/
lemma pentagon_right_second (W X Y Z : FinStoch)
    (wxyz : ((W ⊗ X) ⊗ (Y ⊗ Z)).carrier)
    (wxyz' : (W ⊗ (X ⊗ (Y ⊗ Z))).carrier) :
    (α_ W X (Y ⊗ Z)).hom.toMatrix wxyz wxyz' =
    if wxyz.1.1 = wxyz'.1 ∧ wxyz.1.2 = wxyz'.2.1 ∧
       wxyz.2 = wxyz'.2.2 then 1 else 0 := by
  simp only [associator_matrix]

/-- Left side composition equals indicator function -/
lemma pentagon_left_composition (W X Y Z : FinStoch)
    (wwxyz : (((W ⊗ X) ⊗ Y) ⊗ Z).carrier)
    (wxyz : (W ⊗ (X ⊗ (Y ⊗ Z))).carrier) :
    ((α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom).toMatrix wwxyz wxyz =
    if wwxyz.1.1.1 = wxyz.1 ∧ wwxyz.1.1.2 = wxyz.2.1 ∧
       wwxyz.1.2 = wxyz.2.2.1 ∧ wwxyz.2 = wxyz.2.2.2 then 1 else 0 := by
  simp only [CategoryStruct.comp, StochasticMatrix.comp]
  obtain ⟨⟨⟨w, x⟩, y⟩, z⟩ := wwxyz
  obtain ⟨w', ⟨x', ⟨y', z'⟩⟩⟩ := wxyz
  -- First composition: (α_ W X Y).hom ▷ Z
  rw [Finset.sum_eq_single ⟨⟨w, ⟨x, y⟩⟩, z⟩]
  · -- Second composition: (α_ W (X ⊗ Y) Z).hom
    rw [Finset.sum_eq_single ⟨w, ⟨⟨x, y⟩, z⟩⟩]
    · simp only [pentagon_whisker_right, pentagon_middle_assoc, pentagon_whisker_left]
      by_cases h : w = w' ∧ x = x' ∧ y = y' ∧ z = z'
      · obtain ⟨hw, hx, hy, hz⟩ := h
        subst hw hx hy hz
        simp only [true_and, if_true, mul_one]
      · push_neg at h
        -- When not all equal, at least one condition fails
        by_cases hw : w = w'
        · by_cases hxyz : x = x' ∧ y = y' ∧ z = z'
          · obtain ⟨hx, hy, hz⟩ := hxyz
            exfalso; exact h hw hx hy hz
          · push_neg at hxyz
            simp only [hw, true_and]
            -- Goal: ((if True ∧ True ∧ True ∧ True then 1 else 0) * ...) = if False...
            -- Since hw is true but not all of x,y,z match, result should be 0
            have h_not_all : ¬(x = x' ∧ y = y' ∧ z = z') := by
              push_neg
              exact hxyz
            simp only [h_not_all, if_false]
            -- Now show the LHS equals 0
            split_ifs <;> simp
        · simp only [hw, false_and, if_false, mul_zero]
    · intro b _ hb
      simp only [pentagon_middle_assoc, mul_eq_zero]
      left
      split_ifs with h
      · exfalso
        obtain ⟨h1, h2, h3⟩ := h
        have : b = ⟨w, ⟨⟨x, y⟩, z⟩⟩ := by
          cases b; simp only [h1, h2, h3, Prod.mk.eta]
        exact hb this
      · rfl
    · intro habs; exfalso; exact habs (Finset.mem_univ _)
  · intro b _ hb
    simp only [pentagon_whisker_right, mul_eq_zero]
    left
    split_ifs with h
    · exfalso
      obtain ⟨h1, h2, h3, h4⟩ := h
      have : b = ⟨⟨w, ⟨x, y⟩⟩, z⟩ := by
        cases b
        simp only at h1 h2 h3 h4 ⊢
        simp only [h1, h2, h3, Prod.mk.eta, h4]
      exact hb this
    · rfl
  · intro habs; exfalso; exact habs (Finset.mem_univ _)

/-- Right side composition equals indicator function -/
lemma pentagon_right_composition (W X Y Z : FinStoch)
    (wwxyz : (((W ⊗ X) ⊗ Y) ⊗ Z).carrier)
    (wxyz : (W ⊗ (X ⊗ (Y ⊗ Z))).carrier) :
    ((α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom).toMatrix wwxyz wxyz =
    if wwxyz.1.1.1 = wxyz.1 ∧ wwxyz.1.1.2 = wxyz.2.1 ∧
       wwxyz.1.2 = wxyz.2.2.1 ∧ wwxyz.2 = wxyz.2.2.2 then 1 else 0 := by
  simp only [CategoryStruct.comp, StochasticMatrix.comp]
  obtain ⟨⟨⟨w, x⟩, y⟩, z⟩ := wwxyz
  obtain ⟨w', ⟨x', ⟨y', z'⟩⟩⟩ := wxyz
  -- The composition sums over intermediate states
  -- (α_ (W ⊗ X) Y Z) maps ((w,x),y,z) to ((w,x),(y,z))
  -- (α_ W X (Y ⊗ Z)) maps ((w,x),(y,z)) to (w,(x,(y,z)))
  -- Since both are deterministic, the sum has only one non-zero term
  rw [Finset.sum_eq_single ⟨⟨w, x⟩, ⟨y, z⟩⟩]
  · -- Evaluate at the unique intermediate point
    simp only [pentagon_right_first, pentagon_right_second]
    -- First associator: ((w,x),y,z) → ((w,x),(y,z)) gives 1 iff all match
    -- This is always 1 since we're mapping ((w,x),y,z) to ((w,x),(y,z))
    simp only [if_true, true_and]
    -- Second associator: ((w,x),(y,z)) → (w,(x,(y,z))) gives 1 iff components match
    -- This is 1 iff w = w' ∧ x = x' ∧ (y,z) = (y',z')
    -- Which is equivalent to w = w' ∧ x = x' ∧ y = y' ∧ z = z'
    simp only [one_mul]
    -- The conditional is: if (w,x) = (w',x') ∧ (y,z) = (y',z') then 1 else 0
    -- This equals: if w = w' ∧ x = x' ∧ y = y' ∧ z = z' then 1 else 0
    congr 1
    -- Expand the product equalities
    rw [Prod.mk.injEq]
  · -- Show other terms in sum are zero
    intro b _ hb
    simp only [pentagon_right_first, mul_eq_zero]
    left
    -- First associator is deterministic: only maps to ((w,x),(y,z))
    split_ifs with h
    · exfalso
      obtain ⟨h1, h2, h3⟩ := h
      have : b = ⟨⟨w, x⟩, ⟨y, z⟩⟩ := by
        obtain ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩ := b
        simp only at h1 h2 h3
        simp only [h1, h2, h3]
      exact hb this
    · rfl
  · intro habs; exfalso; exact habs (Finset.mem_univ _)

end PentagonHelpers

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
      by_cases h₁ : y₁ = y₁
      · by_cases h₂ : x₂ = x₂
        · simp only [NNReal.coe_mul, ↓reduceIte, mul_one, one_mul]
        · exfalso; exact h₂ rfl
      · exfalso; exact h₁ rfl
    · intro ⟨y₁', x₂'⟩ _ h_ne
      simp only [StochasticMatrix.id, CategoryStruct.id]
      by_cases h₁ : y₁' = y₁
      · by_cases h₂ : x₂ = x₂'
        · exfalso
          apply h_ne
          rw [h₁, ← h₂]
        · simp only [h₂, ↓reduceIte, mul_zero, ite_mul, one_mul, zero_mul, mul_ite, ite_self]
      · simp only [mul_ite, mul_one, mul_zero, h₁, ↓reduceIte, zero_mul]
    · intro h; exfalso; exact h (Finset.mem_univ _)
  id_tensorHom_id := by
    intros X Y
    apply StochasticMatrix.ext
    ext ⟨x, y⟩ ⟨x', y'⟩
    simp only [MonoidalCategoryStruct.tensorHom, StochasticMatrix.tensor]
    simp only [CategoryStruct.id, StochasticMatrix.id]
    by_cases hx : x = x'
    · by_cases hy : y = y'
      · simp only [hx, ↓reduceIte, hy, mul_one, NNReal.coe_one]
      · simp only [hx, ↓reduceIte, hy, mul_zero, NNReal.coe_zero]
        split_ifs with h
        · exfalso
          obtain ⟨_, h2⟩ := h
          exact hy rfl
        · rfl
    · simp only [hx, ↓reduceIte, mul_ite, mul_one, mul_zero, ite_self, NNReal.coe_zero]
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
        simp only [hy, if_false, mul_zero]
        by_cases h : (x, y) = (x, y')
        · exfalso
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, h2⟩ := h
          exact hy h2
        · simp only [NNReal.coe_zero, h, ↓reduceIte]
    · simp only [hx, if_false, zero_mul]
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
    by_cases hx : x = x'
    · by_cases hy : y = y'
      · subst hx hy
        simp only [↓reduceIte, mul_one, NNReal.coe_one]
      · subst hx
        simp only [hy, if_false, mul_zero]
        by_cases h : (x, y) = (x, y')
        · exfalso
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, h2⟩ := h
          exact hy h2
        · simp only [NNReal.coe_zero, h, ↓reduceIte]
    · simp only [hx, if_false, zero_mul]
      by_cases h : (x, y) = (x', y')
      · exfalso
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, _⟩ := h
        exact hx h1
      · simp only [NNReal.coe_zero, h, ↓reduceIte]
  associator_naturality := by
    intros X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
    apply StochasticMatrix.ext
    ext ⟨⟨x₁, x₂⟩, x₃⟩ ⟨y₁, ⟨y₂, y₃⟩⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp,
               MonoidalCategoryStruct.tensorHom, StochasticMatrix.tensor]
    rw [Finset.sum_eq_single ⟨⟨y₁, y₂⟩, y₃⟩]
    · simp only [associator_matrix, and_self, ↓reduceIte, mul_one, NNReal.coe_mul, ite_mul,
                 one_mul, zero_mul, NNReal.coe_sum]
      rw [Finset.sum_eq_single ⟨x₁, ⟨x₂, x₃⟩⟩]
      · norm_num; ring
      · intro ⟨x₁', ⟨x₂', x₃'⟩⟩ _ h_ne
        by_cases h : x₁' = x₁ ∧ x₂' = x₂ ∧ x₃' = x₃
        · exfalso
          apply h_ne
          simp only [h]
        · simp only [NNReal.coe_eq_zero, ite_eq_right_iff, mul_eq_zero, and_imp]
          intro a_1 a_2 a_3
          subst a_3 a_2 a_1
          simp_all only [Finset.mem_univ, ne_eq, not_true_eq_false]
      · intro; exfalso; apply ‹_›; exact Finset.mem_univ _
    · intro ⟨⟨y₁', y₂'⟩, y₃'⟩ _ h_ne
      by_cases h : y₁' = y₁ ∧ y₂' = y₂ ∧ y₃' = y₃
      · exfalso
        apply h_ne
        simp only [h]
      · have h_assoc_zero : (MonoidalCategoryStruct.associator Y₁ Y₂ Y₃).hom.toMatrix
                              ((y₁', y₂'), y₃') (y₁, y₂, y₃) = 0 := by
          simp only [associator_matrix]
          simp only [h, if_false]
        rw [h_assoc_zero, mul_zero]
    · intro; exfalso; apply ‹_›; exact Finset.mem_univ _
  leftUnitor_naturality := by
    intros X Y f
    apply StochasticMatrix.ext
    ext ⟨⟨⟩, x⟩ y
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single ⟨⟨⟩, y⟩]
    · simp only [MonoidalCategoryStruct.whiskerLeft, StochasticMatrix.tensor, CategoryStruct.id,
                 StochasticMatrix.id, ↓reduceIte, one_mul, leftUnitor_matrix, mul_one, ite_mul,
                 zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
    · intro ⟨⟨⟩, y'⟩ _ h_ne
      have h_neq : y' ≠ y := by
        intro h_eq
        apply h_ne
        simp only [h_eq]
      simp only [MonoidalCategoryStruct.whiskerLeft, StochasticMatrix.tensor]
      simp only [CategoryStruct.id, StochasticMatrix.id]
      have h_unitor_zero : (MonoidalCategoryStruct.leftUnitor Y).hom.toMatrix (⟨⟩, y') y = 0 := by
        simp only [leftUnitor_matrix, h_neq, if_false]
      simp only [h_unitor_zero, mul_zero]
    · intro h; exfalso; exact h (Finset.mem_univ _)
  rightUnitor_naturality := by
    intros X Y f
    apply StochasticMatrix.ext
    ext ⟨x, ⟨⟩⟩ y
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    rw [Finset.sum_eq_single ⟨y, ⟨⟩⟩]
    · simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor]
      simp only [CategoryStruct.id, StochasticMatrix.id]
      have h_right_unitor : (MonoidalCategoryStruct.rightUnitor Y).hom.toMatrix (y,⟨⟩) y = 1 := by
        simp only [rightUnitor_matrix, if_true]
      simp only [h_right_unitor, mul_one]
      rw [Finset.sum_eq_single x]
      · have h_right_unitor :
          (MonoidalCategoryStruct.rightUnitor X).hom.toMatrix (x, ⟨⟩) x = 1 := by
          simp only [rightUnitor_matrix, if_true]
        simp only [↓reduceIte, mul_one, h_right_unitor, one_mul]
      · intro x' _ h_ne
        have h_unitor_zero :
          (MonoidalCategoryStruct.rightUnitor X).hom.toMatrix (x, ⟨⟩) x' = 0 := by
          simp only [rightUnitor_matrix]
          rw [if_neg h_ne.symm]
        simp only [h_unitor_zero, zero_mul]
      · intro h; exfalso; exact h (Finset.mem_univ _)
    · intro ⟨y', ⟨⟩⟩ _ h_ne
      have h_neq : y' ≠ y := by
        intro h_eq
        apply h_ne
        simp only [h_eq]
      simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor]
      simp only [CategoryStruct.id, StochasticMatrix.id]
      have h_unitor_zero : (MonoidalCategoryStruct.rightUnitor Y).hom.toMatrix (y', ⟨⟩) y = 0 := by
        simp only [rightUnitor_matrix, h_neq, if_false]
      simp only [h_unitor_zero, mul_zero]
    · intro h; exfalso; exact h (Finset.mem_univ _)
  pentagon := by
    intros W X Y Z
    apply StochasticMatrix.ext
    ext ⟨⟨⟨w, x⟩, y⟩, z⟩ ⟨w', ⟨x', ⟨y', z'⟩⟩⟩
    -- Use the helper lemmas we proved
    simp only [pentagon_left_composition, pentagon_right_composition]
  triangle := by
    intros X Y
    apply StochasticMatrix.ext
    ext ⟨⟨x, ⟨⟩⟩, y⟩ ⟨x', y'⟩
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    -- Both sides map ((x, ()), y) ↦ (x, y) deterministically
    rw [Finset.sum_eq_single ⟨x, ⟨⟨⟩, y⟩⟩]
    · simp only [associator_matrix, and_self, ↓reduceIte, NNReal.coe_inj]
      simp only [MonoidalCategoryStruct.whiskerLeft, StochasticMatrix.tensor]
      simp only [CategoryStruct.id, StochasticMatrix.id]
      simp_all only [leftUnitor_matrix]
      simp only [MonoidalCategoryStruct.whiskerRight, StochasticMatrix.tensor]
      simp only [CategoryStruct.id, StochasticMatrix.id]
      simp_all only [rightUnitor_matrix, mul_ite, mul_one, mul_zero]
    · intro ⟨x₁, ⟨⟨⟩, y₁⟩⟩ _ h_ne
      have h_assoc_zero : (MonoidalCategoryStruct.associator X
                           (MonoidalCategoryStruct.tensorUnit FinStoch) Y).hom.toMatrix
                           ((x, PUnit.unit), y) (x₁, PUnit.unit, y₁) = 0 := by
        simp only [associator_matrix]
        simp_all only [Finset.mem_univ, ne_eq, true_and, ite_eq_right_iff, one_ne_zero,
                       imp_false, not_and]
        intro a; subst a
        intro a; subst a
        simp_all only [not_true_eq_false]
      simp only [h_assoc_zero, zero_mul]
    · intro h; exfalso; exact h (Finset.mem_univ _)

end CategoryTheory.MarkovCategory
