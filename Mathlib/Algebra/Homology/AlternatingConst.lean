/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The alternating constant complex

In this file we define the chain complex `X ←0- X ←𝟙- X ←0- X ←𝟙- X ⋯`, and calculate its homology.

-/

open CategoryTheory Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C]

@[simp]
lemma ComplexShape.down_next (i : ℕ) : (ComplexShape.down ℕ).next i = i - 1 := by
  cases' i with i
  · simp
  · apply (ComplexShape.down ℕ).next_eq'
    simp

/-- The chain complex `X ←0- X ←𝟙- X ←0- X ←𝟙- X ⋯`.
It is exact away from `0` and has homology `X` at `0`. -/
@[simps]
def ChainComplex.alternatingConst : C ⥤ ChainComplex C ℕ where
  obj X :=
  { X _ := X
    d i j := if Even i ∧ j + 1 = i then 𝟙 X else 0
    shape := by simp +contextual
    d_comp_d' := by
      simp only [ComplexShape.down_Rel]
      rintro _ _ i rfl rfl
      by_cases h : Even i <;> simp [Nat.even_add_one, ← Nat.not_even_iff_odd, h] }
  map {X Y} f := { f _ := f }
  map_id X := by ext; simp
  map_comp f g := by ext; simp

variable [HasZeroObject C]

open ZeroObject

/-- The `n`-th homology of the alternating constant complex is zero for non-zero even `n`. -/
noncomputable
def ChainComplex.alternatingConstHomologyDataEvenNEZero (X : C) (n : ℕ) (hn : Even n) (h₀ : n ≠ 0) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofIsLimitKernelFork _ (by simp [Nat.even_add_one, hn]) _ (Limits.zeroKernelOfCancelZero _ (by
    simp [hn, tsub_add_cancel_iff_le, Nat.one_le_iff_ne_zero, h₀]))

/-- The `n`-th homology of the alternating constant complex is zero for odd `n`. -/
noncomputable
def ChainComplex.alternatingConstHomologyDataOdd (X : C) (n : ℕ) (hn : Odd n) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofIsColimitCokernelCofork _ (by simp [hn]) _ (Limits.zeroCokernelOfZeroCancel _ (by simp [hn]))

/-- The `n`-th homology of the alternating constant complex is `X` for `n = 0`. -/
noncomputable
def ChainComplex.alternatingConstHomologyDataZero (X : C) (n : ℕ) (hn : n = 0) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofZeros _ (by simp [hn]) (by simp [hn])

instance (X : C) (n : ℕ) : (ChainComplex.alternatingConst.obj X).HasHomology n := by
  cases' n.even_or_odd with h h
  · cases' n with n
    · exact ⟨⟨ChainComplex.alternatingConstHomologyDataZero X _ rfl⟩⟩
    · exact ⟨⟨ChainComplex.alternatingConstHomologyDataEvenNEZero X _ h (by simp)⟩⟩
  · exact ⟨⟨ChainComplex.alternatingConstHomologyDataOdd X _ h⟩⟩

lemma ChainComplex.isZero_alternatingConst_homology (X : C) (n : ℕ) (hn : n ≠ 0) :
    Limits.IsZero ((alternatingConst.obj X).homology n) := by
  cases' n.even_or_odd with h h
  · exact (Limits.isZero_zero C).of_iso
      (ChainComplex.alternatingConstHomologyDataEvenNEZero X _ h hn).left.homologyIso
  · exact (Limits.isZero_zero C).of_iso
      (ChainComplex.alternatingConstHomologyDataOdd X _ h).left.homologyIso

/-- The `n`-th homology of the alternating constant complex is `X` for `n = 0`. -/
noncomputable
def ChainComplex.alternatingConstHomologyZero
    {C : Type*} [Category C] [Limits.HasZeroMorphisms C] [Limits.HasZeroObject C]
    (X : C) : (alternatingConst.obj X).homology 0 ≅ X :=
  (ChainComplex.alternatingConstHomologyDataZero X _ rfl).left.homologyIso
