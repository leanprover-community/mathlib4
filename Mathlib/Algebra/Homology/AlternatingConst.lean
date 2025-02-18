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

namespace ChainComplex

/-- The chain complex `X ←0- X ←𝟙- X ←0- X ←𝟙- X ⋯`.
It is exact away from `0` and has homology `X` at `0`. -/
@[simps]
def alternatingConst : C ⥤ ChainComplex C ℕ where
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
def alternatingConstHomologyDataEvenNEZero (X : C) (n : ℕ) (hn : Even n) (h₀ : n ≠ 0) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofIsLimitKernelFork _ (by simp [Nat.even_add_one, hn]) _
    (Limits.zeroKernelOfCancelZero _ (by cases n <;> simp_all))

/-- The `n`-th homology of the alternating constant complex is zero for odd `n`. -/
noncomputable
def alternatingConstHomologyDataOdd (X : C) (n : ℕ) (hn : Odd n) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofIsColimitCokernelCofork _ (by simp [hn]) _ (Limits.zeroCokernelOfZeroCancel _ (by simp [hn]))

/-- The `n`-th homology of the alternating constant complex is `X` for `n = 0`. -/
noncomputable
def alternatingConstHomologyDataZero (X : C) (n : ℕ) (hn : n = 0) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofZeros _ (by simp [hn]) (by simp [hn])

instance (X : C) (n : ℕ) : (alternatingConst.obj X).HasHomology n := by
  rcases n.even_or_odd with h | h
  · rcases n with - | n
    · exact ⟨⟨alternatingConstHomologyDataZero X _ rfl⟩⟩
    · exact ⟨⟨alternatingConstHomologyDataEvenNEZero X _ h (by simp)⟩⟩
  · exact ⟨⟨alternatingConstHomologyDataOdd X _ h⟩⟩

/-- The `n`-th homology of the alternating constant complex is `X` for `n ≠ 0`. -/
lemma alternatingConst_exactAt (X : C) (n : ℕ) (hn : n ≠ 0) :
    (alternatingConst.obj X).ExactAt n := by
  rcases n.even_or_odd with h | h
  · exact ⟨(alternatingConstHomologyDataEvenNEZero X _ h hn), isZero_zero C⟩
  · exact ⟨(alternatingConstHomologyDataOdd X _ h), isZero_zero C⟩

/-- The `n`-th homology of the alternating constant complex is `X` for `n = 0`. -/
noncomputable
def alternatingConstHomologyZero (X : C) : (alternatingConst.obj X).homology 0 ≅ X :=
  (alternatingConstHomologyDataZero X _ rfl).left.homologyIso

end ChainComplex
