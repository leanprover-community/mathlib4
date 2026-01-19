/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Euler characteristic of homological complexes

The Euler characteristic is defined using the `ComplexShape.EulerCharSigns` typeclass,
which provides the alternating signs for each index. This allows the definition to work
uniformly for chain complexes, cochain complexes, and complexes with other index types.

The definitions work on graded objects, with the homological complex versions
defined as abbreviations that apply the graded object versions to `C.X` and `C.homology`.

## Main definitions

* `ComplexShape.EulerCharSigns`: Typeclass providing alternating signs for Euler characteristic
* `GradedObject.eulerChar`: The Euler characteristic of a graded object over a finite set
* `GradedObject.finrankSupport`: The support of a graded object (indices with nonzero rank)
* `GradedObject.eulerCharTsum`: The Euler characteristic of a graded object as an infinite sum
* `HomologicalComplex.eulerChar`: The Euler characteristic over a finite set of indices
* `HomologicalComplex.eulerCharTsum`: The Euler characteristic as an infinite sum
* `HomologicalComplex.homologyEulerChar`: The homological Euler characteristic over a
  finite set
* `HomologicalComplex.homologyEulerCharTsum`: The homological Euler characteristic as an
  infinite sum

## Main results

* `GradedObject.eulerCharTsum_eq_eulerChar`: The infinite sum equals the finite sum
  when the graded object vanishes outside the finite set
* `HomologicalComplex.eulerCharTsum_eq_eulerChar`: The infinite sum equals the finite sum
  when the complex vanishes outside the finite set
* `HomologicalComplex.homologyEulerCharTsum_eq_homologyEulerChar`: The infinite homological
  Euler characteristic equals the finite one when homology vanishes outside the finite set

-/

@[expose] public section

namespace ComplexShape

variable {ι : Type*} (c : ComplexShape ι)

/-- Signs for terms of Euler characteristic on complexes. -/
class EulerCharSigns where
  /-- The sign for each index -/
  χ : ι → ℤˣ
  /-- Signs alternate along relations in the complex shape -/
  χ_next {i j : ι} (h : c.Rel i j) : χ j = - χ i

variable [c.EulerCharSigns]

/-- The sign at index `i` for Euler characteristic computations. -/
abbrev χ : ι → ℤˣ := EulerCharSigns.χ c

/-- Signs alternate in the forward direction of the complex shape. -/
lemma χ_next {i j : ι} (h : c.Rel i j) : c.χ j = - c.χ i := EulerCharSigns.χ_next h

/-- Signs alternate in the backward direction of the complex shape. -/
lemma χ_prev {i j : ι} (h : c.Rel i j) : c.χ i = - c.χ j := by simp [c.χ_next h]

@[simps]
instance eulerCharSignsUpInt : (up ℤ).EulerCharSigns where
  χ := Int.negOnePow
  χ_next := by rintro _ _ rfl; rw [Int.negOnePow_succ]

@[simps]
instance eulerCharSignsDownInt : (down ℤ).EulerCharSigns where
  χ := Int.negOnePow
  χ_next := by rintro _ _ rfl; simp [Int.negOnePow_succ]

@[simps]
instance eulerCharSignsUpNat : (up ℕ).EulerCharSigns where
  χ n := (-1) ^ n
  χ_next := by rintro _ _ rfl; simp [pow_add]

@[simps]
instance eulerCharSignsDownNat : (down ℕ).EulerCharSigns where
  χ n := (-1) ^ n
  χ_next := by rintro _ _ rfl; simp [pow_add]

end ComplexShape

open ComplexShape CategoryTheory

variable {R : Type*} [Ring R] {ι : Type*}

namespace GradedObject

variable (c : ComplexShape ι) [c.EulerCharSigns]

/-- The Euler characteristic of a graded object over a finite set of indices.
The sign at each index is determined by the `ComplexShape.EulerCharSigns` instance. -/
noncomputable def eulerChar (X : CategoryTheory.GradedObject ι (ModuleCat R))
    (indices : Finset ι) : ℤ :=
  ∑ i ∈ indices, (c.χ i : ℤ) * Module.finrank R (X i)

/-- The support of a graded object with respect to finite rank:
the set of indices where the rank is nonzero. -/
def finrankSupport (X : CategoryTheory.GradedObject ι (ModuleCat R)) : Set ι :=
  Function.support (fun i => Module.finrank R (X i))

/-- The finite rank support is contained in a set if and only if
the rank vanishes outside that set. -/
lemma finrankSupport_subset_iff (X : CategoryTheory.GradedObject ι (ModuleCat R)) (s : Set ι) :
    finrankSupport X ⊆ s ↔ ∀ i ∉ s, Module.finrank R (X i) = 0 :=
  Function.support_subset_iff'

/-- The Euler characteristic as a sum over all indices. Defaults to 0 if the support of the ranks of the objects of `X` is
infinite. -/
noncomputable def eulerCharTsum (X : CategoryTheory.GradedObject ι (ModuleCat R)) : ℤ :=
  ∑ᶠ i : ι, (c.χ i : ℤ) * Module.finrank R (X i)

/-- If a graded object has finite rank support contained in a finite set,
the infinite Euler characteristic equals the finite one. -/
theorem eulerCharTsum_eq_eulerChar (X : CategoryTheory.GradedObject ι (ModuleCat R))
    (indices : Finset ι)
    (h_support : finrankSupport X ⊆ indices) :
    eulerCharTsum c X = eulerChar c X indices := by
  simp only [eulerCharTsum, eulerChar]
  symm
  apply Finset.sum_subset (Finset.subset_univ indices)
  intro i _ hi
  simp [(finrankSupport_subset_iff X indices).mp h_support i hi]

end GradedObject

namespace HomologicalComplex

variable {c : ComplexShape ι} [c.EulerCharSigns]

/-- The Euler characteristic of a homological complex over a finite set of indices.
The sign at each index is determined by the `ComplexShape.EulerCharSigns` instance. -/
noncomputable abbrev eulerChar (C : HomologicalComplex (ModuleCat R) c)
    (indices : Finset ι) : ℤ :=
  GradedObject.eulerChar c C.X indices

/-- The homological Euler characteristic over a finite set of indices.
This is the Euler characteristic computed from the homology groups rather than
the original complex. -/
noncomputable abbrev homologyEulerChar (C : HomologicalComplex (ModuleCat R) c)
    [∀ i : ι, C.HasHomology i] (indices : Finset ι) : ℤ :=
  GradedObject.eulerChar c (fun i => C.homology i) indices

variable [Fintype ι]

/-- The Euler characteristic as an infinite sum over all indices.
This requires the index type to be finite. -/
noncomputable abbrev eulerCharTsum (C : HomologicalComplex (ModuleCat R) c) : ℤ :=
  GradedObject.eulerCharTsum c C.X

/-- The homological Euler characteristic as an infinite sum. -/
noncomputable abbrev homologyEulerCharTsum (C : HomologicalComplex (ModuleCat R) c)
    [∀ i : ι, C.HasHomology i] : ℤ :=
  GradedObject.eulerCharTsum c (fun i => C.homology i)

/-- If a complex has finite rank support contained in a finite set,
the infinite Euler characteristic equals the finite one. -/
theorem eulerCharTsum_eq_eulerChar (C : HomologicalComplex (ModuleCat R) c)
    (indices : Finset ι)
    (h_support : GradedObject.finrankSupport (C.X) ⊆ indices) :
    eulerCharTsum C = eulerChar C indices :=
  GradedObject.eulerCharTsum_eq_eulerChar c C.X indices h_support

/-- If homology has finite rank support contained in a finite set,
the infinite homological Euler characteristic equals the finite one. -/
theorem homologyEulerCharTsum_eq_homologyEulerChar (C : HomologicalComplex (ModuleCat R) c)
    [∀ i : ι, C.HasHomology i] (indices : Finset ι)
    (h_support : GradedObject.finrankSupport (fun i => C.homology i) ⊆ indices) :
    homologyEulerCharTsum C = homologyEulerChar C indices :=
  GradedObject.eulerCharTsum_eq_eulerChar c (fun i => C.homology i) indices h_support

end HomologicalComplex
