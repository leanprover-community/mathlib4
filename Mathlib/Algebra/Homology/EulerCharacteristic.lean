/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Euler characteristic of homological complexes

This file defines the Euler characteristic of a homological complex.

The Euler characteristic is defined using the `ComplexShape.EulerCharSigns` typeclass,
which provides the alternating signs for each index. This allows the definition to work
uniformly for chain complexes, cochain complexes, and complexes with other index types.

## Main definitions

* `ComplexShape.EulerCharSigns`: Typeclass providing alternating signs for Euler characteristic
* `HomologicalComplex.eulerChar`: The Euler characteristic over a finite set of indices
* `HomologicalComplex.eulerCharTsum`: The Euler characteristic as an infinite sum
* `HomologicalComplex.homologyEulerChar`: The homological Euler characteristic over a
  finite set
* `HomologicalComplex.homologyEulerCharTsum`: The homological Euler characteristic as an
  infinite sum

## Main results

* `HomologicalComplex.eulerCharTsum_eq_eulerChar`: The infinite sum equals the finite sum
  when the complex vanishes outside the finite set

## Implementation notes

The sign at index `i` is given by `c.χ i` where `c : ComplexShape ι` has an instance of
`c.EulerCharSigns`. This provides a uniform treatment of both homological (down) and
cohomological (up) indexing conventions.

-/

namespace ComplexShape

variable {ι : Type*} (c : ComplexShape ι)

/-- Signs for Euler characteristic computations on complexes.
This typeclass provides the alternating signs that appear in the definition
of the Euler characteristic of a homological complex. -/
class EulerCharSigns where
  /-- The sign for each index -/
  χ : ι → ℤˣ
  /-- Signs alternate along relations in the complex shape -/
  χ_next {i j : ι} (h : c.Rel i j) : χ j = - χ i

variable [c.EulerCharSigns]

/-- The sign at index `i` for Euler characteristic computations. -/
abbrev χ : ι → ℤˣ := EulerCharSigns.χ c

lemma χ_next {i j : ι} (h : c.Rel i j) : c.χ j = - c.χ i := EulerCharSigns.χ_next h

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

open ComplexShape

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}

namespace HomologicalComplex

section FiniteSum

/-- The Euler characteristic of a homological complex over a finite set of indices.
The sign at each index is determined by the `ComplexShape.EulerCharSigns` instance. -/
noncomputable def eulerChar [c.EulerCharSigns] (C : HomologicalComplex (ModuleCat R) c)
    (indices : Finset ι) : ℤ :=
  ∑ i ∈ indices, (c.χ i : ℤ) * Module.finrank R (C.X i)

/-- The homological Euler characteristic over a finite set of indices.
This is the Euler characteristic computed from the homology groups rather than
the original complex. -/
noncomputable def homologyEulerChar [c.EulerCharSigns]
    (C : HomologicalComplex (ModuleCat R) c) [∀ i : ι, C.HasHomology i]
    (indices : Finset ι) : ℤ :=
  ∑ i ∈ indices, (c.χ i : ℤ) * Module.finrank R (C.homology i)

end FiniteSum

section InfiniteSum

variable [Fintype ι]

/-- The Euler characteristic as an infinite sum over all indices.
This requires the index type to be finite. -/
noncomputable def eulerCharTsum [c.EulerCharSigns]
    (C : HomologicalComplex (ModuleCat R) c) : ℤ :=
  ∑ i : ι, (c.χ i : ℤ) * Module.finrank R (C.X i)

/-- The homological Euler characteristic as an infinite sum. -/
noncomputable def homologyEulerCharTsum [c.EulerCharSigns]
    (C : HomologicalComplex (ModuleCat R) c) [∀ i : ι, C.HasHomology i] : ℤ :=
  ∑ i : ι, (c.χ i : ℤ) * Module.finrank R (C.homology i)

/-- If a complex vanishes outside a finite set, the infinite Euler characteristic
equals the finite one. -/
theorem eulerCharTsum_eq_eulerChar [c.EulerCharSigns]
    (C : HomologicalComplex (ModuleCat R) c)
    (indices : Finset ι)
    (h_zero : ∀ i ∉ indices, Module.finrank R (C.X i) = 0) :
    eulerCharTsum C = eulerChar C indices := by
  simp only [eulerCharTsum, eulerChar]
  symm
  apply Finset.sum_subset (Finset.subset_univ indices)
  intro i _ hi
  simp [h_zero i hi]

/-- If homology vanishes outside a finite set, the infinite homological Euler
characteristic equals the finite one. -/
theorem homologyEulerCharTsum_eq_homologyEulerChar [c.EulerCharSigns]
    (C : HomologicalComplex (ModuleCat R) c) [∀ i : ι, C.HasHomology i]
    (indices : Finset ι)
    (h_zero : ∀ i ∉ indices, Module.finrank R (C.homology i) = 0) :
    homologyEulerCharTsum C = homologyEulerChar C indices := by
  simp only [homologyEulerCharTsum, homologyEulerChar]
  symm
  apply Finset.sum_subset (Finset.subset_univ indices)
  intro i _ hi
  simp [h_zero i hi]

end InfiniteSum

end HomologicalComplex

-- Chain complex specializations for Euler-Poincaré formula

namespace ChainComplex

variable {R : Type*} [Ring R]

/-- The bounded Euler characteristic of a chain complex over a finite set.
For chain complexes, we use the formula with `(-1)^i.natAbs` directly. -/
noncomputable def boundedEulerChar (C : ChainComplex (ModuleCat R) ℤ)
    (indices : Finset ℤ) : ℤ :=
  ∑ i ∈ indices, (-1 : ℤ) ^ i.natAbs * Module.finrank R (C.X i)

/-- The bounded homological Euler characteristic for chain complexes. -/
noncomputable def homologyBoundedEulerChar (C : ChainComplex (ModuleCat R) ℤ)
    [∀ i : ℤ, C.HasHomology i]
    (indices : Finset ℤ) : ℤ :=
  ∑ i ∈ indices, (-1 : ℤ) ^ i.natAbs * Module.finrank R (C.homology i)

end ChainComplex
