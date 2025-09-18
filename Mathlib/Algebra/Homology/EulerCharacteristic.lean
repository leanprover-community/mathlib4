/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Euler characteristic of chain complexes

This file defines the Euler characteristic of a chain complex indexed by ℤ.

## Main definitions

* `ChainComplex.boundedEulerChar`: The Euler characteristic over a finite set
* `ChainComplex.eulerChar`: The Euler characteristic as an infinite sum
* `ChainComplex.homologyBoundedEulerChar`: The homological Euler characteristic over a finite set
* `ChainComplex.homologyEulerChar`: The homological Euler characteristic as an infinite sum

## Main results

* `ChainComplex.eulerChar_eq_boundedEulerChar`: The infinite sum equals the finite sum when the
  complex vanishes outside the finite set

## Implementation notes

Chain complexes are indexed by ℤ and use a reference point to determine the sign pattern,
allowing flexibility in choosing where the alternating signs start. The sign at index `i`
relative to reference point `ref` is `(-1)^(i - ref).natAbs`.

-/

namespace ChainComplex

variable {R : Type*} [Ring R]

section BoundedSums

/-- The bounded Euler characteristic of a chain complex over a finite set. -/
noncomputable def boundedEulerChar (C : ChainComplex (ModuleCat R) ℤ)
    (indices : Finset ℤ) (ref : ℤ) : ℤ :=
  indices.sum (fun i => (-1 : ℤ) ^ (i - ref).natAbs * Module.finrank R (C.X i))

/-- The bounded homological Euler characteristic for chain complexes. -/
noncomputable def homologyBoundedEulerChar (C : ChainComplex (ModuleCat R) ℤ)
    [∀ i : ℤ, (C.sc i).HasHomology]
    (indices : Finset ℤ) (ref : ℤ) : ℤ :=
  indices.sum (fun i => (-1 : ℤ) ^ (i - ref).natAbs * Module.finrank R (C.homology i))

end BoundedSums

section InfiniteSums

/-- The Euler characteristic as an infinite sum.
The reference point determines where the sign pattern starts. -/
noncomputable def eulerChar (C : ChainComplex (ModuleCat R) ℤ) (ref : ℤ) : ℤ :=
  ∑' i : ℤ, (-1 : ℤ) ^ (i - ref).natAbs * Module.finrank R (C.X i)

/-- The homological Euler characteristic as an infinite sum. -/
noncomputable def homologyEulerChar (C : ChainComplex (ModuleCat R) ℤ)
    [∀ i : ℤ, (C.sc i).HasHomology] (ref : ℤ) : ℤ :=
  ∑' i : ℤ, (-1 : ℤ) ^ (i - ref).natAbs * Module.finrank R (C.homology i)

/-- If a chain complex vanishes outside a finite set, the infinite Euler
characteristic equals the bounded one. -/
theorem eulerChar_eq_boundedEulerChar (C : ChainComplex (ModuleCat R) ℤ)
    (indices : Finset ℤ) (ref : ℤ)
    (h_zero : ∀ i ∉ indices, Module.finrank R (C.X i) = 0) :
    eulerChar C ref = boundedEulerChar C indices ref := by
  simp only [eulerChar, boundedEulerChar]
  have h_support : ∀ i ∉ indices, (-1 : ℤ) ^ (i - ref).natAbs * Module.finrank R (C.X i) = 0 := by
    intro i hi
    simp [h_zero i hi]
  rw [tsum_eq_sum h_support]

end InfiniteSums

end ChainComplex
