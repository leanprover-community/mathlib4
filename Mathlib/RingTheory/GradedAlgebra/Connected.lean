/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Connected graded algebras

A graded algebra is *connected* if the unit map identifies the base ring `R` with the
degree-zero part `𝒜 0`. Over a field this says `𝒜 0` is one-dimensional.

## Main definitions

* `GradedAlgebra.IsConnected 𝒜`: the degree-zero part of the grading `𝒜` is the canonical
  copy of `R`, and `algebraMap R A` is injective.

## References

* [Grinberg, D. and Reiner, V., *Hopf Algebras in Combinatorics*][GrinbergReiner2020],
  Definition 1.3.15 and Exercise 1.3.20.
-/

public section

namespace GradedAlgebra

variable {ι R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Zero ι]
  (𝒜 : ι → Submodule R A)

/-- A graded algebra is *connected* if the unit map identifies `R` with the degree-zero part. -/
class IsConnected : Prop where
  /-- The degree-zero part is the canonical copy of `R`. -/
  eq_one : 𝒜 0 = 1
  /-- The unit map is injective. -/
  algebraMap_injective : Function.Injective (algebraMap R A)

/-- An element of `A` lies in the degree-zero part of a connected grading iff it is an
`R`-multiple of `1`. -/
theorem IsConnected.mem_zero_iff [IsConnected 𝒜] {a : A} :
    a ∈ 𝒜 0 ↔ ∃ r : R, r • 1 = a := by
  rw [eq_one (𝒜 := 𝒜), Submodule.one_eq_span, Submodule.mem_span_singleton]

end GradedAlgebra
