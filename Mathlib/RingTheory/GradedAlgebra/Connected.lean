/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Connected graded algebras

A graded algebra is *connected* if its degree-zero part is the `R`-span of the unit `1`.
Over a field this says `𝒜 0` is one-dimensional; for a graded bialgebra it is equivalent to the
counit restricting to an isomorphism `𝒜 0 ≃ R`.

## Main definitions

* `GradedAlgebra.IsConnected 𝒜`: the degree-zero part of the grading `𝒜` is spanned by `1`.

## References

* [Grinberg, D. and Reiner, V., *Hopf Algebras in Combinatorics*][grinberg-reiner-2020],
  Definition 1.3.15 and Exercise 1.3.20.
-/

public section

/-- A graded algebra is *connected* if its degree-zero part is spanned by the unit element
`1 : A`. Over a field this is the statement that `𝒜 0` is one-dimensional. -/
class GradedAlgebra.IsConnected {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {ι : Type*} [Zero ι] (𝒜 : ι → Submodule R A) : Prop where
  /-- The degree-zero part is the `R`-span of `1`. -/
  eq_span_one : 𝒜 0 = Submodule.span R {(1 : A)}

/-- An element of `A` lies in the degree-zero part of a connected grading iff it is an
`R`-multiple of `1`. -/
theorem GradedAlgebra.IsConnected.mem_zero_iff {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] {ι : Type*} [Zero ι] (𝒜 : ι → Submodule R A) [GradedAlgebra.IsConnected 𝒜]
    {a : A} : a ∈ 𝒜 0 ↔ ∃ r : R, r • (1 : A) = a := by
  rw [eq_span_one (𝒜 := 𝒜), Submodule.mem_span_singleton]
