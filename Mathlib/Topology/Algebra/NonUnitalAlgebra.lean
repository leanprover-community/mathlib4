/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Non-unital topological (sub)algebras

A non-unital topological algebra over a topological semiring `R` is a topological (non-unital)
semiring with a compatible continuous scalar multiplication by elements of `R`. We reuse
typeclass `ContinuousSMul` to express the latter condition.

## Results

Any non-unital subalgebra of a non-unital topological algebra is itself a non-unital
topological algebra, and its closure is again a non-unital subalgebra.

-/

namespace NonUnitalSubalgebra

section Semiring

variable {R A : Type*} [CommSemiring R] [TopologicalSpace A]
variable [NonUnitalSemiring A] [Module R A] [TopologicalSemiring A]
variable [ContinuousConstSMul R A]

instance instTopologicalSemiring (s : NonUnitalSubalgebra R A) : TopologicalSemiring s :=
  s.toNonUnitalSubsemiring.instTopologicalSemiring

/-- The (topological) closure of a non-unital subalgebra of a non-unital topological algebra is
itself a non-unital subalgebra. -/
def topologicalClosure (s : NonUnitalSubalgebra R A) : NonUnitalSubalgebra R A :=
  { s.toNonUnitalSubsemiring.topologicalClosure, s.toSubmodule.topologicalClosure with
    carrier := _root_.closure (s : Set A) }

theorem le_topologicalClosure (s : NonUnitalSubalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure

theorem isClosed_topologicalClosure (s : NonUnitalSubalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) := isClosed_closure

theorem topologicalClosure_minimal (s : NonUnitalSubalgebra R A) {t : NonUnitalSubalgebra R A}
    (h : s ≤ t) (ht : IsClosed (t : Set A)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

/-- If a non-unital subalgebra of a non-unital topological algebra is commutative, then so is its
topological closure.

See note [reducible non-instances]. -/
abbrev nonUnitalCommSemiringTopologicalClosure [T2Space A] (s : NonUnitalSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommSemiring s.topologicalClosure :=
  s.toNonUnitalSubsemiring.nonUnitalCommSemiringTopologicalClosure hs

end Semiring

section Ring

variable {R A : Type*} [CommRing R] [TopologicalSpace A]
variable [NonUnitalRing A] [Module R A] [TopologicalRing A]
variable [ContinuousConstSMul R A]

instance instTopologicalRing (s : NonUnitalSubalgebra R A) : TopologicalRing s :=
  s.toNonUnitalSubring.instTopologicalRing

/-- If a non-unital subalgebra of a non-unital topological algebra is commutative, then so is its
topological closure.

See note [reducible non-instances]. -/
abbrev nonUnitalCommRingTopologicalClosure [T2Space A] (s : NonUnitalSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalClosure :=
  { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end Ring

end NonUnitalSubalgebra
