/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import Mathlib.Topology.Algebra.NonUnitalAlgebra
import Mathlib.Topology.Algebra.Star

/-!
# Non-unital topological star (sub)algebras

A non-unital topological star algebra over a topological semiring `R` is a topological 
(non-unital) semiring with a compatible continuous scalar multiplication by elements 
of `R` and a continuous `star` operation. We reuse typeclasses `ContinuousSMul` and 
`ContinuousStar` to express the latter two conditions.

## Results

Any non-unital star subalgebra of a non-unital topological star algebra is itself a 
non-unital topological star algebra, and its closure is again a non-unital star subalgebra.

-/

namespace NonUnitalStarSubalgebra

section Semiring

variable {R A : Type*} [CommSemiring R] [TopologicalSpace A] [Star A]
variable [NonUnitalSemiring A] [Module R A] [TopologicalSemiring A] [ContinuousStar A]
variable [ContinuousConstSMul R A]

instance instTopologicalSemiring (s : NonUnitalStarSubalgebra R A) : TopologicalSemiring s :=
  s.toNonUnitalSubalgebra.instTopologicalSemiring

/-- The (topological) closure of a non-unital star subalgebra of a non-unital topological star
algebra is itself a non-unital star subalgebra. -/
def topologicalClosure (s : NonUnitalStarSubalgebra R A) : NonUnitalStarSubalgebra R A :=
  { s.toNonUnitalSubalgebra.topologicalClosure with
    star_mem' := fun h ↦ map_mem_closure continuous_star h fun _ ↦ star_mem
    carrier := _root_.closure (s : Set A) }

theorem le_topologicalClosure (s : NonUnitalStarSubalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure

theorem isClosed_topologicalClosure (s : NonUnitalStarSubalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) := isClosed_closure

theorem topologicalClosure_minimal (s : NonUnitalStarSubalgebra R A)
    {t : NonUnitalStarSubalgebra R A} (h : s ≤ t) (ht : IsClosed (t : Set A)) :
    s.topologicalClosure ≤ t :=
  closure_minimal h ht

/-- If a non-unital star subalgebra of a non-unital topological star algebra is commutative, then
so is its topological closure. -/
abbrev nonUnitalCommSemiringTopologicalClosure [T2Space A] (s : NonUnitalStarSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommSemiring s.topologicalClosure :=
  s.toNonUnitalSubalgebra.nonUnitalCommSemiringTopologicalClosure hs

end Semiring

section Ring

variable {R A : Type*} [CommRing R] [TopologicalSpace A]
variable [NonUnitalRing A] [Module R A] [Star A] [TopologicalSemiring A] [ContinuousStar A]
variable [ContinuousConstSMul R A]

/-- If a non-unital star subalgebra of a non-unital topological star algebra is commutative, then
so is its topological closure.

See note [reducible non-instances]. -/
abbrev nonUnitalCommRingTopologicalClosure [T2Space A] (s : NonUnitalStarSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalClosure :=
  { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end Ring

end NonUnitalStarSubalgebra
