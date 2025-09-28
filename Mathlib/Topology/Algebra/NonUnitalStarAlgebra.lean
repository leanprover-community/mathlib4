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

variable {R A B : Type*} [CommSemiring R] [TopologicalSpace A] [Star A]
variable [NonUnitalSemiring A] [Module R A] [IsTopologicalSemiring A] [ContinuousStar A]
variable [ContinuousConstSMul R A]

instance instIsTopologicalSemiring (s : NonUnitalStarSubalgebra R A) : IsTopologicalSemiring s :=
  s.toNonUnitalSubalgebra.instIsTopologicalSemiring

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
so is its topological closure.

See note [reducible non-instances] -/
abbrev nonUnitalCommSemiringTopologicalClosure [T2Space A] (s : NonUnitalStarSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommSemiring s.topologicalClosure :=
  s.toNonUnitalSubalgebra.nonUnitalCommSemiringTopologicalClosure hs

variable [TopologicalSpace B] [Star B] [NonUnitalSemiring B] [Module R B]
    [IsTopologicalSemiring B] [ContinuousConstSMul R B] [ContinuousStar B]
    (s : NonUnitalStarSubalgebra R A) {φ : A →⋆ₙₐ[R] B}

lemma map_topologicalClosure_le (hφ : Continuous φ) :
    map φ s.topologicalClosure ≤ (map φ s).topologicalClosure :=
  image_closure_subset_closure_image hφ

lemma topologicalClosure_map_le (hφ : IsClosedMap φ) :
    (map φ s).topologicalClosure ≤ map φ s.topologicalClosure :=
  hφ.closure_image_subset _

lemma topologicalClosure_map (hφ : IsClosedMap φ) (hφ' : Continuous φ) :
    (map φ s).topologicalClosure = map φ s.topologicalClosure :=
  SetLike.coe_injective <| hφ.closure_image_eq_of_continuous hφ' _

open NonUnitalStarAlgebra in
-- we have to shadow the variables because some things currently require `StarRing`
lemma topologicalClosure_adjoin_le_centralizer_centralizer (R : Type*) {A : Type*}
    [CommSemiring R] [StarRing R] [TopologicalSpace A] [NonUnitalSemiring A] [StarRing A]
    [Module R A] [IsTopologicalSemiring A] [ContinuousStar A] [ContinuousConstSMul R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] [T2Space A] (s : Set A) :
    (adjoin R s).topologicalClosure ≤ centralizer R (centralizer R s) :=
  topologicalClosure_minimal _ (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

end Semiring

section Ring

variable {R A : Type*} [CommRing R] [TopologicalSpace A]
variable [NonUnitalRing A] [Module R A] [Star A] [IsTopologicalRing A] [ContinuousStar A]
variable [ContinuousConstSMul R A]

instance instIsTopologicalRing (s : NonUnitalStarSubalgebra R A) : IsTopologicalRing s :=
  s.toNonUnitalSubring.instIsTopologicalRing

/-- If a non-unital star subalgebra of a non-unital topological star algebra is commutative, then
so is its topological closure.

See note [reducible non-instances]. -/
abbrev nonUnitalCommRingTopologicalClosure [T2Space A] (s : NonUnitalStarSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalClosure :=
  { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end Ring

end NonUnitalStarSubalgebra

namespace NonUnitalStarAlgebra

open NonUnitalStarSubalgebra

variable (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [TopologicalSpace A] [IsTopologicalSemiring A] [ContinuousConstSMul R A] [ContinuousStar A]

/-- The topological closure of the non-unital star subalgebra generated by a single element. -/
def elemental (x : A) : NonUnitalStarSubalgebra R A :=
  adjoin R {x} |>.topologicalClosure

namespace elemental

@[simp, aesop safe (rule_sets := [SetLike])]
theorem self_mem (x : A) : x ∈ elemental R x :=
  le_topologicalClosure _ <| self_mem_adjoin_singleton R x

@[simp, aesop safe (rule_sets := [SetLike])]
theorem star_self_mem (x : A) : star x ∈ elemental R x :=
  le_topologicalClosure _ <| star_self_mem_adjoin_singleton R x

variable {R} in
theorem le_of_mem {x : A} {s : NonUnitalStarSubalgebra R A} (hs : IsClosed (s : Set A))
    (hx : x ∈ s) : elemental R x ≤ s :=
  topologicalClosure_minimal _ (adjoin_le <| by simpa using hx) hs

variable {R} in
theorem le_iff_mem {x : A} {s : NonUnitalStarSubalgebra R A} (hs : IsClosed (s : Set A)) :
    elemental R x ≤ s ↔ x ∈ s :=
  ⟨fun h ↦ h (self_mem R x), fun h ↦ le_of_mem hs h⟩

theorem isClosed (x : A) : IsClosed (elemental R x : Set A) :=
  isClosed_topologicalClosure _

instance [T2Space A] {x : A} [IsStarNormal x] : NonUnitalCommSemiring (elemental R x) :=
  nonUnitalCommSemiringTopologicalClosure _ <| by
    letI : NonUnitalCommSemiring (adjoin R {x}) := by
      refine NonUnitalStarAlgebra.adjoinNonUnitalCommSemiringOfComm R ?_ ?_
      all_goals
        intro y hy z hz
        rw [Set.mem_singleton_iff] at hy hz
        rw [hy, hz]
      exact (star_comm_self' x).symm
    exact fun _ _ => mul_comm _ _

instance {R A : Type*} [CommRing R] [StarRing R] [NonUnitalRing A] [StarRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
    [TopologicalSpace A] [IsTopologicalRing A] [ContinuousConstSMul R A] [ContinuousStar A]
    [T2Space A] {x : A} [IsStarNormal x] : NonUnitalCommRing (elemental R x) where
  mul_comm := mul_comm

instance {A : Type*} [UniformSpace A] [CompleteSpace A] [NonUnitalSemiring A] [StarRing A]
    [IsTopologicalSemiring A] [ContinuousStar A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [StarModule R A] [ContinuousConstSMul R A] (x : A) :
    CompleteSpace (elemental R x) :=
  isClosed_closure.completeSpace_coe

/-- The coercion from an elemental algebra to the full algebra is a `IsClosedEmbedding`. -/
theorem isClosedEmbedding_coe (x : A) : Topology.IsClosedEmbedding ((↑) : elemental R x → A) where
  eq_induced := rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x

lemma le_centralizer_centralizer [T2Space A] (x : A) :
    elemental R x ≤ centralizer R (centralizer R {x}) :=
  topologicalClosure_adjoin_le_centralizer_centralizer ..

end elemental

end NonUnitalStarAlgebra
