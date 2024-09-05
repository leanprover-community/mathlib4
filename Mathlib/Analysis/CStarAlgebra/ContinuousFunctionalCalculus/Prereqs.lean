import Mathlib.Algebra.Star.NonUnitalSubalgebra
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Star

namespace NonUnitalSubalgebra

variable {R A B : Type*} [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [TopologicalSemiring A]
variable [NonUnitalNonAssocSemiring B] [TopologicalSpace B] [TopologicalSemiring B]
variable [Module R A] [Module R B] [ContinuousConstSMul R A] [ContinuousConstSMul R B]
variable (s : NonUnitalSubalgebra R A)

-- TODO: once we have topological closures of more elementary structures, relate this to them
/-- The closure of a non-unital subalgebra in a non-unital topological algebra as a non-unital
subalgebra. -/
def topologicalClosure (s : NonUnitalSubalgebra R A) : NonUnitalSubalgebra R A where
  carrier := closure (s : Set A)
  smul_mem' r a ha := map_mem_closure (continuous_const_smul r) ha fun _ ↦ s.smul_mem' r
  zero_mem' := subset_closure <| zero_mem s
  add_mem' := (map_mem_closure₂ continuous_add · · fun _ _ _ _ ↦ by aesop)
  mul_mem' := (map_mem_closure₂ continuous_mul · · fun _ _ _ _ ↦ by aesop)

@[simp]
lemma topologicalClosure_coe : (s.topologicalClosure : Set A) = closure (s : Set A) := rfl

lemma le_topologicalClosure : s ≤ s.topologicalClosure := subset_closure

lemma isClosed_topologicalClosure : IsClosed (s.topologicalClosure : Set A) := isClosed_closure

instance {A : Type*} [UniformSpace A] [CompleteSpace A] [NonUnitalNonAssocSemiring A]
    [TopologicalSemiring A] [Module R A] [ContinuousConstSMul R A]
    {S : NonUnitalSubalgebra R A} : CompleteSpace S.topologicalClosure :=
  isClosed_closure.completeSpace_coe

lemma topologicalClosure_minimal {s t : NonUnitalSubalgebra R A} (h : s ≤ t)
    (ht : IsClosed (t : Set A)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

lemma topologicalClosure_mono : Monotone (topologicalClosure : _ → NonUnitalSubalgebra R A) :=
  fun _ S₂ h => topologicalClosure_minimal (h.trans <| le_topologicalClosure S₂)
    (isClosed_topologicalClosure S₂)

lemma topologicalClosure_map_le (φ : A →ₙₐ[R] B) (hφ : IsClosedMap φ) :
    (map φ s).topologicalClosure ≤ map φ s.topologicalClosure :=
  hφ.closure_image_subset _

lemma map_topologicalClosure_le (φ : A →ₙₐ[R] B) (hφ : Continuous φ) :
    map φ s.topologicalClosure ≤ (map φ s).topologicalClosure :=
  image_closure_subset_closure_image hφ

lemma topologicalClosure_map (φ : A →ₙₐ[R] B) (hφ : ClosedEmbedding φ) :
    (map φ s).topologicalClosure = map φ s.topologicalClosure :=
  SetLike.coe_injective <| hφ.closure_image_eq _

end NonUnitalSubalgebra

namespace NonUnitalStarSubalgebra

variable {R A B : Type*} [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [TopologicalSemiring A]
variable [NonUnitalNonAssocSemiring B] [TopologicalSpace B] [TopologicalSemiring B]
variable [Module R A] [Module R B] [ContinuousConstSMul R A] [ContinuousConstSMul R B]
variable [Star A] [Star B] [ContinuousStar A] [ContinuousStar B]
variable (s : NonUnitalStarSubalgebra R A)

/-- The closure of a non-unital star subalgebra in a non-unital topological star algebra as a
non-unital star subalgebra. -/
def topologicalClosure : NonUnitalStarSubalgebra R A :=
  { s.toNonUnitalSubalgebra.topologicalClosure with
    carrier := closure (s : Set A)
    star_mem' := (map_mem_closure continuous_star · fun _ ↦ star_mem) }

lemma topologicalClosure_toNonUnitalSubalgebra_comm :
    s.topologicalClosure.toNonUnitalSubalgebra = s.toNonUnitalSubalgebra.topologicalClosure :=
  SetLike.coe_injective rfl

@[simp]
lemma topologicalClosure_coe : (s.topologicalClosure : Set A) = closure (s : Set A) := rfl

lemma le_topologicalClosure : s ≤ s.topologicalClosure := subset_closure

lemma isClosed_topologicalClosure : IsClosed (s.topologicalClosure : Set A) := isClosed_closure

instance {A : Type*} [UniformSpace A] [CompleteSpace A] [NonUnitalNonAssocSemiring A]
    [TopologicalSemiring A] [Star A] [ContinuousStar A] [Module R A] [ContinuousConstSMul R A]
    {s : NonUnitalStarSubalgebra R A} : CompleteSpace s.topologicalClosure :=
  isClosed_closure.completeSpace_coe

lemma topologicalClosure_minimal {s t : NonUnitalStarSubalgebra R A} (h : s ≤ t)
    (ht : IsClosed (t : Set A)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

lemma topologicalClosure_mono : Monotone (topologicalClosure : _ → NonUnitalStarSubalgebra R A) :=
  fun _ S₂ h => topologicalClosure_minimal (h.trans <| le_topologicalClosure S₂)
    (isClosed_topologicalClosure S₂)

lemma topologicalClosure_map_le (φ : A →⋆ₙₐ[R] B) (hφ : IsClosedMap φ) :
    (map φ s).topologicalClosure ≤ map φ s.topologicalClosure :=
  hφ.closure_image_subset _

lemma map_topologicalClosure_le (φ : A →⋆ₙₐ[R] B) (hφ : Continuous φ) :
    map φ s.topologicalClosure ≤ (map φ s).topologicalClosure :=
  image_closure_subset_closure_image hφ

lemma topologicalClosure_map (φ : A →⋆ₙₐ[R] B) (hφ : ClosedEmbedding φ) :
    (map φ s).topologicalClosure = map φ s.topologicalClosure :=
  SetLike.coe_injective <| hφ.closure_image_eq _

end NonUnitalStarSubalgebra
