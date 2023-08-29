/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Star

#align_import topology.algebra.star_subalgebra from "leanprover-community/mathlib"@"b7f5a77fa29ad9a3ccc484109b0d7534178e7ecd"

/-!
# Topological star (sub)algebras

A topological star algebra over a topological semiring `R` is a topological semiring with a
compatible continuous scalar multiplication by elements of `R` and a continuous star operation.
We reuse typeclass `ContinuousSMul` for topological algebras.

## Results

This is just a minimal stub for now!

The topological closure of a star subalgebra is still a star subalgebra,
which as a star algebra is a topological star algebra.
-/


open Classical Set TopologicalSpace

open Classical

namespace StarSubalgebra

section TopologicalStarAlgebra

variable {R A B : Type*} [CommSemiring R] [StarRing R]

variable [TopologicalSpace A] [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

instance [TopologicalSpace R] [ContinuousSMul R A] (s : StarSubalgebra R A) : ContinuousSMul R s :=
  s.toSubalgebra.continuousSMul

instance [TopologicalSemiring A] (s : StarSubalgebra R A) : TopologicalSemiring s :=
  s.toSubalgebra.topologicalSemiring

/-- The `StarSubalgebra.inclusion` of a star subalgebra is an `Embedding`. -/
theorem embedding_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) : Embedding (inclusion h) :=
  { induced := Eq.symm induced_compose
    inj := Subtype.map_injective h Function.injective_id }
#align star_subalgebra.embedding_inclusion StarSubalgebra.embedding_inclusion

/-- The `StarSubalgebra.inclusion` of a closed star subalgebra is a `ClosedEmbedding`. -/
theorem closedEmbedding_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂)
    (hS₁ : IsClosed (S₁ : Set A)) : ClosedEmbedding (inclusion h) :=
  { embedding_inclusion h with
    closed_range := isClosed_induced_iff.2
      ⟨S₁, hS₁, by
          convert(Set.range_subtype_map id _).symm
          -- ⊢ ↑S₁ = id '' {x | x ∈ S₁}
          · rw [Set.image_id]; rfl
            -- ⊢ ↑S₁ = {x | x ∈ S₁}
                               -- 🎉 no goals
          · intro _ h'
            -- ⊢ id x✝ ∈ S₂
            apply h h' ⟩ }
            -- 🎉 no goals
#align star_subalgebra.closed_embedding_inclusion StarSubalgebra.closedEmbedding_inclusion

variable [TopologicalSemiring A] [ContinuousStar A]

variable [TopologicalSpace B] [Semiring B] [Algebra R B] [StarRing B]

/-- The closure of a star subalgebra in a topological star algebra as a star subalgebra. -/
def topologicalClosure (s : StarSubalgebra R A) : StarSubalgebra R A :=
  {
    s.toSubalgebra.topologicalClosure with
    carrier := closure (s : Set A)
    star_mem' := fun ha =>
      map_mem_closure continuous_star ha fun x => (star_mem : x ∈ s → star x ∈ s) }
#align star_subalgebra.topological_closure StarSubalgebra.topologicalClosure

theorem topologicalClosure_toSubalgebra_comm (s : StarSubalgebra R A) :
    s.topologicalClosure.toSubalgebra = s.toSubalgebra.topologicalClosure :=
  SetLike.coe_injective rfl

@[simp]
theorem topologicalClosure_coe (s : StarSubalgebra R A) :
    (s.topologicalClosure : Set A) = closure (s : Set A) :=
  rfl
#align star_subalgebra.topological_closure_coe StarSubalgebra.topologicalClosure_coe

theorem le_topologicalClosure (s : StarSubalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure
#align star_subalgebra.le_topological_closure StarSubalgebra.le_topologicalClosure

theorem isClosed_topologicalClosure (s : StarSubalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) :=
  isClosed_closure
#align star_subalgebra.is_closed_topological_closure StarSubalgebra.isClosed_topologicalClosure

instance {A : Type*} [UniformSpace A] [CompleteSpace A] [Semiring A] [StarRing A]
    [TopologicalSemiring A] [ContinuousStar A] [Algebra R A] [StarModule R A]
    {S : StarSubalgebra R A} : CompleteSpace S.topologicalClosure :=
  isClosed_closure.completeSpace_coe

theorem topologicalClosure_minimal {s t : StarSubalgebra R A} (h : s ≤ t)
    (ht : IsClosed (t : Set A)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align star_subalgebra.topological_closure_minimal StarSubalgebra.topologicalClosure_minimal

theorem topologicalClosure_mono : Monotone (topologicalClosure : _ → StarSubalgebra R A) :=
  fun _ S₂ h =>
  topologicalClosure_minimal (h.trans <| le_topologicalClosure S₂) (isClosed_topologicalClosure S₂)
#align star_subalgebra.topological_closure_mono StarSubalgebra.topologicalClosure_mono

theorem topologicalClosure_map_le [StarModule R B] [TopologicalSemiring B] [ContinuousStar B]
    (s : StarSubalgebra R A) (φ : A →⋆ₐ[R] B) (hφ : IsClosedMap φ) :
    (map φ s).topologicalClosure ≤ map φ s.topologicalClosure :=
  hφ.closure_image_subset _

theorem map_topologicalClosure_le [StarModule R B] [TopologicalSemiring B] [ContinuousStar B]
    (s : StarSubalgebra R A) (φ : A →⋆ₐ[R] B) (hφ : Continuous φ) :
    map φ s.topologicalClosure ≤ (map φ s).topologicalClosure :=
  image_closure_subset_closure_image hφ

theorem topologicalClosure_map [StarModule R B] [TopologicalSemiring B] [ContinuousStar B]
    (s : StarSubalgebra R A) (φ : A →⋆ₐ[R] B) (hφ : ClosedEmbedding φ) :
    (map φ s).topologicalClosure = map φ s.topologicalClosure :=
  SetLike.coe_injective <| hφ.closure_image_eq _

theorem _root_.Subalgebra.topologicalClosure_star_comm (s : Subalgebra R A) :
    (star s).topologicalClosure = star s.topologicalClosure := by
  suffices ∀ t : Subalgebra R A, (star t).topologicalClosure ≤ star t.topologicalClosure from
    le_antisymm (this s) (by simpa only [star_star] using Subalgebra.star_mono (this (star s)))
  exact fun t => (star t).topologicalClosure_minimal (Subalgebra.star_mono subset_closure)
    (isClosed_closure.preimage continuous_star)

/-- If a star subalgebra of a topological star algebra is commutative, then so is its topological
closure. See note [reducible non-instances]. -/
@[reducible]
def commSemiringTopologicalClosure [T2Space A] (s : StarSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  s.toSubalgebra.commSemiringTopologicalClosure hs
#align star_subalgebra.comm_semiring_topological_closure StarSubalgebra.commSemiringTopologicalClosure

/-- If a star subalgebra of a topological star algebra is commutative, then so is its topological
closure. See note [reducible non-instances]. -/
@[reducible]
def commRingTopologicalClosure {R A} [CommRing R] [StarRing R] [TopologicalSpace A] [Ring A]
    [Algebra R A] [StarRing A] [StarModule R A] [TopologicalRing A] [ContinuousStar A] [T2Space A]
    (s : StarSubalgebra R A) (hs : ∀ x y : s, x * y = y * x) : CommRing s.topologicalClosure :=
  s.toSubalgebra.commRingTopologicalClosure hs
#align star_subalgebra.comm_ring_topological_closure StarSubalgebra.commRingTopologicalClosure

/-- Continuous `StarAlgHom`s from the topological closure of a `StarSubalgebra` whose
compositions with the `StarSubalgebra.inclusion` map agree are, in fact, equal. -/
theorem _root_.StarAlgHom.ext_topologicalClosure [T2Space B] {S : StarSubalgebra R A}
    {φ ψ : S.topologicalClosure →⋆ₐ[R] B} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h :
      φ.comp (inclusion (le_topologicalClosure S)) = ψ.comp (inclusion (le_topologicalClosure S))) :
    φ = ψ := by
  rw [FunLike.ext'_iff]
  -- ⊢ ↑φ = ↑ψ
  have : Dense (Set.range <| inclusion (le_topologicalClosure S)) := by
    refine' embedding_subtype_val.toInducing.dense_iff.2 fun x => _
    convert show ↑x ∈ closure (S : Set A) from x.prop
    rw [← Set.range_comp]
    exact
      Set.ext fun y =>
        ⟨by
          rintro ⟨y, rfl⟩
          exact y.prop, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩
  refine' Continuous.ext_on this hφ hψ _
  -- ⊢ EqOn (↑φ) (↑ψ) (range ↑(inclusion (_ : S ≤ topologicalClosure S)))
  rintro _ ⟨x, rfl⟩
  -- ⊢ ↑φ (↑(inclusion (_ : S ≤ topologicalClosure S)) x) = ↑ψ (↑(inclusion (_ : S  …
  simpa only using FunLike.congr_fun h x
  -- 🎉 no goals
#align star_alg_hom.ext_topological_closure StarAlgHom.ext_topologicalClosure

theorem _root_.StarAlgHomClass.ext_topologicalClosure [T2Space B] {F : Type*}
    {S : StarSubalgebra R A} [StarAlgHomClass F R S.topologicalClosure B] {φ ψ : F}
    (hφ : Continuous φ) (hψ : Continuous ψ) (h : ∀ x : S,
        φ (inclusion (le_topologicalClosure S) x) = ψ ((inclusion (le_topologicalClosure S)) x)) :
    φ = ψ := by
  -- Porting note: an intervening coercion seems to have appeared since ML3
  have : (φ : S.topologicalClosure →⋆ₐ[R] B) = (ψ : S.topologicalClosure →⋆ₐ[R] B) := by
    refine StarAlgHom.ext_topologicalClosure (R := R) (A := A) (B := B) hφ hψ (StarAlgHom.ext ?_)
    simpa only [StarAlgHom.coe_comp, StarAlgHom.coe_coe] using h
  rw [FunLike.ext'_iff, ← StarAlgHom.coe_coe]
  -- ⊢ ↑↑φ = ↑ψ
  apply congrArg _ this
  -- 🎉 no goals
#align star_alg_hom_class.ext_topological_closure StarAlgHomClass.ext_topologicalClosure

end TopologicalStarAlgebra

end StarSubalgebra

section Elemental

open StarSubalgebra

variable (R : Type*) {A B : Type*} [CommSemiring R] [StarRing R]

variable [TopologicalSpace A] [Semiring A] [StarRing A] [TopologicalSemiring A]

variable [ContinuousStar A] [Algebra R A] [StarModule R A]

variable [TopologicalSpace B] [Semiring B] [StarRing B] [Algebra R B]

/-- The topological closure of the subalgebra generated by a single element. -/
def elementalStarAlgebra (x : A) : StarSubalgebra R A :=
  (adjoin R ({x} : Set A)).topologicalClosure
#align elemental_star_algebra elementalStarAlgebra

namespace elementalStarAlgebra

theorem self_mem (x : A) : x ∈ elementalStarAlgebra R x :=
  SetLike.le_def.mp (le_topologicalClosure _) (self_mem_adjoin_singleton R x)
#align elemental_star_algebra.self_mem elementalStarAlgebra.self_mem

theorem star_self_mem (x : A) : star x ∈ elementalStarAlgebra R x :=
  star_mem <| self_mem R x
#align elemental_star_algebra.star_self_mem elementalStarAlgebra.star_self_mem

/-- The `elementalStarAlgebra` generated by a normal element is commutative. -/
instance [T2Space A] {x : A} [IsStarNormal x] : CommSemiring (elementalStarAlgebra R x) :=
  StarSubalgebra.commSemiringTopologicalClosure _ mul_comm

/-- The `elementalStarAlgebra` generated by a normal element is commutative. -/
instance {R A} [CommRing R] [StarRing R] [TopologicalSpace A] [Ring A] [Algebra R A] [StarRing A]
    [StarModule R A] [TopologicalRing A] [ContinuousStar A] [T2Space A] {x : A} [IsStarNormal x] :
    CommRing (elementalStarAlgebra R x) :=
  StarSubalgebra.commRingTopologicalClosure _ mul_comm

protected theorem isClosed (x : A) : IsClosed (elementalStarAlgebra R x : Set A) :=
  isClosed_closure
#align elemental_star_algebra.is_closed elementalStarAlgebra.isClosed

instance {A : Type*} [UniformSpace A] [CompleteSpace A] [Semiring A] [StarRing A]
    [TopologicalSemiring A] [ContinuousStar A] [Algebra R A] [StarModule R A] (x : A) :
    CompleteSpace (elementalStarAlgebra R x) :=
  isClosed_closure.completeSpace_coe

theorem le_of_isClosed_of_mem {S : StarSubalgebra R A} (hS : IsClosed (S : Set A)) {x : A}
    (hx : x ∈ S) : elementalStarAlgebra R x ≤ S :=
  topologicalClosure_minimal (adjoin_le <| Set.singleton_subset_iff.2 hx) hS
#align elemental_star_algebra.le_of_is_closed_of_mem elementalStarAlgebra.le_of_isClosed_of_mem

/-- The coercion from an elemental algebra to the full algebra as a `ClosedEmbedding`. -/
theorem closedEmbedding_coe (x : A) : ClosedEmbedding ((↑) : elementalStarAlgebra R x → A) :=
  { induced := rfl
    inj := Subtype.coe_injective
    closed_range := by
      convert elementalStarAlgebra.isClosed R x
      -- ⊢ range Subtype.val = ↑(elementalStarAlgebra R x)
      exact
        Set.ext fun y =>
          ⟨by
            rintro ⟨y, rfl⟩
            exact y.prop, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩ }
#align elemental_star_algebra.closed_embedding_coe elementalStarAlgebra.closedEmbedding_coe

theorem starAlgHomClass_ext [T2Space B] {F : Type*} {a : A}
    [StarAlgHomClass F R (elementalStarAlgebra R a) B] {φ ψ : F} (hφ : Continuous φ)
    (hψ : Continuous ψ) (h : φ ⟨a, self_mem R a⟩ = ψ ⟨a, self_mem R a⟩) : φ = ψ := by
  refine StarAlgHomClass.ext_topologicalClosure hφ hψ fun x => ?_
  -- ⊢ ↑φ (↑(StarSubalgebra.inclusion (_ : adjoin R {a} ≤ topologicalClosure (adjoi …
  apply adjoin_induction' x ?_ ?_ ?_ ?_ ?_
  exacts [fun y hy => by simpa only [Set.mem_singleton_iff.mp hy] using h, fun r => by
    simp only [AlgHomClass.commutes], fun x y hx hy => by simp only [map_add, hx, hy],
    fun x y hx hy => by simp only [map_mul, hx, hy], fun x hx => by simp only [map_star, hx]]
#align elemental_star_algebra.star_alg_hom_class_ext elementalStarAlgebra.starAlgHomClass_ext

end elementalStarAlgebra

end Elemental
