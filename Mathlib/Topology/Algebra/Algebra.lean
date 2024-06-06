/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.RingTheory.Adjoin.Basic

#align_import topology.algebra.algebra from "leanprover-community/mathlib"@"43afc5ad87891456c57b5a183e3e617d67c2b1db"

/-!
# Topological (sub)algebras

A topological algebra over a topological semiring `R` is a topological semiring with a compatible
continuous scalar multiplication by elements of `R`. We reuse typeclass `ContinuousSMul` for
topological algebras.

## Results

This is just a minimal stub for now!

The topological closure of a subalgebra is still a subalgebra,
which as an algebra is a topological algebra.
-/


open scoped Classical
open Set TopologicalSpace Algebra

open scoped Classical

universe u v w

section TopologicalAlgebra

variable (R : Type*) (A : Type u)
variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [TopologicalSpace R] [TopologicalSpace A]

 @[continuity, fun_prop]
theorem continuous_algebraMap [ContinuousSMul R A] : Continuous (algebraMap R A) := by
  rw [algebraMap_eq_smul_one']
  exact continuous_id.smul continuous_const
#align continuous_algebra_map continuous_algebraMap

theorem continuous_algebraMap_iff_smul [TopologicalSemiring A] :
    Continuous (algebraMap R A) ↔ Continuous fun p : R × A => p.1 • p.2 := by
  refine ⟨fun h => ?_, fun h => have : ContinuousSMul R A := ⟨h⟩; continuous_algebraMap _ _⟩
  simp only [Algebra.smul_def]
  exact (h.comp continuous_fst).mul continuous_snd
#align continuous_algebra_map_iff_smul continuous_algebraMap_iff_smul

theorem continuousSMul_of_algebraMap [TopologicalSemiring A] (h : Continuous (algebraMap R A)) :
    ContinuousSMul R A :=
  ⟨(continuous_algebraMap_iff_smul R A).1 h⟩
#align has_continuous_smul_of_algebra_map continuousSMul_of_algebraMap

variable [ContinuousSMul R A]

/-- The inclusion of the base ring in a topological algebra as a continuous linear map. -/
@[simps]
def algebraMapCLM : R →L[R] A :=
  { Algebra.linearMap R A with
    toFun := algebraMap R A
    cont := continuous_algebraMap R A }
#align algebra_map_clm algebraMapCLM

theorem algebraMapCLM_coe : ⇑(algebraMapCLM R A) = algebraMap R A :=
  rfl
#align algebra_map_clm_coe algebraMapCLM_coe

theorem algebraMapCLM_toLinearMap : (algebraMapCLM R A).toLinearMap = Algebra.linearMap R A :=
  rfl
#align algebra_map_clm_to_linear_map algebraMapCLM_toLinearMap

end TopologicalAlgebra

section TopologicalAlgebra

variable {R : Type*} [CommSemiring R]
variable {A : Type u} [TopologicalSpace A]
variable [Semiring A] [Algebra R A]

#align subalgebra.has_continuous_smul SMulMemClass.continuousSMul

variable [TopologicalSemiring A]

/-- The closure of a subalgebra in a topological algebra as a subalgebra. -/
def Subalgebra.topologicalClosure (s : Subalgebra R A) : Subalgebra R A :=
  { s.toSubsemiring.topologicalClosure with
    carrier := closure (s : Set A)
    algebraMap_mem' := fun r => s.toSubsemiring.le_topologicalClosure (s.algebraMap_mem r) }
#align subalgebra.topological_closure Subalgebra.topologicalClosure

@[simp]
theorem Subalgebra.topologicalClosure_coe (s : Subalgebra R A) :
    (s.topologicalClosure : Set A) = closure (s : Set A) :=
  rfl
#align subalgebra.topological_closure_coe Subalgebra.topologicalClosure_coe

instance Subalgebra.topologicalSemiring (s : Subalgebra R A) : TopologicalSemiring s :=
  s.toSubsemiring.topologicalSemiring
#align subalgebra.topological_semiring Subalgebra.topologicalSemiring

theorem Subalgebra.le_topologicalClosure (s : Subalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure
#align subalgebra.le_topological_closure Subalgebra.le_topologicalClosure

theorem Subalgebra.isClosed_topologicalClosure (s : Subalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) := by convert @isClosed_closure A s _
#align subalgebra.is_closed_topological_closure Subalgebra.isClosed_topologicalClosure

theorem Subalgebra.topologicalClosure_minimal (s : Subalgebra R A) {t : Subalgebra R A} (h : s ≤ t)
    (ht : IsClosed (t : Set A)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align subalgebra.topological_closure_minimal Subalgebra.topologicalClosure_minimal

/-- If a subalgebra of a topological algebra is commutative, then so is its topological closure. -/
def Subalgebra.commSemiringTopologicalClosure [T2Space A] (s : Subalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }
#align subalgebra.comm_semiring_topological_closure Subalgebra.commSemiringTopologicalClosure

/-- This is really a statement about topological algebra isomorphisms,
but we don't have those, so we use the clunky approach of talking about
an algebra homomorphism, and a separate homeomorphism,
along with a witness that as functions they are the same.
-/
theorem Subalgebra.topologicalClosure_comap_homeomorph (s : Subalgebra R A) {B : Type*}
    [TopologicalSpace B] [Ring B] [TopologicalRing B] [Algebra R B] (f : B →ₐ[R] A) (f' : B ≃ₜ A)
    (w : (f : B → A) = f') : s.topologicalClosure.comap f = (s.comap f).topologicalClosure := by
  apply SetLike.ext'
  simp only [Subalgebra.topologicalClosure_coe]
  simp only [Subalgebra.coe_comap, Subsemiring.coe_comap, AlgHom.coe_toRingHom]
  rw [w]
  exact f'.preimage_closure _
#align subalgebra.topological_closure_comap_homeomorph Subalgebra.topologicalClosure_comap_homeomorph

end TopologicalAlgebra

section Ring

variable {R : Type*} [CommRing R]
variable {A : Type u} [TopologicalSpace A]
variable [Ring A]
variable [Algebra R A] [TopologicalRing A]

/-- If a subalgebra of a topological algebra is commutative, then so is its topological closure.
See note [reducible non-instances]. -/
abbrev Subalgebra.commRingTopologicalClosure [T2Space A] (s : Subalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : CommRing s.topologicalClosure :=
  { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }
#align subalgebra.comm_ring_topological_closure Subalgebra.commRingTopologicalClosure

variable (R)

/-- The topological closure of the subalgebra generated by a single element. -/
def Algebra.elementalAlgebra (x : A) : Subalgebra R A :=
  (Algebra.adjoin R ({x} : Set A)).topologicalClosure
#align algebra.elemental_algebra Algebra.elementalAlgebra

@[aesop safe apply (rule_sets := [SetLike])]
theorem Algebra.self_mem_elementalAlgebra (x : A) : x ∈ Algebra.elementalAlgebra R x :=
  SetLike.le_def.mp (Subalgebra.le_topologicalClosure (Algebra.adjoin R ({x} : Set A))) <|
    Algebra.self_mem_adjoin_singleton R x
#align algebra.self_mem_elemental_algebra Algebra.self_mem_elementalAlgebra

variable {R}

instance [T2Space A] {x : A} : CommRing (Algebra.elementalAlgebra R x) :=
  Subalgebra.commRingTopologicalClosure _
    letI : CommRing (Algebra.adjoin R ({x} : Set A)) :=
      Algebra.adjoinCommRingOfComm R fun y hy z hz => by
        rw [mem_singleton_iff] at hy hz
        rw [hy, hz]
    fun _ _ => mul_comm _ _

end Ring

section DivisionRing

/-- The action induced by `algebraRat` is continuous. -/
instance DivisionRing.continuousConstSMul_rat {A} [DivisionRing A] [TopologicalSpace A]
    [ContinuousMul A] [CharZero A] : ContinuousConstSMul ℚ A :=
  ⟨fun r => by simpa only [Algebra.smul_def] using continuous_const.mul continuous_id⟩
#align division_ring.has_continuous_const_smul_rat DivisionRing.continuousConstSMul_rat

end DivisionRing
