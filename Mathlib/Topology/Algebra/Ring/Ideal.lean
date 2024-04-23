/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.RingTheory.Ideal.Quotient

#align_import topology.algebra.ring.ideal from "leanprover-community/mathlib"@"9a59dcb7a2d06bf55da57b9030169219980660cd"

/-!
# Ideals and quotients of topological rings

In this file we define `Ideal.closure` to be the topological closure of an ideal in a topological
ring. We also define a `TopologicalSpace` structure on the quotient of a topological ring by an
ideal and prove that the quotient is a topological ring.
-/


section Ring

variable {R : Type*} [TopologicalSpace R] [Ring R] [TopologicalRing R]

/-- The closure of an ideal in a topological ring as an ideal. -/
protected def Ideal.closure (I : Ideal R) : Ideal R :=
  {
    AddSubmonoid.topologicalClosure
      I.toAddSubmonoid with
    carrier := closure I
    smul_mem' := fun c _ hx => map_mem_closure (mulLeft_continuous _) hx fun _ => I.mul_mem_left c }
#align ideal.closure Ideal.closure

@[simp]
theorem Ideal.coe_closure (I : Ideal R) : (I.closure : Set R) = closure I :=
  rfl
#align ideal.coe_closure Ideal.coe_closure

-- Porting note: removed `@[simp]` because we make the instance argument explicit since otherwise
-- it causes timeouts as `simp` tries and fails to generated an `IsClosed` instance.
-- we also `alignₓ` because of the change in argument type
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/!4.234852.20heartbeats.20of.20the.20linter
theorem Ideal.closure_eq_of_isClosed (I : Ideal R) (hI : IsClosed (I : Set R)) : I.closure = I :=
  SetLike.ext' hI.closure_eq
#align ideal.closure_eq_of_is_closed Ideal.closure_eq_of_isClosedₓ

end Ring

section CommRing

variable {R : Type*} [TopologicalSpace R] [CommRing R] (N : Ideal R)

open Ideal.Quotient

instance topologicalRingQuotientTopology : TopologicalSpace (R ⧸ N) :=
  instTopologicalSpaceQuotient
#align topological_ring_quotient_topology topologicalRingQuotientTopology

-- note for the reader: in the following, `mk` is `Ideal.Quotient.mk`, the canonical map `R → R/I`.
variable [TopologicalRing R]

theorem QuotientRing.isOpenMap_coe : IsOpenMap (mk N) := by
  intro s s_op
  change IsOpen (mk N ⁻¹' (mk N '' s))
  rw [quotient_ring_saturate]
  exact isOpen_iUnion fun ⟨n, _⟩ => isOpenMap_add_left n s s_op
#align quotient_ring.is_open_map_coe QuotientRing.isOpenMap_coe

theorem QuotientRing.quotientMap_coe_coe : QuotientMap fun p : R × R => (mk N p.1, mk N p.2) :=
  IsOpenMap.to_quotientMap ((QuotientRing.isOpenMap_coe N).prod (QuotientRing.isOpenMap_coe N))
    ((continuous_quot_mk.comp continuous_fst).prod_mk (continuous_quot_mk.comp continuous_snd))
    (by rintro ⟨⟨x⟩, ⟨y⟩⟩; exact ⟨(x, y), rfl⟩)
#align quotient_ring.quotient_map_coe_coe QuotientRing.quotientMap_coe_coe

instance topologicalRing_quotient : TopologicalRing (R ⧸ N) :=
  TopologicalSemiring.toTopologicalRing
    { continuous_add :=
        have cont : Continuous (mk N ∘ fun p : R × R => p.fst + p.snd) :=
          continuous_quot_mk.comp continuous_add
        (QuotientMap.continuous_iff (QuotientRing.quotientMap_coe_coe N)).mpr cont
      continuous_mul :=
        have cont : Continuous (mk N ∘ fun p : R × R => p.fst * p.snd) :=
          continuous_quot_mk.comp continuous_mul
        (QuotientMap.continuous_iff (QuotientRing.quotientMap_coe_coe N)).mpr cont }
#align topological_ring_quotient topologicalRing_quotient

end CommRing
