/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Field.Subfield
import Mathlib.Topology.Algebra.Field.Basic

/-!
# Topological properties of subfields

This file constructs the topological closure of a subfield as a subfield.
-/

namespace Subfield
variable {α : Type*} [Field α] [TopologicalSpace α] [TopologicalDivisionRing α]

/-- The (topological-space) closure of a subfield of a topological field is
itself a subfield. -/
@[pp_dot]
def topologicalClosure (K : Subfield α) : Subfield α where
  toSubring := K.toSubring.topologicalClosure
  inv_mem' x hx := by
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subring.coe_toSubsemiring, SetLike.mem_coe,
      Subring.topologicalClosure, Subfield.coe_toSubring] at hx ⊢
    obtain rfl | h := eq_or_ne x 0
    · rwa [inv_zero]
    · rw [← inv_coe_set (H := K), ← Set.image_inv]
      exact mem_closure_image (continuousAt_inv₀ h) hx
#align subfield.topological_closure Subfield.topologicalClosure

lemma le_topologicalClosure (s : Subfield α) : s ≤ s.topologicalClosure := _root_.subset_closure
#align subfield.le_topological_closure Subfield.le_topologicalClosure

lemma isClosed_topologicalClosure (s : Subfield α) : IsClosed (s.topologicalClosure : Set α) :=
  isClosed_closure
#align subfield.is_closed_topological_closure Subfield.isClosed_topologicalClosure

lemma topologicalClosure_minimal (s : Subfield α) {t : Subfield α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t := closure_minimal h ht
#align subfield.topological_closure_minimal Subfield.topologicalClosure_minimal

end Subfield
