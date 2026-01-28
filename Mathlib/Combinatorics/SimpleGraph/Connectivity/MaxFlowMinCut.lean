/-
Copyright (c) 2026 Julius Tranquilli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Tranquilli
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Max-Flow / Min-Cut (basic definitions, weak duality)

This file sets up a convenient notion of an `s`-`t` flow on an undirected simple graph, modelled as
a skew-symmetric function `V → V → α` bounded by a (symmetric) capacity on unordered pairs and
supported on the edges of the given graph.

At the moment, we only prove the "easy" inequality: the value of any flow is bounded above by the
capacity of any `s`-`t` cut.

The full max-flow/min-cut theorem (existence of a cut achieving equality for a maximal flow) is not
yet in Mathlib.
-/

@[expose] public section

namespace SimpleGraph

open scoped BigOperators

variable {V α : Type*} [Fintype V] [DecidableEq V]
variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
variable {G : SimpleGraph V} {c : Sym2 V → α}

/-- For a set `S` of vertices, the total capacity leaving `S`. -/
noncomputable def cutCapacity (G : SimpleGraph V) (c : Sym2 V → α) (S : Finset V) : α := by
  classical
  exact ∑ u ∈ S, ∑ v ∈ Sᶜ, if G.Adj u v then c s(u, v) else 0

variable {s t : V}

/-- An `s`-`t` flow on an undirected graph, expressed as a skew-symmetric function `V → V → α`
supported on the edges of `G` and bounded above by a capacity on unordered pairs, together with the
usual flow conservation law away from `s` and `t`.

(Skew-symmetry plus the upper bound applied to `(v, u)` yields the corresponding lower bound.) -/
structure Flow (G : SimpleGraph V) (c : Sym2 V → α) (s t : V) where
  val : V → V → α
  skew : ∀ u v, val u v = -val v u
  capacity : ∀ u v, val u v ≤ c s(u, v)
  support : ∀ u v, ¬ G.Adj u v → val u v = 0
  conserve : ∀ v, v ≠ s → v ≠ t → (∑ u, val v u) = 0

/-- The value of a flow on ordered pairs of vertices. -/
add_decl_doc SimpleGraph.Flow.val

/-- Skew-symmetry: reversing an edge negates the flow. -/
add_decl_doc SimpleGraph.Flow.skew

/-- Capacity constraint: flow on any edge is bounded above by its capacity. -/
add_decl_doc SimpleGraph.Flow.capacity

/-- Support constraint: non-edges carry zero flow. -/
add_decl_doc SimpleGraph.Flow.support

/-- Flow conservation away from `s` and `t`. -/
add_decl_doc SimpleGraph.Flow.conserve

namespace Flow

variable (f : Flow G c s t)

/-- The net outflow at a vertex. -/
def netOut (v : V) : α := ∑ u, f.val v u

/-- The value of an `s`-`t` flow (net outflow at `s`). -/
def value : α := f.netOut s

/-- For a set `S` of vertices, the total flow leaving `S`. -/
def cutValue (S : Finset V) : α := ∑ u ∈ S, ∑ v ∈ Sᶜ, f.val u v

omit [DecidableEq V] [IsOrderedAddMonoid α] in
lemma value_def : f.value = ∑ v, f.val s v := rfl

omit [DecidableEq V] [IsOrderedAddMonoid α] in
lemma netOut_def (v : V) : f.netOut v = ∑ u, f.val v u := rfl

omit [DecidableEq V] [IsOrderedAddMonoid α] in
private lemma sum_sum_skew_eq_zero (S : Finset V) :
    (∑ u ∈ S, ∑ v ∈ S, f.val u v) = 0 := by
  classical
  have hrewrite :
      (∑ u ∈ S, ∑ v ∈ S, f.val u v) = ∑ p ∈ S ×ˢ S, f.val p.1 p.2 := by
    simpa using (Finset.sum_product' (s := S) (t := S) (f := fun u v => f.val u v)).symm
  refine hrewrite.trans ?_
  refine Finset.sum_involution (s := S ×ˢ S) (f := fun p : V × V => f.val p.1 p.2)
      (g := fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    rcases p with ⟨u, v⟩
    simp [f.skew u v]
  · intro p hp hpne hfix
    have huv : p.1 = p.2 := by
      have := congrArg Prod.fst hfix
      simpa using this.symm
    have hdiag : f.val p.1 p.1 = 0 := f.support _ _ (G.loopless _)
    exact hpne (by simpa [huv] using hdiag)
  · intro p hp
    have hp' : p.1 ∈ S ∧ p.2 ∈ S := by simpa [Finset.mem_product] using hp
    simpa [Finset.mem_product] using hp'.symm
  · intro p hp
    rfl

omit [IsOrderedAddMonoid α] in
lemma value_eq_cutValue (S : Finset V) (hs : s ∈ S) (ht : t ∉ S) :
    f.value = f.cutValue S := by
  classical
  have h_other : (∑ v ∈ S.erase s, f.netOut v) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro v hv
    have hv' : v ≠ s ∧ v ∈ S := Finset.mem_erase.mp hv
    have hv_ne_t : v ≠ t := by
      intro hvt
      exact ht (hvt ▸ hv'.2)
    simpa [Flow.netOut, netOut] using f.conserve v hv'.1 hv_ne_t
  have hsum : f.netOut s = ∑ v ∈ S, f.netOut v := by
    have h := (Finset.sum_erase_add (s := S) (a := s) (f := fun v => f.netOut v) hs)
    -- `h : (∑ v in S.erase s, netOut v) + netOut s = ∑ v in S, netOut v`.
    -- The first summand is `0` by conservation away from `s` and `t`.
    simpa [h_other] using h
  have hsplit :
      (∑ v ∈ S, f.netOut v) =
        (∑ u ∈ S, ∑ v ∈ S, f.val u v) + (∑ u ∈ S, ∑ v ∈ Sᶜ, f.val u v) := by
    -- Split the inner sum over `univ` as `S + Sᶜ`.
    simp only [netOut]
    have hinner (v : V) :
        (∑ u, f.val v u) = (∑ u ∈ S, f.val v u) + (∑ u ∈ Sᶜ, f.val v u) := by
      simpa using (Finset.sum_add_sum_compl (s := S) (f := fun u => f.val v u)).symm
    simp_rw [hinner]
    simp [Finset.sum_add_distrib]
  -- Internal edges cancel by skew-symmetry.
  calc
    f.value = f.netOut s := rfl
    _ = ∑ v ∈ S, f.netOut v := hsum
    _ = (∑ u ∈ S, ∑ v ∈ S, f.val u v) + (∑ u ∈ S, ∑ v ∈ Sᶜ, f.val u v) := hsplit
    _ = 0 + f.cutValue S := by
          simp [Flow.cutValue, cutValue, f.sum_sum_skew_eq_zero S]
    _ = f.cutValue S := by simp

lemma cutValue_le_cutCapacity (S : Finset V) : f.cutValue S ≤ SimpleGraph.cutCapacity G c S := by
  classical
  simp only [Flow.cutValue, cutValue, SimpleGraph.cutCapacity, cutCapacity]
  refine Finset.sum_le_sum ?_
  intro u hu
  refine Finset.sum_le_sum ?_
  intro v hv
  by_cases hAdj : G.Adj u v
  · simpa [hAdj] using f.capacity u v
  · have hzero : f.val u v = 0 := f.support u v hAdj
    simp [hAdj, hzero]

/-- Weak duality: the value of any flow is bounded by the capacity of any `s`-`t` cut. -/
theorem value_le_cutCapacity (S : Finset V) (hs : s ∈ S) (ht : t ∉ S) :
    f.value ≤ SimpleGraph.cutCapacity G c S := by
  exact (f.value_eq_cutValue S hs ht).le.trans (f.cutValue_le_cutCapacity (S := S))

end Flow

end SimpleGraph
