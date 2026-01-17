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
variable {G : SimpleGraph V} {c : Sym2 V → α} {s t : V}

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

namespace Flow

variable (f : Flow G c s t)

/-- The net outflow at a vertex. -/
def netOut (v : V) : α := ∑ u, f.val v u

/-- The value of an `s`-`t` flow (net outflow at `s`). -/
def value : α := f.netOut s

/-- For a set `S` of vertices, the total flow leaving `S`. -/
def cutValue (S : Finset V) : α := ∑ u ∈ S, ∑ v ∈ Sᶜ, f.val u v

/-- For a set `S` of vertices, the total capacity leaving `S`. -/
def cutCapacity (S : Finset V) : α := by
  classical
  exact ∑ u ∈ S, ∑ v ∈ Sᶜ, if G.Adj u v then c s(u, v) else 0

omit [DecidableEq V] [IsOrderedAddMonoid α] in
lemma value_def : f.value = ∑ v, f.val s v := rfl

omit [DecidableEq V] [IsOrderedAddMonoid α] in
lemma netOut_def (v : V) : f.netOut v = ∑ u, f.val v u := rfl

private lemma sum_sum_skew_eq_zero (S : Finset V) :
    (∑ u ∈ S, ∑ v ∈ S, f.val u v) = 0 := by
  classical
  have hrewrite :
      (∑ u ∈ S, ∑ v ∈ S, f.val u v) = ∑ p ∈ S ×ˢ S, f.val p.1 p.2 := by
    simpa using
      (Finset.sum_product' (s := S) (t := S) (f := fun u v => f.val u v)).symm
  refine hrewrite.trans ?_
  refine Finset.sum_involution (s := S ×ˢ S) (f := fun p : V × V => f.val p.1 p.2)
      (g := fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    rcases p with ⟨u, v⟩
    simpa [f.skew u v]
  · intro p hp hpne
    intro hfix
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
    simpa [h_other, Flow.netOut, netOut, f.netOut_def] using h
  have hsplit :
      (∑ v ∈ S, f.netOut v) =
        (∑ u ∈ S, ∑ v ∈ S, f.val u v) + (∑ u ∈ S, ∑ v ∈ Sᶜ, f.val u v) := by
    -- Split the inner sum over `univ` as `S + Sᶜ`.
    simpa [Flow.netOut, netOut, Finset.sum_add_sum_compl, Finset.sum_add_distrib, Finset.sum_sum,
      add_comm, add_left_comm, add_assoc] using congrArg (fun x => (∑ u ∈ S, x u))
        (funext fun u => (Finset.sum_add_sum_compl (s := S) (f := fun v => f.val u v)).symm)
  -- Internal edges cancel by skew-symmetry.
  calc
    f.value = f.netOut s := rfl
    _ = ∑ v ∈ S, f.netOut v := hsum
    _ = (∑ u ∈ S, ∑ v ∈ S, f.val u v) + (∑ u ∈ S, ∑ v ∈ Sᶜ, f.val u v) := hsplit
    _ = 0 + f.cutValue S := by
          simp [Flow.cutValue, cutValue, f.sum_sum_skew_eq_zero S]
    _ = f.cutValue S := by simp

lemma cutValue_le_cutCapacity (S : Finset V) : f.cutValue S ≤ f.cutCapacity S := by
  classical
  unfold Flow.cutValue Flow.cutCapacity cutValue cutCapacity
  refine Finset.sum_le_sum ?_
  intro u hu
  refine Finset.sum_le_sum ?_
  intro v hv
  by_cases hAdj : G.Adj u v
  · simpa [hAdj] using f.capacity u v
  · have hzero : f.val u v = 0 := f.support u v hAdj
    simpa [hAdj, hzero]

/-- Weak duality: the value of any flow is bounded by the capacity of any `s`-`t` cut. -/
theorem value_le_cutCapacity (S : Finset V) (hs : s ∈ S) (ht : t ∉ S) :
    f.value ≤ f.cutCapacity S := by
  simp [f.value_eq_cutValue S hs ht] using f.cutValue_le_cutCapacity (S := S)

end Flow

end SimpleGraph
