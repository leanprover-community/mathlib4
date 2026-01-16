/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Tranquilli
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Int.Order.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Max-Flow / Min-Cut (basic definitions, weak duality)

This file sets up a convenient notion of an `s`-`t` flow on an undirected simple graph, modelled as
a skew-symmetric function `V → V → ℤ` bounded by a (symmetric) capacity on unordered pairs.

At the moment, we only prove the "easy" inequality: the value of any flow is bounded above by the
capacity of any `s`-`t` cut.

The full max-flow/min-cut theorem (existence of a cut achieving equality for a maximal flow) is not
yet in Mathlib.
-/

@[expose] public section

namespace SimpleGraph

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {c : Sym2 V → ℕ} {s t : V}

/-- An `s`-`t` flow on an undirected graph, expressed as a skew-symmetric function `V → V → ℤ`
whose absolute value is bounded by a capacity on unordered pairs, together with the usual flow
conservation law away from `s` and `t`. -/
structure Flow (G : SimpleGraph V) (c : Sym2 V → ℕ) (s t : V) where
  val : V → V → ℤ
  skew : ∀ u v, val u v = -val v u
  capacity : ∀ u v, |val u v| ≤ (c s(u, v) : ℤ)
  conserve : ∀ v, v ≠ s → v ≠ t → (∑ u, val v u) = 0

namespace Flow

variable (f : Flow G c s t)

/-- The net outflow at a vertex. -/
def netOut (v : V) : ℤ := ∑ u, f.val v u

/-- The value of an `s`-`t` flow (net outflow at `s`). -/
def value : ℤ := f.netOut s

/-- For a set `S` of vertices, the total flow leaving `S`. -/
def cutValue (S : Finset V) : ℤ := ∑ u in S, ∑ v in Sᶜ, f.val u v

/-- For a set `S` of vertices, the total capacity leaving `S`. -/
def cutCapacity (S : Finset V) : ℤ := ∑ u in S, ∑ v in Sᶜ, (c s(u, v) : ℤ)

lemma value_def : f.value = ∑ v, f.val s v := rfl

lemma netOut_def (v : V) : f.netOut v = ∑ u, f.val v u := rfl

private lemma sum_sum_skew_eq_zero (S : Finset V) :
    (∑ u in S, ∑ v in S, f.val u v) = 0 := by
  classical
  set A : ℤ := ∑ u in S, ∑ v in S, f.val u v
  have hA : A = -A := by
    -- Swap the two sums and use skew-symmetry.
    simp [A, Finset.sum_comm, f.skew, Finset.sum_neg_distrib]
  have h2A : (2 : ℤ) * A = 0 := by
    -- From `A = -A`, conclude `A + A = 0`, hence `2*A = 0`.
    have : A + A = 0 := by
      calc
        A + A = A + (-A) := by simpa [hA]
        _ = 0 := by simp
    simpa [two_mul] using this
  -- `2 ≠ 0` in `ℤ`, so `A = 0`.
  have : A = 0 := (mul_eq_zero.mp h2A).resolve_left (by decide)
  simpa [A] using this

lemma value_eq_cutValue (S : Finset V) (hs : s ∈ S) (ht : t ∉ S) :
    f.value = f.cutValue S := by
  classical
  have h_other : (∑ v in S.erase s, f.netOut v) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro v hv
    have hv' : v ≠ s ∧ v ∈ S := Finset.mem_erase.mp hv
    have hv_ne_t : v ≠ t := by
      intro hvt
      exact ht (hvt ▸ hv'.2)
    simpa [Flow.netOut, netOut] using f.conserve v hv'.1 hv_ne_t
  have hsum : f.netOut s = ∑ v in S, f.netOut v := by
    have h := (Finset.sum_erase_add (s := S) (a := s) (f := fun v => f.netOut v) hs)
    -- `h : (∑ v in S.erase s, netOut v) + netOut s = ∑ v in S, netOut v`.
    -- The first summand is `0` by conservation away from `s` and `t`.
    simpa [h_other, Flow.netOut, netOut, f.netOut_def] using h
  have hsplit :
      (∑ v in S, f.netOut v) = (∑ u in S, ∑ v in S, f.val u v) + (∑ u in S, ∑ v in Sᶜ, f.val u v) := by
    -- Split the inner sum over `univ` as `S + Sᶜ`.
    simpa [Flow.netOut, netOut, Finset.sum_add_sum_compl, Finset.sum_add_distrib, Finset.sum_sum,
      add_comm, add_left_comm, add_assoc] using congrArg (fun x => (∑ u in S, x u))
        (funext fun u => (Finset.sum_add_sum_compl (s := S) (f := fun v => f.val u v)).symm)
  -- Internal edges cancel by skew-symmetry.
  calc
    f.value = f.netOut s := rfl
    _ = ∑ v in S, f.netOut v := hsum
    _ = (∑ u in S, ∑ v in S, f.val u v) + (∑ u in S, ∑ v in Sᶜ, f.val u v) := hsplit
    _ = 0 + f.cutValue S := by
          simp [Flow.cutValue, cutValue, f.sum_sum_skew_eq_zero S]
    _ = f.cutValue S := by simp

lemma cutValue_le_cutCapacity (S : Finset V) : f.cutValue S ≤ f.cutCapacity S := by
  classical
  -- Pointwise bound: `f.val u v ≤ c s(u,v)` since `f.val u v ≤ |f.val u v| ≤ c s(u,v)`.
  have hle : ∀ u ∈ S, ∀ v ∈ Sᶜ, f.val u v ≤ (c s(u, v) : ℤ) := by
    intro u hu v hv
    exact (le_abs_self (f.val u v)).trans (f.capacity u v)
  -- Sum the pointwise bounds.
  unfold Flow.cutValue Flow.cutCapacity cutValue cutCapacity
  refine Finset.sum_le_sum ?_
  intro u hu
  refine Finset.sum_le_sum ?_
  intro v hv
  exact hle u hu v hv

/-- Weak duality: the value of any flow is bounded by the capacity of any `s`-`t` cut. -/
theorem value_le_cutCapacity (S : Finset V) (hs : s ∈ S) (ht : t ∉ S) :
    f.value ≤ f.cutCapacity S := by
  simpa [f.value_eq_cutValue S hs ht] using f.cutValue_le_cutCapacity (S := S)

end Flow

end SimpleGraph
