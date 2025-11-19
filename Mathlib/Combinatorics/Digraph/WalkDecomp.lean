/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Combinatorics.Digraph.Walk

/-!
# Decomposing walks in directed graphs

This file defines operations for decomposing walks in directed graphs.

## Main definitions

- `takeUntil`: The path obtained by taking edges of an existing path until a given vertex.
- `dropUntil`: The path obtained by dropping edges of an existing path until a given vertex.
- `rotate`: Rotate a loop walk such that it is centered at the given vertex.

## Implementation notes

This implementation is based on the corresponding functions for `SimpleGraph.Walk`,
but adapted to respect the directionality of edges in a digraph.
-/

namespace Digraph.Walk

universe u

variable {V : Type u} {G : Digraph V} {v w u : V}

/-! ### Walk decompositions -/

section WalkDecomp

variable [DecidableEq V]

/-- Given a vertex in the support of a path, give the path up until (and including) that vertex. -/
def takeUntil {v w : V} : ∀ (p : G.Walk v w) (u : V), u ∈ p.support → G.Walk v u
  | nil, u, h => by rw [List.mem_singleton.mp h]; exact nil
  | cons r p, u, h =>
    if hx : v = u then
      hx ▸ nil
    else
      cons r (takeUntil p u <| by
        simp [support_cons] at h
        cases h
        · exact (hx h).elim
        · exact h)

@[simp] theorem takeUntil_nil {u : V} {h} : takeUntil (nil : G.Walk u u) u h = nil := rfl

@[simp]
lemma takeUntil_first (p : G.Walk u v) :
    p.takeUntil u p.start_mem_support = nil := by cases p <;> simp [takeUntil]

/-- Given a vertex in the support of a path, give the path from (and including) that vertex to
the end. In other words, drop vertices from the front of a path until (and not including)
that vertex. -/
def dropUntil {v w : V} : ∀ (p : G.Walk v w) (u : V), u ∈ p.support → G.Walk u w
  | nil, u, h => by rw [List.mem_singleton.mp h]; exact nil
  | cons r p, u, h =>
    if hx : v = u then by
      subst u
      exact cons r p
    else dropUntil p u <| by
      simp [support_cons] at h
      cases h
      · exact (hx h).elim
      · exact h

/-- The `takeUntil` and `dropUntil` functions split a walk into two pieces.
The lemma `Digraph.Walk.count_support_takeUntil_eq_one` specifies where this split occurs. -/
@[simp]
theorem take_spec {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).append (p.dropUntil u h) = p := by
  induction p
  · simp [List.mem_singleton] at h
    subst u
    rfl
  · simp [support_cons] at h
    split_ifs with h'
    · simp [h', append]
    · cases h
      · exact False.elim (h' h)
      · simp [takeUntil, h', dropUntil, append]
        congr 1
        apply p_ih h

theorem support_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    ∀ x ∈ (p.takeUntil u h).support, x ∈ p.support := by
  intro x hx
  induction p
  · simp [List.mem_singleton] at h
    subst u
    simp [takeUntil] at hx
    exact hx
  · simp [support_cons] at h
    split_ifs with h'
    · simp [h', takeUntil] at hx
      simp [support_cons]
      exact List.mem_cons_self v _
    · cases h
      · exact False.elim (h' h)
      · simp [takeUntil, h', support_cons] at hx
        cases hx
        · simp [support_cons]; exact List.mem_cons_self v _
        · simp [support_cons]
          right
          apply p_ih h hx

theorem support_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    ∀ x ∈ (p.dropUntil u h).support, x ∈ p.support := by
  intro x hx
  induction p
  · simp [List.mem_singleton] at h
    subst u
    simp [dropUntil] at hx
    exact hx
  · simp [support_cons] at h
    split_ifs with h'
    · simp [h', dropUntil, support_cons] at hx
      simp [support_cons]
      cases hx
      · right; exact p.start_mem_support
      · right; exact p.support_dropUntil_subset h' hx
    · cases h
      · exact False.elim (h' h)
      · simp [dropUntil, h', support_cons] at hx
        simp [support_cons]
        right
        apply p_ih h hx

theorem length_takeUntil_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).length ≤ p.length := by
  have := congr_arg Walk.length (p.take_spec h)
  simp [length, append] at this
  linarith

theorem length_dropUntil_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).length ≤ p.length := by
  have := congr_arg Walk.length (p.take_spec h)
  simp [length, append] at this
  linarith

/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) : G.Walk u u :=
  (c.dropUntil u h).append (c.takeUntil u h)

end WalkDecomp

/-- Given a walk `w` and a node in the support, there exists a natural `n`, such that given node
is the `n`-th node (zero-indexed) in the walk. In addition, `n` is at most the length of the path.
Due to the definition of `getVert` it would otherwise be legal to return a larger `n` for the last
node. -/
theorem mem_support_iff_exists_getVert {u v w : V} {p : G.Walk v w} :
    u ∈ p.support ↔ ∃ n, p.getVert n = u ∧ n ≤ p.length := by
  constructor
  · intro h
    induction p
    · simp [List.mem_singleton] at h
      subst h
      use 0
      simp [length]
    · simp [support_cons] at h
      cases h
      · use 0
        simp [getVert, length]
      · obtain ⟨n, hn, hn'⟩ := p_ih h
        use n + 1
        simp [getVert, length, hn, Nat.add_le_add_right hn']
  · rintro ⟨n, hn, hn'⟩
    induction p
    · simp [getVert] at hn
      subst hn
      simp [support]
    · cases n
      · simp [getVert] at hn
        subst hn
        simp [support_cons]
        exact List.mem_cons_self v _
      · simp [getVert] at hn
        have : n ≤ p.length := by
          simp [length] at hn'
          exact Nat.le_of_succ_le_succ hn'
        simp [support_cons, p_ih ⟨hn, this⟩]

end Digraph.Walk
