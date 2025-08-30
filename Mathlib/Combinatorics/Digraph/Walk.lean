/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Combinatorics.Digraph.Basic

/-!
# Walks in Digraphs

This file defines walks in directed graphs and some of their properties.

## Main definitions

* `Digraph.Walk` - A walk in a directed graph from one vertex to another.
* Various operations and properties of walks, like `append`, `reverse`, etc.

## Implementation notes

The implementation closely follows the structure of `SimpleGraph.Walk`, but respects
the directionality of edges in a digraph.
-/

namespace Digraph

universe u v

variable {V : Type u} {G : Digraph V} {a b c : V}

/--
A `Walk` from vertex `a` to vertex `b` in a directed graph `G` is a sequence of adjacent
vertices starting at `a` and ending at `b`. The adjacency must respect the direction
of edges in the digraph.
-/
inductive Walk (G : Digraph V) : V → V → Type u
  /-- The empty walk from a vertex to itself. -/
  | nil {a : V} : Walk G a a
  /-- Cons constructor: Given a walk from `b` to `c` and a directed edge from `a` to `b`,
     we get a walk from `a` to `c`. Note the order matters for a digraph! -/
  | cons {a b c : V} (h : G.Adj a b) (p : Walk G b c) : Walk G a c

namespace Walk

/-- A predicate that is true if a walk is exactly the empty walk. -/
def Nil : {a b : V} → Walk G a b → Prop
  | _, _, nil => True
  | _, _, _ => False

instance {a : V} : Unique (Walk G a a | nil) where
  default := nil
  uniq := by
    intro x
    cases x
    · rfl
    · cases x.2

/-- Two walks are equal if they are between the same endpoints and have the same structure. -/
@[ext]
theorem ext {a b : V} : ∀ {p q : Walk G a b}, p = q ↔ p.Nil = q.Nil
  | nil, nil => by simp [Nil]
  | cons _ _, nil => by simp [Nil]
  | nil, cons _ _ => by simp [Nil]
  | cons _ _, cons _ _ => by simp [Nil]

@[simp]
theorem nil_nil_iff {a b : V} {p : Walk G a b} : p = nil ↔ a = b ∧ p.Nil := by
  cases p <;> simp [Nil]

/-- Nil iff there's no edge in the walk -/
theorem nil_iff_length_eq {a b : V} {p : G.Walk a b} : p.Nil ↔ a = b ∧ p = nil := by
  cases p
  · simp [Nil]
  · simp [Nil]

/-- Append two walks when the endpoint of the first matches the start point of the second. -/
def append {a b c : V} : G.Walk a b → G.Walk b c → G.Walk a c
  | nil, q => q
  | cons h p, q => cons h (p.append q)

/-- Length of a walk in a directed graph (number of edges). -/
def length {a b : V} : G.Walk a b → ℕ
  | nil => 0
  | cons _ p => p.length + 1

@[simp]
theorem length_nil {a : V} : (nil : G.Walk a a).length = 0 := rfl

@[simp]
theorem length_cons {a b c : V} (h : G.Adj a b) (p : G.Walk b c) :
    (cons h p).length = p.length + 1 := rfl

/-- Reverse a walk if the digraph has symmetric adjacency relation. -/
def reverse {a b : V} (h : ∀ (x y : V), G.Adj x y → G.Adj y x) : G.Walk a b → G.Walk b a
  | nil => nil
  | cons h' p => (p.reverse h).append (cons (h _ _ h') nil)

/-- A list of vertices encountered in a walk. -/
def support {a b : V} : G.Walk a b → List V
  | nil => [a]
  | cons _ p => a :: p.support

@[simp]
theorem support_nil {a : V} : (nil : G.Walk a a).support = [a] := rfl

@[simp]
theorem support_cons {a b c : V} (h : G.Adj a b) (p : G.Walk b c) :
    (cons h p).support = a :: p.support := rfl

theorem start_mem_support {a b : V} (p : G.Walk a b) : a ∈ p.support := by
  cases p
  · simp [support]
  · simp [support]

/-- The first element of a walk is its starting vertex. -/
@[simp]
theorem support_head {a b : V} (p : G.Walk a b) : p.support.head? = some a := by
  cases p <;> simp

theorem end_mem_support {a b : V} (p : G.Walk a b) : b ∈ p.support := by
  induction p with
  | nil => simp [support]
  | cons h p ih =>
    simp [support]
    cases p
    · simp [support]
    · simp [ih, support]

/-- Get the vertex at position `n` in the walk. If `n` is beyond the length, returns the end vertex. -/
def getVert {a b : V} : G.Walk a b → ℕ → V
  | nil, _ => a
  | cons _ p, 0 => a
  | cons _ p, n+1 => p.getVert n

@[simp]
theorem getVert_zero {a b : V} (p : G.Walk a b) : p.getVert 0 = a := by
  cases p <;> rfl

@[simp]
theorem getVert_of_ge {a b : V} (p : G.Walk a b) {n : ℕ} (h : p.length ≤ n) :
    p.getVert n = b := by
  induction p with
  | nil => rfl
  | cons h' p ih =>
    cases n
    · simp [length] at h; contradiction
    · simp [getVert, ih (Nat.le_of_succ_le_succ h)]

/-- Copy of a walk with different endpoints that are definitionally equal. -/
def copy {a b a' b'} (ha : a = a') (hb : b = b') :
    G.Walk a b → G.Walk a' b'
  | nil => by
    subst ha
    subst hb
    exact nil
  | cons h p => by
    subst ha
    exact cons h (p.copy rfl hb)

end Walk

end Digraph
