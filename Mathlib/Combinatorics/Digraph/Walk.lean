/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shashank Kirtania
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
inductive Nil : {a b : V} → Walk G a b → Prop
  | nil {u : V} : Nil (nil : G.Walk u u)

@[simp]
lemma nil_nil {u : V} : (nil : G.Walk u u).Nil := Nil.nil

@[simp]
lemma not_nil_cons {a b c : V} {h : G.Adj a b} {p : G.Walk b c} :
    ¬ (cons h p).Nil := nofun

instance (p : G.Walk a b) : Decidable p.Nil :=
  match p with
  | nil => isTrue .nil
  | cons _ _ => isFalse nofun

protected lemma Nil.eq {p : G.Walk a b} : p.Nil → a = b
  | .nil => rfl

lemma not_nil_of_ne {p : G.Walk a b} : a ≠ b → ¬ p.Nil := mt Nil.eq

lemma nil_iff_eq_nil {a : V} {p : G.Walk a a} : p.Nil ↔ p = nil := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact Nil.nil

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
  cases p <;> simp [support]

/-- The first element of a walk is its starting vertex. -/
@[simp]
theorem support_head {a b : V} (p : G.Walk a b) :
    p.support.head? = some a := by
  cases p <;> simp

theorem end_mem_support {a b : V} (p : G.Walk a b) : b ∈ p.support := by
  induction p with
  | nil => simp [support]
  | cons h p ih =>
    simp [support]
    right
    exact ih

/-- Two walks with the same support are equal. -/
theorem ext_support {a b : V} {p q : G.Walk a b}
  (h : p.support = q.support)
  (adj_sub : ∀ x y, Subsingleton (G.Adj x y)) : p = q := by
  sorry
  -- no walk has empty support
  -- have support_ne_nil : ∀ {x y : V} (r : G.Walk x y), r.support ≠ [] := by
  --   intro x y r
  --   induction r with
  --   | nil => simp [Walk.support]; intro hh; contradiction
  --   | cons _ r' _ => simp [Walk.support]; intro hh; contradiction

  -- induction p with
  -- | nil =>
  --   -- p = nil, so support p = [a]; q must be nil
  --   simp [Walk.support] at h
  --   cases q with
  --   | nil => rfl
  --   | cons hq q' =>
  --     simp [Walk.support] at h
  --     -- [a] = a :: q'.support → q'.support = [] which is impossible
  --     injection h with h_tail
  --     exact False.elim (support_ne_nil q' h_tail)

  -- | cons hp p' ih =>
  --   -- p = cons hp p', so p.support = a :: p'.support
  --   simp [Walk.support] at h
  --   cases q with
  --   | nil =>
  --     simp [Walk.support] at h
  --     -- a :: p'.support = [a] → p'.support = [] impossible
  --     injection h with h_tail
  --     exact False.elim (support_ne_nil p' h_tail)
  --   | cons hq q' =>
  --     -- a :: p'.support = a :: q'.support → p'.support = q'.support
  --     injection h with _ h_tail
  --     have tail_eq : p' = q' := ih h_tail
  --     -- equate adjacency proofs using Subsingleton, then finish
  --     have head_eq : hp = hq := Subsingleton.elim (adj_sub _ _) hp hq
  --     rw [head_eq]
  --     congr
  --     exact tail_eq





@[simp]
theorem nil_iff_endpoints_eq {a b : V} {p : G.Walk a b} :
    p.Nil → a = b :=
  Nil.eq

theorem length_eq_zero_iff_nil {a : V} {p : G.Walk a a} :
    p.length = 0 ↔ p.Nil := by
  constructor
  · intro h
    cases p
    · exact Nil.nil
    · simp [length] at h
  · intro h
    cases h
    rfl

/-- Get the vertex at position `n` in the walk.
    If `n` is beyond the length, returns the end vertex. -/
def getVert {a b : V} : G.Walk a b → ℕ → V
  | nil, _ => a
  | cons _ p, 0 => a
  | cons _ p, n+1 => p.getVert n

@[simp]
theorem getVert_zero {a b : V} (p : G.Walk a b) : p.getVert 0 = a := by
  cases p <;> rfl

theorem getVert_of_length_le {a b : V} (p : G.Walk a b) {n : ℕ}
    (h : p.length ≤ n) : p.getVert n = b := by
  induction p generalizing n with
  | nil => rfl
  | cons h' p ih =>
    cases n
    · simp [length] at h
    · simp [getVert]
      apply ih
      simp [length] at h
      omega

@[simp]
theorem getVert_length {a b : V} (p : G.Walk a b) :
    p.getVert p.length = b :=
  p.getVert_of_length_le (le_refl _)

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

@[simp]
theorem copy_rfl_rfl {a b : V} (p : G.Walk a b) :
    p.copy rfl rfl = p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp [copy]
    exact ih

@[simp]
theorem support_copy {a b a' b' : V} (p : G.Walk a b) (ha : a = a') (hb : b = b') :
    (p.copy ha hb).support = p.support := by
  subst ha
  subst hb
  simp

@[simp]
theorem length_copy {a b a' b' : V} (p : G.Walk a b) (ha : a = a') (hb : b = b') :
    (p.copy ha hb).length = p.length := by
  subst ha
  subst hb
  simp

/-- Reverse a walk if the digraph has symmetric adjacency relation. -/
def reverse {a b : V} (h : ∀ (x y : V), G.Adj x y → G.Adj y x) :
    G.Walk a b → G.Walk b a
  | nil => nil
  | cons h' p => (p.reverse h).append (cons (h _ _ h') nil)

end Walk

end Digraph
