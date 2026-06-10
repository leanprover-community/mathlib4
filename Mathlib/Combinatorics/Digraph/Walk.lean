/-
Copyright (c) 2026 Kyle Miller, Laurance Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurance Lau
-/
module

public import Mathlib.Combinatorics.Digraph.Basic

/-!
# Walks

This module defines walks on digraphs. A walk is a finite sequence of adjacent vertices.
The definitions are identical to those for `SimpleGraph`.

## Main definitions

* `Digraph.Walk`
* `Digraph.Walk.support`
* `Digraph.Walk.IsCycle`

## Tags

walks
-/

@[expose] public section

namespace Digraph

universe u
variable {V : Type u} (G : Digraph V)

/-- A walk is a sequence of adjacent vertices and can be thought of equally well as a sequence of
directed edges. For vertices `u v : V`, the type `walk u v` consists of all walks starting at `u`
and ending at `v`. -/
inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[match_pattern, reducible]
def Adj.toWalk {G : Digraph V} {u v : V} (h : G.Adj u v) : G.Walk u v :=
  Walk.cons h Walk.nil

namespace Walk

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support {G : Digraph V} {u v : V} : G.Walk u v → List V
  | nil => [u]
  | cons _ p => u :: p.support

@[simp]
lemma support_nil {u : V} : (nil : G.Walk u u).support = [u] := by
  trivial

@[simp]
theorem support_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).support = u :: p.support := rfl

/-- A *cycle* at `u : V` is a nonempty trail beginning and ending at `u`
whose only repeating vertex is `u` (which appears exactly twice). -/
structure IsCycle {u : V} (p : G.Walk u u) : Prop where
  ne_nil : p ≠ nil
  support_nodup : p.support.tail.Nodup

end Walk

end Digraph
