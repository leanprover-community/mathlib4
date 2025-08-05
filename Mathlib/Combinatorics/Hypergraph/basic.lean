import Mathlib.Data.Set.Basic
import Mathlib.Data.Sym.Sym2

variable {α β : Type*} {a b c : α} {u v w : Set α} {x y z : β}

open Set

structure Hypergraph (α β : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- Incidence predicate stating that a set of vertices `v` form a hyperedge -/
  IsHyperedge : β → Set α → Prop
  /-- The hyperedge set. Currently representing this as a Set
    TODO: Multiset β would be more general... -/
  hyperedgeSet: Set β := {x | ∃ u, IsHyperedge x u}
  -- /-- A hyperedge `x` is incident to something if and only if `x` is in the hyperedge set -/
  -- hyperedge_mem_iff_exists_isHyperedge : ∀ x, x ∈ hyperedgeSet ↔ ∃ u, IsHyperedge x u := by
  --   exact fun _ ↦ Iff.rfl
  -- /-- If some hyperedge `x` is incident to vertex `a`, then `a ∈ V` -/
  -- left_mem_of_isHyperedge : ∀ ⦃x u⦄, ∀ a ∈ u, IsHyperedge x u → a ∈ vertexSet

namespace Hypergraph

variable {H : Hypergraph α β}

/-! ## Notation-/

/-- `V(H)` denotes the `vertexSet` of a hypergraph `H` -/
scoped notation "V(" H ")" => Hypergraph.vertexSet H

/-- `E(H)` denotes the `hyperedgeSet` of a hypergraph `H` -/
scoped notation "E(" H ")" => Hypergraph.hyperedgeSet H

/--
The empty hypergraph

An empty hypergraph contains an empty vertex set and an empty hyperedge set
-/
def emptyHypergraph (α β : Type*) : Hypergraph α β := Hypergraph.mk ∅ (fun _ _ => False) ∅

/--
Predicate to determin if a hypergraph is empty
-/
def isEmpty (H : Hypergraph α β) : Prop := V(H) = ∅ ∧ E(H) = ∅

/--
Predicate to determine if a hypergraph is trivial

A hypergraph is trivial if it has a nonempty vertex set and an empty hyperedge set
-/
def isTrivial (H : Hypergraph α β) : Prop := (Nonempty V(H)) ∧ (E(H) = ∅)


end Hypergraph
