/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.ConnectedComponent

/-!
# Strongly Connected Quivers

This file defines strongly connected quivers and related concepts.

## Main definitions

* `IsStronglyConnected V`: A quiver where every pair of vertices is connected by a path
* `IsStronglyConnectedPos V`: A quiver where every pair of vertices is connected by a path of
positive length
* `StronglyConnectedComponent V`: The type of strongly connected components of a quiver
* `stronglyConnectedSetoid V`: The equivalence relation defining strong connectivity

## Main results

* Equivalence between different formulations of strong connectivity
* Basic properties of strongly connected components
* Relationship between strong connectivity and weak connectivity via symmetrification

## Implementation notes

We distinguish between allowing paths of length 0 (`IsStronglyConnected`) and requiring
positive length paths (`IsStronglyConnectedPos`) as this distinction is important in
applications to (non-negative) matrix theory and Markov chains.

## Tags
quiver, strongly connected, connectivity, components
-/

namespace Quiver

section Connected

/-- Strong reachability: every pair of vertices is connected by some path (length ≥ 0). -/
def IsStronglyConnected (V : Type*) [Quiver V] : Prop :=
  ∀ i j : V, Nonempty (Path i j)

/-- A quiver is strongly connected if for any two vertices there exists a path of positive
length between them. -/
def IsStronglyConnectedPos (V : Type*) [Quiver V] : Prop :=
  ∀ i j : V, Nonempty { p : Path i j // p.length > 0 }

/-- Expand `IsStronglyConnectedPos` to an existential over paths with positive length. -/
lemma isStronglyConnectedPos_iff_forall_exists_pos_length_path
    (V : Type*) [Quiver V] :
    IsStronglyConnectedPos V ↔ ∀ i j : V, ∃ p : Path i j, 0 < p.length := by
  constructor
  · intro h i j
    obtain ⟨⟨p, hp⟩⟩ := h i j
    exact ⟨p, hp⟩
  · intro h i j
    obtain ⟨p, hp⟩ := h i j
    exact ⟨⟨p, hp⟩⟩

/-- From strong connectivity with positive paths, get a path of positive length from `i` to `j`. -/
lemma exists_pos_length_path_of_isStronglyConnectedPos
    {V : Type*} [Quiver V] (h : IsStronglyConnectedPos V) (i j : V) :
    ∃ p : Path i j, 0 < p.length :=
  (isStronglyConnectedPos_iff_forall_exists_pos_length_path V).1 h i j

/-- From strong connectivity with positive paths, get a cycle of positive length at any vertex. -/
lemma exists_pos_length_cycle_of_isStronglyConnectedPos
    {V : Type*} [Quiver V] (h : IsStronglyConnectedPos V) (i : V) :
    ∃ p : Path i i, 0 < p.length :=
  exists_pos_length_path_of_isStronglyConnectedPos h i i

/-- Equivalence relation for strong connectivity: each direction has a path. -/
def stronglyConnectedSetoid (V : Type*) [Quiver V] : Setoid V :=
  ⟨fun a b => (Nonempty (Path a b)) ∧ (Nonempty (Path b a)),
   fun _ => ⟨⟨Path.nil⟩, ⟨Path.nil⟩⟩,
   fun ⟨hab, hba⟩ => ⟨hba, hab⟩,
   fun ⟨hab, hba⟩ ⟨hbc, hcb⟩ => ⟨⟨hab.some.comp hbc.some⟩, ⟨hcb.some.comp hba.some⟩⟩⟩

/-- Strongly connected components of a quiver. -/
def StronglyConnectedComponent (V : Type*) [Quiver V] : Type _ :=
  Quotient (stronglyConnectedSetoid V)

namespace StronglyConnectedComponent

variable {V} [Quiver V]

/-- The strongly connected component in which a vertex lives. -/
protected def mk : V → StronglyConnectedComponent V :=
  @Quotient.mk' _ (stronglyConnectedSetoid V)

instance : CoeTC V (StronglyConnectedComponent V) := ⟨StronglyConnectedComponent.mk⟩

instance [Inhabited V] : Inhabited (StronglyConnectedComponent V) := ⟨(default : V)⟩

protected lemma eq (a b : V) :
  (a : StronglyConnectedComponent V) = b
    ↔ (Nonempty (Path a b) ∧ Nonempty (Path b a)) :=
  Quotient.eq''

@[simp]
lemma mk_eq_mk {a b : V} :
    (StronglyConnectedComponent.mk a : StronglyConnectedComponent V) =
    StronglyConnectedComponent.mk b ↔
    (Nonempty (Path a b) ∧ Nonempty (Path b a)) :=
  StronglyConnectedComponent.eq a b

/-- In a strongly connected quiver with positive paths, every vertex has a self-loop
    (possibly of length > 1) -/
lemma exists_self_path_of_isStronglyConnectedPos {V : Type*} [Quiver V]
    (h : IsStronglyConnectedPos V) (v : V) :
    ∃ p : Path v v, 0 < p.length := by
  exact exists_pos_length_cycle_of_isStronglyConnectedPos h v

/-- Strong connectivity is transitive -/
lemma isStronglyConnected_transitive {V : Type*} [Quiver V]
    (a b c : V) :
    Nonempty (Path a b) → Nonempty (Path b c) → Nonempty (Path a c) :=
  fun ⟨p⟩ ⟨q⟩ => ⟨p.comp q⟩

/-- If there's a path in both directions, vertices are in the same SCC -/
lemma stronglyConnectedComponent_eq_of_path {V : Type*} [Quiver V] {a b : V}
    (hab : Nonempty (Path a b)) (hba : Nonempty (Path b a)) :
    (a : StronglyConnectedComponent V) = b :=
  (StronglyConnectedComponent.eq a b).2 ⟨hab, hba⟩

/-- Vertices in the same SCC have paths in both directions -/
lemma exists_path_of_stronglyConnectedComponent_eq {V : Type*} [Quiver V] {a b : V}
    (h : (a : StronglyConnectedComponent V) = b) :
    (Nonempty (Path a b)) ∧ (Nonempty (Path b a)) :=
  (StronglyConnectedComponent.eq a b).1 h

/-- A vertex forms a singleton strongly connected component iff
    no other vertex has bidirectional paths with it -/
lemma stronglyConnectedComponent_singleton_iff {V : Type*} [Quiver V] (v : V) :
    (∀ w : V, (w : StronglyConnectedComponent V) = v → w = v) ↔
    (∀ w : V, w ≠ v → ¬(Nonempty (Path v w) ∧ Nonempty (Path w v))) := by
  constructor
  · intro h_singleton w hw_ne h_bidir
    obtain ⟨hab, hba⟩ := h_bidir
    have h_same_scc : (w : StronglyConnectedComponent V) = v :=
      stronglyConnectedComponent_eq_of_path hba hab
    have : w = v := h_singleton w h_same_scc
    exact hw_ne this
  · intro h_no_bidir w h_same_scc
    by_contra hw_ne
    obtain ⟨hab, hba⟩ := exists_path_of_stronglyConnectedComponent_eq h_same_scc
    grind

/-- Strong connectivity implies weak connectivity -/
lemma isPreconnected_of_isStronglyConnected {V : Type*} [Quiver V]
    (h : IsStronglyConnected V) : IsPreconnected V :=
  h

/-- Strong connectivity implies preconnectivity of the symmetrification -/
lemma isPreconnected_symmetrify_of_isStronglyConnected {V : Type*} [Quiver V]
    (h : IsStronglyConnected V) : @IsPreconnected (Symmetrify V) _ := by
  intro a b
  obtain ⟨p⟩ := h a b
  -- Convert the path in V to a path in Symmetrify V using forward edges
  induction p with
  | nil => exact ⟨Path.nil⟩
  | cons q e ih => exact ⟨ih.some.cons (Sum.inl e)⟩

/-- If every vertex can reach every other vertex in the symmetrification,
    then we have weak connectivity -/
lemma weakly_connected_of_preconnected_symmetrify {V : Type*} [Quiver V]
    (h : @IsPreconnected (Symmetrify V) _) :
    ∀ a b : V, Nonempty (@Path (Symmetrify V) _ a b) := h

/-- Strong connectivity of a quiver implies its symmetrification is preconnected.
    The converse is false in general. -/
lemma isStronglyConnected_implies_symmetrify_preconnected {V : Type*} [Quiver V] :
    IsStronglyConnected V → @IsPreconnected (Symmetrify V) _ :=
  isPreconnected_symmetrify_of_isStronglyConnected

/-- A strongly connected quiver with positive paths is also strongly connected
    in the usual sense -/
lemma isStronglyConnected_of_pos {V : Type*} [Quiver V]
    (h : IsStronglyConnectedPos V) : IsStronglyConnected V := by
  intro i j
  obtain ⟨p, _⟩ := exists_pos_length_path_of_isStronglyConnectedPos h i j
  exact ⟨p⟩

/-- If a strongly connected quiver has at least one edge, then it satisfies
    strong connectivity with positive paths -/
lemma isStronglyConnectedPos_of_hasEdge {V : Type*} [Quiver V]
    (h_sc : IsStronglyConnected V)
    (h_edge : ∃ (i j : V), Nonempty (i ⟶ j)) :
    IsStronglyConnectedPos V := by
  obtain ⟨i₀, j₀, ⟨e₀⟩⟩ := h_edge
  intro i j
  obtain ⟨p₁⟩ := h_sc i i₀
  obtain ⟨p₂⟩ := h_sc j₀ j
  let p : Path i j := p₁.comp (e₀.toPath.comp p₂)
  have hp_pos : 0 < p.length := by
    simp [p, Path.length_comp]
    exact Nat.pos_of_neZero (p₁.length + (1 + p₂.length))
  exact ⟨⟨p, hp_pos⟩⟩

end StronglyConnectedComponent

end Connected

end Quiver
