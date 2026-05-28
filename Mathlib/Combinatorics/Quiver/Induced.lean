/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Combinatorics.Quiver.Prefunctor

/-!
# Vertex-induced quivers

Given `S : Set V`, the induced quiver on `S` has an arrow `a ⟶ b` whenever `a.val ⟶ b.val`
in the ambient quiver. Cf. `SimpleGraph.induce` and `SimpleGraph.Walk.induce`.
-/

@[expose] public section

open Quiver

namespace Quiver

variable {V : Type*} [Quiver V] (S : Set V)

/-- The quiver on `S` induced by the ambient quiver on `V`. -/
@[reducible]
def induce : Quiver S :=
  ⟨fun a b => a.val ⟶ b.val⟩

end Quiver

namespace Quiver

variable {V : Type*} [Quiver V] (S : Set V)

attribute [local instance] induce

/-- Inclusion of the induced quiver into the ambient quiver. -/
def inducePrefunctor : Prefunctor S V where
  obj := Subtype.val
  map := id

namespace Path

open Quiver.Path

variable {i j : S}

/-- Vertices of `mapPath` on the inclusion lie in `S`. -/
lemma mapPath_inducePrefunctor_mem_vertices {v : V} (p : Path i j)
    (hv : v ∈ ((inducePrefunctor S).mapPath p).activeVertices) : v ∈ S := by
  induction p with
  | nil =>
    simp only [Prefunctor.mapPath_nil, activeVertices_nil, Set.mem_singleton_iff] at hv
    subst hv
    exact i.property
  | cons p' e ih =>
    simp only [Prefunctor.mapPath_cons, activeVertices_cons, Set.mem_union, Set.mem_singleton_iff] at hv
    rcases hv with h | h
    · exact ih h
    · subst h
      simpa [end_cons, inducePrefunctor] using j.property

/--
A path in `V` whose vertices stay in `S` induces a path in the induced quiver on `S`.
-/
noncomputable def induce {i j : V} (p : Path i j) (hp : ∀ k, k ∈ p.vertices → k ∈ S) :
    letI : Quiver S := Quiver.induce S
    Path (⟨i, hp i (start_mem_vertices p)⟩ : S) (⟨j, hp j (end_mem_vertices p)⟩ : S) := by
  letI : Quiver S := Quiver.induce S
  induction p with
  | nil => exact Path.nil
  | cons p' e ih =>
    exact Path.cons (ih fun k hk => hp k ((mem_vertices_cons p' e).mpr (Or.inl hk))) e

end Path

end Quiver
