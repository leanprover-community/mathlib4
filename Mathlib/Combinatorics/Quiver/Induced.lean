/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Vertex-induced quivers

Given `S : Set V`, the induced quiver on `S` has an arrow `a ⟶ b` whenever `a.val ⟶ b.val`
in the ambient quiver. Cf. `SimpleGraph.induce` and `SimpleGraph.Walk.induce`.
-/

@[expose] public section

namespace Quiver

variable {V : Type*} [Quiver V] (S : Set V)

/-- The quiver on `S` induced by the ambient quiver on `V`. -/
@[reducible]
def induce : Quiver S :=
  ⟨fun a b => a.val ⟶ b.val⟩

attribute [local instance] induce

/-- Inclusion of the induced quiver into the ambient quiver. -/
def inducePrefunctor : Prefunctor S V where
  obj := Subtype.val
  map := id

namespace Path

variable {i j : S}

/-- The vertices of `mapPath` on the inclusion are those of the path, viewed in `V`. -/
lemma vertices_mapPath_inducePrefunctor (p : Path i j) :
    ((inducePrefunctor S).mapPath p).vertices = p.vertices.map Subtype.val :=
  vertices_mapPath _ p

/-- Vertices of `mapPath` on the inclusion lie in `S`. -/
lemma mapPath_inducePrefunctor_mem_vertices {v : V} (p : Path i j)
    (hv : v ∈ ((inducePrefunctor S).mapPath p).vertices) : v ∈ S := by
  rw [vertices_mapPath_inducePrefunctor, List.mem_map] at hv
  obtain ⟨w, -, rfl⟩ := hv
  exact w.property

/-- A path in `V` whose vertices stay in `S` induces a path in the induced quiver on `S`. -/
def induce {i j : V} (p : Path i j) (hp : ∀ k, k ∈ p.vertices → k ∈ S) :
    letI : Quiver S := Quiver.induce S
    Path (⟨i, hp i (start_mem_vertices p)⟩ : S) (⟨j, hp j (end_mem_vertices p)⟩ : S) := by
  letI : Quiver S := Quiver.induce S
  induction p with
  | nil => exact Path.nil
  | cons p' e ih => exact Path.cons (ih fun k hk ↦ hp k ((mem_vertices_cons p' e).2 (.inl hk))) e

end Path

end Quiver
