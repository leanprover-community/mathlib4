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

/-- Vertices of `mapPath` on the inclusion lie in `S`. -/
lemma mapPath_inducePrefunctor_mem_vertices {v : V} (p : Path i j)
    (hv : v ∈ ((inducePrefunctor S).mapPath p).vertices) : v ∈ S := by
  induction p with
  | nil =>
    rw [Prefunctor.mapPath_nil, vertices_nil, List.mem_singleton] at hv
    exact hv ▸ i.property
  | cons p' e ih =>
    simp only [Prefunctor.mapPath_cons, vertices_cons, List.concat_eq_append,
      List.mem_append, List.mem_singleton] at hv
    rcases hv with h | rfl
    · exact ih h
    · exact Subtype.coe_prop _

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
