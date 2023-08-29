/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring

#align_import combinatorics.simple_graph.partition from "leanprover-community/mathlib"@"2303b3e299f1c75b07bceaaac130ce23044d1386"

/-!
# Graph partitions

This module provides an interface for dealing with partitions on simple graphs. A partition of
a graph `G`, with vertices `V`, is a set `P` of disjoint nonempty subsets of `V` such that:

* The union of the subsets in `P` is `V`.

* Each element of `P` is an independent set. (Each subset contains no pair of adjacent vertices.)

Graph partitions are graph colorings that do not name their colors.  They are adjoint in the
following sense. Given a graph coloring, there is an associated partition from the set of color
classes, and given a partition, there is an associated graph coloring from using the partition's
subsets as colors.  Going from graph colorings to partitions and back makes a coloring "canonical":
all colors are given a canonical name and unused colors are removed.  Going from partitions to
graph colorings and back is the identity.

## Main definitions

* `SimpleGraph.Partition` is a structure to represent a partition of a simple graph

* `SimpleGraph.Partition.PartsCardLe` is whether a given partition is an `n`-partition.
  (a partition with at most `n` parts).

* `SimpleGraph.Partitionable n` is whether a given graph is `n`-partite

* `SimpleGraph.Partition.toColoring` creates colorings from partitions

* `SimpleGraph.Coloring.toPartition` creates partitions from colorings

## Main statements

* `SimpleGraph.partitionable_iff_colorable` is that `n`-partitionability and
  `n`-colorability are equivalent.

-/


universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-- A `Partition` of a simple graph `G` is a structure constituted by
* `parts`: a set of subsets of the vertices `V` of `G`
* `isPartition`: a proof that `parts` is a proper partition of `V`
* `independent`: a proof that each element of `parts` doesn't have a pair of adjacent vertices
-/
structure Partition where
  /-- `parts`: a set of subsets of the vertices `V` of `G`. -/
  parts : Set (Set V)
  /-- `isPartition`: a proof that `parts` is a proper partition of `V`. -/
  isPartition : Setoid.IsPartition parts
  /-- `independent`: a proof that each element of `parts` doesn't have a pair of adjacent vertices.
-/
  independent : ∀ s ∈ parts, IsAntichain G.Adj s
#align simple_graph.partition SimpleGraph.Partition

/-- Whether a partition `P` has at most `n` parts. A graph with a partition
satisfying this predicate called `n`-partite. (See `SimpleGraph.Partitionable`.) -/
def Partition.PartsCardLe {G : SimpleGraph V} (P : G.Partition) (n : ℕ) : Prop :=
  ∃ h : P.parts.Finite, h.toFinset.card ≤ n
#align simple_graph.partition.parts_card_le SimpleGraph.Partition.PartsCardLe

/-- Whether a graph is `n`-partite, which is whether its vertex set
can be partitioned in at most `n` independent sets. -/
def Partitionable (n : ℕ) : Prop := ∃ P : G.Partition, P.PartsCardLe n
#align simple_graph.partitionable SimpleGraph.Partitionable

namespace Partition

variable {G} (P : G.Partition)

/-- The part in the partition that `v` belongs to -/
def partOfVertex (v : V) : Set V := Classical.choose (P.isPartition.2 v)
#align simple_graph.partition.part_of_vertex SimpleGraph.Partition.partOfVertex

theorem partOfVertex_mem (v : V) : P.partOfVertex v ∈ P.parts := by
  obtain ⟨h, -⟩ := (P.isPartition.2 v).choose_spec.1
  -- ⊢ partOfVertex P v ∈ P.parts
  exact h
  -- 🎉 no goals
#align simple_graph.partition.part_of_vertex_mem SimpleGraph.Partition.partOfVertex_mem

theorem mem_partOfVertex (v : V) : v ∈ P.partOfVertex v := by
  obtain ⟨⟨h1, h2⟩, _h3⟩ := (P.isPartition.2 v).choose_spec
  -- ⊢ v ∈ partOfVertex P v
  exact h2.1
  -- 🎉 no goals
#align simple_graph.partition.mem_part_of_vertex SimpleGraph.Partition.mem_partOfVertex

theorem partOfVertex_ne_of_adj {v w : V} (h : G.Adj v w) : P.partOfVertex v ≠ P.partOfVertex w := by
  intro hn
  -- ⊢ False
  have hw := P.mem_partOfVertex w
  -- ⊢ False
  rw [← hn] at hw
  -- ⊢ False
  exact P.independent _ (P.partOfVertex_mem v) (P.mem_partOfVertex v) hw (G.ne_of_adj h) h
  -- 🎉 no goals
#align simple_graph.partition.part_of_vertex_ne_of_adj SimpleGraph.Partition.partOfVertex_ne_of_adj

/-- Create a coloring using the parts themselves as the colors.
Each vertex is colored by the part it's contained in. -/
def toColoring : G.Coloring P.parts :=
  Coloring.mk (fun v ↦ ⟨P.partOfVertex v, P.partOfVertex_mem v⟩) fun hvw ↦ by
    rw [Ne.def, Subtype.mk_eq_mk]
    -- ⊢ ¬partOfVertex P v✝ = partOfVertex P w✝
    exact P.partOfVertex_ne_of_adj hvw
    -- 🎉 no goals
#align simple_graph.partition.to_coloring SimpleGraph.Partition.toColoring

/-- Like `SimpleGraph.Partition.toColoring` but uses `Set V` as the coloring type. -/
def toColoring' : G.Coloring (Set V) :=
  Coloring.mk P.partOfVertex fun hvw ↦ P.partOfVertex_ne_of_adj hvw
#align simple_graph.partition.to_coloring' SimpleGraph.Partition.toColoring'

theorem to_colorable [Fintype P.parts] : G.Colorable (Fintype.card P.parts) :=
  P.toColoring.to_colorable
#align simple_graph.partition.to_colorable SimpleGraph.Partition.to_colorable

end Partition

variable {G}

/-- Creates a partition from a coloring. -/
@[simps]
def Coloring.toPartition {α : Type v} (C : G.Coloring α) : G.Partition
    where
  parts := C.colorClasses
  isPartition := C.colorClasses_isPartition
  independent := by
    rintro s ⟨c, rfl⟩
    -- ⊢ IsAntichain G.Adj {x | Setoid.Rel (Setoid.ker ↑C) x c}
    apply C.color_classes_independent
    -- 🎉 no goals
#align simple_graph.coloring.to_partition SimpleGraph.Coloring.toPartition

/-- The partition where every vertex is in its own part. -/
@[simps]
instance : Inhabited (Partition G) := ⟨G.selfColoring.toPartition⟩

theorem partitionable_iff_colorable {n : ℕ} : G.Partitionable n ↔ G.Colorable n := by
  constructor
  -- ⊢ Partitionable G n → Colorable G n
  · rintro ⟨P, hf, hc⟩
    -- ⊢ Colorable G n
    have : Fintype P.parts := hf.fintype
    -- ⊢ Colorable G n
    rw [Set.Finite.card_toFinset hf] at hc
    -- ⊢ Colorable G n
    apply P.to_colorable.mono hc
    -- 🎉 no goals
  · rintro ⟨C⟩
    -- ⊢ Partitionable G n
    refine' ⟨C.toPartition, C.colorClasses_finite, le_trans _ (Fintype.card_fin n).le⟩
    -- ⊢ Finset.card (Set.Finite.toFinset (_ : Set.Finite (Coloring.colorClasses C))) …
    generalize_proofs h
    -- ⊢ Finset.card (Set.Finite.toFinset h) ≤ Fintype.card (Fin n)
    haveI : Fintype C.colorClasses := C.colorClasses_finite.fintype
    -- ⊢ Finset.card (Set.Finite.toFinset h) ≤ Fintype.card (Fin n)
    rw [h.card_toFinset]
    -- ⊢ Fintype.card ↑(Coloring.colorClasses C) ≤ Fintype.card (Fin n)
    exact C.card_colorClasses_le
    -- 🎉 no goals
#align simple_graph.partitionable_iff_colorable SimpleGraph.partitionable_iff_colorable

end SimpleGraph
