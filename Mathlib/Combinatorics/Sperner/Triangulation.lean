/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/

import Mathlib.Combinatorics.Sperner.Basic
import Mathlib.Data.Finset.Sort

/-!
# SimplicialComplex to CellComplex Bridge for Sperner's Lemma

This file bridges the gap between simplicial complexes and our
abstract `CellComplex` structure from `Sperner.Basic`.

## The Architecture

Part 1 (done in Sperner.Basic): Abstract `CellComplex`
  with adjacency axioms, and the Sperner parity theorem proved
  for any `CellComplex`.

Part 2 (this file): Show that a triangulation of the standard
  simplex satisfying a pseudomanifold condition gives rise to a
  `CellComplex` instance.

## Strategy

We define a `Triangulation` structure that axiomatizes exactly
what we need: a finite pure simplicial complex with the
pseudomanifold property. The structure has the same fields as
`CellComplex` plus vertex injectivity, so the bridge is
immediate.

We also define `AbstractSimplicialData` for constructing a
`Triangulation` from unordered simplices (as in Mathlib's
`Geometry.SimplicialComplex`), and provide a concrete 1-d
interval example with fully proved axioms.

## Main definitions

* `Triangulation V n`: A triangulation with ordered vertices.
* `Triangulation.toCellComplex`: The `CellComplex` instance.
* `AbstractSimplicialData V n`: Unordered simplicial data.
* `intervalTriangulation m`: Concrete 1-d example.

## Main results

* `Triangulation.sperner`: Sperner's lemma for triangulations.
* Interval triangulation: all axioms fully proved (0 sorries).

## References

* [M. De Longueville, *A Course in Topological Combinatorics*]
* Yael Dillies, mathlib4#25231, mathlib4#34310

## Tags

Sperner, simplicial complex, triangulation, cell complex, bridge
-/

open Finset

/-! ## Triangulation Structure

We axiomatize a finite pure simplicial complex with the
pseudomanifold property. This is the minimal interface needed
to construct a `CellComplex`.

The key insight: `Triangulation` has exactly the same fields as
`CellComplex` plus `vertex_injective`, so the bridge construction
`toCellComplex` is trivial (just forget the extra field). -/

/-- A `Triangulation V n` is a finite collection of
top-dimensional simplices (each an ordered `(n+1)`-tuple of
vertices from `V`) satisfying the pseudomanifold condition:
each codimension-1 face belongs to at most 2 top simplices.

This is the minimal abstraction needed to instantiate
`CellComplex` and apply the abstract Sperner theorem. -/
structure Triangulation (V : Type*) [DecidableEq V]
    (n : ℕ) where
  /-- The type of top-dimensional cells (n-simplices). -/
  Cell : Type
  /-- Decidable equality on cells. -/
  cellDecEq : DecidableEq Cell
  /-- Finiteness of cells. -/
  cellFintype : Fintype Cell
  /-- The ordered vertices of each cell: vertex k is the k-th
  vertex of cell s. Each cell has n+1 distinct vertices. -/
  vertex : Cell → Fin (n + 1) → V
  /-- Vertices within a single cell are distinct. -/
  vertex_injective : ∀ s, Function.Injective (vertex s)
  /-- Pseudomanifold adjacency: for each cell s and face
  position k, either there is a unique neighboring cell s'
  sharing the codim-1 face, or the face is on the boundary. -/
  adj : Cell → Fin (n + 1) → Option (Cell × Fin (n + 1))
  /-- Adjacency is symmetric. -/
  adj_symm : ∀ s k s' k',
    adj s k = some (s', k') → adj s' k' = some (s, k)
  /-- Adjacent cells share the codimension-1 face. -/
  adj_vertex : ∀ s k s' k',
    adj s k = some (s', k') →
    (univ.erase k).image (vertex s) =
    (univ.erase k').image (vertex s')
  /-- Adjacent cells are distinct. -/
  adj_ne : ∀ s k s' k',
    adj s k = some (s', k') → s ≠ s'

attribute [instance] Triangulation.cellDecEq
attribute [instance] Triangulation.cellFintype

namespace Triangulation

variable {V : Type*} [DecidableEq V] {n : ℕ}

/-! ## CellComplex Instance

The bridge is immediate: `Triangulation` extends `CellComplex`
with `vertex_injective`, so we just forget it. -/

/-- Every `Triangulation` gives rise to a `CellComplex`. -/
def toCellComplex (T : Triangulation V n) : CellComplex V n where
  Cell := T.Cell
  cellDecEq := T.cellDecEq
  cellFintype := T.cellFintype
  vertex := T.vertex
  adj := T.adj
  adj_symm := T.adj_symm
  adj_vertex := T.adj_vertex
  adj_ne := T.adj_ne

/-! ## Sperner Coloring and Main Theorem -/

/-- A Sperner coloring: if vertex v is on face k (determined by
the predicate `onFace`), then `c v` is not `k`. -/
def IsSpernerColoring
    (c : V → Fin (n + 1))
    (onFace : V → Fin (n + 1) → Prop) : Prop :=
  ∀ v k, onFace v k → c v ≠ k

/-- **Sperner's Lemma for Triangulations**: Given a triangulation
whose boundary doors are odd, a panchromatic cell exists.

This is a direct application of the abstract `CellComplex.sperner`
theorem via the `toCellComplex` bridge. -/
theorem sperner (T : Triangulation V n)
    (c : V → Fin (n + 1))
    (hbdry : Odd (Finset.univ.filter
      (fun p : T.Cell × Fin (n + 1) =>
        CellComplex.IsDoor c (T.toCellComplex) p.1 p.2 ∧
        T.adj p.1 p.2 = none)).card) :
    ∃ s : T.Cell,
      CellComplex.IsPanchromatic c (T.toCellComplex) s :=
  CellComplex.sperner c T.toCellComplex hbdry

/-! ## Boundary Door Parity

The key geometric fact for the standard simplex: with a Sperner
coloring, boundary doors are odd. This decomposes by face and
uses induction on dimension.

We state this with explicit hypotheses that can be discharged
for any concrete triangulation. -/

/-- **Boundary door parity for triangulations**: Given
decomposition hypotheses about boundary doors on each geometric
face, the total boundary door count is odd.

The hypotheses separate doors by which geometric face they lie
on. Doors on faces 0 through n-1 pair up (even), and doors on
face n are odd (by induction). -/
theorem boundary_doors_odd (T : Triangulation V n)
    (c : V → Fin (n + 1))
    (onFace : V → Fin (n + 1) → Prop)
    [∀ v k, Decidable (onFace v k)]
    (_hSperner : IsSpernerColoring c onFace)
    (_hBoundaryOnFace : ∀ s k, T.adj s k = none →
      ∃ faceIdx : Fin (n + 1), ∀ j : Fin (n + 1),
        j ≠ k → onFace (T.vertex s j) faceIdx)
    (_hLowerDim : ∀ faceIdx : Fin (n + 1),
      faceIdx.val < n →
      Even (Finset.univ.filter (fun p : T.Cell × Fin (n + 1) =>
        CellComplex.IsDoor c (T.toCellComplex) p.1 p.2 ∧
        T.adj p.1 p.2 = none ∧
        (∀ j : Fin (n + 1), j ≠ p.2 →
          onFace (T.vertex p.1 j) faceIdx))).card)
    (_hLastFace : Odd (Finset.univ.filter
      (fun p : T.Cell × Fin (n + 1) =>
        CellComplex.IsDoor c (T.toCellComplex) p.1 p.2 ∧
        T.adj p.1 p.2 = none ∧
        (∀ j : Fin (n + 1), j ≠ p.2 →
          onFace (T.vertex p.1 j)
            ⟨n, by omega⟩))).card) :
    Odd (Finset.univ.filter
      (fun p : T.Cell × Fin (n + 1) =>
        CellComplex.IsDoor c (T.toCellComplex) p.1 p.2 ∧
        T.adj p.1 p.2 = none)).card := by
  -- Strategy: show S = S_n (every boundary door must be on the last face)
  -- then |S| = |S_n| is odd by _hLastFace.
  --
  -- Key insight: if a boundary door (s,k) is on face faceIdx with faceIdx.val < n,
  -- the Sperner condition contradicts the door condition (IsDoor requires color
  -- faceIdx on some non-k vertex, but Sperner forbids it).
  suffices h : Finset.univ.filter
      (fun p : T.Cell × Fin (n + 1) =>
        CellComplex.IsDoor c (T.toCellComplex) p.1 p.2 ∧
        T.adj p.1 p.2 = none) =
    Finset.univ.filter
      (fun p : T.Cell × Fin (n + 1) =>
        CellComplex.IsDoor c (T.toCellComplex) p.1 p.2 ∧
        T.adj p.1 p.2 = none ∧
        (∀ j : Fin (n + 1), j ≠ p.2 →
          onFace (T.vertex p.1 j) ⟨n, by omega⟩)) by
    rw [h]; exact _hLastFace
  -- Prove the two filter sets are equal
  ext ⟨s, k⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · -- S ⊆ S_n: every boundary door is on the last face
    intro ⟨hDoor, hAdj⟩
    refine ⟨hDoor, hAdj, ?_⟩
    -- By _hBoundaryOnFace, this door is on some face faceIdx
    obtain ⟨faceIdx, hOnFace⟩ := _hBoundaryOnFace s k hAdj
    -- Show faceIdx = ⟨n, _⟩ by contradiction
    by_cases hlt : faceIdx.val < n
    · -- Contradiction: IsDoor requires color faceIdx on some non-k vertex,
      -- but Sperner forbids it since all non-k vertices are on face faceIdx
      exfalso
      -- IsDoor at color index ⟨faceIdx.val, hlt⟩ : Fin n gives a witness
      have hDoor' := hDoor ⟨faceIdx.val, hlt⟩
      obtain ⟨i, hi_ne, hi_color⟩ := hDoor'
      -- Vertex i is on face faceIdx (since i ≠ k)
      have hOnFace_i := hOnFace i hi_ne
      -- Sperner says c(vertex s i) ≠ faceIdx
      have hSperner_i := _hSperner (T.vertex s i) faceIdx hOnFace_i
      -- But hi_color says c(vertex s i) = castSucc ⟨faceIdx.val, hlt⟩ = faceIdx
      -- T.toCellComplex.vertex = T.vertex by definition
      change c (T.vertex s i) = _ at hi_color
      -- castSucc ⟨faceIdx.val, hlt⟩ = faceIdx since faceIdx.val < n < n+1
      have hcast : (⟨faceIdx.val, hlt⟩ : Fin n).castSucc = faceIdx :=
        Fin.ext rfl
      rw [hcast] at hi_color
      exact hSperner_i hi_color
    · -- faceIdx.val ≥ n, and faceIdx : Fin (n+1) so faceIdx.val ≤ n
      -- Therefore faceIdx.val = n, so faceIdx = ⟨n, _⟩
      have heq : faceIdx.val = n := by omega
      have hfaceIdx : faceIdx = ⟨n, by omega⟩ := Fin.ext heq
      rw [hfaceIdx] at hOnFace
      exact hOnFace
  · -- S_n ⊆ S: dropping the extra condition
    intro ⟨hDoor, hAdj, _⟩
    exact ⟨hDoor, hAdj⟩

/-! ## Construction from Unordered Simplices

When starting from unordered simplices (Mathlib's
`Geometry.SimplicialComplex` uses `Finset V`), we need a
`LinearOrder V` to produce ordered vertices via `Finset.sort`.

`AbstractSimplicialData` packages this construction. -/

/-- Unordered simplicial data: a finite set of top simplices
with the pseudomanifold property. -/
structure AbstractSimplicialData (V : Type*) [DecidableEq V]
    [LinearOrder V] (n : ℕ) where
  /-- The top-dimensional simplices. -/
  topSimplices : Finset (Finset V)
  /-- Each top simplex has exactly n+1 vertices. -/
  card_eq : ∀ s ∈ topSimplices, s.card = n + 1
  /-- Pseudomanifold: each codim-1 face is in at most 2 top
  simplices. -/
  pseudomanifold : ∀ (face : Finset V),
    face.card = n →
    (topSimplices.filter (fun s => face ⊆ s)).card ≤ 2

/-!
## Face Helper Library

Named helpers for working with codimension-1 faces of top
simplices. These factor out the key operations needed to
construct adjacency for `toTriangulation`. -/

section FaceHelpers

variable {V : Type} [DecidableEq V] [LinearOrder V] {n : ℕ}
variable (D : AbstractSimplicialData V n)

/-- The ordered vertex enumeration of a top simplex. -/
noncomputable def AbstractSimplicialData.vertexEnum
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) : V :=
  (s.sort (· ≤ ·)).get (k.cast (by rw [Finset.length_sort]; exact (D.card_eq s hs).symm))

/-- The k-th vertex is a member of the simplex. -/
lemma AbstractSimplicialData.vertexEnum_mem
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    D.vertexEnum s hs k ∈ s := by
  unfold vertexEnum
  have hmem := List.get_mem (s.sort (· ≤ ·))
    (k.cast (by rw [Finset.length_sort]; exact (D.card_eq s hs).symm))
  exact (s.mem_sort (· ≤ ·)).mp hmem

/-- The codimension-1 face obtained by deleting the k-th vertex. -/
noncomputable def AbstractSimplicialData.faceOf
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) : Finset V :=
  s.erase (D.vertexEnum s hs k)

/-- A face has cardinality n. -/
lemma AbstractSimplicialData.faceOf_card
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    (D.faceOf s hs k).card = n := by
  simp only [faceOf]
  rw [Finset.card_erase_of_mem (D.vertexEnum_mem s hs k)]
  have := D.card_eq s hs
  omega

/-- A face is a subset of the simplex. -/
lemma AbstractSimplicialData.faceOf_subset
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    D.faceOf s hs k ⊆ s :=
  Finset.erase_subset _ _

/-- Top simplices containing a given face. -/
noncomputable def AbstractSimplicialData.containersOf
    (f : Finset V) : Finset (Finset V) :=
  D.topSimplices.filter (fun t => f ⊆ t)

/-- The original simplex contains its own face. -/
lemma AbstractSimplicialData.self_mem_containersOf
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    s ∈ D.containersOf (D.faceOf s hs k) := by
  simp only [containersOf, Finset.mem_filter]
  exact ⟨hs, D.faceOf_subset s hs k⟩

/-- Container count is at most 2 (pseudomanifold). -/
lemma AbstractSimplicialData.containersOf_card_le_two
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    (D.containersOf (D.faceOf s hs k)).card ≤ 2 :=
  D.pseudomanifold _ (D.faceOf_card s hs k)

/-- Container count is 1 or 2. -/
lemma AbstractSimplicialData.containersOf_card_one_or_two
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    (D.containersOf (D.faceOf s hs k)).card = 1 ∨
    (D.containersOf (D.faceOf s hs k)).card = 2 := by
  have h1 : 0 < (D.containersOf (D.faceOf s hs k)).card :=
    Finset.card_pos.mpr ⟨s, D.self_mem_containersOf s hs k⟩
  have h2 := D.containersOf_card_le_two s hs k
  omega

/-- The difference `t \ f` is nonempty when `t` has `n+1` elements
and `f` has `n` elements with `f ⊆ t`. -/
lemma AbstractSimplicialData.sdiff_nonempty
    (t : Finset V) (ht : t ∈ D.topSimplices)
    (f : Finset V) (_hf : f ⊆ t) (hfc : f.card = n) :
    (t \ f).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have hsub := Finset.sdiff_eq_empty_iff_subset.mp h
  have := D.card_eq t ht
  have := Finset.card_le_card hsub
  omega

/-- Given a top simplex `t` containing face `f`, find the index
in `t`'s sorted vertex list of the unique vertex in `t \ f`.
Returns the position of the "opposite" vertex. -/
noncomputable def AbstractSimplicialData.findOppositeIdx
    (t : Finset V) (ht : t ∈ D.topSimplices)
    (f : Finset V) (_hf : f ⊆ t) (hfc : f.card = n) :
    Fin (n + 1) :=
  -- There exists k such that vertexEnum t ht k is not in f.
  -- Since t has n+1 vertices and f has n with f ⊆ t, at least one
  -- vertex of t is not in f.
  have hex : ∃ k : Fin (n + 1), D.vertexEnum t ht k ∉ f := by
    by_contra hall
    push_neg at hall
    -- Every vertex of t is in f, so t ⊆ f
    have hsub : t ⊆ f := by
      intro v hv
      -- v is in t, so v appears somewhere in t.sort
      have hv_sort : v ∈ t.sort (· ≤ ·) := (t.mem_sort (· ≤ ·)).mpr hv
      rw [List.mem_iff_getElem] at hv_sort
      obtain ⟨idx, hidx_lt, hidx_eq⟩ := hv_sort
      have hidx_lt' : idx < n + 1 := by
        rwa [Finset.length_sort, D.card_eq t ht] at hidx_lt
      have hmem := hall ⟨idx, hidx_lt'⟩
      -- vertexEnum t ht ⟨idx, hidx_lt'⟩ = (t.sort (· ≤ ·)).get (cast ⟨idx, ...⟩)
      -- which equals (t.sort (· ≤ ·))[idx] = v
      -- Use the fact that vertexEnum_mem gives us membership
      -- and that vertexEnum at index idx equals (t.sort ...)[idx]
      have heq : D.vertexEnum t ht ⟨idx, hidx_lt'⟩ = v := by
        simp only [vertexEnum, List.get_eq_getElem]
        exact hidx_eq
      rwa [heq] at hmem
    have := Finset.card_le_card hsub
    rw [D.card_eq t ht, hfc] at this
    omega
  hex.choose

/-- The opposite vertex is not in the face. -/
lemma AbstractSimplicialData.vertexEnum_findOppositeIdx_not_mem
    (t : Finset V) (ht : t ∈ D.topSimplices)
    (f : Finset V) (hf : f ⊆ t) (hfc : f.card = n) :
    D.vertexEnum t ht (D.findOppositeIdx t ht f hf hfc) ∉ f := by
  unfold findOppositeIdx
  generalize_proofs hex
  exact hex.choose_spec

/-- Erasing the opposite vertex from t gives back f. -/
lemma AbstractSimplicialData.erase_opposite_eq
    (t : Finset V) (ht : t ∈ D.topSimplices)
    (f : Finset V) (hf : f ⊆ t) (hfc : f.card = n) :
    t.erase (D.vertexEnum t ht (D.findOppositeIdx t ht f hf hfc)) = f := by
  set v := D.vertexEnum t ht (D.findOppositeIdx t ht f hf hfc) with hv_def
  have hv_not_f : v ∉ f := D.vertexEnum_findOppositeIdx_not_mem t ht f hf hfc
  have hv_mem_t : v ∈ t := D.vertexEnum_mem t ht (D.findOppositeIdx t ht f hf hfc)
  have h_sub : f ⊆ t.erase v := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun h => hv_not_f (h ▸ hx), hf hx⟩
  have h_card : (t.erase v).card ≤ f.card := by
    rw [Finset.card_erase_of_mem hv_mem_t, D.card_eq t ht, hfc]
    omega
  exact (Finset.eq_of_subset_of_card_le h_sub h_card).symm

/-- The vertex enumeration of a top simplex is injective. -/
lemma AbstractSimplicialData.vertexEnum_injective
    (s : Finset V) (hs : s ∈ D.topSimplices) :
    Function.Injective (D.vertexEnum s hs) := by
  intro i j hij
  have hnd : (s.sort (· ≤ ·)).Nodup := s.sort_nodup (· ≤ ·)
  set L := s.sort (· ≤ ·) with hL_def
  set i' : Fin L.length := i.cast (by rw [hL_def, Finset.length_sort]; exact (D.card_eq s hs).symm)
  set j' : Fin L.length := j.cast (by rw [hL_def, Finset.length_sort]; exact (D.card_eq s hs).symm)
  have hi'j' : L.get i' = L.get j' := hij
  have key : (i' : ℕ) = (j' : ℕ) := by
    rw [List.nodup_iff_injective_get] at hnd
    exact Fin.val_eq_of_eq (hnd hi'j')
  exact Fin.ext key

/-- The vertex enumeration covers all of s. -/
lemma AbstractSimplicialData.vertexEnum_image_univ
    (s : Finset V) (hs : s ∈ D.topSimplices) :
    Finset.univ.image (D.vertexEnum s hs) = s := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, rfl⟩; exact D.vertexEnum_mem s hs k
  · intro hv
    have hv_sort : v ∈ s.sort (· ≤ ·) := (s.mem_sort (· ≤ ·)).mpr hv
    rw [List.mem_iff_getElem] at hv_sort
    obtain ⟨idx, hidx_lt, hidx_eq⟩ := hv_sort
    have hidx_lt' : idx < n + 1 := by
      rwa [Finset.length_sort, D.card_eq s hs] at hidx_lt
    exact ⟨⟨idx, hidx_lt'⟩, by show (s.sort (· ≤ ·)).get _ = v; simp only [List.get_eq_getElem]; exact hidx_eq⟩

/-- Image of `univ.erase k` under vertexEnum equals faceOf. -/
lemma AbstractSimplicialData.vertexEnum_image_erase
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    (Finset.univ.erase k).image (D.vertexEnum s hs) = D.faceOf s hs k := by
  have hinj := D.vertexEnum_injective s hs
  ext v
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
             faceOf, Finset.mem_erase]
  constructor
  · rintro ⟨j, hj_ne, rfl⟩
    exact ⟨fun h => hj_ne (hinj h), D.vertexEnum_mem s hs j⟩
  · rintro ⟨hne, hv⟩
    have hv_sort : v ∈ s.sort (· ≤ ·) := (s.mem_sort (· ≤ ·)).mpr hv
    rw [List.mem_iff_getElem] at hv_sort
    obtain ⟨idx, hidx_lt, hidx_eq⟩ := hv_sort
    have hidx_lt' : idx < n + 1 := by
      rwa [Finset.length_sort, D.card_eq s hs] at hidx_lt
    refine ⟨⟨idx, hidx_lt'⟩, ?_, ?_⟩
    · intro heq
      apply hne
      have : D.vertexEnum s hs ⟨idx, hidx_lt'⟩ = v := by
        show (s.sort (· ≤ ·)).get _ = v; simp only [List.get_eq_getElem]; exact hidx_eq
      rw [← this, heq]
    · show (s.sort (· ≤ ·)).get _ = v; simp only [List.get_eq_getElem]; exact hidx_eq

/-- Unfold faceOf. -/
lemma AbstractSimplicialData.faceOf_eq
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n+1)) :
    D.faceOf s hs k = s.erase (D.vertexEnum s hs k) := rfl

/-- Vertex j is not in face k iff j = k.
The forward direction: if vertexEnum j is not in s.erase(vertexEnum k),
then vertexEnum j = vertexEnum k (since vertexEnum j ∈ s), hence j = k by injectivity.
The backward direction: vertexEnum k ∉ s.erase(vertexEnum k) by Finset.not_mem_erase. -/
lemma AbstractSimplicialData.vertexEnum_not_mem_faceOf_iff
    (s : Finset V) (hs : s ∈ D.topSimplices) (j k : Fin (n+1)) :
    D.vertexEnum s hs j ∉ D.faceOf s hs k ↔ j = k := by
  simp only [faceOf, Finset.mem_erase, not_and_or, not_not]
  constructor
  · intro h
    cases h with
    | inl h => exact D.vertexEnum_injective s hs h
    | inr h => exact absurd (D.vertexEnum_mem s hs j) h
  · intro h; left; congr 1

/-- findOppositeIdx of the face obtained by removing vertex k gives back k.
Since the only vertex not in faceOf s hs k is vertexEnum s hs k (at index k),
and findOppositeIdx picks such an index, it must pick k. -/
lemma AbstractSimplicialData.findOppositeIdx_eq
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n+1)) :
    D.findOppositeIdx s hs (D.faceOf s hs k) (D.faceOf_subset s hs k) (D.faceOf_card s hs k) = k := by
  set idx := D.findOppositeIdx s hs (D.faceOf s hs k) (D.faceOf_subset s hs k) (D.faceOf_card s hs k)
  have h_not_mem : D.vertexEnum s hs idx ∉ D.faceOf s hs k :=
    D.vertexEnum_findOppositeIdx_not_mem s hs (D.faceOf s hs k) (D.faceOf_subset s hs k) (D.faceOf_card s hs k)
  exact (D.vertexEnum_not_mem_faceOf_iff s hs idx k).mp h_not_mem

end FaceHelpers

/-!
## Adjacency Construction

We define adjacency for `AbstractSimplicialData.toTriangulation`
using the face helper library. For each cell `(s, hs)` and face
index `k`:
1. Compute face `f = D.faceOf s hs k`
2. Compute containers `cs = D.containersOf f`
3. If `cs.card = 1`: boundary face, return `none`
4. If `cs.card = 2`: find the other simplex `t != s` in `cs`,
   compute the opposite index in `t`, return `some (t, k')`
-/

/-- The adjacency function for `toTriangulation`. Factored out to
enable standalone reasoning about adj = some results. -/
noncomputable def AbstractSimplicialData.adjFn
    {V : Type} [DecidableEq V] [LinearOrder V] {n : ℕ}
    (D : AbstractSimplicialData V n)
    (p : { s : Finset V // s ∈ D.topSimplices })
    (k : Fin (n + 1)) :
    Option ({ s : Finset V // s ∈ D.topSimplices } × Fin (n + 1)) :=
  let f := D.faceOf p.1 p.2 k
  let cs := D.containersOf f
  if _hc : cs.card ≤ 1 then
    none
  else
    let cs_without_s := cs.erase p.1
    if ht_exists : cs_without_s.Nonempty then
      let t := ht_exists.choose
      have ht_mem_erase : t ∈ cs_without_s := ht_exists.choose_spec
      have ht_mem_cs : t ∈ cs := Finset.mem_of_mem_erase ht_mem_erase
      have ht_top : t ∈ D.topSimplices := (Finset.mem_filter.mp ht_mem_cs).1
      have hf_sub_t : f ⊆ t := (Finset.mem_filter.mp ht_mem_cs).2
      let k' := D.findOppositeIdx t ht_top f hf_sub_t (D.faceOf_card p.1 p.2 k)
      some (⟨t, ht_top⟩, k')
    else
      none

/-- When `adjFn` returns `some`, the shared face sets are equal. -/
lemma AbstractSimplicialData.adjFn_vertex
    {V : Type} [DecidableEq V] [LinearOrder V] {n : ℕ}
    (D : AbstractSimplicialData V n)
    (s : Finset V) (hs : s ∈ D.topSimplices)
    (k : Fin (n + 1))
    (s' : Finset V) (hs' : s' ∈ D.topSimplices)
    (k' : Fin (n + 1))
    (hadj : D.adjFn ⟨s, hs⟩ k = some (⟨s', hs'⟩, k')) :
    (Finset.univ.erase k).image (D.vertexEnum s hs) =
    (Finset.univ.erase k').image (D.vertexEnum s' hs') := by
  -- Unfold adjFn to expose the dite structure
  unfold adjFn at hadj
  simp only at hadj
  -- split_ifs produces 3 cases from the nested dite; the happy path
  -- (hc false, hne true) comes first as `case pos`
  split_ifs at hadj with hc hne
  · -- Happy path: ¬(cs.card ≤ 1) and (cs.erase s).Nonempty
    -- hadj : some (⟨t, _⟩, k_adj) = some (⟨s', hs'⟩, k')
    -- Extract the Subtype and Fin equalities
    simp only [Option.some.injEq, Prod.mk.injEq] at hadj
    obtain ⟨hs'_sub_eq, hk'_eq⟩ := hadj
    -- hs'_sub_eq : ⟨Exists.choose ..., ...⟩ = ⟨s', hs'⟩ (subtype equality)
    -- Extract value equality from subtype equality
    have hs'_val : s' = hne.choose := (Subtype.ext_iff.mp hs'_sub_eq).symm
    -- Both sides equal faceOf s hs k
    set f := D.faceOf s hs k
    -- LHS = faceOf s hs k
    have hLHS : (Finset.univ.erase k).image (D.vertexEnum s hs) = f :=
      D.vertexEnum_image_erase s hs k
    -- Extract neighbor data from hne (the Nonempty proof)
    have ht_mem_erase := hne.choose_spec
    have ht_mem_cs : hne.choose ∈ D.containersOf f :=
      Finset.mem_of_mem_erase ht_mem_erase
    have ht_top : hne.choose ∈ D.topSimplices :=
      (Finset.mem_filter.mp ht_mem_cs).1
    have hf_sub_t : f ⊆ hne.choose :=
      (Finset.mem_filter.mp ht_mem_cs).2
    -- RHS = faceOf s' hs' k' = f
    -- We prove this by showing both sides reduce to f
    have hRHS : (Finset.univ.erase k').image (D.vertexEnum s' hs') = f := by
      rw [D.vertexEnum_image_erase s' hs' k']
      -- Goal: faceOf s' hs' k' = f, i.e., s'.erase (vertexEnum s' hs' k') = f
      simp only [faceOf]
      subst hs'_val
      -- After subst: s' = hne.choose
      -- Goal: hne.choose.erase (vertexEnum hne.choose hs' k') = f
      -- k' comes from hk'_eq: findOppositeIdx ... = k'
      -- Rewrite k' back to findOppositeIdx
      rw [← hk'_eq]
      -- Goal: hne.choose.erase (vertexEnum hne.choose hs' (findOppositeIdx ...)) = f
      -- The findOppositeIdx and vertexEnum use proof terms that may differ from ht_top
      -- but by proof irrelevance they compute the same value
      -- Use erase_opposite_eq: t.erase (vertexEnum t ht (findOppositeIdx t ht f hf hfc)) = f
      -- We need to match: vertexEnum hne.choose hs' (findOppositeIdx with other proofs)
      -- = vertexEnum hne.choose ht_top (findOppositeIdx hne.choose ht_top f hf_sub_t ...)
      -- All proof arguments are interchangeable by proof irrelevance
      exact D.erase_opposite_eq hne.choose ht_top f hf_sub_t (D.faceOf_card s hs k)
    rw [hLHS, hRHS]

/-- When adjFn returns some, the containers of the face have exactly 2 elements. -/
lemma AbstractSimplicialData.containersOf_card_eq_two_of_adjFn
    {V : Type} [DecidableEq V] [LinearOrder V] {n : ℕ}
    (D : AbstractSimplicialData V n)
    (s : Finset V) (hs : s ∈ D.topSimplices)
    (k : Fin (n + 1))
    (s' : Finset V) (hs' : s' ∈ D.topSimplices)
    (k' : Fin (n + 1))
    (hadj : D.adjFn ⟨s, hs⟩ k = some (⟨s', hs'⟩, k')) :
    (D.containersOf (D.faceOf s hs k)).card = 2 := by
  unfold adjFn at hadj
  simp only at hadj
  split_ifs at hadj with hc hne
  · have hcard := D.containersOf_card_one_or_two s hs k
    omega

/-- When adjFn returns some, the neighbor s' is in containersOf f. -/
lemma AbstractSimplicialData.adjFn_s'_mem_containers
    {V : Type} [DecidableEq V] [LinearOrder V] {n : ℕ}
    (D : AbstractSimplicialData V n)
    (s : Finset V) (hs : s ∈ D.topSimplices)
    (k : Fin (n + 1))
    (s' : Finset V) (hs' : s' ∈ D.topSimplices)
    (k' : Fin (n + 1))
    (hadj : D.adjFn ⟨s, hs⟩ k = some (⟨s', hs'⟩, k')) :
    s' ∈ D.containersOf (D.faceOf s hs k) := by
  simp only [containersOf, Finset.mem_filter]
  refine ⟨hs', ?_⟩
  unfold adjFn at hadj
  simp only at hadj
  split_ifs at hadj with hc hne
  · simp only [Option.some.injEq, Prod.mk.injEq] at hadj
    obtain ⟨hs'_sub_eq, _⟩ := hadj
    have hs'_val : s' = hne.choose := (Subtype.ext_iff.mp hs'_sub_eq).symm
    have ht_mem_erase := hne.choose_spec
    have ht_mem_cs : hne.choose ∈ D.containersOf (D.faceOf s hs k) :=
      Finset.mem_of_mem_erase ht_mem_erase
    rw [hs'_val]
    exact (Finset.mem_filter.mp ht_mem_cs).2

/-- When adjFn returns some, s' != s (as Finset values). -/
lemma AbstractSimplicialData.adjFn_ne
    {V : Type} [DecidableEq V] [LinearOrder V] {n : ℕ}
    (D : AbstractSimplicialData V n)
    (s : Finset V) (hs : s ∈ D.topSimplices)
    (k : Fin (n + 1))
    (s' : Finset V) (hs' : s' ∈ D.topSimplices)
    (k' : Fin (n + 1))
    (hadj : D.adjFn ⟨s, hs⟩ k = some (⟨s', hs'⟩, k')) :
    s' ≠ s := by
  unfold adjFn at hadj
  simp only at hadj
  split_ifs at hadj with hc hne
  · simp only [Option.some.injEq, Prod.mk.injEq] at hadj
    obtain ⟨hs'_sub_eq, _⟩ := hadj
    have hs'_val : s' = hne.choose := (Subtype.ext_iff.mp hs'_sub_eq).symm
    have ht_mem_erase := hne.choose_spec
    have ht_ne_s : hne.choose ≠ s := (Finset.mem_erase.mp ht_mem_erase).1
    rw [hs'_val]
    exact ht_ne_s

/-- When adjFn returns some, faceOf s' hs' k' = faceOf s hs k. -/
lemma AbstractSimplicialData.adjFn_face_eq
    {V : Type} [DecidableEq V] [LinearOrder V] {n : ℕ}
    (D : AbstractSimplicialData V n)
    (s : Finset V) (hs : s ∈ D.topSimplices)
    (k : Fin (n + 1))
    (s' : Finset V) (hs' : s' ∈ D.topSimplices)
    (k' : Fin (n + 1))
    (hadj : D.adjFn ⟨s, hs⟩ k = some (⟨s', hs'⟩, k')) :
    D.faceOf s' hs' k' = D.faceOf s hs k := by
  have himg := D.adjFn_vertex s hs k s' hs' k' hadj
  rw [D.vertexEnum_image_erase s hs k, D.vertexEnum_image_erase s' hs' k'] at himg
  exact himg.symm

/-- When adjFn returns some from s, adjFn from s' returns s. -/
lemma AbstractSimplicialData.adjFn_symm
    {V : Type} [DecidableEq V] [LinearOrder V] {n : ℕ}
    (D : AbstractSimplicialData V n)
    (s : Finset V) (hs : s ∈ D.topSimplices)
    (k : Fin (n + 1))
    (s' : Finset V) (hs' : s' ∈ D.topSimplices)
    (k' : Fin (n + 1))
    (hadj : D.adjFn ⟨s, hs⟩ k = some (⟨s', hs'⟩, k')) :
    D.adjFn ⟨s', hs'⟩ k' = some (⟨s, hs⟩, k) := by
  -- Key facts
  set f := D.faceOf s hs k with hf_def
  have hne : s' ≠ s := D.adjFn_ne s hs k s' hs' k' hadj
  have hface_eq : D.faceOf s' hs' k' = f := D.adjFn_face_eq s hs k s' hs' k' hadj
  have hs_cont : s ∈ D.containersOf f := D.self_mem_containersOf s hs k
  have hs'_cont : s' ∈ D.containersOf f := D.adjFn_s'_mem_containers s hs k s' hs' k' hadj
  have hcard2 : (D.containersOf f).card = 2 :=
    D.containersOf_card_eq_two_of_adjFn s hs k s' hs' k' hadj
  -- Step through the dite chain of adjFn ⟨s', hs'⟩ k'
  unfold adjFn
  simp only
  -- First branch: containers not small (card = 2 > 1)
  have hcs_not_le_1 : ¬((D.containersOf (D.faceOf s' hs' k')).card ≤ 1) := by
    rw [hface_eq]; omega
  rw [dif_neg hcs_not_le_1]
  -- Second branch: erase s' is nonempty (s is in there)
  have hne_erase : ((D.containersOf (D.faceOf s' hs' k')).erase s').Nonempty := by
    rw [hface_eq]
    exact ⟨s, Finset.mem_erase.mpr ⟨hne.symm, hs_cont⟩⟩
  rw [dif_pos hne_erase]
  -- Show hne_erase.choose = s (singleton argument)
  -- hne_erase.choose is in (containersOf (faceOf s' hs' k')).erase s'
  -- which equals (containersOf f).erase s' since faceOf s' hs' k' = f
  have ht_mem_f : hne_erase.choose ∈ (D.containersOf f).erase s' := by
    have h := hne_erase.choose_spec
    have hset_eq : (D.containersOf (D.faceOf s' hs' k')).erase s' =
        (D.containersOf f).erase s' := by rw [hface_eq]
    rw [← hset_eq]; exact h
  have ht_in_cs : hne_erase.choose ∈ D.containersOf f :=
    Finset.mem_of_mem_erase ht_mem_f
  have h_erase_card : ((D.containersOf f).erase s').card = 1 := by
    rw [Finset.card_erase_of_mem hs'_cont, hcard2]
  have hs_in_erase : s ∈ (D.containersOf f).erase s' :=
    Finset.mem_erase.mpr ⟨hne.symm, hs_cont⟩
  have ht_eq_s : hne_erase.choose = s := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h_erase_card
    have hs_a : s = a := Finset.mem_singleton.mp (ha ▸ hs_in_erase)
    have ht_a : hne_erase.choose = a := Finset.mem_singleton.mp (ha ▸ ht_mem_f)
    exact ht_a.trans hs_a.symm
  -- Prove the full equality via Option/Prod injectivity
  simp only [Option.some.injEq, Prod.mk.injEq]
  refine ⟨Subtype.ext ht_eq_s, ?_⟩
  -- Fin component: findOppositeIdx hne_erase.choose _ face _ _ = k
  -- Strategy: the vertex at the chosen index is not in the face.
  -- Since hne_erase.choose = s and face = faceOf s hs k, use List-level
  -- reasoning to show the index must be k.
  -- Fin component: findOppositeIdx hne_erase.choose ht' (faceOf s' hs' k') hf' hfc' = k
  -- Since hne_erase.choose = s and faceOf s' hs' k' = faceOf s hs k,
  -- the vertex at the result index is not in faceOf s hs k, so by
  -- vertexEnum_not_mem_faceOf_iff it must equal k.
  have h_idx_eq : ∀ (ht' : hne_erase.choose ∈ D.topSimplices)
      (hf' : D.faceOf s' hs' k' ⊆ hne_erase.choose)
      (hfc' : (D.faceOf s' hs' k').card = n),
      D.findOppositeIdx hne_erase.choose ht' (D.faceOf s' hs' k') hf' hfc' = k := by
    intro ht' hf' hfc'
    set idx := D.findOppositeIdx hne_erase.choose ht' (D.faceOf s' hs' k') hf' hfc'
    -- vertexEnum is determined by the Finset sort, not the membership proof
    have hve : D.vertexEnum hne_erase.choose ht' idx = D.vertexEnum s hs idx := by
      simp [AbstractSimplicialData.vertexEnum, ht_eq_s]
    -- Vertex at idx is not in faceOf s' hs' k' = faceOf s hs k
    have h_nmem : D.vertexEnum s hs idx ∉ D.faceOf s hs k := by
      have := D.vertexEnum_findOppositeIdx_not_mem hne_erase.choose ht' _ hf' hfc'
      rwa [hface_eq, hve] at this
    exact (D.vertexEnum_not_mem_faceOf_iff s hs idx k).mp h_nmem
  exact h_idx_eq _ _ _

/-- Construct a `Triangulation` from `AbstractSimplicialData`.
Uses `V : Type` (universe 0) to match `CellComplex.Cell : Type`.

All axioms fully proved: vertex_injective, adj_symm (via adjFn_symm),
adj_vertex (via adjFn_vertex), adj_ne (via adjFn_ne). -/
noncomputable def AbstractSimplicialData.toTriangulation
    {V : Type} [DecidableEq V] [LinearOrder V] {n : ℕ}
    (D : AbstractSimplicialData V n) :
    Triangulation V n where
  Cell := { s : Finset V // s ∈ D.topSimplices }
  cellDecEq := inferInstance
  cellFintype := Finset.Subtype.fintype D.topSimplices
  vertex := fun ⟨s, hs⟩ k => D.vertexEnum s hs k
  vertex_injective := by
    intro ⟨s, hs⟩ i j hij
    have hnd : (s.sort (· ≤ ·)).Nodup := s.sort_nodup (· ≤ ·)
    set L := s.sort (· ≤ ·) with hL_def
    set i' : Fin L.length := i.cast (by rw [hL_def, Finset.length_sort]; exact (D.card_eq s hs).symm)
    set j' : Fin L.length := j.cast (by rw [hL_def, Finset.length_sort]; exact (D.card_eq s hs).symm)
    have hi'j' : L.get i' = L.get j' := hij
    have key : (i' : ℕ) = (j' : ℕ) := by
      rw [List.nodup_iff_injective_get] at hnd
      exact Fin.val_eq_of_eq (hnd hi'j')
    exact Fin.ext key
  adj := D.adjFn
  adj_symm := by
    intro ⟨s, hs⟩ k ⟨s', hs'⟩ k' hadj
    exact D.adjFn_symm s hs k s' hs' k' hadj
  adj_vertex := by
    intro ⟨s, hs⟩ k ⟨s', hs'⟩ k' hadj
    exact D.adjFn_vertex s hs k s' hs' k' hadj
  adj_ne := by
    intro ⟨s, hs⟩ k ⟨s', hs'⟩ k' hadj heq
    have hval : s = s' := congr_arg Subtype.val heq
    exact (D.adjFn_ne s hs k s' hs' k' hadj) hval.symm

/-! ## Example: 1-Dimensional Interval Triangulation

A subdivision of an interval into m segments, with all
`CellComplex` axioms fully proved (no sorries).

Vertices are natural numbers {0, 1, ..., m}. Cell i (for
i : Fin m) is the edge [i, i+1] with:
  vertex 0 = i
  vertex 1 = i + 1

Adjacency:
- Face opposite vertex 0 of cell i = {i+1}
  = face opposite vertex 1 of cell (i+1)
  So adj i 0 = some (i+1, 1) when i+1 < m
- Face opposite vertex 1 of cell i = {i}
  = face opposite vertex 0 of cell (i-1)
  So adj i 1 = some (i-1, 0) when 0 < i
-/

section Interval

variable {m : ℕ}

/-- Vertex map for the interval triangulation. -/
private def ivtx (_ : 0 < m) (i : Fin m) (k : Fin 2) : ℕ :=
  if k.val = 0 then i.val else i.val + 1

/-- Adjacency for the interval triangulation. Defined as an
opaque `if/dite` chain. -/
private def iadj (m : ℕ) (i : Fin m)
    (k : Fin 2) : Option (Fin m × Fin 2) :=
  if hk : k.val = 0 then
    if h : i.val + 1 < m then
      some (⟨i.val + 1, h⟩, ⟨1, by omega⟩)
    else
      none
  else
    if h : 0 < i.val then
      some (⟨i.val - 1, by omega⟩, ⟨0, by omega⟩)
    else
      none

/-- Extract data from iadj = some. -/
private lemma iadj_cases {s s' : Fin m}
    {k k' : Fin 2}
    (hadj : iadj m s k = some (s', k')) :
    (k.val = 0 ∧ s'.val = s.val + 1 ∧ k'.val = 1 ∧
      s.val + 1 < m) ∨
    (k.val ≠ 0 ∧ s'.val = s.val - 1 ∧ k'.val = 0 ∧
      0 < s.val) := by
  unfold iadj at hadj
  by_cases hk : k.val = 0
  · -- k.val = 0
    rw [dif_pos hk] at hadj
    by_cases h : s.val + 1 < m
    · rw [dif_pos h] at hadj
      left
      simp only [Option.some.injEq, Prod.mk.injEq] at hadj
      obtain ⟨hs'_eq, hk'_eq⟩ := hadj
      exact ⟨hk,
        by have := congr_arg Fin.val hs'_eq; simp at this; omega,
        by have := congr_arg Fin.val hk'_eq; simp at this; omega,
        h⟩
    · rw [dif_neg h] at hadj; exact Option.noConfusion hadj
  · -- k.val ≠ 0
    rw [dif_neg hk] at hadj
    by_cases h : (0 : ℕ) < s.val
    · rw [dif_pos h] at hadj
      right
      simp only [Option.some.injEq, Prod.mk.injEq] at hadj
      obtain ⟨hs'_eq, hk'_eq⟩ := hadj
      exact ⟨hk,
        by have := congr_arg Fin.val hs'_eq; simp at this; omega,
        by have := congr_arg Fin.val hk'_eq; simp at this; omega,
        h⟩
    · rw [dif_neg h] at hadj; exact Option.noConfusion hadj

private lemma iadj_symm' {s s' : Fin m}
    {k k' : Fin 2}
    (hadj : iadj m s k = some (s', k')) :
    iadj m s' k' = some (s, k) := by
  obtain (⟨hk, hs', hk', hlt⟩ | ⟨hk, hs', hk', hpos⟩) :=
    iadj_cases hadj
  · -- k.val=0, s'=s+1, k'.val=1: need iadj m s' k' = some (s, k)
    -- i.e. iadj m ⟨s.val+1,_⟩ ⟨1,_⟩ = some (s, ⟨0,_⟩)
    -- which reduces to: 0 < s'.val → some (⟨s'.val-1,_⟩, ⟨0,_⟩)
    show iadj m s' k' = some (s, k)
    unfold iadj
    have : ¬(k'.val = 0) := by omega
    rw [dif_neg this]
    have : (0 : ℕ) < s'.val := by omega
    rw [dif_pos this]
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
  · -- k.val≠0, s'=s-1, k'.val=0: need iadj m s' k' = some (s, k)
    show iadj m s' k' = some (s, k)
    unfold iadj
    have : k'.val = 0 := by omega
    rw [dif_pos this]
    have : s'.val + 1 < m := by omega
    rw [dif_pos this]
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩

private lemma iadj_ne' {s s' : Fin m}
    {k k' : Fin 2}
    (hadj : iadj m s k = some (s', k')) :
    s ≠ s' := by
  obtain (⟨_, hs', _, _⟩ | ⟨_, hs', _, _⟩) := iadj_cases hadj
  · intro heq; have := congr_arg Fin.val heq; omega
  · intro heq; have := congr_arg Fin.val heq; omega

private lemma iadj_vertex' {hm : 0 < m} {s s' : Fin m}
    {k k' : Fin 2}
    (hadj : iadj m s k = some (s', k')) :
    (univ.erase k).image (ivtx hm s) =
    (univ.erase k').image (ivtx hm s') := by
  obtain (⟨hk, hs', hk', _⟩ | ⟨hk, hs', hk', _⟩) :=
    iadj_cases hadj
  · -- k.val=0, s'=s+1, k'.val=1
    have hkeq : k = ⟨0, by omega⟩ := Fin.ext hk
    have hk'eq : k' = ⟨1, by omega⟩ := Fin.ext hk'
    rw [hkeq, hk'eq]
    ext v; constructor
    · intro hv
      rw [mem_image] at hv ⊢
      obtain ⟨a, ha_mem, ha_eq⟩ := hv
      rw [mem_erase] at ha_mem
      have ha1 : a.val = 1 := by have := a.isLt; omega
      refine ⟨⟨0, by omega⟩,
        mem_erase.mpr ⟨by omega, mem_univ _⟩, ?_⟩
      rw [show a = ⟨1, by omega⟩ from Fin.ext ha1] at ha_eq
      simp [ivtx] at ha_eq ⊢; omega
    · intro hv
      rw [mem_image] at hv ⊢
      obtain ⟨a, ha_mem, ha_eq⟩ := hv
      rw [mem_erase] at ha_mem
      have ha0 : a.val = 0 := by have := a.isLt; omega
      refine ⟨⟨1, by omega⟩,
        mem_erase.mpr ⟨by omega, mem_univ _⟩, ?_⟩
      rw [show a = ⟨0, by omega⟩ from Fin.ext ha0] at ha_eq
      simp [ivtx] at ha_eq ⊢; omega
  · -- k.val≠0 (so k.val=1), s'=s-1, k'.val=0
    have hk1 : k.val = 1 := by have := k.isLt; omega
    have hkeq : k = ⟨1, by omega⟩ := Fin.ext hk1
    have hk'eq : k' = ⟨0, by omega⟩ := Fin.ext hk'
    rw [hkeq, hk'eq]
    ext v; constructor
    · intro hv
      rw [mem_image] at hv ⊢
      obtain ⟨a, ha_mem, ha_eq⟩ := hv
      rw [mem_erase] at ha_mem
      have ha0 : a.val = 0 := by have := a.isLt; omega
      refine ⟨⟨1, by omega⟩,
        mem_erase.mpr ⟨by omega, mem_univ _⟩, ?_⟩
      rw [show a = ⟨0, by omega⟩ from Fin.ext ha0] at ha_eq
      simp [ivtx] at ha_eq ⊢; omega
    · intro hv
      rw [mem_image] at hv ⊢
      obtain ⟨a, ha_mem, ha_eq⟩ := hv
      rw [mem_erase] at ha_mem
      have ha1 : a.val = 1 := by have := a.isLt; omega
      refine ⟨⟨0, by omega⟩,
        mem_erase.mpr ⟨by omega, mem_univ _⟩, ?_⟩
      rw [show a = ⟨1, by omega⟩ from Fin.ext ha1] at ha_eq
      simp [ivtx] at ha_eq ⊢; omega

/-- A subdivision of [0,m] into m unit intervals, as a
`Triangulation Nat 1`. All axioms fully proved. -/
def intervalTriangulation (m : ℕ) (hm : 0 < m) :
    Triangulation ℕ 1 where
  Cell := Fin m
  cellDecEq := inferInstance
  cellFintype := inferInstance
  vertex := ivtx hm
  vertex_injective := by
    intro i a b hab
    simp only [ivtx] at hab
    fin_cases a <;> fin_cases b <;> simp_all
  adj := iadj m
  adj_symm := fun s k s' k' hadj => iadj_symm' hadj
  adj_vertex := fun s k s' k' hadj => iadj_vertex' hadj
  adj_ne := fun s k s' k' hadj => iadj_ne' hadj

end Interval

/-! ## Interval Sperner's Lemma

As a sanity check, we state the 1-d Sperner theorem for the
interval triangulation and prove it via the abstract theorem. -/

/-- 1-d Sperner's lemma for intervals: if the boundary doors
are odd, a panchromatic cell exists. -/
theorem interval_sperner (m : ℕ) (hm : 0 < m)
    (c : ℕ → Fin 2)
    (hbdry : Odd (Finset.univ.filter
      (fun p : Fin m × Fin 2 =>
        CellComplex.IsDoor c
          (intervalTriangulation m hm).toCellComplex p.1 p.2 ∧
        (intervalTriangulation m hm).adj p.1 p.2 = none)).card) :
    ∃ s : Fin m,
      CellComplex.IsPanchromatic c
        (intervalTriangulation m hm).toCellComplex s :=
  Triangulation.sperner (intervalTriangulation m hm) c hbdry

end Triangulation
