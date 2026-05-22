/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer

# The dual Langer graph: line-collinearity of GH(2,2)

The split Cayley hexagon GH(2,2) has 63 points and 63 lines, with incidence
graph the Tutte 12-cage (126 vertices, cubic, girth 12). The **Langer graph**
is the point-collinearity graph: p ~ q iff they share a line (distance-2 in
the Tutte 12-cage restricted to points).

The **dual Langer graph** is the line-collinearity graph: l₁ ~ l₂ iff they
share a point (distance-2 restricted to lines). It has the same intersection
array {6, 4, 4; 1, 1, 3} as the Langer graph but is **not isomorphic** to it.

## Why GH(2,2) is not self-dual

A generalized hexagon GH(q, q) is self-dual if and only if q is a power of 3
(Cohen–Tits). Since q = 2 is not a power of 3, the split Cayley hexagon H(2)
and its dual H(2)^D are non-isomorphic as geometries, though they share the
same incidence graph. Their collinearity graphs (the Langer and dual Langer
graphs) have identical intersection arrays but are non-isomorphic.

## The distinguishing invariant

For any vertex v, the subgraph induced on vertices at graph distance 3 is:
  - **Connected** in the Langer graph (1 component of 32 vertices)
  - **Disconnected** in the dual Langer graph (2 components of 16 vertices)

This is a graph invariant: any isomorphism φ : G ≃g H preserves graph
distances and hence connectivity of distance shells. The d₃-connectivity
therefore provides a computable certificate of non-isomorphism.

## Group-theoretic interpretation

G₂(2) has two non-conjugate maximal subgroups of order 192:
  - Point stabiliser: (SL(2,3) : C₄) : C₂ → Langer graph on G₂(2)/H₁₉₂
  - Line stabiliser: (((C₄ × C₄) : C₃) : C₂) : C₂ → dual Langer on G₂(2)/H'₁₉₂

Same group, non-conjugate stabilisers, non-isomorphic coset graphs.

## References

- Cohen, Tits, *On generalized hexagons and a near octagon whose lines have three points*
- Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798
- Brouwer–Cohen–Neumaier, *Distance-Regular Graphs* (1989), §6.5
-/

import Archive.LangerGraph
import Mathlib.Combinatorics.SimpleGraph.Maps

/-! ## The dual Langer graph -/

/-- Distance-2 adjacency on **lines**: two lines l₁, l₂ of GH(2,2) are
    adjacent iff they share a point. In the Tutte 12-cage, line vertices have
    indices 63–125, and a shared point means a common point-neighbor. -/
def dualLangerAdjBool (l₁ l₂ : Fin 63) : Bool :=
  l₁ != l₂ &&
  let lv₁ : Fin 126 := ⟨l₁.val + 63, by omega⟩
  let lv₂ : Fin 126 := ⟨l₂.val + 63, by omega⟩
  (List.finRange 63).any fun p =>
    let pv : Fin 126 := ⟨p.val, by omega⟩
    tutte12AdjBool pv lv₁ && tutte12AdjBool pv lv₂

set_option maxHeartbeats 400000 in
/-- The **dual Langer graph**: line-collinearity of GH(2,2).

    Two lines are adjacent iff they are concurrent (share a point).
    This is the distance-2 graph of the Tutte 12-cage restricted to
    line vertices, dual to the Langer graph (point-collinearity). -/
def dualLangerSimpleGraph : SimpleGraph (Fin 63) where
  Adj l₁ l₂ := dualLangerAdjBool l₁ l₂
  symm l₁ l₂ := by simp only [dualLangerAdjBool]; revert l₁ l₂; native_decide
  loopless := ⟨fun l => by simp only [dualLangerAdjBool]; revert l; native_decide⟩

instance dualLangerDecAdj : DecidableRel dualLangerSimpleGraph.Adj :=
  fun l₁ l₂ => inferInstanceAs (Decidable (dualLangerAdjBool l₁ l₂))

/-! ## Basic properties — same parameters as Langer -/

/-- The dual Langer graph is 6-regular: each line meets 6 other lines. -/
theorem dualLanger_regular :
    ∀ v : Fin 63, (Finset.univ.filter fun w => dualLangerSimpleGraph.Adj v w).card = 6 := by
  native_decide

/-- The dual Langer graph has 189 undirected edges. -/
theorem dualLanger_edges :
    (Finset.univ.filter fun p : Fin 63 × Fin 63 =>
      p.1 < p.2 ∧ dualLangerSimpleGraph.Adj p.1 p.2).card = 189 := by
  native_decide

/-- λ = 1: each pair of concurrent lines shares exactly 1 common neighbor. -/
theorem dualLanger_lambda :
    ∀ l₁ l₂ : Fin 63, dualLangerSimpleGraph.Adj l₁ l₂ →
      (Finset.univ.filter fun w =>
        dualLangerSimpleGraph.Adj l₁ w ∧ dualLangerSimpleGraph.Adj l₂ w).card = 1 := by
  native_decide

/-! ## The duality: both graphs are halved Tutte 12-cage

The Langer graph is the distance-2 graph on points (Tutte12Cage.lean).
The dual Langer graph is the distance-2 graph on lines. -/

/-- The dual Langer graph equals the distance-2 graph of the Tutte 12-cage
    restricted to line vertices (indices 63–125), mirroring the Langer graph's
    relationship to point vertices (indices 0–62). -/
theorem dualLanger_eq_tutte12_distance2_lines :
    ∀ l₁ l₂ : Fin 63,
      dualLangerSimpleGraph.Adj l₁ l₂ ↔ dualLangerAdjBool l₁ l₂ := by
  intro l₁ l₂; rfl

/-! ## The distinguishing invariant: d₃-subgraph connectivity

For a graph G on Fin n, the **d₃-subgraph** at vertex v is the subgraph
induced on vertices at graph distance exactly 3 from v. We compute this
via BFS and check connectivity. -/

section BFS

/-- BFS neighborhood expansion: the set of vertices reachable in exactly
    one step from a set S, excluding vertices in `visited`. -/
def bfsExpand (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S visited : Finset (Fin n)) : Finset (Fin n) :=
  S.biUnion (fun v => Finset.univ.filter (G.Adj v)) \ visited

/-- BFS layer computation: returns (layer_k, all_visited_through_k). -/
def bfsLayers (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : (depth : Nat) → Finset (Fin n) × Finset (Fin n)
  | 0 => ({v}, {v})
  | k + 1 =>
    let (prevLayer, prevVisited) := bfsLayers G v k
    let nextLayer := bfsExpand G prevLayer prevVisited
    (nextLayer, prevVisited ∪ nextLayer)

/-- The set of vertices at graph distance exactly `d` from `v`, computed by BFS. -/
def distanceLayer (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (d : Nat) : Finset (Fin n) :=
  (bfsLayers G v d).1

/-- Connectivity check via BFS on a subgraph induced by a vertex set.
    Returns `true` iff the induced subgraph is connected (or empty). -/
def isInducedConnectedBool (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) : Bool :=
  if h : S = ∅ then true
  else
    -- BFS from the first vertex of S, restricted to S
    let start := S.min' (Finset.nonempty_of_ne_empty h)
    let rec bfsReach (frontier visited : Finset (Fin n)) (fuel : Nat) : Finset (Fin n) :=
      match fuel with
      | 0 => visited
      | fuel + 1 =>
        let next := frontier.biUnion (fun v =>
          S.filter (fun w => v ≠ w && G.Adj v w)) \ visited
        if next = ∅ then visited
        else bfsReach next (visited ∪ next) fuel
    let reached := bfsReach {start} {start} S.card
    reached.card == S.card

/-- Is the d₃-subgraph at vertex v connected? -/
def isD3ConnectedBool (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : Bool :=
  isInducedConnectedBool G (distanceLayer G v 3)

/-- Number of connected components in the d₃-subgraph, computed by
    iterating BFS until all vertices are assigned a component. -/
def numD3Components (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : Nat :=
  let S := distanceLayer G v 3
  let rec countComps (remaining : Finset (Fin n)) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 =>
      if h : remaining = ∅ then 0
      else
        let start := remaining.min' (Finset.nonempty_of_ne_empty h)
        let rec bfsComp (frontier visited : Finset (Fin n)) (f2 : Nat) : Finset (Fin n) :=
          match f2 with
          | 0 => visited
          | f2 + 1 =>
            let next := frontier.biUnion (fun w =>
              remaining.filter (fun u => w ≠ u && G.Adj w u)) \ visited
            if next = ∅ then visited
            else bfsComp next (visited ∪ next) f2
        let comp := bfsComp {start} {start} remaining.card
        1 + countComps (remaining \ comp) fuel
  countComps S S.card

/-- BFS reach within a vertex set S: starting from `frontier`, expand
    to neighbors in S not yet visited, for `fuel` steps.
    Unlike `isInducedConnectedBool`, this is a top-level named function
    suitable for proving isomorphism invariance by induction. -/
def inducedBfsReach (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S frontier visited : Finset (Fin n)) : Nat → Finset (Fin n)
  | 0 => visited
  | fuel + 1 =>
    let next := frontier.biUnion (fun v =>
      S.filter (fun w => v ≠ w ∧ G.Adj v w)) \ visited
    if next = ∅ then visited
    else inducedBfsReach G S next (visited ∪ next) fuel

/-- All-pairs reachability within a vertex set S: every pair u, v ∈ S
    can reach each other via BFS restricted to S.
    This is a **starting-vertex-independent** connectivity predicate,
    unlike `isInducedConnectedBool` which starts from `S.min'`. -/
def AllPairsReachable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, v ∈ inducedBfsReach G S {u} {u} S.card

instance decAllPairsReachable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) : Decidable (AllPairsReachable G S) :=
  Finset.decidableBAll _ _

end BFS

/-! ## Computational verification of d₃-connectivity

We verify at vertex 0 (fast) and also at all 63 vertices (the universal
quantifier is needed for the non-isomorphism proof). -/

/-- The Langer graph has 32 vertices at distance 3 from vertex 0. -/
theorem langer_d3_size :
    (distanceLayer langerSimpleGraph 0 3).card = 32 := by
  native_decide

/-- The dual Langer graph has 32 vertices at distance 3 from vertex 0. -/
theorem dualLanger_d3_size :
    (distanceLayer dualLangerSimpleGraph 0 3).card = 32 := by
  native_decide

/-- The d₃-subgraph of the Langer graph is **connected** at every vertex. -/
theorem langer_d3_connected :
    ∀ v : Fin 63, isD3ConnectedBool langerSimpleGraph v = true := by
  native_decide

/-- The d₃-subgraph of the dual Langer graph is **disconnected** at every vertex.
    This is the key computational certificate for non-isomorphism. -/
theorem dualLanger_d3_not_connected :
    ∀ v : Fin 63, isD3ConnectedBool dualLangerSimpleGraph v = false := by
  native_decide

/-- The Langer d₃-subgraph has exactly 1 connected component at every vertex. -/
theorem langer_d3_num_components :
    ∀ v : Fin 63, numD3Components langerSimpleGraph v = 1 := by
  native_decide

/-- The dual Langer d₃-subgraph has exactly 2 connected components at every vertex. -/
theorem dualLanger_d3_num_components :
    ∀ v : Fin 63, numD3Components dualLangerSimpleGraph v = 2 := by
  native_decide

/-! ## All-pairs reachability: starting-vertex-independent connectivity

The `isAllPairsReachable` predicate checks every pair, so it doesn't
depend on `S.min'`. This makes it suitable for proving isomorphism
invariance without needing a BFS-start-independence lemma. -/

set_option maxHeartbeats 800000 in
/-- The Langer d₃-subgraph is all-pairs reachable at every vertex.
    Every pair of d₃-vertices can reach each other via BFS within d₃. -/
theorem langer_d3_allPairs :
    ∀ v : Fin 63, AllPairsReachable langerSimpleGraph
      (distanceLayer langerSimpleGraph v 3) := by
  native_decide

set_option maxHeartbeats 800000 in
/-- The dual Langer d₃-subgraph is NOT all-pairs reachable at any vertex.
    Some pair of d₃-vertices cannot reach each other via BFS within d₃. -/
theorem dualLanger_d3_not_allPairs :
    ∀ v : Fin 63, ¬ AllPairsReachable dualLangerSimpleGraph
      (distanceLayer dualLangerSimpleGraph v 3) := by
  native_decide

/-! ## Non-isomorphism

The d₃-subgraph connectivity is a graph invariant: an isomorphism φ : G ≃g H
maps BFS layers to BFS layers (since it preserves adjacency), hence maps
d₃-vertices to d₃-vertices, and preserves connectivity of the induced
d₃-subgraph. Since the Langer graph has connected d₃-subgraphs at every
vertex and the dual Langer has disconnected ones, no isomorphism can exist.

We prove the invariance by induction on BFS depth: φ commutes with
`bfsExpand` because it bijects neighbors and commutes with set difference
(being injective). -/

section NonIsomorphism

variable {n : Nat} {G H : SimpleGraph (Fin n)}
  [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- A graph isomorphism commutes with neighbor-set biUnion. -/
private theorem iso_biUnion_neighbors (φ : G ≃g H) (S : Finset (Fin n)) :
    (S.biUnion (fun v => Finset.univ.filter (G.Adj v))).image φ =
    (S.image φ).biUnion (fun v => Finset.univ.filter (H.Adj v)) := by
  ext w
  simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, ⟨v, hv, hvadj⟩, rfl⟩
    exact ⟨φ v, ⟨v, hv, rfl⟩, φ.map_adj_iff.mpr hvadj⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, hadj⟩
    exact ⟨φ.symm w, ⟨v, hv, by rwa [← φ.map_adj_iff, φ.apply_symm_apply]⟩,
           φ.apply_symm_apply w⟩

/-- A graph isomorphism commutes with `bfsExpand`. -/
private theorem iso_bfsExpand (φ : G ≃g H) (S visited : Finset (Fin n)) :
    (bfsExpand G S visited).image φ = bfsExpand H (S.image φ) (visited.image φ) := by
  unfold bfsExpand
  rw [Finset.image_sdiff _ _ φ.injective]
  congr 1
  exact iso_biUnion_neighbors φ S

/-- A graph isomorphism commutes with `bfsLayers`. -/
private theorem iso_bfsLayers (φ : G ≃g H) (v : Fin n) (d : Nat) :
    ((bfsLayers G v d).1).image φ = (bfsLayers H (φ v) d).1 ∧
    ((bfsLayers G v d).2).image φ = (bfsLayers H (φ v) d).2 := by
  induction d with
  | zero => simp [bfsLayers, Finset.image_singleton]
  | succ d ih =>
    simp only [bfsLayers]
    have hexp := iso_bfsExpand φ (bfsLayers G v d).1 (bfsLayers G v d).2
    rw [ih.1, ih.2] at hexp
    exact ⟨hexp, by rw [Finset.image_union, hexp, ih.2]⟩

/-- A graph isomorphism commutes with `distanceLayer`. -/
theorem iso_distanceLayer (φ : G ≃g H) (v : Fin n) (d : Nat) :
    (distanceLayer G v d).image φ = distanceLayer H (φ v) d :=
  (iso_bfsLayers φ v d).1

/-- A graph isomorphism commutes with restricted neighbor biUnion within S. -/
private theorem iso_induced_neighbors (φ : G ≃g H)
    (S frontier : Finset (Fin n)) :
    (frontier.biUnion (fun v => S.filter (fun w => v ≠ w ∧ G.Adj v w))).image φ =
    (frontier.image φ).biUnion (fun v =>
      (S.image φ).filter (fun w => v ≠ w ∧ H.Adj v w)) := by
  ext w
  simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨u, ⟨v, hv, hu_S, hne, hadj⟩, rfl⟩
    exact ⟨φ v, ⟨v, hv, rfl⟩, Finset.mem_image_of_mem φ hu_S,
           φ.injective.ne hne, φ.map_adj_iff.mpr hadj⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, hw_S', hne, hadj⟩
    rw [Finset.mem_image] at hw_S'
    obtain ⟨u, hu_S, rfl⟩ := hw_S'
    exact ⟨u, ⟨v, hv, hu_S, fun h => hne (congrArg φ h),
           φ.map_adj_iff.mp hadj⟩, rfl⟩

/-- A graph isomorphism commutes with `inducedBfsReach`.

    This is the key structural lemma: φ maps the BFS-within-S reach set
    bijectively to the corresponding reach set in the image graph.
    Proved by induction on fuel, using `iso_induced_neighbors` at each step. -/
private theorem iso_inducedBfsReach (φ : G ≃g H) (S frontier visited : Finset (Fin n))
    (fuel : Nat) :
    (inducedBfsReach G S frontier visited fuel).image φ =
    inducedBfsReach H (S.image φ) (frontier.image φ) (visited.image φ) fuel := by
  induction fuel generalizing frontier visited with
  | zero => simp [inducedBfsReach]
  | succ fuel ih =>
    simp only [inducedBfsReach]
    -- Abbreviate the next frontiers
    set nextG := frontier.biUnion (fun v =>
      S.filter (fun w => v ≠ w ∧ G.Adj v w)) \ visited with hNextG_def
    set nextH := (frontier.image φ).biUnion (fun v =>
      (S.image φ).filter (fun w => v ≠ w ∧ H.Adj v w)) \ (visited.image φ) with hNextH_def
    -- Key: φ maps nextG to nextH
    have hcomm : nextG.image φ = nextH := by
      simp only [hNextG_def, hNextH_def]
      rw [Finset.image_sdiff _ _ φ.injective]
      congr 1
      exact iso_induced_neighbors φ S frontier
    -- Both sides branch on emptiness, which agrees under φ
    by_cases h : nextG = ∅
    · -- Next frontier is empty: both sides return visited
      have hH : nextH = ∅ := by
        rw [← hcomm, Finset.image_eq_empty]; exact h
      simp [h, hH]
    · -- Next frontier is non-empty: recurse with updated sets
      have hH : nextH ≠ ∅ := by
        intro habs; rw [← hcomm, Finset.image_eq_empty] at habs; exact h habs
      simp only [h, ↓reduceIte, hH]
      rw [← hcomm, Finset.image_union]
      exact ih nextG (visited ∪ nextG)

/-- A graph isomorphism preserves `AllPairsReachable`.

    The key property: `AllPairsReachable` quantifies over ALL pairs in S,
    so it doesn't depend on `S.min'`. Under the bijection φ|_S : S → S.image φ,
    each pair (u, v) maps to (φ u, φ v), and reachability is preserved by
    `iso_inducedBfsReach`. -/
private theorem iso_AllPairsReachable (φ : G ≃g H) (S : Finset (Fin n)) :
    AllPairsReachable G S ↔ AllPairsReachable H (S.image φ) := by
  have hcard : (S.image φ).card = S.card :=
    Finset.card_image_of_injective S φ.injective
  -- Helper: iso_inducedBfsReach with singletons simplified
  have key : ∀ u, (inducedBfsReach G S {u} {u} S.card).image φ =
      inducedBfsReach H (S.image φ) {φ u} {φ u} S.card := by
    intro u
    have := iso_inducedBfsReach φ S {u} {u} S.card
    rwa [Finset.image_singleton, Finset.image_singleton] at this
  constructor
  · -- Forward: if all pairs reachable in G|S, then in H|S'
    intro h u' hu' v' hv'
    rw [Finset.mem_image] at hu' hv'
    obtain ⟨u, hu, rfl⟩ := hu'
    obtain ⟨v, hv, rfl⟩ := hv'
    rw [hcard, ← key]
    exact Finset.mem_image_of_mem φ (h u hu v hv)
  · -- Backward: if all pairs reachable in H|S', then in G|S
    intro h u hu v hv
    have hmem := h (φ u) (Finset.mem_image_of_mem φ hu) (φ v) (Finset.mem_image_of_mem φ hv)
    rw [hcard, ← key, Finset.mem_image] at hmem
    obtain ⟨w, hw, hφw⟩ := hmem
    rwa [φ.injective hφw] at hw

/-- The Langer and dual Langer graphs are **not isomorphic**.

    **Proof**: The `AllPairsReachable` predicate is a graph invariant:
    it checks ALL pairs via BFS within the d₃-set, making it independent
    of BFS starting vertex. We prove φ commutes with BFS reach sets
    (`iso_inducedBfsReach`), hence preserves all-pairs reachability.

    Computational verification shows this predicate holds for the Langer
    graph and fails for the dual Langer graph at every vertex.
    Under any hypothetical isomorphism φ, the d₃-set at 0 maps to the
    d₃-set at φ(0), but their all-pairs reachability disagrees. -/
theorem langer_not_iso_dualLanger :
    IsEmpty (langerSimpleGraph ≃g dualLangerSimpleGraph) := by
  rw [isEmpty_iff]
  intro φ
  have h1 := langer_d3_allPairs 0
  have h2 := dualLanger_d3_not_allPairs (φ 0)
  have h3 : AllPairsReachable dualLangerSimpleGraph
      (distanceLayer dualLangerSimpleGraph (φ 0) 3) := by
    rw [← iso_distanceLayer φ 0 3]
    exact (iso_AllPairsReachable φ _).mp h1
  exact h2 h3

end NonIsomorphism
