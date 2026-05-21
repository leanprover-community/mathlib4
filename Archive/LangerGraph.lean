/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Action
import Mathlib.Combinatorics.SimpleGraph.Representation

/-!
# The Langer graph, the Tutte 12-cage, and the GH(2,2) ecosystem

The **Langer graph** is the collinearity graph of the split Cayley hexagon GH(2,2),
the unique generalized 6-gon over 𝔽₂. It has 63 vertices (the points of the parabolic
quadric Q(6,2) in PG(6,2)), is 6-regular with 189 edges, and is the unique
distance-regular graph with intersection array {6, 4, 4; 1, 1, 3}.

The **Tutte 12-cage** is the incidence graph of GH(2,2): 126 vertices
(63 points + 63 lines), 189 edges, girth 12. It is semisymmetric — edge-transitive
but not vertex-transitive — because no polarity exists for GH(2,2) over 𝔽₂.

The main result `langer_eq_tutte12_distance2` proves that the Langer graph (defined
algebraically via the Zorn product on Q(6,2)) equals the distance-2 graph of the
Tutte 12-cage restricted to points (defined combinatorially from the edge list).
The proof uses G₂(2) transitivity: both graphs are invariant under two generators
of G₂(2), so they agree everywhere if they agree at vertex 0.

## Main definitions

* `langerSimpleGraph` — the Langer graph on `Fin 63`, via Zorn product
* `tutte12CageGraph` — the Tutte 12-cage on `Fin 126`, via edge list
* `Q62form` — the quadratic form Q(x) = x₀x₄ + x₁x₅ + x₂x₆ + x₃² on 𝔽₂⁷
* `Q62_H` — the 7 × 63 parity-check matrix from Q(6,2)

## Main results

* `Q62_self_orthogonal` — H · Hᵀ = 0 over 𝔽₂
* `langer_regular` — the Langer graph is 6-regular
* `tutte12_bipartite` — the Tutte 12-cage is bipartite
* `langer_eq_tutte12_distance2'` — algebraic Langer = geometric distance-2
  (structural proof via G₂(2) transitivity)

## Visualizations

* [The Langer graph](https://raw.githubusercontent.com/RaggedR/symmetric-graphs/main/lean/named_graphs/langer-63v.jpg) — symmetry-aware drawing with 6-fold rotational layout
* [The Tutte 12-cage](https://raw.githubusercontent.com/RaggedR/symmetric-graphs/main/lean/named_graphs/tutte-12cage.jpg) — incidence graph of GH(2,2)

## References

* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798
* Benson, *Minimal regular graphs of girth 8 and 12*, Canad. J. Math. 18 (1966)
* Springer–Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*, §1.8
-/

set_option linter.style.nativeDecide false

open Matrix

/-! ## Part 1: The quadratic form Q(6,2) -/

/-- The quadratic form Q(x) = x₀x₄ + x₁x₅ + x₂x₆ + x₃² on 𝔽₂⁷.
Points of Q(6,2) are the nonzero vectors with Q(x) = 0. -/
def Q62form (x : Fin 7 → ZMod 2) : ZMod 2 :=
  x 0 * x 4 + x 1 * x 5 + x 2 * x 6 + x 3 * x 3

/-- Convert a natural number (1..127) to its bit vector in 𝔽₂⁷. -/
def toBitVec (n : Fin 128) : Fin 7 → ZMod 2 :=
  fun i => if n.val / (2 ^ i.val) % 2 = 0 then 0 else 1

/-- The list of indices (1..127) whose bit vectors lie on Q(6,2). -/
def q62Indices : List (Fin 128) :=
  (List.finRange 128).tail.filter fun n => Q62form (toBitVec n) = 0

/-- Q(6,2) has exactly 63 points. -/
theorem q62_card : q62Indices.length = 63 := by native_decide

/-- Get the n-th point of Q(6,2) (as an index into Fin 128). -/
def q62Point (j : Fin 63) : Fin 128 :=
  q62Indices.get (j.cast (by native_decide))

/-- The parity-check matrix: H[i][j] = (j-th Q(6,2) point)[i-th coordinate]. -/
def Q62_H : Matrix (Fin 7) (Fin 63) (ZMod 2) :=
  fun i j => toBitVec (q62Point j) i

/-- **Self-orthogonality of Q(6,2)**: H · Hᵀ = 0 over 𝔽₂.
The CSS condition: the code C = ker(H) contains its dual C⊥ = rowspan(H). -/
theorem Q62_self_orthogonal : Q62_H * Q62_Hᵀ = (0 : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
  native_decide

/-! ## Part 2: The Langer graph via Zorn product -/

/-- Adjacency test for the Langer graph via the Zorn product criterion.
Returns `true` iff `i ≠ j` and all eight entries of M_x · M_y vanish,
where M_x is the Zorn vector matrix of the split octonion algebra over 𝔽₂. -/
def langerAdjBool (i j : Fin 63) : Bool :=
  if i == j then false else
  let x := toBitVec (q62Point i)
  let y := toBitVec (q62Point j)
  let α := x 3; let γ := y 3
  (α * γ + x 0 * y 4 + x 1 * y 5 + x 2 * y 6 == 0) &&
  (α * γ + x 4 * y 0 + x 5 * y 1 + x 6 * y 2 == 0) &&
  (γ * x 0 + α * y 0 + x 5 * y 6 + x 6 * y 5 == 0) &&
  (γ * x 1 + α * y 1 + x 6 * y 4 + x 4 * y 6 == 0) &&
  (γ * x 2 + α * y 2 + x 4 * y 5 + x 5 * y 4 == 0) &&
  (γ * x 4 + α * y 4 + x 1 * y 2 + x 2 * y 1 == 0) &&
  (γ * x 5 + α * y 5 + x 2 * y 0 + x 0 * y 2 == 0) &&
  (γ * x 6 + α * y 6 + x 0 * y 1 + x 1 * y 0 == 0)

/-- The **Langer graph**: collinearity graph of the split Cayley hexagon GH(2,2)
on the 63 points of Q(6,2). 6-regular, 189 edges, distance-regular with
intersection array {6, 4, 4; 1, 1, 3}. Aut ≅ G₂(2) of order 12096. -/
def langerSimpleGraph : SimpleGraph (Fin 63) where
  Adj i j := langerAdjBool i j
  symm i j := by simp only [langerAdjBool]; revert i j; native_decide
  loopless := ⟨fun i => by simp only [langerAdjBool]; revert i; native_decide⟩

instance langerDecAdj : DecidableRel langerSimpleGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (langerAdjBool i j))

/-- The Langer graph is 6-regular. -/
theorem langer_regular :
    ∀ v : Fin 63, (Finset.univ.filter fun w => langerSimpleGraph.Adj v w).card = 6 := by
  native_decide

/-- The Langer graph has 189 undirected edges. -/
theorem langer_edges :
    (Finset.univ.filter fun p : Fin 63 × Fin 63 =>
      p.1 < p.2 ∧ langerSimpleGraph.Adj p.1 p.2).card = 189 := by
  native_decide

/-! ## Part 3: The Tutte 12-cage -/

/-- Edge list for the Tutte 12-cage (189 edges, 0-indexed).
Vertices 0–62 are points of GH(2,2), vertices 63–125 are lines.
Every edge connects a point to a line (bipartite). -/
private def tutte12Edges : Array (Fin 126 × Fin 126) := #[
  (0,63), (0,64), (0,65), (1,66), (1,67), (1,68),
  (2,69), (2,70), (2,71), (3,72), (3,73), (3,74),
  (4,75), (4,76), (4,77), (5,78), (5,79), (5,80),
  (6,81), (6,82), (6,83), (7,66), (7,72), (7,78),
  (8,66), (8,84), (8,85), (9,72), (9,86), (9,87),
  (10,78), (10,88), (10,89), (11,90), (11,91), (11,92),
  (12,93), (12,94), (12,95), (13,96), (13,97), (13,98),
  (14,99), (14,100), (14,101), (15,63), (15,73), (15,75),
  (16,63), (16,102), (16,103), (17,73), (17,90), (17,96),
  (18,75), (18,104), (18,105), (19,86), (19,106), (19,107),
  (20,99), (20,108), (20,109), (21,87), (21,110), (21,111),
  (22,93), (22,112), (22,113), (23,69), (23,74), (23,81),
  (24,69), (24,114), (24,115), (25,74), (25,93), (25,99),
  (26,81), (26,116), (26,117), (27,96), (27,118), (27,119),
  (28,87), (28,120), (28,121), (29,90), (29,122), (29,123),
  (30,86), (30,124), (30,125), (31,64), (31,67), (31,70),
  (32,64), (32,106), (32,108), (33,67), (33,91), (33,94),
  (34,70), (34,118), (34,120), (35,84), (35,102), (35,114),
  (36,100), (36,103), (36,124), (37,85), (37,112), (37,122),
  (38,97), (38,110), (38,115), (39,68), (39,76), (39,82),
  (40,68), (40,97), (40,100), (41,76), (41,107), (41,113),
  (42,82), (42,121), (42,123), (43,94), (43,104), (43,125),
  (44,91), (44,111), (44,116), (45,85), (45,105), (45,117),
  (46,84), (46,109), (46,119), (47,65), (47,79), (47,83),
  (48,65), (48,110), (48,112), (49,79), (49,92), (49,101),
  (50,83), (50,119), (50,125), (51,88), (51,108), (51,123),
  (52,98), (52,106), (52,117), (53,89), (53,103), (53,116),
  (54,95), (54,102), (54,121), (55,71), (55,77), (55,80),
  (56,71), (56,122), (56,124), (57,77), (57,109), (57,111),
  (58,80), (58,95), (58,98), (59,101), (59,105), (59,120),
  (60,89), (60,113), (60,118), (61,88), (61,104), (61,115),
  (62,92), (62,107), (62,114)]

private def tutte12AdjBool (u v : Fin 126) : Bool :=
  tutte12Edges.any fun (a, b) => (u == a && v == b) || (u == b && v == a)

/-- The **Tutte 12-cage**: incidence graph of GH(2,2) on 126 vertices.
3-regular, 189 edges, girth 12. Semisymmetric (edge-transitive, not vertex-transitive). -/
def tutte12CageGraph : SimpleGraph (Fin 126) where
  Adj u v := tutte12AdjBool u v
  symm u v := by simp only [tutte12AdjBool]; revert u v; native_decide
  loopless := ⟨fun u => by simp only [tutte12AdjBool]; revert u; native_decide⟩

instance tutte12DecAdj : DecidableRel tutte12CageGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (tutte12AdjBool u v))

/-- The Tutte 12-cage is 3-regular. -/
theorem tutte12_regular :
    ∀ v : Fin 126, (Finset.univ.filter fun w => tutte12CageGraph.Adj v w).card = 3 := by
  native_decide

/-- The bipartition: point (< 63) or line (≥ 63). -/
def tutte12Side (v : Fin 126) : Fin 2 :=
  if v.val < 63 then 0 else 1

/-- The Tutte 12-cage is bipartite: every edge connects a point to a line. -/
theorem tutte12_bipartite :
    ∀ u v : Fin 126, tutte12CageGraph.Adj u v → tutte12Side u ≠ tutte12Side v := by
  native_decide

/-! ## Part 4: Distance-2 adjacency on points -/

/-- Distance-2 adjacency on points: p ~ q iff they share a line vertex
in the Tutte 12-cage. -/
def tutte12Distance2Bool (p q : Fin 63) : Bool :=
  p != q &&
  let pv : Fin 126 := ⟨p.val, by omega⟩
  let qv : Fin 126 := ⟨q.val, by omega⟩
  (List.finRange 63).any fun l =>
    let lv : Fin 126 := ⟨l.val + 63, by omega⟩
    tutte12AdjBool pv lv && tutte12AdjBool qv lv

/-! ## Part 5: G₂(2) generators and invariance -/

private def g2gen1Fwd : Array (Fin 63) := #[
  ⟨1, by omega⟩, ⟨3, by omega⟩, ⟨5, by omega⟩, ⟨2, by omega⟩, ⟨0, by omega⟩,
  ⟨6, by omega⟩, ⟨4, by omega⟩, ⟨23, by omega⟩, ⟨25, by omega⟩, ⟨24, by omega⟩,
  ⟨26, by omega⟩, ⟨28, by omega⟩, ⟨30, by omega⟩, ⟨27, by omega⟩, ⟨29, by omega⟩,
  ⟨31, by omega⟩, ⟨33, by omega⟩, ⟨34, by omega⟩, ⟨32, by omega⟩, ⟨35, by omega⟩,
  ⟨37, by omega⟩, ⟨38, by omega⟩, ⟨36, by omega⟩, ⟨55, by omega⟩, ⟨58, by omega⟩,
  ⟨56, by omega⟩, ⟨57, by omega⟩, ⟨60, by omega⟩, ⟨61, by omega⟩, ⟨59, by omega⟩,
  ⟨62, by omega⟩, ⟨7, by omega⟩, ⟨8, by omega⟩, ⟨9, by omega⟩, ⟨10, by omega⟩,
  ⟨12, by omega⟩, ⟨11, by omega⟩, ⟨14, by omega⟩, ⟨13, by omega⟩, ⟨15, by omega⟩,
  ⟨17, by omega⟩, ⟨16, by omega⟩, ⟨18, by omega⟩, ⟨19, by omega⟩, ⟨21, by omega⟩,
  ⟨20, by omega⟩, ⟨22, by omega⟩, ⟨39, by omega⟩, ⟨40, by omega⟩, ⟨42, by omega⟩,
  ⟨41, by omega⟩, ⟨45, by omega⟩, ⟨46, by omega⟩, ⟨44, by omega⟩, ⟨43, by omega⟩,
  ⟨47, by omega⟩, ⟨49, by omega⟩, ⟨48, by omega⟩, ⟨50, by omega⟩, ⟨51, by omega⟩,
  ⟨53, by omega⟩, ⟨52, by omega⟩, ⟨54, by omega⟩]

private def g2gen1Inv : Array (Fin 63) := #[
  ⟨4, by omega⟩, ⟨0, by omega⟩, ⟨3, by omega⟩, ⟨1, by omega⟩, ⟨6, by omega⟩,
  ⟨2, by omega⟩, ⟨5, by omega⟩, ⟨31, by omega⟩, ⟨32, by omega⟩, ⟨33, by omega⟩,
  ⟨34, by omega⟩, ⟨36, by omega⟩, ⟨35, by omega⟩, ⟨38, by omega⟩, ⟨37, by omega⟩,
  ⟨39, by omega⟩, ⟨41, by omega⟩, ⟨40, by omega⟩, ⟨42, by omega⟩, ⟨43, by omega⟩,
  ⟨45, by omega⟩, ⟨44, by omega⟩, ⟨46, by omega⟩, ⟨7, by omega⟩, ⟨9, by omega⟩,
  ⟨8, by omega⟩, ⟨10, by omega⟩, ⟨13, by omega⟩, ⟨11, by omega⟩, ⟨14, by omega⟩,
  ⟨12, by omega⟩, ⟨15, by omega⟩, ⟨18, by omega⟩, ⟨16, by omega⟩, ⟨17, by omega⟩,
  ⟨19, by omega⟩, ⟨22, by omega⟩, ⟨20, by omega⟩, ⟨21, by omega⟩, ⟨47, by omega⟩,
  ⟨48, by omega⟩, ⟨50, by omega⟩, ⟨49, by omega⟩, ⟨54, by omega⟩, ⟨53, by omega⟩,
  ⟨51, by omega⟩, ⟨52, by omega⟩, ⟨55, by omega⟩, ⟨57, by omega⟩, ⟨56, by omega⟩,
  ⟨58, by omega⟩, ⟨59, by omega⟩, ⟨61, by omega⟩, ⟨60, by omega⟩, ⟨62, by omega⟩,
  ⟨23, by omega⟩, ⟨25, by omega⟩, ⟨26, by omega⟩, ⟨24, by omega⟩, ⟨29, by omega⟩,
  ⟨27, by omega⟩, ⟨28, by omega⟩, ⟨30, by omega⟩]

private def g2gen2Fwd : Array (Fin 63) := #[
  ⟨10, by omega⟩, ⟨20, by omega⟩, ⟨29, by omega⟩, ⟨49, by omega⟩, ⟨55, by omega⟩,
  ⟨36, by omega⟩, ⟨44, by omega⟩, ⟨14, by omega⟩, ⟨25, by omega⟩, ⟨59, by omega⟩,
  ⟨40, by omega⟩, ⟨0, by omega⟩, ⟨19, by omega⟩, ⟨50, by omega⟩, ⟨35, by omega⟩,
  ⟨5, by omega⟩, ⟨7, by omega⟩, ⟨47, by omega⟩, ⟨58, by omega⟩, ⟨18, by omega⟩,
  ⟨24, by omega⟩, ⟨34, by omega⟩, ⟨41, by omega⟩, ⟨11, by omega⟩, ⟨17, by omega⟩,
  ⟨62, by omega⟩, ⟨33, by omega⟩, ⟨6, by omega⟩, ⟨28, by omega⟩, ⟨48, by omega⟩,
  ⟨45, by omega⟩, ⟨51, by omega⟩, ⟨61, by omega⟩, ⟨32, by omega⟩, ⟨42, by omega⟩,
  ⟨3, by omega⟩, ⟨8, by omega⟩, ⟨22, by omega⟩, ⟨27, by omega⟩, ⟨57, by omega⟩,
  ⟨46, by omega⟩, ⟨4, by omega⟩, ⟨21, by omega⟩, ⟨52, by omega⟩, ⟨31, by omega⟩,
  ⟨12, by omega⟩, ⟨23, by omega⟩, ⟨53, by omega⟩, ⟨60, by omega⟩, ⟨16, by omega⟩,
  ⟨26, by omega⟩, ⟨38, by omega⟩, ⟨43, by omega⟩, ⟨1, by omega⟩, ⟨9, by omega⟩,
  ⟨56, by omega⟩, ⟨37, by omega⟩, ⟨2, by omega⟩, ⟨30, by omega⟩, ⟨54, by omega⟩,
  ⟨39, by omega⟩, ⟨13, by omega⟩, ⟨15, by omega⟩]

private def g2gen2Inv : Array (Fin 63) := #[
  ⟨11, by omega⟩, ⟨53, by omega⟩, ⟨57, by omega⟩, ⟨35, by omega⟩, ⟨41, by omega⟩,
  ⟨15, by omega⟩, ⟨27, by omega⟩, ⟨16, by omega⟩, ⟨36, by omega⟩, ⟨54, by omega⟩,
  ⟨0, by omega⟩, ⟨23, by omega⟩, ⟨45, by omega⟩, ⟨61, by omega⟩, ⟨7, by omega⟩,
  ⟨62, by omega⟩, ⟨49, by omega⟩, ⟨24, by omega⟩, ⟨19, by omega⟩, ⟨12, by omega⟩,
  ⟨1, by omega⟩, ⟨42, by omega⟩, ⟨37, by omega⟩, ⟨46, by omega⟩, ⟨20, by omega⟩,
  ⟨8, by omega⟩, ⟨50, by omega⟩, ⟨38, by omega⟩, ⟨28, by omega⟩, ⟨2, by omega⟩,
  ⟨58, by omega⟩, ⟨44, by omega⟩, ⟨33, by omega⟩, ⟨26, by omega⟩, ⟨21, by omega⟩,
  ⟨14, by omega⟩, ⟨5, by omega⟩, ⟨56, by omega⟩, ⟨51, by omega⟩, ⟨60, by omega⟩,
  ⟨10, by omega⟩, ⟨22, by omega⟩, ⟨34, by omega⟩, ⟨52, by omega⟩, ⟨6, by omega⟩,
  ⟨30, by omega⟩, ⟨40, by omega⟩, ⟨17, by omega⟩, ⟨29, by omega⟩, ⟨3, by omega⟩,
  ⟨13, by omega⟩, ⟨31, by omega⟩, ⟨43, by omega⟩, ⟨47, by omega⟩, ⟨59, by omega⟩,
  ⟨4, by omega⟩, ⟨55, by omega⟩, ⟨39, by omega⟩, ⟨18, by omega⟩, ⟨9, by omega⟩,
  ⟨48, by omega⟩, ⟨32, by omega⟩, ⟨25, by omega⟩]

private theorem g2gen1Fwd_size : g2gen1Fwd.size = 63 := by native_decide
private theorem g2gen1Inv_size : g2gen1Inv.size = 63 := by native_decide
private theorem g2gen2Fwd_size : g2gen2Fwd.size = 63 := by native_decide
private theorem g2gen2Inv_size : g2gen2Inv.size = 63 := by native_decide

/-- First generator of G₂(2): order 7, from companion matrix of x³ + x + 1. -/
def g2gen1 : Equiv.Perm (Fin 63) where
  toFun i := g2gen1Fwd[i.val]'(by have := g2gen1Fwd_size; omega)
  invFun i := g2gen1Inv[i.val]'(by have := g2gen1Inv_size; omega)
  left_inv := by intro i; revert i; native_decide
  right_inv := by intro i; revert i; native_decide

/-- Second generator of G₂(2): order 6, maps vertex 0 → 10. -/
def g2gen2 : Equiv.Perm (Fin 63) where
  toFun i := g2gen2Fwd[i.val]'(by have := g2gen2Fwd_size; omega)
  invFun i := g2gen2Inv[i.val]'(by have := g2gen2Inv_size; omega)
  left_inv := by intro i; revert i; native_decide
  right_inv := by intro i; revert i; native_decide

/-- σ₁ preserves Langer adjacency. -/
theorem g2gen1_langer_inv :
    ∀ i j : Fin 63,
      langerSimpleGraph.Adj i j ↔ langerSimpleGraph.Adj (g2gen1 i) (g2gen1 j) := by
  native_decide

/-- σ₂ preserves Langer adjacency. -/
theorem g2gen2_langer_inv :
    ∀ i j : Fin 63,
      langerSimpleGraph.Adj i j ↔ langerSimpleGraph.Adj (g2gen2 i) (g2gen2 j) := by
  native_decide

/-- σ₁ preserves distance-2 adjacency. -/
theorem g2gen1_dist2_inv :
    ∀ p q : Fin 63,
      tutte12Distance2Bool p q = tutte12Distance2Bool (g2gen1 p) (g2gen1 q) := by
  native_decide

/-- σ₂ preserves distance-2 adjacency. -/
theorem g2gen2_dist2_inv :
    ∀ p q : Fin 63,
      tutte12Distance2Bool p q = tutte12Distance2Bool (g2gen2 p) (g2gen2 q) := by
  native_decide

/-! ## Part 6: Word induction (structural, no native_decide) -/

/-- The four generator actions: σ₁, σ₁⁻¹, σ₂, σ₂⁻¹. -/
def applyGen : Fin 4 → Equiv.Perm (Fin 63)
  | 0 => g2gen1
  | 1 => g2gen1.symm
  | 2 => g2gen2
  | 3 => g2gen2.symm

/-- Apply a generator word (left-to-right). -/
def applyWord : List (Fin 4) → Equiv.Perm (Fin 63)
  | [] => Equiv.refl _
  | g :: gs => (applyGen g).trans (applyWord gs)

private theorem symm_preserves_langer (σ : Equiv.Perm (Fin 63))
    (h : ∀ i j : Fin 63,
      langerSimpleGraph.Adj i j ↔ langerSimpleGraph.Adj (σ i) (σ j))
    (i j : Fin 63) :
    langerSimpleGraph.Adj i j ↔ langerSimpleGraph.Adj (σ.symm i) (σ.symm j) := by
  have := h (σ.symm i) (σ.symm j)
  simp only [Equiv.apply_symm_apply] at this
  exact this.symm

private theorem applyGen_langer_inv (g : Fin 4) (i j : Fin 63) :
    langerSimpleGraph.Adj i j ↔ langerSimpleGraph.Adj (applyGen g i) (applyGen g j) := by
  fin_cases g <;> simp only [applyGen]
  · exact g2gen1_langer_inv i j
  · exact symm_preserves_langer g2gen1 (g2gen1_langer_inv) i j
  · exact g2gen2_langer_inv i j
  · exact symm_preserves_langer g2gen2 (g2gen2_langer_inv) i j

/-- Any generator word preserves Langer adjacency (structural induction). -/
theorem applyWord_langer_inv (w : List (Fin 4)) :
    ∀ i j : Fin 63, langerSimpleGraph.Adj i j ↔
      langerSimpleGraph.Adj (applyWord w i) (applyWord w j) := by
  induction w with
  | nil => intro i j; simp [applyWord]
  | cons g gs ih =>
    intro i j
    simp only [applyWord, Equiv.trans_apply]
    rw [applyGen_langer_inv g i j]
    exact ih (applyGen g i) (applyGen g j)

private theorem symm_preserves_dist2 (σ : Equiv.Perm (Fin 63))
    (h : ∀ p q : Fin 63, tutte12Distance2Bool p q = tutte12Distance2Bool (σ p) (σ q))
    (p q : Fin 63) :
    tutte12Distance2Bool p q = tutte12Distance2Bool (σ.symm p) (σ.symm q) := by
  have := h (σ.symm p) (σ.symm q)
  simp only [Equiv.apply_symm_apply] at this
  exact this.symm

private theorem applyGen_dist2_inv (g : Fin 4) (p q : Fin 63) :
    tutte12Distance2Bool p q = tutte12Distance2Bool (applyGen g p) (applyGen g q) := by
  fin_cases g <;> simp only [applyGen]
  · exact g2gen1_dist2_inv p q
  · exact symm_preserves_dist2 g2gen1 (g2gen1_dist2_inv) p q
  · exact g2gen2_dist2_inv p q
  · exact symm_preserves_dist2 g2gen2 (g2gen2_dist2_inv) p q

/-- Any generator word preserves distance-2 adjacency (structural induction). -/
theorem applyWord_dist2_inv (w : List (Fin 4)) :
    ∀ p q : Fin 63, tutte12Distance2Bool p q =
      tutte12Distance2Bool (applyWord w p) (applyWord w q) := by
  induction w with
  | nil => intro p q; simp [applyWord]
  | cons g gs ih =>
    intro p q
    simp only [applyWord, Equiv.trans_apply]
    rw [applyGen_dist2_inv g p q]
    exact ih (applyGen g p) (applyGen g q)

/-! ## Part 7: Transitivity witnesses and main theorem -/

private def witnessWordData : Array (List (Fin 4)) := #[
  [],           [0],          [0,0,0],      [0,0],        [1],
  [1,1,1],      [1,1],        [3,3,1],      [3,1,2],      [0,2,2,1],
  [2],          [3],          [0,0,3,0],    [1,1,3,1],    [0,0,3,3],
  [1,1,1,3],    [1,3,0],      [2,1,1],      [2,1,2,0],    [0,0,3,1],
  [0,2],        [2,1,3],      [1,3,3],      [3,3],        [0,2,2],
  [1,2,2,1],    [2,0],        [1,1,3],      [3,0],        [0,0,0,2],
  [0,2,1,3],    [0,3,0,2],    [2,0,2,2],    [2,0,2],      [2,1],
  [0,0,3],      [3,1],        [0,2,0],      [1,1,3,3],    [0,3,1,2],
  [2,2],        [1,3],        [2,1,2],      [0,0,3,1,1],  [0,3,0],
  [0,2,1],      [2,2,2],      [0,3,3],      [2,2,1],      [0,0,2],
  [1,3,1],      [0,2,1,1],    [2,2,2,1],    [0,3],        [0,2,2,1,3],
  [1,2],        [1,2,2],      [2,0,0],      [0,2,2,0],    [0,0,0,2,0],
  [0,3,1],      [3,0,0],      [0,2,1,3,0]]

private theorem witnessWordData_size : witnessWordData.size = 63 := by native_decide

/-- BFS witness words: `witnessWord v` is a generator word mapping 0 → v. -/
def witnessWord (v : Fin 63) : List (Fin 4) :=
  witnessWordData[v.val]'(by have := witnessWordData_size; omega)

/-- Each witness word correctly maps 0 to its target vertex. -/
theorem witnessWord_correct :
    ∀ v : Fin 63, applyWord (witnessWord v) 0 = v := by
  native_decide

/-- The Langer graph and distance-2 graph agree at vertex 0. -/
theorem graphs_agree_at_zero :
    ∀ v : Fin 63,
      langerSimpleGraph.Adj 0 v ↔ (tutte12Distance2Bool 0 v = true) := by
  native_decide

private theorem transport_langer (w : List (Fin 4)) (q : Fin 63) :
    langerSimpleGraph.Adj (applyWord w 0) q ↔
      langerSimpleGraph.Adj 0 ((applyWord w).symm q) := by
  conv_lhs => rw [← Equiv.apply_symm_apply (applyWord w) q]
  exact ((applyWord_langer_inv w) 0 ((applyWord w).symm q)).symm

private theorem transport_dist2 (w : List (Fin 4)) (q : Fin 63) :
    tutte12Distance2Bool (applyWord w 0) q =
      tutte12Distance2Bool 0 ((applyWord w).symm q) := by
  conv_lhs => rw [← Equiv.apply_symm_apply (applyWord w) q]
  exact ((applyWord_dist2_inv w) 0 ((applyWord w).symm q)).symm

/-- **The Langer graph equals the distance-2 graph of the Tutte 12-cage
restricted to points** — proved structurally via G₂(2) transitivity.

The argument:
1. Let σ = applyWord (witnessWord p), so σ(0) = p
2. Adj p q ↔ Adj 0 (σ⁻¹ q)  [by transport_langer]
3. dist2 p q = dist2 0 (σ⁻¹ q)  [by transport_dist2]
4. Adj 0 (σ⁻¹ q) ↔ dist2 0 (σ⁻¹ q)  [by graphs_agree_at_zero] -/
theorem langer_eq_tutte12_distance2' :
    ∀ p q : Fin 63,
      langerSimpleGraph.Adj p q ↔ (tutte12Distance2Bool p q = true) := by
  intro p q
  rw [← witnessWord_correct p]
  rw [transport_langer, transport_dist2]
  exact graphs_agree_at_zero _
=======

/-! ## The Langer graph is a Sabidussi coset graph

G₂(2) = ⟨σ₁, σ₂⟩ acts vertex-transitively on the 63 points of GH(2,2),
so by the Sabidussi representation theorem:
  `langerSimpleGraph ≃g cosetGraph(Stab_G₂(0), connectionSet G₂ langer 0)` -/

/-- The two G₂(2) generators as a `Fin 2`-indexed family. -/
def langerGens : Fin 2 → Equiv.Perm (Fin 63)
  | 0 => g2gen1
  | 1 => g2gen2

/-- G₂(2) as a subgroup of Sym(63), generated by σ₁ and σ₂. -/
def langerG : Subgroup (Equiv.Perm (Fin 63)) :=
  Subgroup.closure (Set.range langerGens)

private theorem applyGen_mem (i : Fin 4) : applyGen i ∈ langerG := by
  unfold langerG
  match i with
  | 0 => exact Subgroup.subset_closure ⟨0, rfl⟩
  | 1 => exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨0, rfl⟩)
  | 2 => exact Subgroup.subset_closure ⟨1, rfl⟩
  | 3 => exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨1, rfl⟩)

private theorem applyWord_mem (w : List (Fin 4)) : applyWord w ∈ langerG := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i rest ih => exact langerG.mul_mem ih (applyGen_mem i)

noncomputable instance langerMulAction : MulAction langerG (Fin 63) :=
  MulAction.compHom (Fin 63) langerG.subtype

noncomputable instance langerGraphAction :
    GraphAction langerG (Fin 63) langerSimpleGraph where
  adj_smul := by
    intro ⟨σ, hσ⟩ u v hadj
    change langerSimpleGraph.Adj (σ u) (σ v)
    revert u v; change ∀ u v, langerSimpleGraph.Adj u v → langerSimpleGraph.Adj (σ u) (σ v)
    refine Subgroup.closure_induction
      (p := fun σ _ => ∀ u v, langerSimpleGraph.Adj u v → langerSimpleGraph.Adj (σ u) (σ v))
      ?_ ?_ ?_ ?_ hσ
    · intro x ⟨i, hi⟩; subst hi
      match i with
      | 0 => exact fun u v h => (g2gen1_langer_inv u v).mp h
      | 1 => exact fun u v h => (g2gen2_langer_inv u v).mp h
    · intro u v h; simpa
    · intro x y _ _ hx hy u v hadj
      simp only [Equiv.Perm.mul_apply]; exact hx _ _ (hy u v hadj)
    · intro x _ hx u v hadj
      let f : { p : Fin 63 × Fin 63 // langerSimpleGraph.Adj p.1 p.2 } →
              { p : Fin 63 × Fin 63 // langerSimpleGraph.Adj p.1 p.2 } :=
        fun ⟨⟨a, b⟩, hab⟩ => ⟨⟨x a, x b⟩, hx a b hab⟩
      have hf_surj : Function.Surjective f := Finite.surjective_of_injective (by
        intro ⟨⟨a₁, b₁⟩, _⟩ ⟨⟨a₂, b₂⟩, _⟩ h
        simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at h
        exact Subtype.ext (Prod.ext (x.injective h.1) (x.injective h.2)))
      obtain ⟨⟨⟨a, b⟩, hab⟩, heq⟩ := hf_surj ⟨⟨u, v⟩, hadj⟩
      simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at heq
      rw [show a = x⁻¹ u from by rw [← heq.1]; simp,
          show b = x⁻¹ v from by rw [← heq.2]; simp] at hab
      exact hab

noncomputable instance langerPretransitive :
    MulAction.IsPretransitive langerG (Fin 63) where
  exists_smul_eq := by
    intro x y
    let σ_x := applyWord (witnessWord x)
    let σ_y := applyWord (witnessWord y)
    have hmem : σ_x.symm.trans σ_y ∈ langerG :=
      langerG.mul_mem (applyWord_mem _) (langerG.inv_mem (applyWord_mem _))
    exact ⟨⟨σ_x.symm.trans σ_y, hmem⟩, by
      change (σ_x.symm.trans σ_y) x = y
      simp only [Equiv.trans_apply]
      rw [show σ_x.symm x = 0 from by
        rw [Equiv.symm_apply_eq]; exact (witnessWord_correct x).symm]
      exact witnessWord_correct y⟩

/-- **The Langer graph is a Sabidussi coset graph.**

  `langerSimpleGraph ≃g Sab(G₂(2), H₁₉₂, D)`

where H₁₉₂ = Stab(0) has order 192. -/
noncomputable def langerSabidussiIso :
    langerSimpleGraph ≃g SimpleGraph.cosetGraph
      (MulAction.stabilizer langerG (0 : Fin 63))
      (connectionSet langerG langerSimpleGraph 0)

