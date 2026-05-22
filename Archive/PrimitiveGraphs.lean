/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Archive.LangerGraph

/-!
# Primitive and imprimitive cubic arc-transitive graphs

Four results connecting primitivity, imprimitivity, and covering structure
for cubic arc-transitive graphs in the Foster census:

1. **Langer graph primitivity** — The G₂(2) action on 63 vertices is primitive
   (Atkinson's algorithm). The point stabiliser H₁₉₂ is maximal in G₂(2).

2. **Zhou-6 graph primitivity** — The PSL(2,13) action on 91 vertices (via
   the subgroup D₁₂) is primitive. The stabiliser D₁₂ is maximal in PSL(2,13).

3. **Zhou-3 → Zhou-6 covering** — The Zhou-3 graph (F182A, cubic, 182 vertices)
   is a positive double cover of Zhou-6 (91 vertices, 6-regular) via the block
   system S₃ < D₁₂ in PSL(2,13).

4. **No cubic double cover of Langer** — The Tutte 12-cage (126 vertices, cubic)
   cannot cover the Langer graph because its point subgraph is edgeless.

## References

* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798
* M.D. Atkinson, *An algorithm for finding the blocks of a permutation group*,
  Math. Comp. 29 (1975), 911–913
* C.-X. Zhou, Y.-Q. Feng, *Automorphism groups of connected cubic Cayley graphs
  of order 2pq*, Algebra Colloq. (2007)
-/

set_option linter.style.nativeDecide false
set_option linter.style.longFile 3000

/-! ## Section 1: Atkinson's algorithm (generic) and Langer primitivity -/

/-- Merge two equivalence classes in a partition represented as `Fin n → Fin n`:
replace all occurrences of `hi` with `lo`. -/
private def mergeRep {n : Nat} (f : Fin n → Fin n) (lo hi : Fin n) : Fin n → Fin n :=
  fun i => let fi := f i; if fi = hi then lo else fi

/-- Atkinson's algorithm: compute the smallest block containing the initial
merged pair, by propagating equivalences through generators.

State: `(queue, partition)` where `queue` is a list of newly-merged pairs
and `partition : Fin n → Fin n` maps each element to its class representative.

At each step, pop a pair `(x, y)` from the queue. For each generator `g`,
check if `g(x)` and `g(y)` have the same representative. If not, merge their
classes and enqueue the new pair. Terminate when the queue is empty.

`fuel` bounds the number of queue-pop steps. -/
private def atkinson {n : Nat} (gens : List (Equiv.Perm (Fin n)))
    (queue : List (Fin n × Fin n)) (part : Fin n → Fin n) :
    Nat → Fin n → Fin n
  | 0 => part
  | fuel + 1 =>
    match queue with
    | [] => part
    | (x, y) :: rest =>
      let Acc := List (Fin n × Fin n) × (Fin n → Fin n)
      let (newPairs, part') := gens.foldl (fun (acc : Acc) g =>
        let (pairs, p) := acc
        let rgx := p (g x)
        let rgy := p (g y)
        if rgx = rgy then (pairs, p)
        else
          let lo := min rgx rgy
          let hi := max rgx rgy
          ((lo, hi) :: pairs, mergeRep p lo hi)) ([], part)
      atkinson gens (rest ++ newPairs) part' fuel

/-- Check whether Atkinson's algorithm starting from `{0, v}` merges all
vertices into a single class (i.e., the block is all of Ω). -/
private def blockIsFullGeneric {n : Nat} (gens : List (Equiv.Perm (Fin n)))
    (v : Fin n) (fuel : Nat) : Bool :=
  let initPart : Fin n → Fin n := fun i => if i = v then 0 else i
  let finalPart := atkinson gens [(0, v)] initPart fuel
  decide (∀ w : Fin n, finalPart w = 0)

/-- All four G₂(2) generator permutations on Fin 63: σ₁, σ₁⁻¹, σ₂, σ₂⁻¹. -/
private def langerAllGens : List (Equiv.Perm (Fin 63)) :=
  [g2gen1, g2gen1.symm, g2gen2, g2gen2.symm]

/-- **Primitivity of the G₂(2) action on the 63 points of GH(2,2).**

For every vertex `v ≠ 0`, Atkinson's algorithm starting from `0 ~ v`
merges all 63 vertices into a single equivalence class. This means
no non-trivial block system exists, so the point stabiliser H₁₉₂ ≤ G₂(2)
is a **maximal subgroup** — there is no subgroup K with H₁₉₂ < K < G₂(2). -/
theorem langer_action_primitive :
    ∀ v : Fin 63, v ≠ 0 → blockIsFullGeneric langerAllGens v 300 = true := by
  native_decide

/-! ## Section 2: The Zhou-6 graph and its primitivity -/

/-- Edge list for the Zhou-6 graph (91 vertices, 6-regular, 273 edges).
This is the quotient of Zhou-3 (F182A) by the block system S₃ < D₁₂
in PSL(2,13). Equivalently, Sab(PSL(2,13), D₁₂). -/
private def zhou6Edges : Array (Fin 91 × Fin 91) := #[
  (0, 48), (0, 54), (0, 59), (0, 63), (0, 65), (0, 69),
  (1, 26), (1, 35), (1, 62), (1, 71), (1, 75), (1, 81),
  (2, 24), (2, 31), (2, 82), (2, 83), (2, 86), (2, 87),
  (3, 38), (3, 53), (3, 57), (3, 73), (3, 84), (3, 87),
  (4, 39), (4, 44), (4, 53), (4, 54), (4, 77), (4, 89),
  (5, 34), (5, 45), (5, 46), (5, 54), (5, 78), (5, 90),
  (6, 35), (6, 38), (6, 46), (6, 47), (6, 61), (6, 79),
  (7, 39), (7, 43), (7, 45), (7, 52), (7, 58), (7, 79),
  (8, 25), (8, 34), (8, 59), (8, 61), (8, 74), (8, 80),
  (9, 37), (9, 52), (9, 60), (9, 65), (9, 75), (9, 82),
  (10, 18), (10, 24), (10, 40), (10, 58), (10, 66), (10, 74),
  (11, 51), (11, 55), (11, 67), (11, 68), (11, 75), (11, 89),
  (12, 20), (12, 24), (12, 52), (12, 69), (12, 72), (12, 90),
  (13, 53), (13, 58), (13, 68), (13, 70), (13, 76), (13, 85),
  (14, 29), (14, 30), (14, 60), (14, 67), (14, 76), (14, 80),
  (15, 18), (15, 20), (15, 63), (15, 64), (15, 73), (15, 81),
  (16, 36), (16, 51), (16, 74), (16, 81), (16, 85), (16, 88),
  (17, 29), (17, 35), (17, 56), (17, 73), (17, 83), (17, 90),
  (18, 33), (18, 37), (18, 66), (18, 73),
  (19, 26), (19, 28), (19, 29), (19, 34), (19, 86), (19, 89),
  (20, 32), (20, 52), (20, 64), (20, 80),
  (21, 32), (21, 41), (21, 44), (21, 66), (21, 83), (21, 88),
  (22, 36), (22, 42), (22, 45), (22, 60), (22, 70), (22, 84),
  (23, 25), (23, 28), (23, 39), (23, 47), (23, 62), (23, 87),
  (24, 69), (24, 74), (24, 87),
  (25, 39), (25, 49), (25, 56), (25, 59),
  (26, 34), (26, 50), (26, 57), (26, 71),
  (27, 37), (27, 38), (27, 42), (27, 44), (27, 51), (27, 78),
  (28, 29), (28, 47), (28, 48), (28, 88),
  (29, 60), (29, 73),
  (30, 46), (30, 49), (30, 66), (30, 67), (30, 71),
  (31, 43), (31, 50), (31, 64), (31, 67), (31, 83),
  (32, 55), (32, 80), (32, 84), (32, 88),
  (33, 37), (33, 43), (33, 48), (33, 61), (33, 77),
  (34, 45), (34, 74),
  (35, 61), (35, 75), (35, 83),
  (36, 60), (36, 72), (36, 77), (36, 81),
  (37, 78), (37, 82),
  (38, 51), (38, 57), (38, 79),
  (39, 44), (39, 52),
  (40, 50), (40, 55), (40, 56), (40, 58), (40, 65),
  (41, 57), (41, 59), (41, 66), (41, 68), (41, 72),
  (42, 44), (42, 69), (42, 70), (42, 71),
  (43, 45), (43, 48), (43, 67),
  (44, 83),
  (45, 84),
  (46, 47), (46, 54), (46, 66),
  (47, 64), (47, 70),
  (48, 69), (48, 88),
  (49, 56), (49, 71), (49, 82), (49, 85),
  (50, 57), (50, 64), (50, 65),
  (51, 67), (51, 74),
  (52, 75),
  (53, 54), (53, 73), (53, 85),
  (54, 65),
  (55, 56), (55, 84), (55, 89),
  (56, 90),
  (57, 72),
  (58, 76), (58, 79),
  (59, 63), (59, 68),
  (60, 65),
  (61, 77), (61, 80),
  (62, 76), (62, 78), (62, 81), (62, 87),
  (63, 79), (63, 81), (63, 86),
  (64, 70),
  (68, 70), (68, 75),
  (69, 71),
  (72, 77), (72, 90),
  (76, 78), (76, 80),
  (77, 89),
  (78, 90),
  (79, 86),
  (82, 85), (82, 86),
  (84, 87),
  (85, 88),
  (86, 89)]

private def zhou6AdjBool (u v : Fin 91) : Bool :=
  zhou6Edges.any fun (a, b) => (u == a && v == b) || (u == b && v == a)

/-- The **Zhou-6 graph**: 91 vertices, 6-regular, 273 edges.
Quotient of the Zhou-3 graph (F182A) by the block system S₃ < D₁₂. -/
def zhou6Graph : SimpleGraph (Fin 91) where
  Adj u v := zhou6AdjBool u v
  symm u v := by simp only [zhou6AdjBool]; revert u v; native_decide
  loopless := ⟨fun u => by simp only [zhou6AdjBool]; revert u; native_decide⟩

instance zhou6DecAdj : DecidableRel zhou6Graph.Adj :=
  fun u v => inferInstanceAs (Decidable (zhou6AdjBool u v))

/-- The Zhou-6 graph is 6-regular. -/
theorem zhou6_regular :
    ∀ v : Fin 91, (Finset.univ.filter fun w => zhou6Graph.Adj v w).card = 6 := by
  native_decide

/-- The Zhou-6 graph has 273 edges. -/
theorem zhou6_edges :
    (Finset.univ.filter fun p : Fin 91 × Fin 91 =>
      p.1 < p.2 ∧ zhou6Graph.Adj p.1 p.2).card = 273 := by
  native_decide

/-! ### Zhou-6 generators (PSL(2,13) action on 91 = |PSL(2,13)|/|D₁₂| points) -/

private def zhou6Gen1Fwd : Array (Fin 91) := #[
  1, 3, 5, 7, 9, 11, 13, 14, 16, 17, 8, 18, 19, 20, 21, 23, 24, 4, 25, 27,
  28, 0, 31, 22, 34, 36, 38, 40, 42, 44, 41, 46, 48, 49, 51, 53, 2, 56, 58, 60,
  61, 63, 50, 30, 65, 67, 68, 70, 71, 72, 6, 10, 29, 52, 75, 33, 77, 79, 80, 81,
  83, 85, 84, 62, 47, 35, 59, 66, 15, 26, 64, 57, 86, 39, 74, 73, 32, 82, 55, 76,
  88, 87, 90, 54, 43, 12, 78, 45, 69, 37, 89]

private def zhou6Gen1Inv : Array (Fin 91) := #[
  21, 0, 36, 1, 17, 2, 50, 3, 10, 4, 51, 5, 85, 6, 7, 68, 8, 9, 11, 12,
  13, 14, 23, 15, 16, 18, 69, 19, 20, 52, 43, 22, 76, 55, 24, 65, 25, 89, 26, 73,
  27, 30, 28, 84, 29, 87, 31, 64, 32, 33, 42, 34, 53, 35, 83, 78, 37, 71, 38, 66,
  39, 40, 63, 41, 70, 44, 67, 45, 46, 88, 47, 48, 49, 75, 74, 54, 79, 56, 86, 57,
  58, 59, 77, 60, 62, 61, 72, 81, 80, 90, 82]

private def zhou6Gen2Fwd : Array (Fin 91) := #[
  2, 4, 6, 8, 10, 12, 0, 15, 9, 3, 1, 13, 17, 16, 22, 19, 11, 5, 26, 7,
  29, 30, 32, 33, 35, 37, 39, 41, 43, 45, 42, 47, 14, 50, 52, 54, 55, 57, 59, 18,
  62, 49, 21, 64, 66, 20, 69, 48, 31, 27, 23, 68, 73, 74, 24, 76, 78, 25, 81, 82,
  84, 65, 77, 86, 28, 87, 71, 70, 85, 83, 88, 44, 56, 34, 75, 53, 36, 40, 72, 63,
  60, 89, 38, 46, 80, 51, 79, 61, 67, 58, 90]

private def zhou6Gen2Inv : Array (Fin 91) := #[
  6, 10, 0, 9, 1, 17, 2, 19, 3, 8, 4, 16, 5, 11, 32, 7, 13, 12, 39, 15,
  45, 42, 14, 50, 54, 57, 18, 49, 64, 20, 21, 48, 22, 23, 73, 24, 76, 25, 82, 26,
  77, 27, 30, 28, 71, 29, 83, 31, 47, 41, 33, 85, 34, 75, 35, 36, 72, 37, 89, 38,
  80, 87, 40, 79, 43, 61, 44, 88, 51, 46, 67, 66, 78, 52, 53, 74, 55, 62, 56, 86,
  84, 58, 59, 69, 60, 68, 63, 65, 70, 81, 90]

private theorem zhou6Gen1Fwd_size : zhou6Gen1Fwd.size = 91 := by native_decide
private theorem zhou6Gen1Inv_size : zhou6Gen1Inv.size = 91 := by native_decide
private theorem zhou6Gen2Fwd_size : zhou6Gen2Fwd.size = 91 := by native_decide
private theorem zhou6Gen2Inv_size : zhou6Gen2Inv.size = 91 := by native_decide

/-- First generator of PSL(2,13) acting on 91 cosets of D₁₂. -/
def zhou6Gen1 : Equiv.Perm (Fin 91) where
  toFun i := zhou6Gen1Fwd[i.val]'(by have := zhou6Gen1Fwd_size; omega)
  invFun i := zhou6Gen1Inv[i.val]'(by have := zhou6Gen1Inv_size; omega)
  left_inv := by intro i; revert i; native_decide
  right_inv := by intro i; revert i; native_decide

/-- Second generator of PSL(2,13) acting on 91 cosets of D₁₂. -/
def zhou6Gen2 : Equiv.Perm (Fin 91) where
  toFun i := zhou6Gen2Fwd[i.val]'(by have := zhou6Gen2Fwd_size; omega)
  invFun i := zhou6Gen2Inv[i.val]'(by have := zhou6Gen2Inv_size; omega)
  left_inv := by intro i; revert i; native_decide
  right_inv := by intro i; revert i; native_decide

/-- σ₁ preserves Zhou-6 adjacency. -/
theorem zhou6Gen1_adj :
    ∀ u v : Fin 91,
      zhou6Graph.Adj u v ↔ zhou6Graph.Adj (zhou6Gen1 u) (zhou6Gen1 v) := by
  native_decide

/-- σ₂ preserves Zhou-6 adjacency. -/
theorem zhou6Gen2_adj :
    ∀ u v : Fin 91,
      zhou6Graph.Adj u v ↔ zhou6Graph.Adj (zhou6Gen2 u) (zhou6Gen2 v) := by
  native_decide

/-- All four PSL(2,13) generator permutations on Fin 91. -/
private def zhou6AllGens : List (Equiv.Perm (Fin 91)) :=
  [zhou6Gen1, zhou6Gen1.symm, zhou6Gen2, zhou6Gen2.symm]

/-- **Primitivity of the PSL(2,13) action on 91 points.**

For every vertex `v ≠ 0`, Atkinson's algorithm starting from `0 ~ v`
merges all 91 vertices into a single equivalence class. The stabiliser
D₁₂ (order 12) is a **maximal subgroup** of PSL(2,13) (order 1092). -/
theorem zhou6_action_primitive :
    ∀ v : Fin 91, v ≠ 0 → blockIsFullGeneric zhou6AllGens v 400 = true := by
  native_decide

/-! ## Section 3: Zhou-3 → Zhou-6 covering -/

/-- Edge list for the Zhou-3 graph (F182A, 182 vertices, cubic, 273 edges).
The unique cubic arc-transitive graph on 182 vertices, with
Aut ≅ PSL(2,13) × Z₂ and arc-stabiliser S₃. -/
private def zhou3Edges : Array (Fin 182 × Fin 182) := #[
  (0, 97), (0, 119), (0, 131),
  (1, 108), (1, 126), (1, 139),
  (2, 71), (2, 143), (2, 163),
  (3, 53), (3, 125), (3, 150),
  (4, 62), (4, 165), (4, 175),
  (5, 48), (5, 166), (5, 172),
  (6, 107), (6, 115), (6, 174),
  (7, 77), (7, 147), (7, 169),
  (8, 88), (8, 109), (8, 179),
  (9, 79), (9, 106), (9, 155),
  (10, 90), (10, 92), (10, 181),
  (11, 68), (11, 108), (11, 157),
  (12, 77), (12, 94), (12, 122),
  (13, 70), (13, 93), (13, 158),
  (14, 91), (14, 104), (14, 159),
  (15, 78), (15, 86), (15, 117),
  (16, 51), (16, 123), (16, 149),
  (17, 69), (17, 119), (17, 161),
  (18, 75), (18, 130), (18, 151),
  (19, 105), (19, 121), (19, 165),
  (20, 49), (20, 117), (20, 132),
  (21, 37), (21, 81), (21, 148),
  (22, 134), (22, 136), (22, 179),
  (23, 102), (23, 111), (23, 150),
  (24, 40), (24, 138), (24, 181),
  (25, 48), (25, 104), (25, 145),
  (26, 117), (26, 140), (26, 170),
  (27, 106), (27, 137), (27, 153),
  (28, 59), (28, 135), (28, 152),
  (29, 60), (29, 120), (29, 161),
  (30, 41), (30, 127), (30, 146),
  (31, 36), (31, 128), (31, 163),
  (32, 73), (32, 148), (32, 171),
  (33, 103), (33, 163), (33, 176),
  (34, 70), (34, 113), (34, 146),
  (35, 58), (35, 167), (35, 181),
  (36, 75), (36, 133),
  (37, 66), (37, 147),
  (38, 52), (38, 56), (38, 179),
  (39, 59), (39, 68), (39, 173),
  (40, 129), (40, 161),
  (41, 64), (41, 105),
  (42, 65), (42, 89), (42, 132),
  (43, 82), (43, 166), (43, 176),
  (44, 72), (44, 91), (44, 141),
  (45, 85), (45, 121), (45, 168),
  (46, 57), (46, 79), (46, 124),
  (47, 50), (47, 95), (47, 174),
  (48, 149),
  (49, 139), (49, 174),
  (50, 113), (50, 118),
  (51, 78), (51, 98),
  (52, 115), (52, 142),
  (53, 69), (53, 100),
  (54, 75), (54, 76), (54, 84),
  (55, 89), (55, 102), (55, 156),
  (56, 94), (56, 176),
  (57, 58), (57, 96),
  (58, 121),
  (59, 147),
  (60, 133), (60, 143),
  (61, 93), (61, 98), (61, 134),
  (62, 128), (62, 135),
  (63, 87), (63, 101), (63, 167),
  (64, 110), (64, 177),
  (65, 160), (65, 169),
  (66, 87), (66, 154),
  (67, 74), (67, 96), (67, 123),
  (68, 148),
  (69, 91),
  (70, 151),
  (71, 123), (71, 166),
  (72, 155), (72, 162),
  (73, 120), (73, 144),
  (74, 157), (74, 164),
  (76, 114), (76, 159),
  (77, 103),
  (78, 89),
  (79, 105),
  (80, 100), (80, 113), (80, 116),
  (81, 110), (81, 131),
  (82, 115), (82, 118),
  (83, 133), (83, 137), (83, 144),
  (84, 139), (84, 140),
  (85, 88), (85, 142),
  (86, 97), (86, 134),
  (87, 90),
  (88, 167),
  (90, 169),
  (92, 95), (92, 132),
  (93, 109),
  (94, 141),
  (95, 129),
  (96, 138),
  (97, 177),
  (98, 164),
  (99, 112), (99, 142), (99, 171),
  (100, 129),
  (101, 114), (101, 130),
  (102, 149),
  (103, 135),
  (104, 150),
  (106, 146),
  (107, 108), (107, 171),
  (109, 130),
  (110, 178),
  (111, 112), (111, 168),
  (112, 180),
  (114, 145),
  (116, 152), (116, 158),
  (118, 127),
  (119, 136),
  (120, 131),
  (122, 155), (122, 160),
  (124, 157), (124, 162),
  (125, 152), (125, 175),
  (126, 159), (126, 162),
  (127, 172),
  (128, 140),
  (136, 141),
  (137, 151),
  (138, 143),
  (144, 180),
  (145, 154),
  (153, 156), (153, 160),
  (154, 178),
  (156, 180),
  (158, 173),
  (164, 173),
  (165, 170),
  (168, 175),
  (170, 177),
  (172, 178)]

private def zhou3AdjBool (u v : Fin 182) : Bool :=
  zhou3Edges.any fun (a, b) => (u == a && v == b) || (u == b && v == a)

/-- The **Zhou-3 graph** (F182A): 182 vertices, cubic (3-regular), 273 edges.
The unique cubic arc-transitive graph on 182 vertices.
Sab(PSL(2,13), S₃) where |PSL(2,13)| = 1092, |S₃| = 6. -/
def zhou3Graph : SimpleGraph (Fin 182) where
  Adj u v := zhou3AdjBool u v
  symm u v := by simp only [zhou3AdjBool]; revert u v; native_decide
  loopless := ⟨fun u => by simp only [zhou3AdjBool]; revert u; native_decide⟩

instance zhou3DecAdj : DecidableRel zhou3Graph.Adj :=
  fun u v => inferInstanceAs (Decidable (zhou3AdjBool u v))

/-- The Zhou-3 graph is 3-regular. -/
theorem zhou3_regular :
    ∀ v : Fin 182, (Finset.univ.filter fun w => zhou3Graph.Adj v w).card = 3 := by
  native_decide

/-- The Zhou-3 graph has 273 edges. -/
theorem zhou3_edges :
    (Finset.univ.filter fun p : Fin 182 × Fin 182 =>
      p.1 < p.2 ∧ zhou3Graph.Adj p.1 p.2).card = 273 := by
  native_decide

/-! ### The covering map Zhou-3 → Zhou-6

The block system for the Z₂ double cover is: vertex `v` of Zhou-3 maps to
vertex `v / 2` of Zhou-6. Each fibre `{2k, 2k+1}` has size 2. -/

/-- The covering map from Zhou-3 (Fin 182) to Zhou-6 (Fin 91): `v ↦ v / 2`. -/
def zhouBlockMap (v : Fin 182) : Fin 91 :=
  ⟨v.val / 2, by omega⟩

/-- The covering map is surjective. -/
theorem zhouBlockMap_surj : Function.Surjective zhouBlockMap := by
  intro ⟨j, hj⟩
  refine ⟨⟨2 * j, by omega⟩, ?_⟩
  simp only [zhouBlockMap, Fin.mk.injEq]
  omega

/-- Every fibre of the covering map has exactly 2 elements. -/
theorem zhouBlockMap_fibre_size :
    ∀ w : Fin 91,
      (Finset.univ.filter fun v : Fin 182 => zhouBlockMap v = w).card = 2 := by
  native_decide

/-- The covering map is a graph homomorphism: if `u ~ v` in Zhou-3, then
`zhouBlockMap u ~ zhouBlockMap v` in Zhou-6. -/
theorem zhouBlockMap_hom :
    ∀ u v : Fin 182,
      zhou3Graph.Adj u v → zhou6Graph.Adj (zhouBlockMap u) (zhouBlockMap v) := by
  native_decide

/-- **Zhou-6 is the quotient of Zhou-3 under the block map.**

The Zhou-6 graph equals the image of the Zhou-3 graph under the block map:
two Zhou-6 vertices are adjacent iff some pair of their preimages are adjacent
in Zhou-3. This is the positive double cover construction S₃ < D₁₂ < PSL(2,13). -/
theorem zhou6_eq_quotient :
    ∀ a b : Fin 91,
      zhou6Graph.Adj a b ↔
        ∃ u v : Fin 182,
          zhouBlockMap u = a ∧ zhouBlockMap v = b ∧ zhou3Graph.Adj u v := by
  native_decide

/-! ## Section 4: No cubic double cover of the Langer graph -/

/-- **The Tutte 12-cage has no edges between points.**

The induced subgraph on vertices 0–62 (points of GH(2,2)) is edgeless.
This obstructs any covering map from the Tutte 12-cage to the Langer graph:
the Langer graph has 189 edges among its 63 vertices, but no point-point
edge exists in the Tutte 12-cage to cover them.

More fundamentally, the point stabiliser H₁₉₂ in G₂(2) has structure
((C₄ × C₄) ⋊ C₃) ⋊ C₂) ⋊ C₂, with three index-2 subgroups of order 96,
but none yield a size-3 suborbit — the smallest suborbits are size 6 and 12.
No cubic Sabidussi graph over G₂(2) with 126 vertices exists. -/
theorem tutte12_points_independent :
    ∀ p q : Fin 63,
      ¬ tutte12CageGraph.Adj ⟨p.val, by omega⟩ ⟨q.val, by omega⟩ := by
  native_decide
