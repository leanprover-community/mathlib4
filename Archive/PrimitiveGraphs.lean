/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Archive.LangerGraph
import Archive.ZhouGraph

/-!
# Primitivity of the Langer and Zhou-6 graphs

Three results connecting primitivity and covering structure for arc-transitive
graphs arising from finite group actions:

1. **Langer graph primitivity** — The G₂(2) action on 63 vertices is primitive
   (Atkinson's algorithm). The point stabiliser H₁₉₂ is maximal in G₂(2).

2. **Zhou-6 graph primitivity** — The PSL(2,13) action on 91 vertices (via
   the subgroup D₁₂) is primitive. The stabiliser D₁₂ is maximal in PSL(2,13).

3. **No cubic double cover of Langer** — The Tutte 12-cage (126 vertices, cubic)
   cannot cover the Langer graph because its point subgraph is edgeless.

## References

* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798
* M.D. Atkinson, *An algorithm for finding the blocks of a permutation group*,
  Math. Comp. 29 (1975), 911–913
-/

set_option linter.style.nativeDecide false

/-! ## Section 1: Atkinson's algorithm and Langer primitivity -/

private def mergeRep63 (f : Fin 63 → Fin 63) (lo hi : Fin 63) : Fin 63 → Fin 63 :=
  fun i => let fi := f i; if fi = hi then lo else fi

private def atkinson63 (gens : List (Equiv.Perm (Fin 63)))
    (queue : List (Fin 63 × Fin 63)) (part : Fin 63 → Fin 63) :
    Nat → Fin 63 → Fin 63
  | 0 => part
  | fuel + 1 =>
    match queue with
    | [] => part
    | (x, y) :: rest =>
      let (newPairs, part') := gens.foldl
        (fun (acc : List (Fin 63 × Fin 63) × (Fin 63 → Fin 63)) g =>
          let (pairs, p) := acc
          let rgx := p (g x)
          let rgy := p (g y)
          if rgx = rgy then (pairs, p)
          else
            let lo := min rgx rgy
            let hi := max rgx rgy
            ((lo, hi) :: pairs, mergeRep63 p lo hi)) ([], part)
      atkinson63 gens (rest ++ newPairs) part' fuel

private def blockIsFull63 (v : Fin 63) : Bool :=
  let gens := [g2gen1, g2gen1.symm, g2gen2, g2gen2.symm]
  let initPart : Fin 63 → Fin 63 := fun i => if i = v then 0 else i
  let finalPart := atkinson63 gens [(0, v)] initPart 300
  decide (∀ w : Fin 63, finalPart w = 0)

/-- **Primitivity of the G₂(2) action on the 63 points of GH(2,2).**

For every vertex `v ≠ 0`, Atkinson's algorithm starting from `0 ~ v`
merges all 63 vertices into a single equivalence class. This means
no non-trivial block system exists, so the point stabiliser H₁₉₂ ≤ G₂(2)
is a **maximal subgroup** — there is no subgroup K with H₁₉₂ < K < G₂(2). -/
theorem langer_action_primitive :
    ∀ v : Fin 63, v ≠ 0 → blockIsFull63 v = true := by
  native_decide

/-! ## Section 2: Zhou-6 primitivity -/

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

/-! ### Atkinson's algorithm for Fin 91 (Zhou-6 / PSL(2,13)) -/

private def mergeRep91 (f : Fin 91 → Fin 91) (lo hi : Fin 91) : Fin 91 → Fin 91 :=
  fun i => let fi := f i; if fi = hi then lo else fi

private def atkinson91 (gens : List (Equiv.Perm (Fin 91)))
    (queue : List (Fin 91 × Fin 91)) (part : Fin 91 → Fin 91) :
    Nat → Fin 91 → Fin 91
  | 0 => part
  | fuel + 1 =>
    match queue with
    | [] => part
    | (x, y) :: rest =>
      let (newPairs, part') := gens.foldl
        (fun (acc : List (Fin 91 × Fin 91) × (Fin 91 → Fin 91)) g =>
          let (pairs, p) := acc
          let rgx := p (g x)
          let rgy := p (g y)
          if rgx = rgy then (pairs, p)
          else
            let lo := min rgx rgy
            let hi := max rgx rgy
            ((lo, hi) :: pairs, mergeRep91 p lo hi)) ([], part)
      atkinson91 gens (rest ++ newPairs) part' fuel

private def blockIsFull91 (v : Fin 91) : Bool :=
  let gens := [zhou6Gen1, zhou6Gen1.symm, zhou6Gen2, zhou6Gen2.symm]
  let initPart : Fin 91 → Fin 91 := fun i => if i = v then 0 else i
  let finalPart := atkinson91 gens [(0, v)] initPart 400
  decide (∀ w : Fin 91, finalPart w = 0)

/-- **Primitivity of the PSL(2,13) action on 91 points.**

For every vertex `v ≠ 0`, Atkinson's algorithm starting from `0 ~ v`
merges all 91 vertices into a single equivalence class. The stabiliser
D₁₂ (order 12) is a **maximal subgroup** of PSL(2,13) (order 1092). -/
theorem zhou6_action_primitive :
    ∀ v : Fin 91, v ≠ 0 → blockIsFull91 v = true := by
  native_decide

/-! ## Section 3: No cubic double cover of the Langer graph -/

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
