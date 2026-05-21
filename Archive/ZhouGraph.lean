/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.QuotientGraph

/-!
# The Zhou graph (F182A)

The Zhou graph (Foster census F182A) is a cubic arc-transitive graph on 182 vertices.

  - **Sabidussi**: Sab(PSL(2,13), S₃), |PSL(2,13)| = 1092
  - **Imprimitive**: has a Z₂ block system with 91 blocks of size 2.
    S₃ is NOT maximal in PSL(2,13) — the maximal subgroups are D₁₄, D₁₂, A₄,
    Z₁₃ ⋊ Z₆, and Z₇ ⋊ Z₃ (none of order 6).
  - 273 edges, 3-regular

## Visualizations

* [The Zhou graph](https://raw.githubusercontent.com/RaggedR/symmetric-graphs/main/lean/named_graphs/zhou-F182A.jpg) — symmetry-aware drawing with imprimitive block structure

## References

* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798
-/

set_option linter.style.nativeDecide false

private def zhouEdges : List (Fin 182 × Fin 182) := [
  (0,55), (0,135), (0,147), (1,68), (1,139), (1,171),
  (2,9), (2,162), (2,181), (3,22), (3,137), (3,178),
  (4,35), (4,150), (4,167), (5,43), (5,131), (5,134),
  (6,64), (6,91), (6,106), (7,70), (7,120), (7,158),
  (8,15), (8,87), (8,105), (9,153), (9,157), (10,53),
  (10,123), (10,163), (11,20), (11,102), (11,155), (12,41),
  (12,118), (12,131), (13,52), (13,143), (13,179), (14,44),
  (14,97), (14,107), (15,92), (15,181), (16,65), (16,90),
  (16,173), (17,30), (17,130), (17,135), (18,76), (18,98),
  (18,114), (19,33), (19,109), (19,130), (20,85), (20,165),
  (21,27), (21,92), (21,112), (22,142), (22,176), (23,61),
  (23,88), (23,179), (24,49), (24,123), (24,135), (25,60),
  (25,153), (25,173), (26,56), (26,102), (26,115), (27,99),
  (27,137), (28,77), (28,97), (28,154), (29,42), (29,139),
  (29,160), (30,105), (30,122), (31,73), (31,95), (31,153),
  (32,46), (32,117), (32,160), (33,93), (33,158), (34,40),
  (34,99), (34,119), (35,133), (35,145), (36,54), (36,162),
  (36,164), (37,63), (37,88), (37,139), (38,72), (38,142),
  (38,154), (39,69), (39,109), (39,120), (40,106), (40,150),
  (41,102), (41,174), (42,87), (42,112), (43,148), (43,157),
  (44,103), (44,142), (45,58), (45,125), (45,164), (46,100),
  (46,165), (47,48), (47,84), (47,106), (48,114), (48,134),
  (49,109), (49,136), (50,66), (50,149), (50,178), (51,75),
  (51,95), (51,162), (52,145), (52,174), (53,85), (53,117),
  (54,92), (54,119), (55,163), (55,176), (56,110), (56,145),
  (57,71), (57,90), (57,149), (58,107), (58,158), (59,62),
  (59,91), (59,114), (60,136), (60,148), (61,93), (61,125),
  (62,122), (62,147), (63,117), (63,140), (64,167), (64,172),
  (65,103), (65,178), (66,84), (66,99), (67,74), (67,98),
  (67,122), (68,133), (68,179), (69,118), (69,148), (70,97),
  (70,172), (71,115), (71,165), (72,140), (72,163), (73,90),
  (73,100), (74,87), (74,171), (75,125), (75,143), (76,131),
  (76,155), (77,110), (77,167), (78,101), (78,137), (78,151),
  (79,108), (79,129), (79,150), (80,113), (80,134), (80,169),
  (81,121), (81,147), (81,156), (82,86), (82,171), (82,175),
  (83,94), (83,146), (83,181), (84,96), (85,168), (86,173),
  (86,177), (88,169), (89,119), (89,129), (89,168), (91,104),
  (93,166), (94,127), (94,154), (95,156), (96,166), (96,169),
  (98,111), (100,138), (101,161), (101,174), (103,175), (104,138),
  (104,156), (105,116), (107,152), (108,136), (108,177), (110,146),
  (111,152), (111,175), (112,124), (113,127), (113,140), (115,159),
  (116,146), (116,159), (118,151), (120,126), (121,143), (121,161),
  (123,129), (124,126), (124,151), (126,144), (127,157), (128,132),
  (128,152), (128,155), (130,141), (132,164), (132,168), (133,177),
  (138,180), (141,159), (141,170), (144,160), (144,180), (149,170),
  (161,176), (166,170), (172,180)]

private def zhouAdjBool (u v : Fin 182) : Bool :=
  zhouEdges.any fun (a, b) => (u == a && v == b) || (u == b && v == a)

/-- The **Zhou graph** (Foster census F182A): a cubic arc-transitive graph on 182 vertices.
Sab(PSL(2,13), S₃), imprimitive with Z₂ block system (91 blocks of size 2). -/
def zhouGraph : SimpleGraph (Fin 182) where
  Adj u v := zhouAdjBool u v
  symm u v := by simp only [zhouAdjBool]; revert u v; native_decide
  loopless := ⟨fun u => by simp only [zhouAdjBool]; revert u; native_decide⟩

instance : DecidableRel zhouGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (zhouAdjBool u v))

/-- The Zhou graph is 3-regular. -/
theorem zhouGraph_regular :
    ∀ v : Fin 182, (Finset.univ.filter fun w => zhouGraph.Adj v w).card = 3 := by
  native_decide

/-- The Zhou graph has 273 edges. -/
theorem zhouGraph_edgeCount :
    (Finset.univ.filter fun p : Fin 182 × Fin 182 =>
      p.1 < p.2 ∧ zhouGraph.Adj p.1 p.2).card = 273 := by
  native_decide

/-! ### The Z₂ quotient: Sab(PSL(2,13), D₁₂)

S₃ is not maximal in PSL(2,13) — it sits inside D₁₂ (dihedral of order 12,
index 91). The Z₂ block system pairs each of the 182 vertices with one partner,
giving 91 blocks of size 2. The quotient is a 6-regular primitive graph on 91
vertices. D₁₂ IS maximal in PSL(2,13), so this quotient is primitive. -/

private def zhouBlockData : List (Fin 91) := [
  0, 27, 14, 7, 3, 1, 15, 5, 77, 70, 21, 75, 52, 56, 87, 68, 42, 49, 59, 2,
  45, 11, 31, 89, 85, 29, 36, 64, 24, 67, 48, 90, 72, 39, 41, 66, 80, 44, 22, 65,
  71, 46, 25, 13, 6, 15, 50, 33, 43, 68, 42, 8, 9, 49, 23, 30, 18, 85, 88, 4,
  29, 12, 16, 74, 40, 67, 28, 41, 53, 73, 22, 69, 65, 20, 60, 37, 0, 62, 38, 83,
  9, 8, 54, 59, 23, 19, 34, 82, 31, 64, 74, 58, 48, 72, 28, 76, 73, 80, 81, 44,
  46, 17, 61, 10, 1, 83, 27, 26, 62, 5, 35, 57, 11, 19, 4, 89, 16, 40, 79, 90,
  63, 76, 71, 20, 10, 47, 77, 50, 57, 51, 87, 56, 82, 88, 36, 12, 84, 58, 39, 66,
  69, 25, 60, 61, 32, 38, 14, 86, 75, 51, 55, 2, 84, 53, 32, 26, 43, 70, 21, 35,
  52, 30, 78, 17, 13, 37, 7, 47, 33, 34, 78, 63, 86, 54, 45, 6, 3, 18, 79, 81,
  24, 55]

private theorem zhouBlockData_length : zhouBlockData.length = 182 := by native_decide

/-- The Z₂ block map on the Zhou graph: `Fin 182 → Fin 91`. -/
def zhouBlockMap (v : Fin 182) : Fin 91 :=
  zhouBlockData.get (v.cast zhouBlockData_length.symm)

/-- The **Zhou quotient graph**: Sab(PSL(2,13), D₁₂), a 6-regular primitive graph
on 91 vertices. This is the Z₂ quotient of the Zhou graph by the unique
non-trivial block system. -/
def zhouQuotientGraph : SimpleGraph (Fin 91) :=
  zhouGraph.quotientGraph zhouBlockMap

instance : DecidableRel zhouQuotientGraph.Adj := by
  intro i j; unfold zhouQuotientGraph SimpleGraph.quotientGraph; simp only; exact instDecidableAnd

/-- The Zhou quotient is 6-regular. -/
theorem zhouQuotientGraph_regular :
    ∀ v : Fin 91, (Finset.univ.filter fun w => zhouQuotientGraph.Adj v w).card = 6 := by
  native_decide

/-- The Zhou quotient has 273 edges. -/
theorem zhouQuotientGraph_edgeCount :
    (Finset.univ.filter fun p : Fin 91 × Fin 91 =>
      p.1 < p.2 ∧ zhouQuotientGraph.Adj p.1 p.2).card = 273 := by
  native_decide
