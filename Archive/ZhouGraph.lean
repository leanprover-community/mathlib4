/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.QuotientGraph
import Mathlib.Combinatorics.SimpleGraph.SabidussiWitness

/-!
# The Zhou-3 graph (F182A) and its Z₂ quotient (Zhou-6)

The **Zhou-3 graph** (Foster census F182A) is a cubic arc-transitive graph on 182 vertices.

  - **Sabidussi**: Sab(PSL(2,13), S₃), |PSL(2,13)| = 1092
  - **Imprimitive**: S₃ is NOT maximal — sits inside D₁₂ (dihedral order 12, index 91)
  - 273 edges, 3-regular

The **Zhou-6 graph** is the Z₂ quotient: Sab(PSL(2,13), D₁₂), a 6-regular graph on
91 vertices. D₁₂ IS maximal in PSL(2,13), so the quotient is **primitive**.

## Visualizations

* [The Zhou-3 graph](https://raw.githubusercontent.com/RaggedR/symmetric-graphs/main/lean/named_graphs/zhou3-F182A.jpg) — 182 vertices, imprimitive block structure
* [The Zhou-6 quotient](https://raw.githubusercontent.com/RaggedR/symmetric-graphs/main/lean/named_graphs/zhou6-91v.jpg) — 91-vertex quotient by the Z₂ block system

## Main results

* `zhouGraph_regular` — the Zhou-3 graph is 3-regular
* `zhou6Graph_regular` — the Zhou-6 graph is 6-regular
* `zhou6_eq_quotient` — the Zhou-6 graph equals `zhouGraph.quotientGraph zhouBlockMap`

## References

* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798
-/

set_option linter.style.nativeDecide false

/-! ### The Zhou-3 graph (3-regular, 182 vertices) -/

private def zhouEdges : List (Fin 182 × Fin 182) := [
(0,3),(0,37),(0,68),(1,4),(1,38),(1,71),
  (2,5),(2,8),(2,42),(3,18),(3,47),(4,27),
  (4,56),(5,33),(5,61),(6,7),(6,37),(6,89),
  (7,31),(7,95),(8,15),(8,74),(9,10),(9,20),
  (9,92),(10,16),(10,80),(11,12),(11,31),(11,103),
  (12,35),(12,49),(13,14),(13,32),(13,116),(14,21),
  (14,120),(15,17),(15,111),(16,38),(16,132),(17,19),
  (17,129),(18,24),(18,124),(19,29),(19,137),(20,21),
  (20,144),(21,53),(22,23),(22,36),(22,106),(23,30),
  (23,83),(24,26),(24,149),(25,26),(25,35),(25,162),
  (26,87),(27,28),(27,155),(28,32),(28,91),(29,30),
  (29,166),(30,62),(31,147),(32,134),(33,34),(33,172),
  (34,36),(34,136),(35,176),(36,161),(37,180),(38,121),
  (39,43),(39,56),(39,84),(40,41),(40,45),(40,85),
  (41,63),(41,92),(42,69),(42,99),(43,52),(43,77),
  (44,49),(44,60),(44,73),(45,47),(45,114),(46,48),
  (46,62),(46,112),(47,102),(48,65),(48,106),(49,55),
  (50,51),(50,61),(50,130),(51,60),(51,126),(52,67),
  (52,137),(53,54),(53,63),(54,66),(54,123),(55,57),
  (55,150),(56,105),(57,70),(57,147),(58,59),(58,68),
  (58,90),(59,66),(59,156),(60,162),(61,146),(62,67),
  (63,169),(64,65),(64,71),(64,133),(65,96),(66,116),
  (67,179),(68,168),(69,70),(69,160),(70,138),(71,178),
  (72,73),(72,80),(72,118),(73,94),(74,82),(74,108),
  (75,76),(75,93),(75,116),(76,90),(76,104),(77,95),
  (77,101),(78,79),(78,99),(78,140),(79,88),(79,124),
  (80,126),(81,83),(81,94),(81,150),(82,97),(82,122),
  (83,86),(84,91),(84,152),(85,86),(85,161),(86,127),
  (87,88),(87,96),(88,112),(89,90),(89,142),(91,93),
  (92,163),(93,171),(94,166),(95,174),(96,98),(97,98),
  (97,178),(98,176),(99,177),(100,104),(100,106),(100,125),
  (101,103),(101,110),(102,119),(102,127),(103,131),(104,136),
  (105,107),(105,110),(107,121),(107,151),(108,113),(108,146),
  (109,112),(109,120),(109,158),(110,157),(111,117),(111,160),
  (113,119),(113,167),(114,115),(114,149),(115,117),(115,163),
  (117,175),(118,121),(118,170),(119,180),(120,140),(122,123),
  (122,129),(123,139),(124,145),(125,133),(125,142),(126,143),
  (127,128),(128,135),(128,155),(129,156),(130,136),(130,171),
  (131,139),(131,169),(132,133),(132,164),(134,135),(134,138),
  (135,150),(137,175),(138,140),(139,176),(141,142),(141,147),
  (141,154),(143,144),(143,148),(144,158),(145,151),(145,168),
  (146,148),(148,173),(149,153),(151,177),(152,153),(152,175),
  (153,181),(154,160),(154,164),(155,167),(156,165),(157,159),
  (157,172),(158,179),(159,161),(159,169),(162,181),(163,164),
  (165,166),(165,170),(167,178),(168,170),(171,181),(172,177),
  (173,174),(173,180),(174,179)]

private def zhouAdjBool (u v : Fin 182) : Bool :=
  zhouEdges.any fun (a, b) => (u == a && v == b) || (u == b && v == a)

/-- The **Zhou-3 graph** (F182A): Sab(PSL(2,13), S₃), cubic, 182 vertices. Imprimitive. -/
def zhouGraph : SimpleGraph (Fin 182) where
  Adj u v := zhouAdjBool u v
  symm u v := by simp only [zhouAdjBool]; revert u v; native_decide
  loopless := ⟨fun u => by simp only [zhouAdjBool]; revert u; native_decide⟩

instance : DecidableRel zhouGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (zhouAdjBool u v))

/-- The Zhou-3 graph is 3-regular. -/
theorem zhouGraph_regular :
    ∀ v : Fin 182, (Finset.univ.filter fun w => zhouGraph.Adj v w).card = 3 := by
  native_decide

/-- The Zhou-3 graph has 273 edges. -/
theorem zhouGraph_edgeCount :
    (Finset.univ.filter fun p : Fin 182 × Fin 182 =>
      p.1 < p.2 ∧ zhouGraph.Adj p.1 p.2).card = 273 := by
  native_decide

/-! ### The Z₂ block map -/

private def zhouBlockData : List (Fin 91) := [
  0, 14, 9, 6, 3, 1, 50, 19, 25, 60, 22, 49, 32, 17, 75, 21, 35, 13, 15, 43,
  34, 64, 62, 68, 39, 29, 8, 41, 28, 76, 46, 79, 5, 26, 69, 78, 31, 56, 40, 42,
  18, 53, 56, 11, 61, 58, 70, 40, 74, 64, 27, 7, 37, 46, 57, 51, 25, 71, 16, 4,
  23, 15, 32, 36, 10, 2, 24, 80, 41, 45, 30, 26, 90, 2, 79, 72, 55, 58, 66, 33,
  21, 88, 47, 8, 36, 45, 87, 28, 81, 34, 61, 68, 1, 65, 54, 35, 16, 82, 84, 37,
  89, 81, 23, 5, 47, 24, 6, 73, 54, 48, 38, 78, 18, 83, 51, 52, 9, 12, 65, 86,
  13, 62, 87, 30, 60, 38, 42, 55, 20, 39, 80, 86, 76, 57, 69, 77, 49, 0, 10, 67,
  90, 85, 33, 77, 31, 67, 74, 3, 63, 75, 11, 83, 82, 44, 63, 43, 27, 12, 73, 59,
  70, 50, 14, 72, 20, 59, 19, 48, 71, 7, 52, 66, 29, 44, 84, 89, 22, 88, 53, 4,
  17, 85]

private theorem zhouBlockData_length : zhouBlockData.length = 182 := by native_decide

/-- The Z₂ block map on the Zhou-3 graph: `Fin 182 → Fin 91`. -/
def zhouBlockMap (v : Fin 182) : Fin 91 :=
  zhouBlockData.get (v.cast zhouBlockData_length.symm)

/-! ### The Zhou-6 graph (6-regular, 91 vertices, primitive) -/

private def zhou6AdjBool (u v : Fin 91) : Bool :=
  let edges : List (Fin 91 × Fin 91) := [
(0,6),(0,37),(0,41),(0,43),(0,56),(0,89),
  (1,9),(1,15),(1,26),(1,53),(1,60),(1,72),
  (2,10),(2,16),(2,54),(2,61),(2,74),(2,90),
  (3,14),(3,25),(3,41),(3,71),(3,79),(3,85),
  (4,16),(4,24),(4,27),(4,73),(4,80),(4,84),
  (5,17),(5,28),(5,49),(5,69),(5,81),(5,86),
  (6,15),(6,40),(6,62),(6,74),(6,89),(7,23),
  (7,27),(7,36),(7,42),(7,59),(7,86),(8,28),
  (8,29),(8,39),(8,68),(8,87),(8,88),(9,17),
  (9,24),(9,25),(9,56),(9,72),(10,26),(10,30),
  (10,57),(10,69),(10,90),(11,37),(11,42),(11,51),
  (11,58),(11,77),(11,88),(12,29),(12,38),(12,52),
  (12,59),(12,78),(12,89),(13,21),(13,39),(13,43),
  (13,48),(13,75),(13,90),(14,23),(14,26),(14,29),
  (14,40),(14,85),(15,27),(15,39),(15,60),(15,74),
  (16,28),(16,41),(16,61),(16,84),(17,44),(17,56),
  (17,75),(17,86),(18,45),(18,48),(18,53),(18,58),
  (18,70),(18,81),(19,35),(19,50),(19,54),(19,59),
  (19,76),(19,79),(20,43),(20,55),(20,63),(20,72),
  (20,76),(20,77),(21,22),(21,25),(21,42),(21,78),
  (21,90),(22,35),(22,60),(22,67),(22,78),(22,84),
  (23,40),(23,55),(23,61),(23,86),(24,25),(24,38),
  (24,57),(24,73),(25,42),(25,79),(26,29),(26,53),
  (26,69),(27,39),(27,59),(27,80),(28,41),(28,68),
  (28,81),(29,78),(29,88),(30,45),(30,57),(30,67),
  (30,71),(30,87),(31,34),(31,50),(31,62),(31,69),
  (31,73),(31,77),(32,46),(32,49),(32,64),(32,70),
  (32,78),(32,80),(33,34),(33,38),(33,60),(33,66),
  (33,81),(33,85),(34,50),(34,60),(34,61),(34,64),
  (35,40),(35,58),(35,76),(35,84),(36,42),(36,46),
  (36,53),(36,68),(36,82),(37,56),(37,66),(37,80),
  (37,88),(38,57),(38,81),(38,89),(39,75),(39,87),
  (40,58),(40,62),(41,43),(41,71),(42,77),(43,48),
  (43,76),(44,63),(44,75),(44,82),(44,84),(44,85),
  (45,50),(45,56),(45,70),(45,87),(46,57),(46,64),
  (46,68),(46,76),(47,49),(47,55),(47,79),(47,82),
  (47,87),(47,89),(48,53),(48,73),(48,83),(49,69),
  (49,79),(49,80),(50,56),(50,59),(51,52),(51,58),
  (51,64),(51,71),(51,75),(52,59),(52,65),(52,71),
  (52,72),(53,82),(54,74),(54,79),(54,83),(54,88),
  (55,61),(55,72),(55,87),(57,76),(58,81),(60,67),
  (61,64),(62,65),(62,68),(62,73),(63,70),(63,74),
  (63,77),(63,85),(64,75),(65,66),(65,68),(65,72),
  (65,90),(66,80),(66,85),(66,90),(67,71),(67,83),
  (67,86),(69,77),(70,74),(70,78),(73,83),(82,84),
  (82,89),(83,86),(83,88)]
  edges.any fun (a, b) => (u == a && v == b) || (u == b && v == a)

/-- The **Zhou-6 graph**: Sab(PSL(2,13), D₁₂), 6-regular, 91 vertices, **primitive**. -/
def zhou6Graph : SimpleGraph (Fin 91) where
  Adj u v := zhou6AdjBool u v
  symm u v := by unfold zhou6AdjBool; revert u v; native_decide
  loopless := ⟨fun u => by unfold zhou6AdjBool; revert u; native_decide⟩

instance : DecidableRel zhou6Graph.Adj :=
  fun u v => inferInstanceAs (Decidable (zhou6AdjBool u v))

/-- The Zhou-6 graph is 6-regular. -/
theorem zhou6Graph_regular :
    ∀ v : Fin 91, (Finset.univ.filter fun w => zhou6Graph.Adj v w).card = 6 := by
  native_decide

/-- The Zhou-6 graph has 273 edges. -/
theorem zhou6Graph_edgeCount :
    (Finset.univ.filter fun p : Fin 91 × Fin 91 =>
      p.1 < p.2 ∧ zhou6Graph.Adj p.1 p.2).card = 273 := by
  native_decide

/-! ### Quotient relationship

The Zhou-6 graph is the Z₂ quotient of the Zhou-3 graph via `zhouBlockMap`.
Each block has size 2; we precompute both representatives per block and
reduce the existential to checking 4 pairs. -/

/-- The Z₂ quotient of the Zhou-3 graph (defined abstractly via quotientGraph). -/
def zhouQuotientGraph : SimpleGraph (Fin 91) :=
  zhouGraph.quotientGraph zhouBlockMap

/-- For each block `b ∈ Fin 91`, the two vertices `u₁, u₂ ∈ Fin 182` with
`zhouBlockMap u = b`. Precomputed to make the quotient proof decidable. -/
private def zhouBlockReps : Array (Fin 182 × Fin 182) := #[
  (0,137),(5,92),(65,73),(4,147),(59,179),(32,103),(3,106),(51,169),(26,83),(2,116),
  (64,138),(43,150),(117,157),(17,120),(1,162),(18,61),(58,96),(13,180),(40,112),
  (7,166),(128,164),(15,80),(10,176),(60,102),(66,105),(8,56),(33,71),(50,156),
  (28,87),(25,172),(70,123),(36,144),(12,62),(79,142),(20,89),(16,95),(63,84),
  (52,99),(110,125),(24,129),(38,47),(27,68),(39,126),(19,155),(153,173),(69,85),
  (30,53),(82,104),(109,167),(11,136),(6,161),(55,114),(115,170),(41,178),(94,108),
  (76,127),(37,42),(54,133),(45,77),(159,165),(9,124),(44,90),(22,121),(148,154),
  (21,49),(93,118),(78,171),(139,145),(23,91),(34,134),(46,160),(57,168),(75,163),
  (107,158),(48,146),(14,149),(29,132),(135,143),(35,111),(31,74),(67,130),(88,101),
  (97,152),(113,151),(98,174),(141,181),(119,131),(86,122),(81,177),(100,175),(72,140)]
private theorem zhouBlockReps_size : zhouBlockReps.size = 91 := by native_decide

/-- The precomputed representatives are correct: both map to the given block. -/
private theorem zhouBlockReps_correct :
    ∀ b : Fin 91,
      let r := zhouBlockReps[b.val]'(by have := zhouBlockReps_size; omega)
      zhouBlockMap r.1 = b ∧ zhouBlockMap r.2 = b := by
  native_decide

/-- Every vertex maps to one of the two representatives for its block. -/
private theorem zhouBlockMap_exhaustive :
    ∀ v : Fin 182,
      let r := zhouBlockReps[(zhouBlockMap v).val]'(by have := zhouBlockReps_size; omega)
      v = r.1 ∨ v = r.2 := by
  native_decide

/-- **The Zhou-6 graph equals the Z₂ quotient of the Zhou-3 graph.**

`zhou6Graph.Adj a b ↔ zhouGraph.quotientGraph(zhouBlockMap).Adj a b` for all `a b`. -/
theorem zhou6_eq_quotient : zhou6Graph = zhouQuotientGraph := by
  ext a b
  simp only [zhouQuotientGraph, SimpleGraph.quotientGraph]
  constructor
  · intro h
    refine ⟨by rintro rfl; exact (zhou6Graph.loopless.irrefl a) h, ?_⟩
    let ra := zhouBlockReps[a.val]'(by have := zhouBlockReps_size; omega)
    let rb := zhouBlockReps[b.val]'(by have := zhouBlockReps_size; omega)
    -- At least one of the 4 cross-block pairs must be adjacent in zhouGraph.
    -- We prove this by native_decide on a Bool reformulation.
    have : ∀ a b : Fin 91, zhou6Graph.Adj a b →
        let ra := zhouBlockReps[a.val]'(by have := zhouBlockReps_size; omega)
        let rb := zhouBlockReps[b.val]'(by have := zhouBlockReps_size; omega)
        zhouGraph.Adj ra.1 rb.1 ∨ zhouGraph.Adj ra.1 rb.2 ∨
        zhouGraph.Adj ra.2 rb.1 ∨ zhouGraph.Adj ra.2 rb.2 := by native_decide
    obtain h4 := this a b h
    rcases h4 with h1 | h2 | h3 | h4
    · exact ⟨ra.1, rb.1, (zhouBlockReps_correct a).1, (zhouBlockReps_correct b).1, h1⟩
    · exact ⟨ra.1, rb.2, (zhouBlockReps_correct a).1, (zhouBlockReps_correct b).2, h2⟩
    · exact ⟨ra.2, rb.1, (zhouBlockReps_correct a).2, (zhouBlockReps_correct b).1, h3⟩
    · exact ⟨ra.2, rb.2, (zhouBlockReps_correct a).2, (zhouBlockReps_correct b).2, h4⟩
  · rintro ⟨hne, u, v, hu, hv, hadj⟩
    have key : ∀ u v : Fin 182, zhouGraph.Adj u v →
        zhou6Graph.Adj (zhouBlockMap u) (zhouBlockMap v) := by native_decide
    rw [← hu, ← hv]; exact key u v hadj

/-! ## Sabidussi coset graph representations -/

section ZhouSabidussi

/-! ### Zhou-3: Sab(PSL(2,13), S₃) -/

private def zG1F : Array (Fin 182) := #[120,121,114,109,118,45,13,116,115,101,110,76,104,49,12,117,105,111,112,15,103,11,113,108,46,106,48,72,73,8,74,75,44,47,102,100,119,14,107,165,174,95,149,156,34,179,97,158,178,136,85,161,129,31,147,130,170,171,138,70,36,40,82,7,1,71,57,122,140,153,181,38,172,33,163,150,135,59,26,87,157,61,164,146,166,173,148,65,96,32,134,94,77,81,5,66,64,132,133,24,155,58,144,90,128,168,167,145,92,176,68,175,98,9,67,52,55,137,177,20,35,151,154,141,88,27,159,143,126,160,86,89,56,4,60,51,127,17,162,142,25,91,28,169,131,79,41,93,63,62,50,124,29,30,84,80,69,0,139,37,152,180,22,43,39,42,2,10,78,6,99,83,3,53,54,19,125,18,16,123,21,23]
private def zG1I : Array (Fin 182) := #[157,64,166,172,133,94,169,63,29,113,167,21,14,6,37,19,178,137,177,175,119,180,162,181,99,140,78,125,142,152,153,53,89,73,44,120,60,159,71,164,61,146,165,163,32,5,24,33,26,13,150,135,115,173,174,116,132,66,101,77,134,81,149,148,96,87,95,114,110,156,59,65,27,28,30,31,11,92,168,145,155,93,62,171,154,50,130,79,124,131,103,141,108,147,91,41,88,46,112,170,35,9,34,20,12,16,25,38,23,3,10,17,18,22,2,8,7,15,4,36,0,1,67,179,151,176,128,136,104,52,55,144,97,98,90,76,49,117,58,158,68,123,139,127,102,107,83,54,86,42,75,121,160,69,122,100,43,80,47,126,129,51,138,74,82,39,84,106,105,143,56,57,72,85,40,111,109,118,48,45,161,70]
private def zG2F : Array (Fin 182) := #[150,163,172,135,115,33,94,166,157,64,133,156,59,26,87,110,132,101,134,77,65,96,148,173,32,116,13,114,149,95,174,165,24,5,61,66,146,81,164,175,167,178,177,137,90,155,158,128,144,58,136,104,52,98,176,68,117,168,49,12,76,34,179,97,9,20,35,67,55,151,145,92,142,89,159,162,60,19,78,140,125,37,169,180,152,113,119,14,120,73,44,153,71,181,6,29,21,63,53,99,126,17,127,129,51,111,143,160,161,112,15,105,109,85,27,4,25,56,141,86,88,154,131,139,138,80,100,102,47,103,130,122,16,10,18,3,50,43,124,123,79,118,72,106,48,70,36,170,22,28,0,69,84,91,121,45,11,8,46,74,107,108,75,1,38,31,7,40,57,82,147,171,2,23,30,39,54,42,41,62,83,93]
private def zG2I : Array (Fin 182) := #[150,163,172,135,115,33,94,166,157,64,133,156,59,26,87,110,132,101,134,77,65,96,148,173,32,116,13,114,149,95,174,165,24,5,61,66,146,81,164,175,167,178,177,137,90,155,158,128,144,58,136,104,52,98,176,68,117,168,49,12,76,34,179,97,9,20,35,67,55,151,145,92,142,89,159,162,60,19,78,140,125,37,169,180,152,113,119,14,120,73,44,153,71,181,6,29,21,63,53,99,126,17,127,129,51,111,143,160,161,112,15,105,109,85,27,4,25,56,141,86,88,154,131,139,138,80,100,102,47,103,130,122,16,10,18,3,50,43,124,123,79,118,72,106,48,70,36,170,22,28,0,69,84,91,121,45,11,8,46,74,107,108,75,1,38,31,7,40,57,82,147,171,2,23,30,39,54,42,41,62,83,93]
private theorem zG1F_s : zG1F.size = 182 := by native_decide
private theorem zG1I_s : zG1I.size = 182 := by native_decide
private theorem zG2F_s : zG2F.size = 182 := by native_decide
private theorem zG2I_s : zG2I.size = 182 := by native_decide
private def zG1 : Equiv.Perm (Fin 182) where
  toFun i := zG1F[i.val]'(by have := zG1F_s; omega)
  invFun i := zG1I[i.val]'(by have := zG1I_s; omega)
  left_inv := by native_decide
  right_inv := by native_decide
private def zG2 : Equiv.Perm (Fin 182) where
  toFun i := zG2F[i.val]'(by have := zG2F_s; omega)
  invFun i := zG2I[i.val]'(by have := zG2I_s; omega)
  left_inv := by native_decide
  right_inv := by native_decide
private def zGens : Fin 2 → Equiv.Perm (Fin 182) | 0 => zG1 | 1 => zG2
private def zGroup : Subgroup (Equiv.Perm (Fin 182)) := Subgroup.closure (Set.range zGens)

private def zWD : Array (List (Fin 4)) := #[
  [],[0,1,0,0,0],[2,2,1,0,1,2],[2,2,1,2,2,2],[2,1,0,1],[2,2,2,1,2],[1,0,1,2,2,2],[1,2,1,0,1,0,0],
  [2,1],[0,1,0,0,1],[2,1,0,1,2,1],[0,1,0,1,0],[0,0,0,1,2,2,2],[1,0,1,2,2],[0,0,0,1,0,0,0],[1,2,2,1,2,1,0,0],
  [0,0,1,0,1,2,2],[0,1,0,0,1,0,1],[1,2,2,1,0,1,0],[1,2,2,1,2,1,0],[2,1,0,0,0,1,2],[0,1,0,1],[1,2,1,0],[1,0,0,0,1],
  [0,0,0,1,2,1,0,1,2],[1,0,1,0,0,1,2],[1,0,1,2,2,1],[2,2,1,0],[1,2,2,1,0,0,1],[2,1,2],[0,0,0,1,0,1,2],[1,2,2],
  [1,0,1,0,1,2,2,2],[2,2,2,1,2,1],[1,0,1,0,1,2],[0,0],[0,0,1,2,2,2,1],[0,0,0,1,0,0],[1,2,2,1,2,2,1],[1,2,2,1,2],
  [2,2,1,2,1,2,2],[0,0,1,2,2],[1,2,2,1,0],[0,1,0,0,0,1,0],[1,0,1,0,1,2,2],[2,2,2,1],[0,0,0,1,2,1,0,1],[0,0,0,1,2,1],
  [0,0,1,2,2,1,2],[1,0,1,2],[1,0],[0,0,0,1,2,2,1],[2,1,0,0],[1,2,2,2],[2,2,1,2,1],[1,2,1,0,1,2,2,2],
  [2,2,1,2,1,0,1,2],[0,0,1,0],[0,1,2,1,2],[0,0,0,1,2,2,2,1],[0,1,0,1,0,0,1],[1,0,1,0,1,2,1],[2,2,2,1,0,1],[1,2,1,0,1,0],
  [0,1,0,0],[2,1,0,0,0,1,2,1],[0,0,1],[2,2,1,0,1,0],[2,1,0,1,2,1,0,0],[0,1,2,2,1],[1,0,0,0,1,2,2],[1,0,0,0,1,0,0,1],
  [2,2,1,0,0],[2,2,2,1,2,1,2],[0,0,0,1,0,1],[1,2],[0,1,0,1,0,0],[1,0,0,0,1,0,0,0],[0,0,1,0,1,0],[2,1,2,2,2,1,0,0],
  [2,2],[0,0,0,1,0,0,1],[1,0,1,0,0,0,1],[0,0,1,0,0,0],[2,1,2,2,1],[1,0,0],[1,2,1,0,1,2],[0,0,0,1,0,0,0,1],
  [0,1],[1,0,1,0,1,0,0,0],[2,1,0,0,0,1,0],[0,1,2,2,1,0,1],[1,0,0,0,1,0,0],[1,0,0,0,1,2,1],[2,2,2,1,2,2],[0,0,1,2],
  [0,1,0],[1,2,1,0,1,0,1],[1,2,2,2,1],[2,2,1,2,1,0,1,0],[0,0,0],[0,1,0,0,1,0],[1,0,1,0,1],[2,1,0,0,0,1],
  [0,0,0,1,2,2],[0,0,1,0,1,2],[1,0,1,0,0,1],[2,1,2,2,2,1],[1,0,0,0,1,0],[2,2,1,2,2],[2,1,0,1,2,1,0],[0,0,1,0,1,2,1],
  [1,2,2,2,1,2],[1,0,0,1],[2,2,1,0,1],[2,1,0],[1,0,1,0,0,1,2,1],[0,1,0,0,0,1,0,1,2],[2,1,0,1,0],[1,2,1,0,1,2,1],
  [0],[0,1,2,2,2],[0,1,2,2,2,1,2],[2,2,2,1,0,0],[0,1,2],[2,2,1],[0,0,0,1],[1,0,1,0],
  [0,0,0,1,2],[2,1,0,0,0],[1,2,1,0,1,2,2],[1,0,1,0,1,0,0],[0,0,1,0,1,2,2,1],[2,1,0,1,2],[0,1,0,1,0,0,1,2],[0,1,0,1,0,0,0],
  [1,0,1],[0,1,0,0,0,1,0,1],[0,1,2,1],[2,2,1,0,0,1,2],[1,0,1,0,0,1,2,2],[2,1,0,1,0,1],[2,2,1,0,0,1],[1,0,1,0,0],
  [1,0,1,0,1,0],[2,1,2,2,2,1,0],[0,0,1,2,2,2],[2,2,1,2,1,0],[1,2,1,0,1],[1,2,2,1,0,0],[1],[0,1,2,2],
  [2,1,2,2],[0,1,2,2,1,0],[0,1,2,2,2,1],[2,2,2],[0,1,0,1,0,1],[2],[0,0,0,1,2,1,0],[0,0,0,1,0],
  [2,1,2,2,2],[0,1,0,1,2,2],[1,2,1],[0,1,0,0,0,1],[1,2,2,1,2,2],[1,2,2,1],[2,1,2,2,1,0],[1,0,1,0,0,1,0],
  [0,0,1,0,1],[1,0,1,0,0,0],[2,2,1,2,1,0,1],[0,0,1,0,0],[2,2,1,0,0,0],[1,0,0,0],[2,2,1,2,1,2],[1,2,2,1,2,1],
  [2,2,1,2],[1,2,2,1,0,1],[0,0,1,2,2,1],[2,2,2,1,0],[0,1,0,1,2],[1,0,0,0,1,2]]
private theorem zWD_s : zWD.size = 182 := by native_decide
private def zWit (v : Fin 182) : List (Fin 4) := zWD[v.val]'(by have := zWD_s; omega)
private theorem zWit_ok : ∀ v : Fin 182, applyWord' zGens (zWit v) 0 = v := by native_decide
private noncomputable instance : MulAction zGroup (Fin 182) := MulAction.compHom _ zGroup.subtype
private noncomputable instance : GraphAction zGroup (Fin 182) zhouGraph where
  adj_smul g u v h := closureGraphAction zGens
    (fun i => by match i with | 0 => exact (by native_decide) | 1 => exact (by native_decide))
    g.1 g.2 u v h
private noncomputable instance : MulAction.IsPretransitive zGroup (Fin 182) where
  exists_smul_eq x y :=
    ⟨⟨_, zGroup.mul_mem (applyWord'_mem zGens _) (zGroup.inv_mem (applyWord'_mem zGens _))⟩, by
      change ((applyWord' zGens (zWit x)).symm.trans (applyWord' zGens (zWit y))) x = y
      simp only [Equiv.trans_apply]
      rw [show (applyWord' zGens (zWit x)).symm x = 0 from by
        rw [Equiv.symm_apply_eq]; exact (zWit_ok x).symm]; exact zWit_ok y⟩

/-- **The Zhou-3 graph is a Sabidussi coset graph**: `Sab(PSL(2,13), S₃, D)`.

PSL(2,13) (order 1092) acts vertex-transitively on the 182 vertices.
The stabilizer of vertex 0 has order 6 (≅ S₃), giving 1092/6 = 182 vertices. -/
noncomputable def zhouSabidussiIso :
    zhouGraph ≃g SimpleGraph.cosetGraph (MulAction.stabilizer zGroup (0 : Fin 182))
      (connectionSet zGroup zhouGraph 0) (connectionSet.isConnectionSet 0) :=
  sabidussiIso 0

/-! ### Zhou-6: Sab(PSL(2,13), D₁₂) -/

private def z6G1F : Array (Fin 91) := #[89,71,7,84,68,48,12,90,1,41,86,74,33,55,22,52,36,43,45,80,79,61,64,21,28,16,67,65,53,60,17,88,31,58,11,32,10,6,81,72,78,82,2,47,76,56,69,24,87,73,37,63,85,30,27,25,0,5,70,66,51,42,29,19,77,14,40,75,26,83,50,44,3,8,59,20,49,54,34,4,62,18,57,39,46,35,13,9,15,38,23]
private def z6G1I : Array (Fin 91) := #[56,8,42,72,79,57,37,2,73,87,36,34,6,86,65,88,25,30,81,63,75,23,14,90,47,55,68,54,24,62,53,32,35,12,78,85,16,50,89,83,66,9,61,17,71,18,84,43,5,76,70,60,15,28,77,13,45,82,33,74,29,21,80,51,22,27,59,26,4,46,58,1,39,49,11,67,44,64,40,20,19,38,41,69,3,52,10,48,31,0,7]
private def z6G2F : Array (Fin 91) := #[32,65,53,63,81,56,46,41,87,66,1,79,61,29,20,68,18,37,59,84,21,14,40,43,33,85,72,28,45,55,15,24,86,31,73,35,71,49,34,8,76,70,3,78,11,27,67,75,12,17,4,54,2,52,82,13,80,60,19,16,62,48,57,42,83,10,69,6,30,9,7,74,90,38,36,88,22,25,23,44,5,50,51,89,58,77,0,39,47,64,26]
private def z6G2I : Array (Fin 91) := #[86,10,52,42,50,80,67,70,39,69,65,44,48,55,21,30,59,49,16,58,14,20,76,78,31,77,90,45,27,13,68,33,0,24,38,35,74,17,73,87,22,7,63,23,79,28,6,88,61,37,81,82,53,2,51,29,5,62,84,18,57,12,60,3,89,1,9,46,15,66,41,36,26,34,71,47,40,85,43,11,56,4,54,64,19,25,32,8,75,83,72]
private theorem z6G1F_s : z6G1F.size = 91 := by native_decide
private theorem z6G1I_s : z6G1I.size = 91 := by native_decide
private theorem z6G2F_s : z6G2F.size = 91 := by native_decide
private theorem z6G2I_s : z6G2I.size = 91 := by native_decide
private def z6G1 : Equiv.Perm (Fin 91) where
  toFun i := z6G1F[i.val]'(by have := z6G1F_s; omega)
  invFun i := z6G1I[i.val]'(by have := z6G1I_s; omega)
  left_inv := by native_decide
  right_inv := by native_decide
private def z6G2 : Equiv.Perm (Fin 91) where
  toFun i := z6G2F[i.val]'(by have := z6G2F_s; omega)
  invFun i := z6G2I[i.val]'(by have := z6G2I_s; omega)
  left_inv := by native_decide
  right_inv := by native_decide
private def z6Gens : Fin 2 → Equiv.Perm (Fin 91) | 0 => z6G1 | 1 => z6G2
private def z6Group : Subgroup (Equiv.Perm (Fin 91)) := Subgroup.closure (Set.range z6Gens)

private def z6WD : Array (List (Fin 4)) := #[
  [],[3,2,1],[1,2,2,2,1],[0,3,0,0,0],[0,0,0,3],[2,3],[0,3,2,2,3],[0,0,0,1,2,1],
  [0,0,3,0],[0,3,2,1],[3,2],[0,0,1,0],[1,0,3,2],[3,0],[0,1,2,2],[1,0,0,0],[2,2,2,3],
  [0,0,3,2,1],[2,2,2],[2,1,2],[0,1,2,2,1],[0,1,2,2,3],[0,1,2],[0,0,1,2,1],[1,0,1],
  [0,1,0,1],[0,3,0,0,3],[2,2,1],[2,2,3],[3,0,1],[1,0,0,0,3],[1,0],[1],[1,0,3],[0,0,1],
  [1,2],[3,2,2],[0,0,0,1,0],[0,0],[0,3,0],[0,1,2,1],[0,3,2,1,0],[2,1,2,2,1],
  [0,0,1,2,3],[0,0,1,0,3],[2,2],[0,3,2,2],[1,0,0,1],[2,3,0],[0,0,3,2],[0,0,0,1],
  [0,1,0,0,3],[1,2,2,2],[2,2,3,0],[0,1,0,0],[3,0,0],[2],[2,3,2],[1,0,3,0],[2,2,2,1],
  [2,1,0,3],[2,3,0,3],[2,1,0],[2,1,2,2],[0,1],[3,2,3],[0,3,2,3],[0,3,2,2,1],
  [0,0,0,3,0],[0,3,2],[0,0,0,1,2],[3,2,1,0],[0,3,0,0],[0,0,3],[3,2,2,3],[1,0,0,3],
  [0,1,2,3],[0,1,0],[0,0,1,2],[0,0,0,3,2],[2,1],[0,0,0],[2,3,2,2],[0,3],[2,1,2,1],
  [1,2,2],[3],[0,3,0,3],[1,0,0],[0],[0,3,0,0,1]]
private theorem z6WD_s : z6WD.size = 91 := by native_decide
private def z6Wit (v : Fin 91) : List (Fin 4) := z6WD[v.val]'(by have := z6WD_s; omega)
private theorem z6Wit_ok : ∀ v : Fin 91, applyWord' z6Gens (z6Wit v) 0 = v := by native_decide
private noncomputable instance : MulAction z6Group (Fin 91) := MulAction.compHom _ z6Group.subtype
private noncomputable instance : GraphAction z6Group (Fin 91) zhou6Graph where
  adj_smul g u v h := closureGraphAction z6Gens
    (fun i => by match i with | 0 => exact (by native_decide) | 1 => exact (by native_decide))
    g.1 g.2 u v h
private noncomputable instance : MulAction.IsPretransitive z6Group (Fin 91) where
  exists_smul_eq x y :=
    ⟨⟨_, z6Group.mul_mem (applyWord'_mem z6Gens _) (z6Group.inv_mem (applyWord'_mem z6Gens _))⟩, by
      change ((applyWord' z6Gens (z6Wit x)).symm.trans (applyWord' z6Gens (z6Wit y))) x = y
      simp only [Equiv.trans_apply]
      rw [show (applyWord' z6Gens (z6Wit x)).symm x = 0 from by
        rw [Equiv.symm_apply_eq]; exact (z6Wit_ok x).symm]; exact z6Wit_ok y⟩

/-- **The Zhou-6 graph is a Sabidussi coset graph**: `Sab(PSL(2,13), D₁₂, D)`.

PSL(2,13) (order 1092) acts vertex-transitively on the 91 vertices.
The stabilizer of vertex 0 has order 12 (≅ D₁₂), giving 1092/12 = 91 vertices.
D₁₂ is maximal in PSL(2,13), so the Zhou-6 graph is **primitive**. -/
noncomputable def zhou6SabidussiIso :
    zhou6Graph ≃g SimpleGraph.cosetGraph (MulAction.stabilizer z6Group (0 : Fin 91))
      (connectionSet z6Group zhou6Graph 0) (connectionSet.isConnectionSet 0) :=
  sabidussiIso 0

end ZhouSabidussi
