/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Mathlib.Combinatorics.SimpleGraph.QuotientGraph

/-!
# Named graphs and antipodal quotients

The dodecahedron has an antipodal involution (distance 5) whose quotient is the
Petersen graph. The 3-cube has an antipodal involution (bitwise complement, distance 3)
whose quotient is K₄.

## Main definitions

* `dodecahedronGraph` — the dodecahedron on `Fin 20`, 3-regular, 30 edges
* `petersenGraph` — the Petersen graph on `Fin 10`, as `dodecahedronGraph.quotientGraph`
* `cubeGraph` — the 3-cube Q₃ on `Fin 8`, 3-regular, 12 edges

## Main results

* `dodecahedronGraph_regular` — the dodecahedron is 3-regular
* `petersenGraph_regular` — the Petersen graph is 3-regular
* `cubeQuotient_eq_top` — the antipodal quotient of the cube is K₄

## References

* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798
-/

set_option linter.style.nativeDecide false

open SimpleGraph

/-! ### The dodecahedron graph -/

private def dodecAdjBool (u v : Fin 20) : Bool :=
  let edges : List (Fin 20 × Fin 20) := [
    (0, 1), (0, 4), (0, 5), (1, 2), (1, 7), (2, 3), (2, 9), (3, 4), (3, 11), (4, 13),
    (5, 6), (5, 14), (6, 7), (6, 15), (7, 8), (8, 9), (8, 16), (9, 10), (10, 11), (10, 17),
    (11, 12), (12, 13), (12, 18), (13, 14), (14, 19), (15, 16), (15, 19), (16, 17), (17, 18),
    (18, 19)]
  edges.any fun (a, b) => (u == a && v == b) || (u == b && v == a)

/-- The **dodecahedron graph**, the 1-skeleton of the regular dodecahedron. -/
def dodecahedronGraph : SimpleGraph (Fin 20) where
  Adj u v := dodecAdjBool u v
  symm u v := by simp only [dodecAdjBool]; revert u v; native_decide
  loopless := ⟨fun u => by simp only [dodecAdjBool]; revert u; native_decide⟩

instance : DecidableRel dodecahedronGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (dodecAdjBool u v))

/-! ### The antipodal quotient map -/

private def dodecAntipodalData : List (Fin 10) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 6, 7, 8, 9, 3, 4, 0, 1, 2]

private theorem dodecAntipodalData_length : dodecAntipodalData.length = 20 := by native_decide

/-- The antipodal quotient map: `Fin 20 → Fin 10`. -/
def dodecAntipodalMap (v : Fin 20) : Fin 10 :=
  dodecAntipodalData.get (v.cast dodecAntipodalData_length.symm)

/-! ### The Petersen graph -/

/-- The **Petersen graph**, the antipodal quotient of the dodecahedron. -/
def petersenGraph : SimpleGraph (Fin 10) :=
  dodecahedronGraph.quotientGraph dodecAntipodalMap

instance : DecidableRel petersenGraph.Adj := by
  intro i j; unfold petersenGraph quotientGraph; simp only; exact instDecidableAnd

/-- The dodecahedron is 3-regular. -/
theorem dodecahedronGraph_regular :
    ∀ v : Fin 20, (Finset.univ.filter fun w => dodecahedronGraph.Adj v w).card = 3 := by
  native_decide

/-- The dodecahedron has 30 edges. -/
theorem dodecahedronGraph_edgeCount :
    (Finset.univ.filter fun p : Fin 20 × Fin 20 =>
      p.1 < p.2 ∧ dodecahedronGraph.Adj p.1 p.2).card = 30 := by
  native_decide

/-- The Petersen graph is 3-regular. -/
theorem petersenGraph_regular :
    ∀ v : Fin 10, (Finset.univ.filter fun w => petersenGraph.Adj v w).card = 3 := by
  native_decide

/-- The Petersen graph has 15 edges. -/
theorem petersenGraph_edgeCount :
    (Finset.univ.filter fun p : Fin 10 × Fin 10 =>
      p.1 < p.2 ∧ petersenGraph.Adj p.1 p.2).card = 15 := by
  native_decide

/-! ### The 3-cube graph -/

private def cubeAdjBool (u v : Fin 8) : Bool :=
  let edges : List (Fin 8 × Fin 8) := [
    (0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7),
    (4, 5), (4, 6), (5, 7), (6, 7)]
  edges.any fun (a, b) => (u == a && v == b) || (u == b && v == a)

/-- The **3-cube graph** Q₃, the 1-skeleton of the 3-dimensional hypercube. -/
def cubeGraph : SimpleGraph (Fin 8) where
  Adj u v := cubeAdjBool u v
  symm u v := by simp only [cubeAdjBool]; revert u v; native_decide
  loopless := ⟨fun u => by simp only [cubeAdjBool]; revert u; native_decide⟩

instance : DecidableRel cubeGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (cubeAdjBool u v))

/-! ### The cube antipodal quotient -/

private def cubeAntipodalData : List (Fin 4) := [0, 1, 2, 3, 3, 2, 1, 0]

private theorem cubeAntipodalData_length : cubeAntipodalData.length = 8 := by native_decide

/-- The antipodal quotient map on Q₃: `Fin 8 → Fin 4`. -/
def cubeAntipodalMap (v : Fin 8) : Fin 4 :=
  cubeAntipodalData.get (v.cast cubeAntipodalData_length.symm)

/-- The antipodal quotient of the 3-cube. -/
def cubeQuotientGraph : SimpleGraph (Fin 4) :=
  cubeGraph.quotientGraph cubeAntipodalMap

instance : DecidableRel cubeQuotientGraph.Adj := by
  intro i j; unfold cubeQuotientGraph quotientGraph; simp only; exact instDecidableAnd

/-- The 3-cube is 3-regular. -/
theorem cubeGraph_regular :
    ∀ v : Fin 8, (Finset.univ.filter fun w => cubeGraph.Adj v w).card = 3 := by
  native_decide

/-- The 3-cube has 12 edges. -/
theorem cubeGraph_edgeCount :
    (Finset.univ.filter fun p : Fin 8 × Fin 8 =>
      p.1 < p.2 ∧ cubeGraph.Adj p.1 p.2).card = 12 := by
  native_decide

/-- The antipodal quotient of the 3-cube is 3-regular. -/
theorem cubeQuotientGraph_regular :
    ∀ v : Fin 4, (Finset.univ.filter fun w => cubeQuotientGraph.Adj v w).card = 3 := by
  native_decide

/-- The antipodal quotient of the 3-cube is the complete graph K₄. -/
theorem cubeQuotient_eq_top : cubeQuotientGraph = ⊤ := by
  ext u v; revert u v; native_decide
