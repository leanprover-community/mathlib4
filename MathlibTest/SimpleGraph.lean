import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Tests for the breadth-first search decidability instances of a finite graph

`SimpleGraph.decidableReachable`, `SimpleGraph.decidablePreconnected` and
`SimpleGraph.decidableConnected` decide reachability and (pre)connectedness by running a breadth-
first search, which costs `O(card V ^ 2)` adjacency tests. The `maxHeartbeats` bounds below guard
against a regression to a super-polynomial algorithm.
-/

namespace SimpleGraph

/-- The path graph on `{0, 1, 2, 3, 4}`, together with an isolated vertex `5`. -/
def testPath : SimpleGraph (Fin 6) where
  Adj i j := (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ i.val < 5 ∧ j.val < 5
  symm := ⟨by lia⟩
  loopless := ⟨by lia⟩

instance : DecidableRel testPath.Adj := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The cycle graph on `Fin 60`. -/
def testCycle : SimpleGraph (Fin 60) where
  Adj i j := (i.val + 1) % 60 = j.val ∨ (j.val + 1) % 60 = i.val
  symm := ⟨by lia⟩
  loopless := ⟨by lia⟩

instance : DecidableRel testCycle.Adj := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

-- The vertices visited by the breadth-first search from `0`, most recently visited first.
#guard testPath.bfsList 0 (List.finRange 6) = [4, 3, 2, 1, 0]

example : testPath.Reachable 0 4 := by decide
example : ¬ testPath.Reachable 0 5 := by decide
example : ¬ testPath.Preconnected := by decide
example : ¬ testPath.Connected := by decide

example : (⊤ : SimpleGraph (Fin 5)).Connected := by decide
example : ¬ (⊥ : SimpleGraph (Fin 2)).Connected := by decide
example : (⊥ : SimpleGraph (Fin 1)).Connected := by decide

-- The empty graph is preconnected, but not connected.
example : (⊥ : SimpleGraph (Fin 0)).Preconnected := by decide
example : ¬ (⊥ : SimpleGraph (Fin 0)).Connected := by decide

-- These two take about 8000 and 12000 heartbeats respectively.
set_option maxHeartbeats 50000 in
example : testCycle.Reachable 0 30 := by decide

set_option maxHeartbeats 50000 in
example : testCycle.Connected := by decide

end SimpleGraph
