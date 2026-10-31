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

-- The isolated vertex `5` is not visited, so the search visits fewer vertices than there are.
#guard (testPath.bfsList 0 (List.finRange 6)).length = 5
#guard (testCycle.bfsList 0 (List.finRange 60)).length = 60

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

-- These two take about 8000 heartbeats each.
set_option maxHeartbeats 50000 in
example : testCycle.Reachable 0 30 := by decide

set_option maxHeartbeats 50000 in
example : testCycle.Connected := by decide

/-!
`SimpleGraph.decidablePreconnected` and `SimpleGraph.decidableConnected` check that the breadth-
first search visited every vertex by comparing the *length* of the list of visited vertices to the
number of vertices, rather than by checking that each vertex belongs to that list, which would cost
a further `O(card V ^ 2)` equality tests.

On a complete graph the search stops after a single round, so it only costs `O(card V)` adjacency
tests and the difference is asymptotic: the example below takes about 1650 heartbeats, against
about 42000 for the membership check. The `maxHeartbeats` bound guards against a regression to the
latter.
-/
set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000 in
example : (⊤ : SimpleGraph (Fin 200)).Connected := by decide

end SimpleGraph
