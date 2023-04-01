import Mathlib.Data.ListM.AStar
import Mathlib.Data.Nat.Sqrt

open Lean ListM AStar

def wall : Int × Int → Bool :=
fun ⟨x, y⟩ => x ≤ 3 || y ≤ 3 || x ≥ 20 || y ≥ 20 || (x ≥ 6 && y ≥ 6)

unsafe def LWallGraph : GraphData MetaM Nat (Int × Int) ((Int × Int) × (Int × Int)) :=
{ s := (·.1),
  t := (·.2),
  nbhd := fun ⟨x, y⟩ => ListM.ofList
    ([((x,y),(x+1,y)), ((x,y),(x-1,y)), ((x,y),(x,y+1)), ((x,y),(x,y-1))].filter (wall ·.2)),
  weight := fun _ => 1
  heuristic := fun ⟨x, y⟩ => 5 * Nat.sqrt (x.natAbs ^ 2 + y.natAbs ^ 2) }

#eval AStarSearch LWallGraph false (10, 10) (· == (0,0))
