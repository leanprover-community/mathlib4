import Mathlib.Tactic.Linarith.SimplexAlgo.Gauss
import Mathlib.Tactic.Linarith.SimplexAlgo.SimplexAlgo

namespace Linarith.SimplexAlgo

def augmentMatrix {n m : Nat} (A : Matrix n m) (strictIndexes : Array Nat) : Matrix (n + 2) (m + 3) := Id.run do
  let mut objectiveRow : Array Rat := #[-1, 0] ++ (Array.mkArray m 0) ++ #[0]
  for idx in strictIndexes do
    objectiveRow := objectiveRow.set! (idx + 2) 1

  let mut constraintRow : Array Rat := #[0, 1] ++ (Array.mkArray m 1) ++ #[-1]

  let mut data : Array (Array Rat) := #[objectiveRow, constraintRow]
  for row in A.data do
    data := data.push <| #[0, 0] ++ row ++ #[0]

  return ⟨data⟩

def getVectorFromTable (table : Table) : Array Rat := Id.run do
  let mut ans : Array Rat := Array.mkArray (table.bound.size + table.free.size - 3) 0
  for i in [1:table.mat.data.size] do
    ans := ans.set! (table.bound[i]! - 2) table.mat.data[i]!.back

  return ans

/- Finds non-negative vector v, s.t. Av = 0 and some of its coords from strictCoords are positive -/
def findPositiveVector {n m : Nat} (A : Matrix n m) (strictIndexes : Array Nat) : Array Rat := Id.run do
  /- add auxilary constraint and objective function -/
  -- dbg_trace strictIndexes

  -- dbg_trace "A"
  -- dbg_trace A.data

  let B := augmentMatrix A strictIndexes

  -- dbg_trace "B"
  -- dbg_trace B.data

  /- find free & slack variables -/
  let mut table := Gauss.getInitTable B

  -- dbg_trace ""
  -- dbg_trace table.mat.data
  -- dbg_trace table.bound
  -- dbg_trace table.free
  -- dbg_trace ""

  /- run simplex algo -/
  table ← simplexAlgo.run' table

  /- decode -/
  return getVectorFromTable table

end Linarith.SimplexAlgo
