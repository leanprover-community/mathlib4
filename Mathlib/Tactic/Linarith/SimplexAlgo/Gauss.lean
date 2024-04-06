import Std.Data.Rat.Basic

structure Linarith.SimplexAlgo.Matrix (n m : Nat) where
  data : Array (Array Rat)
deriving Repr

structure Linarith.SimplexAlgo.Table where
  bound : Array Nat
  free : Array Nat
  mat : Matrix bound.size free.size

namespace Linarith.SimplexAlgo.Gauss

structure GaussState (n m : Nat) where
  mat : Matrix n m
  diag : Array (Nat × Nat)
  curRow : Nat
  curCol : Nat

abbrev GaussM (n m : Nat) := StateM <| GaussState n m

def run {n m: Nat} {α : Type} (x : GaussM n m α) (mat : Matrix n m): α := Id.run do
  let s : GaussState n m := {
    mat := mat
    diag := #[]
    curRow := 0
    curCol := 0
  }
  return (← x.run s).fst

def isCurrentColumnZero {n m : Nat} : GaussM n m Bool := do
  for i in [(← get).curRow:n] do
    if (← get).mat.data[i]![(← get).curCol]! != 0 then
      return false
  return true

def incRow {n m : Nat} : GaussM n m Unit := do
  set {← get with curRow := (← get).curRow + 1}

def incCol {n m : Nat} : GaussM n m Unit := do
  set {← get with curCol := (← get).curCol + 1}

def pushToDiag {n m : Nat} (i j : Nat) : GaussM n m Unit := do
  set {← get with diag := (← get).diag.push ⟨i, j⟩}

def swapRows {n m : Nat} (i j : Nat) : GaussM n m Unit := do
  let swapped : Matrix n m := ⟨(← get).mat.data.swap! i j⟩
  set {← get with mat := swapped}

/- subtract i-th row * coef from j-th row -/
def subtractRow {n m : Nat} (i j : Nat) (coef : Rat) : GaussM n m Unit := do
  let mut new_row : Array Rat := #[]
  for k in [:m] do
    new_row := new_row.push <| (← get).mat.data[j]![k]! - coef * (← get).mat.data[i]![k]!
  let subtractedMat : Matrix n m := ⟨(← get).mat.data.set! j new_row⟩
  set {← get with mat := subtractedMat}

def divideRow {n m : Nat} (i : Nat) (coef : Rat) : GaussM n m Unit := do
  let new_row : Array Rat := (← get).mat.data[i]!.map (fun x => x / coef)
  let subtractedMat : Matrix n m := ⟨(← get).mat.data.set! i new_row⟩
  set {← get with mat := subtractedMat}

def getInitTableImp {n m : Nat} : GaussM n m Table := do
  let mut free : Array Nat := #[]
  let mut bound : Array Nat := #[]

  while (← get).curRow < n && (← get).curCol < m do
    if ← isCurrentColumnZero then
      free := free.push (← get).curCol
      incCol
      continue

    for i in [(← get).curRow:n] do
      if (← get).mat.data[i]![(← get).curCol]! != 0 then
        swapRows (← get).curRow i
        break

    divideRow (← get).curRow (← get).mat.data[(← get).curRow]![(← get).curCol]!

    for i in [:n] do
      if i == (← get).curRow then
        continue
      let coef := (← get).mat.data[i]![(← get).curCol]!
      subtractRow (← get).curRow i coef

    pushToDiag (← get).curRow (← get).curCol
    bound := bound.push (← get).curCol
    incRow
    incCol

  for i in [(← get).curCol:m] do
    free := free.push i

  let mut ansData : Array (Array Rat) := #[]
  for ⟨row, _⟩ in (← get).diag do
    let mut newRow := #[]
    for f in free do
      newRow := newRow.push <| -(← get).mat.data[row]![f]!
    ansData := ansData.push newRow

  return {
    free := free
    bound := bound
    mat := ⟨ansData⟩
  }

def getInitTable {n m : Nat} (mat : Matrix n m) : Table := run getInitTableImp mat


end Linarith.SimplexAlgo.Gauss
