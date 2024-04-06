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
  currentRow : Nat
  currentColumn : Nat

abbrev GaussM (n m : Nat) := StateM <| GaussState n m

def run {n m: Nat} {α : Type} (x : GaussM n m α) (mat : Matrix n m): α := Id.run do
  let s : GaussState n m := {
    mat := mat
    diag := #[]
    currentRow := 0
    currentColumn := 0
  }
  return (← x.run s).fst

def curRow {n m : Nat} : GaussM n m Nat := do
  return (← get).currentRow

def curCol {n m : Nat} : GaussM n m Nat := do
  return (← get).currentColumn

def incRow {n m : Nat} : GaussM n m Unit := do
  set {← get with currentRow := (← curRow) + 1}

def incCol {n m : Nat} : GaussM n m Unit := do
  set {← get with currentColumn := (← get).currentColumn + 1}

def pushToDiag {n m : Nat} (i j : Nat) : GaussM n m Unit := do
  set {← get with diag := (← get).diag.push ⟨i, j⟩}

def isCurrentColumnZero {n m : Nat} : GaussM n m Bool := do
  for i in [← curRow:n] do
    if (← get).mat.data[i]![← curCol]! != 0 then
      return false
  return true

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

def getTableImp {n m : Nat} : GaussM n m Table := do
  let mut free : Array Nat := #[]
  let mut bound : Array Nat := #[]

  while (← curRow) < n && (← curCol) < m do
    if ← isCurrentColumnZero then
      free := free.push (← curCol)
      incCol
      continue

    for i in [← curRow:n] do
      if (← get).mat.data[i]![← curCol]! != 0 then
        swapRows (← curRow) i
        break

    divideRow (← curRow) (← get).mat.data[← curRow]![← curCol]!

    for i in [:n] do
      if i == (← curRow) then
        continue
      let coef := (← get).mat.data[i]![← curCol]!
      subtractRow (← curRow) i coef

    pushToDiag (← curRow) (← curCol)
    bound := bound.push (← curCol)
    incRow
    incCol

  for i in [← curCol:m] do
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

def getTable {n m : Nat} (mat : Matrix n m) : Table := run getTableImp mat


end Linarith.SimplexAlgo.Gauss
