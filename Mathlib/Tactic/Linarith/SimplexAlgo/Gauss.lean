import Mathlib.Tactic.Linarith.SimplexAlgo.Datatypes

namespace Linarith.SimplexAlgo.Gauss

/-- State for `GaussM` monad.
-/
structure GaussState (n m : Nat) where
  mat : Matrix n m
  /-- Positions of units corresponding to basic variables in the `mat`. Used to obtain `Table` from
  the processed matrix. -/
  basicPositions : Array (Nat × Nat)
  currentRow : Nat
  currentColumn : Nat

abbrev GaussM (n m : Nat) := StateM <| GaussState n m

def GaussM.run' {n m: Nat} {α : Type} (x : GaussM n m α) (mat : Matrix n m): α := Id.run do
  let s : GaussState n m := {
    mat := mat
    basicPositions := #[]
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

def pushToBasicPos {n m : Nat} (i j : Nat) : GaussM n m Unit := do
  set {← get with basicPositions := (← get).basicPositions.push ⟨i, j⟩}

/-- Find the first row starting from the current column with nonzero element in current column. -/
def findNonzeroRow {n m : Nat} : GaussM n m <| Option Nat := do
  for i in [← curRow:n] do
    if (← get).mat[i]![← curCol]! != 0 then
      return i
  return .none

/-- Swap two rows. -/
def swapRows {n m : Nat} (i j : Nat) : GaussM n m Unit := do
  if i == j then
    return
  let swapped : Matrix n m := ⟨(← get).mat.data.swap! i j⟩
  set {← get with mat := swapped}

/-- Subtract i-th row * coef from j-th row. -/
def subtractRow {n m : Nat} (i j : Nat) (coef : Rat) : GaussM n m Unit := do
  let new_row := (← get).mat[j]!.zip (← get).mat[i]! |>.map fun ⟨x, y⟩ => x - coef * y
  let subtractedMat : Matrix n m := ⟨(← get).mat.data.set! j new_row⟩
  set {← get with mat := subtractedMat}

/-- Divide row by coef. -/
def divideRow {n m : Nat} (i : Nat) (coef : Rat) : GaussM n m Unit := do
  let new_row : Array Rat := (← get).mat[i]!.map (· / coef)
  let subtractedMat : Matrix n m := ⟨(← get).mat.data.set! i new_row⟩
  set {← get with mat := subtractedMat}

def getTableImp {n m : Nat} : GaussM n m Table := do
  let mut free : Array Nat := #[]
  let mut basic : Array Nat := #[]

  while (← curRow) < n && (← curCol) < m do
    match ← findNonzeroRow with
    | .none =>
      free := free.push (← curCol)
      incCol
      continue
    | .some rowToSwap =>
      swapRows (← curRow) rowToSwap

    divideRow (← curRow) (← get).mat[← curRow]![← curCol]!

    for i in [:n] do
      if i == (← curRow) then
        continue
      let coef := (← get).mat[i]![← curCol]!
      subtractRow (← curRow) i coef

    pushToBasicPos (← curRow) (← curCol)
    basic := basic.push (← curCol)
    incRow
    incCol

  for i in [← curCol:m] do
    free := free.push i

  let mut ansData : Array (Array Rat) := #[]
  for ⟨row, _⟩ in (← get).basicPositions do
    let mut newRow := #[]
    for f in free do
      newRow := newRow.push <| -(← get).mat[row]![f]!
    ansData := ansData.push newRow

  return {
    free := free
    basic := basic
    mat := ⟨ansData⟩
  }

/-- Given matrix `A`, this function solves the linear equation `A x = 0` and returns the
solution as a table where some variables are free and others (basic) variable are expressed as
linear combinations of free variables. -/
def getTable {n m : Nat} (A : Matrix n m) : Table := getTableImp.run' A

end Linarith.SimplexAlgo.Gauss
