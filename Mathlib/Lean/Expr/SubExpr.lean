import Lean

namespace Lean.PrettyPrinter.Delaborator

private abbrev N : Nat := SubExpr.maxChildren

/-- Creates a subexpression `Pos` from an array of 'coordinates'.
Each coordinate is a number {0,1,2} expressing which child subexpression should be explored.
The first coordinate in the array corresponds to the root of the expression tree.  -/
def Pos.encode (ps : Array Nat) : Pos := Id.run do
  let mut r := 1
  for p in ps do
    r ← r * N + p
  return r

/-- Decodes a subexpression `Pos` as a sequence of coordinates. See `Pos.encode` for details.-/
def Pos.decode (p : Pos) : Array Nat := Id.run do
    let mut x := p
    let mut a := #[]
    while x >= N do
      let head := x % N
      x ← (x - head) / N
      a ← a.push head
    return a.reverse

end Lean.PrettyPrinter.Delaborator

open Lean.Meta
