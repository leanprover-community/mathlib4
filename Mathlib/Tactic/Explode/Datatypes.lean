import lean
import Lean.Meta.Basic

open Lean Elab
open Std

inductive Status where
  | reg    : Status
  | intro  : Status
  | lam    : Status
  | sintro : Status
deriving Inhabited

inductive Thm where
  | expr   : Expr   → Thm
  | name   : Name   → Thm
  | string : String → Thm

structure Entry where
  expr  : Expr
  line  : Nat
  depth : Nat
  status: Status
  thm   : Thm
  deps  : List Nat

--- Instead of simply keeping a list of entries (List Entry), we create a datatype Entries.
structure Entries : Type :=
  -- allows us to compare Exprs fast
  (s : ExprMap Entry)
  -- is a simple list of Exprs
  (l : List Entry)
deriving Inhabited

def Entries.find (es : Entries) (e : Expr) : Option Entry :=
  es.s.find? e
def Entries.size (es : Entries) : Nat :=
  es.s.size
def Entries.add : Entries → Entry → Entries
  | entries@⟨s, l⟩, entry =>
    if s.contains entry.expr
      then entries
      else ⟨s.insert entry.expr entry, entry :: l⟩
def Entries.head (es : Entries) : Option Entry :=
  es.l.head?

def Thm.toString : Thm → String
  | (Thm.expr _) => "e.toString todo" -- todo
  | (Thm.name n) => n.toString
  | (Thm.string s) => s

-- Examples
def myEntry : Entry := {
  expr   := mkAppN (Expr.const `Nat.add []) #[mkNatLit 1, mkNatLit 2],
  line   := 15,
  depth  := 0,
  status := Status.reg,
  thm    := Thm.string "my_theorem",
  deps   := [1, 2, 3]
}

def myEntry2 : Entry := {
  expr   := mkAppN (Expr.const `Nat.add []) #[mkNatLit 666, mkNatLit 666],
  line   := 15,
  depth  := 0,
  status := Status.reg,
  thm    := Thm.string "my_theorem",
  deps   := [1, 2, 3]
}

def entriesDefault : Entries := default
