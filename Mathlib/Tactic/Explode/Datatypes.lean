import lean
import Lean.Meta.Basic

open Lean Elab
open Std

set_option linter.unusedVariables false

namespace Mathlib.Explode

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
def Thm.toString : Thm → String
  | (Thm.expr e) => Expr.dbgToString e
  | (Thm.name n) => n.toString
  | (Thm.string s) => s

structure Entry where
  expr   : Expr
  type   : Expr
  line   : Nat
  depth  : Nat
  status : Status
  thm    : Thm
  deps   : List Nat
  context: MessageDataContext

/- Instead of simply keeping a list of entries (`List Entry`), we create a datatype `Entries` that allows us to compare expressions faster. -/
structure Entries : Type :=
  /- Allows us to compare `Expr`s fast -/
  (s : ExprMap Entry)
  /- is a simple list of `Expr`s -/
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
def entriesDefault : Entries := default

/-- Head-reduce all let expressions -/
partial def reduceLets : Expr → Expr
  | (Expr.letE _ _ v b _) => reduceLets (b.instantiate1 v)
  | e => e

def mayBeProof (e : Expr) : MetaM Bool := do
  let type : Expr ← Lean.Meta.inferType e
  let metaType : Expr ← Lean.Meta.inferType type
  return metaType == Expr.sort Lean.levelZero

def appendDep (entries : Entries) (expr : Expr) (deps : List Nat) : MetaM (List Nat) := do
  let expr := reduceLets expr
  -- if (← mayBeProof expr) then
  if let some existingEntry := entries.find expr then
    return existingEntry.line :: deps
  else
    return deps

def getContext : MetaM MessageDataContext := do
  return { env := (← getEnv), mctx := {}, lctx := (← read).lctx, opts := {} }
