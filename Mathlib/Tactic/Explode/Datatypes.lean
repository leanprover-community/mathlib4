/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Evgenia Karunus
-/
import Lean

/-!
# Explode command: datatypes

This file contains datatypes used by the `#explode` command and their associated methods.
-/

open Lean

namespace Mathlib.Explode

initialize registerTraceClass `explode

/-- How to display pipes (`│`) for this entry in the Fitch table . -/
inductive Status where
  /-- `├` -/
  | sintro : Status
  /-- `Entry.depth` * `│` + `┌` -/
  | intro  : Status
  /-- `Entry.depth` * `│` -/
  | lam    : Status
  /-- `Entry.depth` * `│` -/
  | reg    : Status
  deriving Inhabited

/-- How to display the theorem in the Fitch table. -/
inductive Thm where
  /-- The theorem expression as a `MessageData`. Make sure to use `addMessageContext`. -/
  | msg   : MessageData → Thm
  /-- Display as a name -/
  | name   : Name → Thm
  /-- Display as a string -/
  | string : String → Thm

/-- The row in the Fitch table. -/
structure Entry where
  /-- A type of this expression as a `MessageData`. Make sure to use `addMessageContext`. -/
  type    : MessageData
  /-- The row number, starting from `0`. -/
  line    : Nat
  /-- How many `if`s (aka lambda-abstractions) this row is nested under. -/
  depth   : Nat
  /-- What `Status` this entry has - this only affects how `│`s are displayed. -/
  status  : Status
  /-- What to display in the "theorem applied" column. -/
  thm     : Thm
  /-- Which other lines (aka rows) this row depends on. -/
  deps    : List Nat

/-- Instead of simply keeping a list of entries (`List Entry`), we create a datatype `Entries`
that allows us to compare expressions faster. -/
structure Entries : Type where
  /-- Allows us to compare `Expr`s fast. -/
  s : ExprMap Entry
  /-- Simple list of `Expr`s. -/
  l : List Entry
  deriving Inhabited

/-- Find a row where `Entry.expr` == `e`. -/
def Entries.find (es : Entries) (e : Expr) : Option Entry :=
  es.s.find? e

/-- Length of our entries. -/
def Entries.size (es : Entries) : Nat :=
  es.s.size

/-- Add the entry unless it already exists. -/
def Entries.add : Entries → Expr → Entry → Entries
  | entries@⟨s, l⟩, expr, entry =>
    if s.contains expr
      then entries
      else ⟨s.insert expr entry, entry :: l⟩

/-- Create an empty `Entries`. -/
def entriesDefault : Entries := default

/-- Head-reduce all let expressions -/
partial def reduceLets : Expr → Expr
  | .letE _ _ v b _ => reduceLets (b.instantiate1 v)
  | e => e

/-- Add a row number to `Entry`'s dependencies. -/
def appendDep (entries : Entries) (expr : Expr) (deps : List Nat) : MetaM (List Nat) := do
  let expr := reduceLets expr
  if let some existingEntry := entries.find expr then
    return existingEntry.line :: deps
  else
    return deps
