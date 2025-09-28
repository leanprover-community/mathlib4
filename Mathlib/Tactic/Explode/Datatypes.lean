/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Evgenia Karunus, Kyle Miller
-/
import Mathlib.Init
import Lean.Util.Trace

/-!
# Explode command: datatypes

This file contains datatypes used by the `#explode` command and their associated methods.
-/

open Lean

namespace Mathlib.Explode

initialize registerTraceClass `explode

/-- How to display pipes (`│`) for this entry in the Fitch table . -/
inductive Status where
  /-- `├` Start intro (top-level) -/
  | sintro : Status
  /-- `Entry.depth` * `│` + `┌` Normal intro -/
  | intro  : Status
  /-- `Entry.depth` * `│` + `├` Continuation intro -/
  | cintro : Status
  /-- `Entry.depth` * `│` -/
  | lam    : Status
  /-- `Entry.depth` * `│` -/
  | reg    : Status
  deriving Inhabited

/-- The row in the Fitch table. -/
structure Entry where
  /-- A type of this expression as a `MessageData`. Make sure to use `addMessageContext`. -/
  type : MessageData
  /-- The row number, starting from `0`. This is set by `Entries.add`. -/
  line : Option Nat := none
  /-- How many `if`s (aka lambda-abstractions) this row is nested under. -/
  depth : Nat
  /-- What `Status` this entry has - this only affects how `│`s are displayed. -/
  status : Status
  /-- What to display in the "theorem applied" column.
  Make sure to use `addMessageContext` if needed. -/
  thm : MessageData
  /-- Which other lines (aka rows) this row depends on.
  `none` means that the dependency has been filtered out of the table. -/
  deps : List (Option Nat)
  /-- Whether or not to use this in future deps lists. Generally controlled by the `select` function
  passed to `explodeCore`. Exception: `∀I` may ignore this for introduced hypotheses. -/
  useAsDep : Bool

/-- Get the `line` for an `Entry` that has been added to the `Entries` structure. -/
def Entry.line! (entry : Entry) : Nat := entry.line.get!

/-- Instead of simply keeping a list of entries (`List Entry`), we create a datatype `Entries`
that allows us to compare expressions faster. -/
structure Entries : Type where
  /-- Allows us to compare `Expr`s fast. -/
  s : ExprMap Entry
  /-- Simple list of `Expr`s. -/
  l : List Entry
  deriving Inhabited

/-- Find a row where `Entry.expr` == `e`. -/
def Entries.find? (es : Entries) (e : Expr) : Option Entry :=
  es.s[e]?

/-- Length of our entries. -/
def Entries.size (es : Entries) : Nat :=
  es.s.size

/-- Add the entry unless it already exists. Sets the `line` field to the next
available value. -/
def Entries.add (entries : Entries) (expr : Expr) (entry : Entry) : Entry × Entries :=
  if let some entry' := entries.find? expr then
    (entry', entries)
  else
    let entry := { entry with line := entries.size }
    (entry, ⟨entries.s.insert expr entry, entry :: entries.l⟩)

/-- Add a pre-existing entry to the `ExprMap` for an additional expression.
This is used by `let` bindings where `expr` is an fvar. -/
def Entries.addSynonym (entries : Entries) (expr : Expr) (entry : Entry) : Entries :=
  ⟨entries.s.insert expr entry, entries.l⟩

end Explode

end Mathlib
