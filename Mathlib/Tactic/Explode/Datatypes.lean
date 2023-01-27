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

/-- Options to give to explode. -/
structure Opts where
  /-- Whether to log what part of the theorem body expression we're parsing at the moment. -/
  verbose : Bool

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
  /-- We'll display it as a full-blown `MessageData`, it will be possibel to hover over it -/
  | expr   : Expr   → Thm
  /-- Display as a name -/
  | name   : Name   → Thm
  /-- Display as a string -/
  | string : String → Thm

/-- The row in the Fitch table. -/
structure Entry where
  /-- Expression -/
  expr   : Expr
  /-- A type of this expression. We need to store it too, because it needs to have been created
  in the right `MessageDataContext` - we can't just `inferType` from `Entry.expr` later. -/
  type   : Expr
  /-- The row number, starting from `0`. -/
  line   : Nat
  /-- How many `if`s (aka lambda-abstractions) this row is nested under. -/
  depth  : Nat
  /-- What `Status` this entry has - this only affects how `│`s are displayed. -/
  status : Status
  /-- What to display in the "theorem applied" column. -/
  thm    : Thm
  /-- What other lines (aka rows) this row depends on. -/
  deps   : List Nat
  /-- Context in which to render our expressions(`Entry.expr`, `Entry.type`, and
  `Entry.thm.expr`). -/
  context: MessageDataContext

/-- Instead of simply keeping a list of entries (`List Entry`), we create a datatype `Entries`
that allows us to compare expressions faster. -/
structure Entries : Type :=
  /-- Allows us to compare `Expr`s fast. -/
  (s : ExprMap Entry)
  /-- Simple list of `Expr`s. -/
  (l : List Entry)
deriving Inhabited
/-- Find a row where `Entry.expr` == `e`. -/
def Entries.find (es : Entries) (e : Expr) : Option Entry :=
  es.s.find? e
/-- Length of our entries. -/
def Entries.size (es : Entries) : Nat :=
  es.s.size
/-- Add the entry unless it already exists. -/
def Entries.add : Entries → Entry → Entries
  | entries@⟨s, l⟩, entry =>
    if s.contains entry.expr
      then entries
      else ⟨s.insert entry.expr entry, entry :: l⟩
/-- Create an empty `Entries`. -/
def entriesDefault : Entries := default

/-- Head-reduce all let expressions -/
partial def reduceLets : Expr → Expr
  | (Expr.letE _ _ v b _) => reduceLets (b.instantiate1 v)
  | e => e

/-- Determine if a given expression might be a proof. -/
def mayBeProof (e : Expr) : MetaM Bool := do
  let type : Expr ← Lean.Meta.inferType e
  let metaType : Expr ← Lean.Meta.inferType type
  return metaType == Expr.sort Lean.levelZero

/-- Add a row number to `Entry`'s dependencies. -/
def appendDep (entries : Entries) (expr : Expr) (deps : List Nat) : MetaM (List Nat) := do
  let expr := reduceLets expr
  if let some existingEntry := entries.find expr then
    return existingEntry.line :: deps
  else
    return deps

/-- Get current `MessageDataContext`.
This allows us to render `Entry`'s `Expr`s when printing out the Fitch table. -/
def getContext : MetaM MessageDataContext := do
  return { env := (← getEnv), mctx := {}, lctx := (← read).lctx, opts := {} }
