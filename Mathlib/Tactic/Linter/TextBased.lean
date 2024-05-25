/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
import Lean.Linter.Util
import Batteries.Data.String.Basic

/-!
## Text-based linters

This file defines various mathlib linters which are based on reading the source code only.
In practice, only style linters will have this form.
All of these have been rewritten from the `lint-style.py` script.

TODO: rewrite more of these lints, e.g.
checking the copyright header, authors line, line length, isolated "where" or "by"

-/

open Lean Elab Command

/-- Possible errors that text-based linters can report. -/
-- We collect these in one inductive type to centralise error reporting.
inductive StyleError where
  /-- Line longer than 100 characters -/
  | lineLength (actual : Int) : StyleError
  deriving BEq

/-- Create the underlying error message for a given `StyleError`. -/
def errorMessage (err : StyleError) : String := match err with
  | StyleError.lineLength n => s!"Line has {n} characters, which is more than 100"

/-- The error code for a given style error. Kept in sync with `lint-style.py` for now. -/
def errorCode (err : StyleError) : String := match err with
  | StyleError.lineLength _n => "ERR_LIN"

/-- Context for a style error: the actual error, the line number in the file we're reading
and the path to the file. -/
structure ErrorContext where
  error : StyleError
  line_number : Int
  path : System.FilePath
  deriving BEq

/-- Output the formatted error message, containing its context. -/
def output_message (errctx : ErrorContext) : String :=
  -- XXX: we're just porting the second branch, running on CI
  -- generating an exceptions file (the first branch) is not implemented yet

  -- We are outputting for github: duplicate path, line_nr and code,
  -- so that they are also visible in the plaintext output.
  let path := errctx.path
  let nr := errctx.line_number
  let code := errorCode errctx.error
  s!"::ERR file={path},line={nr},code={code}::{path}:{nr} {code}: {errorMessage errctx.error}"

/-- Print information about all errors encountered to standard output. -/
def format_errors (errors : Array ErrorContext) (exceptions : Array ErrorContext): IO Unit := do
  -- XXX: `lint-style.py` was `resolve()`ing paths in the `exceptions` list;
  -- do we also need to?
  for e in errors do
    if !exceptions.contains e then IO.println (output_message e)

/-! Definitions of the actual text-based linters. -/
namespace CoreLogic

/-- Iterates over a collection of strings, finding all lines which are longer than 100 chars. -/
def check_line_length (lines : Array String) : Array (StyleError × Nat) :=
  let is_too_long := (fun s : String ↦ if s.length > 100 then some (StyleError.lineLength s.length) else none)
  let errors := Array.filterMap is_too_long lines
  -- TODO: enumerate over all lines, and report actual line numbers!
  Array.map (fun e ↦ (e, 42)) errors

end CoreLogic

/-- All text-based linters registered in this file. -/
def all_linters : Array (Array String → Array (StyleError × Nat)) := Array.mk
  [CoreLogic.check_line_length]

/-- Read a file, apply all text-based linters and return the formatted errors. -/
def lint_file (path : System.FilePath) : IO Unit := do
  let lines ← IO.FS.lines path
  let all_output := (Array.map (fun linter ↦ (Array.map (fun (e, n) ↦ ErrorContext.mk e n path) (linter lines))) all_linters)
  -- XXX: this list is currently not sorted: for github, that's probably fine
  format_errors (Array.flatten all_output) (Array.mkEmpty 0)

/-- Lint all files in `Mathlib.lean`. -/
def check_all_files : IO Unit := do
  -- Read all module names in Mathlib from `Mathlib.lean`.
  let allModules ← IO.FS.lines (System.mkFilePath [(toString "Mathlib.lean")])
  for module in allModules do
    -- Convert the module name to a file name, then lint that file.
    lint_file (System.mkFilePath ((module.split fun c ↦ (c == '.')).append [".lean"]))
