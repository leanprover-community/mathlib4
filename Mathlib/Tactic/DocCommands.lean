/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import Mathlib.Lean.Expr.Basic

/-!
# Documentation commands
-/
open Lean Elab

/--
`copy_doc_string source → target_1 target_2 ... target_n` copies the doc string of the
declaration named `source` to each of `target_1`, `target_2`, ..., `target_n`.
-/
elab "copy_doc_string " fr:ident " → " tos:ident+ : command => do
  let fr : Name ← resolveGlobalConstNoOverloadWithInfo fr
  if let some docString ← findDocString? (← getEnv) fr then
    for to in tos do
      let to : Name ← resolveGlobalConstNoOverloadWithInfo to
      addDocString to docString
