/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/
module

public import Mathlib.Init
public import Lean.Util.CollectAxioms
public import Lean.Elab.Command

@[expose] public section

/-!
# Defines the `assert_no_sorry` command.

Throws an error if the given identifier uses sorryAx.
-/

open Lean Meta Elab Command

/-- Throws an error if the given identifier uses sorryAx. -/
elab "assert_no_sorry " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  if axioms.contains ``sorryAx
  then throwError "{n} contains sorry"
