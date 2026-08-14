module

import Mathlib.Util.PrivateProof
import all Mathlib.Tactic.Linter.PrivateInPublic
import Lean.Elab.Command

/-!
# Tests for the `privateInPublic` linter

The linter is a `ModuleLinter`, so it runs on the terminal command with the commands of the whole
module, and its messages therefore cannot be captured by `#guard_msgs` in the ordinary way. Instead
we invoke it by hand at the end of the file, on the commands obtained by re-parsing this file: the
elaborator's `FileMap` holds the whole source, so the commands we get carry exactly the positions
the declarations were recorded with.
-/

public section

set_option backward.privateInPublic.warn false
set_option linter.privateInPublic true
-- The `privateProof` linter has plenty to say about the declarations below, and is tested
-- separately.
set_option linter.privateProof false

open Lean Elab Command

@[expose] def FEq (_ : (0 : Nat) = 0) := Bool

-- Exported, and nothing public uses it: its `set_option` should be deleted.
set_option backward.privateInPublic true in
private theorem unused : (0 : Nat) = 0 := rfl

-- Exported and used in the public type of `usesIt`: nothing to report.
set_option backward.privateInPublic true in
private theorem used : (0 : Nat) = 0 := rfl

set_option backward.privateInPublic true in
def usesIt (_ : FEq used) : Bool := true

-- Exported and used only from `chainOuter`, which is itself exported and unused: both should be
-- deleted. `chainOuter` carries two `set_option`s, and each is reported separately.
set_option backward.privateInPublic true in
private theorem chainInner : (0 : Nat) = 0 := rfl

set_option backward.privateInPublic.warn false in
set_option backward.privateInPublic true in
private def chainOuter (_ : FEq chainInner) : Bool := true

-- Not exported at all, so not a candidate.
private theorem plain : (0 : Nat) = 0 := rfl

@[expose] def usesPlain : Type := FEq (private plain)

/--
info: `chainInner` exported only because of this `set_option`, but nothing public uses it; delete it:
  [apply] (delete)
---
info: `chainOuter` exported only because of this `set_option`, but nothing public uses it; delete it:
  [apply] (delete)
---
info: `chainOuter` exported only because of this `set_option`, but nothing public uses it; delete it:
  [apply] (delete)
---
info: `unused` exported only because of this `set_option`, but nothing public uses it; delete it:
  [apply] (delete)
-/
#guard_msgs in
run_cmd do
  let ictx := Parser.mkInputContext (← getFileMap).source "PrivateInPublic.lean"
  let (_, mps, _) ← Parser.parseHeader ictx
  let pmctx : Parser.ParserModuleContext :=
    { env := ← getEnv, options := ← getOptions
      currNamespace := ← getCurrNamespace, openDecls := ← getOpenDecls }
  let mut cmds := #[]
  let mut mps := mps
  let mut msgs : MessageLog := {}
  repeat
    let (stx, mps', msgs') := Parser.parseCommand ictx pmctx mps msgs
    cmds := cmds.push stx
    mps := mps'
    msgs := msgs'
    if Parser.isTerminalCommand stx then break
  Mathlib.Linter.PrivateInPublic.run cmds

-- Disable the linter so that the run on the terminal command, which cannot be guarded, is silent.
set_option linter.privateInPublic false
