/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean
import Mathlib.Util.TermUnsafe

/-!
Define a `run_cmd a; b` command which executes code in `CommandElabM Unit`.
This is almost the same as `#eval show CommandElabM Unit from do a; b`,
except that it doesn't print an empty diagnostic.
-/

namespace Lean.Parser.Command
open Meta Elab Command Term

elab (name := runCmd) "run_cmd " elems:doSeq : command => do
  ← liftTermElabM <|
    unsafe evalTerm (CommandElabM Unit)
      (mkApp (mkConst ``CommandElabM) (mkConst ``Unit))
      (← `(discard do $elems))
