/-
Copyright (c) 2018 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
import Lean.Elab.SyntheticMVars
import Mathlib.Util.TermUnsafe

namespace Mathlib.RunTac
open Lean Elab Term Meta Tactic

elab "run_tac" e:doSeq : tactic => do
  ← unsafe evalTerm (TacticM Unit) (mkApp (mkConst ``TacticM) (mkConst ``Unit))
    (← `(discard do $e))
