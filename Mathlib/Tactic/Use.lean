/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arthur Paulino
-/

import Lean

open Lean.Elab.Tactic

namespace Mathlib.Tactic

elab "use " "[" es:term,+ "]" : tactic => do
  for stx in es.getElems do
    try
      evalTactic (← `(tactic|refine Exists.intro $stx ?_))
      evalTactic (← `(tactic|try trivial))
    catch e =>
      throwError "use tactic failed: {e.toMessageData}"
