/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Lean

/-!
# Additional declarations related to linters
-/

set_option autoImplicit true

open Lean Elab

namespace Lean.Linter

/-- If `linterOption` is true, print a linter warning message at the position determined by `stx`.
-/
def logLintIf [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (linterOption : Lean.Option Bool) (stx : Syntax) (msg : MessageData) : m Unit := do
  if linterOption.get (← getOptions) then logLint linterOption stx msg

end Lean.Linter
