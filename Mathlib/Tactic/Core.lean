/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue
-/

import Lean.Expr
import Mathlib.Lean.Expr

namespace Lean

def setProtected {m : Type → Type} [Monad m] [MonadEnv m] (nm : Name) : m Unit := do
  let env ← getEnv
  let env := addProtected env nm
  setEnv env

namespace Parser.Tactic

-- syntax simpArg := simpStar <|> simpErase <|> simpLemma
def simpArg := simpStar.binary `orelse (simpErase.binary `orelse simpLemma)

end Parser.Tactic
end Lean
