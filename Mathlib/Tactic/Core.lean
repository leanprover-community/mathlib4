/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Aurélien Saue, Mario Carneiro
-/

import Lean.Expr
import Mathlib.Lean.Expr

open Lean.Elab.Tactic

namespace Lean

/-- Make `nm` protected. -/
def setProtected {m : Type → Type} [Monad m] [MonadEnv m] (nm : Name) : m Unit := do
  modifyEnv (addProtected · nm)

namespace Parser.Tactic

-- syntax simpArg := simpStar <|> simpErase <|> simpLemma
def simpArg := simpStar.binary `orelse (simpErase.binary `orelse simpLemma)

syntax simpArgs := " [" simpArg,* "] "
syntax withArgs := " with " (colGt ident)+
syntax usingArg := " using " term

/-- Extract the arguments from a `simpArgs` syntax as an array of syntaxes -/
def getSimpArgs : Syntax → TacticM (Array Syntax)
  | `(simpArgs|[$args,*]) => pure args.getElems
  | _                     => Elab.throwUnsupportedSyntax

/-- Extract the arguments from a `withArgs` syntax as an array of syntaxes -/
def getWithArgs : Syntax → TacticM (Array Syntax)
  | `(withArgs|with $args*) => pure args
  | _                       => Elab.throwUnsupportedSyntax

/-- Extract the argument from a `usingArg` syntax as a syntax term -/
def getUsingArg : Syntax → TacticM Syntax
  | `(usingArg|using $e) => pure e
  | _                    => Elab.throwUnsupportedSyntax

end Parser.Tactic
end Lean
