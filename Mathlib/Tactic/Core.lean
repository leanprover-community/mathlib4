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

syntax simpArgs := " [" simpArg,+ "] "
syntax withStx  := " with " (colGt ident)+
syntax usingStx := " using " term

def mkSimpArgs (optStx : Option Syntax) : TacticM (Array Syntax) :=
  match optStx with
  | none     => default
  | some stx => match stx with
    | `(simpArgs|[$args,*]) => pure $ args.getElems
    | _                     => Elab.throwUnsupportedSyntax

def evalTacticM (tacticStxM : TacticM Syntax) : TacticM PUnit :=
  match tacticStxM with
  | `(tactic|$tacticStx) => do evalTactic (← tacticStxM)
  | _                    => Elab.throwUnsupportedSyntax

end Parser.Tactic
end Lean
