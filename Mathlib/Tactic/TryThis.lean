/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import Lean

/-!
# Stub for try-this support

Lean 4 does not yet support code actions
to present tactic suggestions in the editor.
This file contains a preliminary API
that tactics can call to show suggestions.
-/

namespace Tactic.TryThis

open Lean Elab Elab.Tactic PrettyPrinter Meta

partial def replaceMVarsByUnderscores [Monad m] [MonadQuotation m]
    (s : Syntax) : m Syntax := do
  if s matches `(?$_:ident) then
    `(?_)
  else if let Syntax.node _ kind args := s then
    mkNode kind <$> args.mapM replaceMVarsByUnderscores
  else
    pure s

def delabToRefinableSyntax (e : Expr) : TermElabM Syntax := do
  let stx ← delab e
  replaceMVarsByUnderscores stx

def addSuggestion [Monad m] [MonadLog m] [AddMessageContext m]
    (origStx : Syntax) (suggestion : Syntax) : m Unit :=
  -- Use obscure Unicode characters to discourage editor implementations.
  logInfoAt origStx m!"𝔗𝔯𝔶 𝔱𝔥𝔦𝔰: {suggestion}"

def addExactSuggestion (origTac : Syntax) (e : Expr) : TacticM Unit := do
  let stx ← delabToRefinableSyntax e
  let tac ← if e.hasExprMVar then `(tactic| refine $stx) else `(tactic| exact $stx)
  addSuggestion origTac tac

def addTermSuggestion (origTerm : Syntax) (e : Expr) : TermElabM Unit := do
  addSuggestion origTerm (← delabToRefinableSyntax e)
