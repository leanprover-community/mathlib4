/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Scott Morrison
-/
import ProofWidgets.Component.Basic
import Mathlib.Tactic.GPT.Sagredo.Dialog

namespace Mathlib.Tactic.GPT.Sagredo.Widget

open Lean Elab Meta Tactic



structure Data where
  ci : Elab.ContextInfo
  lctx : LocalContext
  σ : State
  deriving TypeName

end Mathlib.Tactic.GPT.Sagredo.Widget

open Mathlib.Tactic.GPT.Sagredo Widget

open ProofWidgets
open Lean Meta Server Elab Tactic

structure RPCData where
  k : WithRpcRef Data

-- Make it possible for widgets to receive `RPCData`.
#mkrpcenc RPCData

/-- Returns the text of the next query we will make. (But doesn't run it.) -/
@[server_rpc_method]
def nextQuery : RPCData → RequestM (RequestTask (String × RPCData))
  | {k := ⟨{ci, lctx, σ}⟩} => RequestM.asTask do
    let (s, σ') ← Mathlib.Tactic.GPT.Sagredo.nextQuery σ
    pure ⟨s, ⟨ci, lctx, σ'⟩⟩

/-- Runs the next query, and returns the entire response, as well as the extracted code block. -/
@[server_rpc_method]
def runQuery : RPCData → RequestM (RequestTask (String × String × RPCData))
  | {k := ⟨{ci, lctx, σ}⟩} => RequestM.asTask do
    let ((response, sol), σ') ← (do
      askForAssistance (← feedback)
      pure (← latestResponse, ← latestSolution)) σ
    pure ⟨response, sol, ⟨ci, lctx, σ'⟩⟩

@[widget_module]
def runnerWidget : Component RPCData where
  javascript := include_str "../../../../build/js/sagredo.js"

syntax (name := makeRunnerTac) "sagredo!" : tactic

@[tactic makeRunnerTac] def makeRunner : Tactic
  | `(tactic| sagredo!%$tk) => do
    let σ ← createState tk (fun decl => decl.replace "sagredo!" "sorry")
    let (_, σ') ← (do sendSystemMessage systemPrompt) σ
    -- Store the continuation and monad context.
    let data : RPCData := {
      k := ⟨{
        ci := (← ContextInfo.save)
        lctx := (← getLCtx)
        σ := σ'
      }⟩}
    -- Save a widget together with a pointer to `props`.
    savePanelWidgetInfo tk ``runnerWidget (rpcEncode data)
    liftMetaTactic fun g => do admitGoal g; pure []
  | _ => throwUnsupportedSyntax

/--please use the refl tactic -/
example : 2 + 2 = 4 := by sagredo!
