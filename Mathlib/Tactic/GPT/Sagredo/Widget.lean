/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Scott Morrison
-/
import ProofWidgets.Component.Basic
import Mathlib.Tactic.GPT.Sagredo.Dialog

-- This requires `npm install react-markdown`
-- Then in `./widget`, `npm run build`.

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

structure NextQueryResponse where
  /-- The next query we will make. -/
  query : String
  data : RPCData

#mkrpcenc NextQueryResponse

structure RunQueryResponse where
  /-- The LLM's entire response. -/
  response : String
  /-- The latest proof suggested by the LLM. -/
  proof : String
  data : RPCData

#mkrpcenc RunQueryResponse

structure MakeProofEditResponse where
  edit : Lsp.WorkspaceEdit

#mkrpcenc MakeProofEditResponse

/-- Returns the text of the next query we will make. (But doesn't run it.) -/
@[server_rpc_method]
def nextQuery : RPCData → RequestM (RequestTask NextQueryResponse)
  | {k := ⟨{ci, lctx, σ}⟩} => RequestM.asTask do
    let (s, σ') ← Mathlib.Tactic.GPT.Sagredo.nextQuery σ
    pure ⟨s, ⟨ci, lctx, σ'⟩⟩

/-- Runs the next query, and returns the entire response, as well as the extracted code block. -/
@[server_rpc_method]
def runQuery : RPCData → RequestM (RequestTask RunQueryResponse)
  | {k := ⟨{ci, lctx, σ}⟩} => RequestM.asTask do
    let ((response, sol), σ') ← (do
      askForAssistance (← feedback)
      pure (← latestResponse, ← latestSolution)) σ
    pure ⟨response, sol, ⟨ci, lctx, σ'⟩⟩

/-- Compute an edit to replace the current proof with one suggested by the LLM. -/
@[server_rpc_method]
def makeProofEdit : RPCData × String → RequestM (RequestTask MakeProofEditResponse)
  | ({k := ⟨{ci, lctx, σ}⟩}, proof) => RequestM.asTask do
    let uri ← documentUriFromModule (← read).srcSearchPath (← ci.runMetaM lctx getMainModule)
    return { edit := Lsp.WorkspaceEdit.ofTextEdit uri.get! <|
      { range := σ.declRange,
        newText := proof }  }

@[widget_module]
def sagredoWidget : Component RPCData where
  javascript := include_str "../../../../build/js/sagredo.js"

syntax (name := sagredoInteractive') "sagredo!" : tactic

@[tactic sagredoInteractive'] def sagredoInteractive : Tactic
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
    savePanelWidgetInfo tk ``sagredoWidget (rpcEncode data)
    liftMetaTactic fun g => do admitGoal g; pure []
  | _ => throwUnsupportedSyntax

-- /-- The length of the concatenation of two lists is the sum of the lengths of the lists. -/
-- theorem length_append : ∀ (L1 L2 : List α), (L1 ++ L2).length = L1.length + L2.length := by
--   sagredo!
