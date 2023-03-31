import ProofWidgets.Component.Basic
import Mathlib.Tactic.GPT.Sagredo.Dialog

namespace Mathlib.Tactic.GPT.Sagredo

def init : M IO String := do
  sendSystemMessage systemPrompt
  askForAssistance (← initialPrompt)
  pure (← latestCodeBlock).body

def step : M IO String := do
  askForAssistance (← feedback)
  pure (← latestCodeBlock).body

open Lean Elab Meta Tactic

def createState (stx : Syntax) (preEdit : String → String) : MetaM Sagredo.State := do
  let (preamble, decl) ← getSourceUpTo stx
  let preambleAnalysis ← analyzeCode (←getEnv) ""
  let editedDecl := preEdit decl
  let analysis ← liftM <| analyzeCode preambleAnalysis.env editedDecl
  pure ⟨⟨[]⟩, preamble, preambleAnalysis, [({ text := editedDecl }, analysis)]⟩

end Mathlib.Tactic.GPT.Sagredo

open Mathlib.Tactic.GPT.Sagredo

open ProofWidgets
open Lean Meta Server Elab Tactic

/-- A `MetaM String` continuation, containing both the computation and all monad state. -/
structure MetaMStringCont where
  ci : Elab.ContextInfo
  lctx : LocalContext
  -- We can only derive `TypeName` for type constants, so this must be monomorphic.
  σ : Mathlib.Tactic.GPT.Sagredo.State
  deriving TypeName

structure RunnerWidgetProps where
  /-- A continuation to run and print the results of when the button is clicked. -/
  k : WithRpcRef MetaMStringCont

-- Make it possible for widgets to receive `RunnerWidgetProps`. Uses the `TypeName` instance.
#mkrpcenc RunnerWidgetProps

@[server_rpc_method]
def runMetaMStringCont : RunnerWidgetProps → RequestM (RequestTask (String × RunnerWidgetProps))
  | {k := ⟨{ci, lctx, σ}⟩} => RequestM.asTask do
    let (s, σ') ← step σ
    pure ⟨s, ⟨ci, lctx, σ'⟩⟩

@[widget_module]
def runnerWidget : Component RunnerWidgetProps where
  javascript := "
    import { RpcContext, mapRpcError } from '@leanprover/infoview'
    import * as React from 'react';
    const e = React.createElement;

    export default function(props) {
      const [contents, setContents] = React.useState('Run!')
      const rs = React.useContext(RpcContext)
      return e('button', { onClick: () => {
        setContents('Running..')
        rs.call('runMetaMStringCont', props)
          .then(setContents)
          .catch(e => { setContents(mapRpcError(e).message) })
      }}, contents)
    }
  "



syntax (name := makeRunnerTac) "sagredo!" : tactic

@[tactic makeRunnerTac] def makeRunner : Tactic
  | `(tactic| sagredo!%$tk) => do
    let σ ← createState tk (fun decl => decl.replace "sagredo!" "sorry")
    let (firstCode, σ') ← init σ
    -- Store the continuation and monad context.
    let props : RunnerWidgetProps := {
      k := ⟨{
        ci := (← ContextInfo.save)
        lctx := (← getLCtx)
        σ := σ'
      }⟩}
    -- Save a widget together with a pointer to `props`.
    savePanelWidgetInfo tk ``runnerWidget (rpcEncode props)
  | _ => throwUnsupportedSyntax

-- example : True := by
--   sagredo!
--   trivial
