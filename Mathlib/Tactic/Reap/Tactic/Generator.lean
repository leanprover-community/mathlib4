import Mathlib.Tactic.Reap.OpenAIClient.Basic
import Mathlib.Tactic.Reap.Options
import Mathlib.Tactic.Reap.Future.Basic
import Mathlib.Tactic.Reap.PremiseSelection.API

open Lean Elab Tactic

structure TacticGenerator where
  llmClient : OpenAIClient
  premiseSelectionClient : PremiseSelectionClient

namespace TacticGenerator

def filterGeneration (s: String) : Bool :=
  let banned := ["sorry", "admit", "▅"]
  !(banned.any fun s' => (s.splitOn s').length > 1)

def parseCompletionResponseOpenAI (res: OpenAICompletionResponse) : Array String :=
  (res.choices.map fun x => (x.text)).toArray

def parseChatResponseOpenAI (res: OpenAIChatResponse) : Array String :=
  (res.choices.map fun x => (x.message.content)).toArray

def mkRelatedTheorem (id: Nat) (ps : PremiseSelectionResult) : String :=
  let formalName := ps.formal_name
  let informalName := ps.informal_name
  let formalStatement := ps.formal_statement
  "ID: " ++ toString id ++ "\n" ++
  "Formal name: " ++ formalName ++ "\n" ++
  "Informal name: " ++ informalName ++ "\n" ++
  "Formal statement: " ++ formalStatement

def mkPrompt (tacticState : String) (relatedTheorems: Array PremiseSelectionResult) : String :=
  "User: Please generate a tactic in lean4 to solve the state.
Here're some theorems that may be helpful:
" ++ (Array.mapIdx mkRelatedTheorem relatedTheorems |>.joinSep "\n") ++
"
STATE:
" ++ tacticState ++ "
TACTIC:

Assistant:"

def getClient : CoreM TacticGenerator := do
  return {
    llmClient := ⟨reap.llm_endpoint.get (← getOptions), reap.llm_api_key.get (← getOptions)⟩
    premiseSelectionClient := ⟨reap.ps_endpoint.get (← getOptions)⟩
  }

/-- Main function to generate tactics -/
def generatePPTactics (ppGoal : String) : CoreM <| Array (String × Float) := do
  let generator ← getClient
  let relatedTheorems ←
    PremiseSelectionClient.getPremises ppGoal (reap.num_premises.get (← getOptions))
  let prompt := mkPrompt ppGoal relatedTheorems
  let mut results : Std.HashSet String := Std.HashSet.emptyWithCapacity
  let req : OpenAIChatRequest := {
    model := reap.model.get (← getOptions),
    messages := [ { role := "user", content := prompt } ],
    n := reap.num_samples.get (← getOptions),
    temperature := 0.7,
    max_tokens := reap.max_tokens.get (← getOptions),
  }
  let res ← generator.llmClient.generateChat req
  for result in (parseChatResponseOpenAI res) do
    results := results.insert result
  let finalResults := (results.toArray.filter filterGeneration).map fun x => (x, 1.0)
  return finalResults

def generateTactics (mvarId : MVarId) : MetaM <| Array (String × Float) := do
  let ppGoal := toString (← Meta.ppGoal mvarId)
  generatePPTactics ppGoal
