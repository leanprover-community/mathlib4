import Mathlib.Tactic.Reap.Options
import Mathlib.Tactic.Reap.Requests.Basic

open Lean

structure PremiseSelectionRequest where
  query : String
  num_results: Nat
deriving ToJson, FromJson

structure PremiseSelectionResult where
  formal_name : String
  formal_statement : String
  informal_statement : String
  informal_name : String
deriving ToJson, FromJson, Repr

structure PremiseSelectionClient where
  apiUrl : String

namespace PremiseSelectionClient

initialize cache :
  IO.Ref (Std.HashMap (String × Nat) (Array PremiseSelectionResult)) ← IO.mkRef {}

def getPremises (s : String) (num_results : Nat := 6) : CoreM <| Array PremiseSelectionResult := do
  match (← cache.get).get? (s, num_results) with
  | some results => return results
  | none => do
    let s' := System.Uri.escapeUri s
    let req := PremiseSelectionRequest.mk s' num_results
    let url := reap.ps_endpoint.get (← getOptions)
    let results : Array PremiseSelectionResult ← Requests.post url req
    cache.modify fun m => m.insert (s, num_results) results
    return results

end PremiseSelectionClient
