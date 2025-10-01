import Mathlib.Tactic.Reap.Requests.Basic
import Mathlib.Tactic.Reap.OpenAIClient.Types

open Lean

def getOpenAIRequestHeaders (apiKey : String) : Json :=
  if apiKey.isEmpty then
    json% {
      "accept" : "application/json",
      "Content-Type" : "application/json"
    }
  else
    json% {
      "accept" : "application/json",
      "Content-Type" : "application/json",
      "Authorization" : $(s!"Bearer {apiKey}")
    }

namespace OpenAIClient

def generateCompletion (client : OpenAIClient) (req : OpenAICompletionRequest) : IO OpenAICompletionResponse := do
  let completeUrl := client.baseUrl ++ "/completions"
  Requests.post completeUrl req <| getOpenAIRequestHeaders client.apiKey

def generateChat (client : OpenAIClient) (req : OpenAIChatRequest) : IO OpenAIChatResponse := do
  let chatUrl := client.baseUrl ++ "/chat/completions"
  Requests.post chatUrl req <| getOpenAIRequestHeaders client.apiKey

end OpenAIClient
