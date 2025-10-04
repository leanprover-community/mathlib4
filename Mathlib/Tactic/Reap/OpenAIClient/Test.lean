import Mathlib.Tactic.Reap.OpenAIClient.Basic

def getClient : IO OpenAIClient := return {
  baseUrl := "https://api.openai.com/v1"
  apiKey := (← IO.getEnv "OPENAI_API_KEY").getD ""
}

def getReq (prompt : String) : OpenAIChatRequest := {
  model := "gpt-4o"
  messages := [{
    role := "user",
    content := prompt
  }]
  n := 1
  temperature := 0.7
}

def chat (prompt : String) : IO OpenAIChatResponse := do
  let client ← getClient
  let req := getReq prompt
  OpenAIClient.generateChat client req

#eval chat "What is the meaning of life?"
