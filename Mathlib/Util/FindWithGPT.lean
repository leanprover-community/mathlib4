/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import LLM
import LeanPinecone
import LeanEmbedding

namespace FindWithGPT

open Lean

def nameSystemMessage : String :=
"You are an expert in both mathematics and the Lean4 interactive proof assistant.
Your task is to convert the user's input into a guess for the name of the associated lemma.
Your resposne should only be a single line.

Examples:

Input:
For every natural number $n$, $n+1$ is positive.
Response:
Nat.succ_pos

Input:
If $G$ is a group and $g ∈ G$, then $g * g^{-1} = 1$.
Response:
mul_inv_self"

def searchNames (k : Nat) (input : String) : Elab.Command.CommandElabM Unit := do
  let gptGeneratedName ← LLM.GPT.send input nameSystemMessage
  IO.println s!"GPT suggestion: {gptGeneratedName}"
  let emb ← EmbeddingM.getIndexedEmbeddings #[gptGeneratedName] |>.run
  if h : 0 < emb.size then
    let emb := emb[0].embedding
    let query : Pinecone.Query := {
      topK := k
      vector := emb
      filter := none -- TODO: make "none" the default.
      nmspace := "names"
    }
    let res ← PineconeM.query query |>.run
    for mtch in res.mtches do
      let some json := mtch.metadata | throwError "Failed to parse pinecone metadata as json."
      let .ok name := json.getObjValAs? String "name" |
        throwError "Failed to fetch name from metadata."
      let .ok type := json.getObjValAs? String "type" |
        throwError "Failed to fetch type from metadata."
      let .ok module := json.getObjValAs? String "module" |
        throwError "Failed to fecth module from metadata."
      IO.println "---"
      IO.println s!"{module}\n{name} : {type}"

def typeSystemMessage : String :=
"You are an expert in both mathematics and the Lean4 interactive proof assistant.
Your task is to convert the user's input into a Lean4 type expression.
Your resposne should only be a single line, expressing the Lean4 type requested by the user.

Examples:

Input:
For every natural number $n$, $n+1$ is positive.
Response:
∀ (n : ℕ), 0 < n+1

Input:
If $G$ is a group and $g ∈ G$, then $g * g^{-1} = 1$.
Response:
∀ {G : Type _} [Group G] (g : G), g * g⁻¹ = 1"

def searchTypes (k : Nat) (input : String) : Elab.Command.CommandElabM Unit := do
  let gptGeneratedType ← LLM.GPT.send input typeSystemMessage
  IO.println s!"GPT suggestion: {gptGeneratedType}"
  let emb ← EmbeddingM.getIndexedEmbeddings #[gptGeneratedType] |>.run
  if h : 0 < emb.size then
    let emb := emb[0].embedding
    let query : Pinecone.Query := {
      topK := k
      vector := emb
      filter := none -- TODO: make "none" the default.
      nmspace := "types"
    }
    let res ← PineconeM.query query |>.run
    for mtch in res.mtches do
      let some json := mtch.metadata | throwError "Failed to parse pinecone metadata as json."
      let .ok name := json.getObjValAs? String "name" |
        throwError "Failed to fetch name from metadata."
      let .ok type := json.getObjValAs? String "type" |
        throwError "Failed to fetch type from metadata."
      let .ok module := json.getObjValAs? String "module" |
        throwError "Failed to fetch module from metadata."
      IO.println "---"
      IO.println s!"{module}\n{name} : {type}"

end FindWithGPT

open FindWithGPT

elab "#find_name_with_gpt" s:str k:num : command => searchNames k.getNat s.getString
elab "#find_type_with_gpt" s:str k:num : command => searchTypes k.getNat s.getString
