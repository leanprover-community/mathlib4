/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import LeanPinecone
import LeanEmbedding

open Lean

namespace FindWithEmbedding

def searchNames (k : Nat) (input : String) : Elab.Command.CommandElabM Unit := do
  let emb ← EmbeddingM.getIndexedEmbeddings #[input] |>.run
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


def searchTypes (k : Nat) (input : String) : Elab.Command.CommandElabM Unit := do
  let emb ← EmbeddingM.getIndexedEmbeddings #[input] |>.run
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
        throwError "Failed to fecth module from metadata."
      IO.println "---"
      IO.println s!"{module}\n{name} : {type}"

end FindWithEmbedding

open FindWithEmbedding

elab "#find_name" s:name k:num : command => searchNames k.getNat (toString s.getName)
elab "#find_type" s:str k:num : command => searchTypes k.getNat s.getString
