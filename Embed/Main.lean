import LeanEmbedding
import LeanPinecone

open System Lean

partial def Json.toLine (j : Json) : String := match j with
  | .obj obj => "{" ++
      (obj.toArray.foldl (fun s ⟨key,j⟩ =>
        s ++ s!"\"{key}\":" ++ Json.toLine j ++ ",") "").dropRight 1
      ++ "}"
  | .arr arr => "[" ++
      (arr.foldl (fun s j => s ++ Json.toLine j ++ ",") "").dropRight 1
      ++ "]"
  | e => toString e

-- TODO: More efficient implementation using `ConstMap.forM`?
local instance : ForIn IO ConstMap (Name × ConstantInfo) where
  forIn C := forIn C.toList

namespace Embed

def typeEmbeddings : FilePath := "typeEmbeddings.jsonl"
def nameEmbeddings : FilePath := "nameEmbeddings.jsonl"

def generateTypes : IO Unit := do
  if ← typeEmbeddings.pathExists then
    IO.println s!"{typeEmbeddings} file already exists. Aborting!"
    return
  IO.FS.withFile typeEmbeddings .write fun handle => do
    let mathlibContents ← IO.FS.readFile "Mathlib.lean"
    let ctx := Parser.mkInputContext mathlibContents "<Mathlib>"
    let (hdr, _, msgs) ← Parser.parseHeader ctx
    if msgs.toList.length != 0 then
      IO.println "Header parsing messages:"
      for m in msgs.msgs do
        IO.println <| ← m.toString
    initSearchPath (← findSysroot)
    let (env, msgs) ← Elab.processHeader hdr {} msgs ctx
    if msgs.toList.length != 0 then
      IO.println "Header processing messages:"
      for m in msgs.msgs do
        IO.println <| ← m.toString
    let mut batch : Array (Name × ConstantInfo) := #[]
    for (nm,c) in env.constants do
      -- TODO: Generalize using arbitrary filter.
      if !(!nm.isInternal && match c with | .thmInfo _ => true | _ => false) then
        continue
      batch := batch.push (nm,c)
      if batch.size == 2000 then
        process env handle batch
        batch := #[]
    process env handle batch
    IO.println "Finished generating type embeddings."
where
process (env handle batch) := do
  let nameData : Array Name := batch.map Prod.fst
  let typeData : Array String ← batch.mapM fun (_, c) =>
    (toString ∘ FormatWithInfos.fmt) <$> ppExprWithInfos { env := env } c.type
  let moduleData : Array Name ← batch.mapM fun (nm,_) => do
    let some moduleIdx := env.getModuleIdxFor? nm | return Name.anonymous
    return env.header.moduleNames[moduleIdx.toNat]!
  let embeddings ← EmbeddingM.getIndexedEmbeddingsRecursively typeData (trace := true) |>.run
  let embeddedData := embeddings.map fun ⟨i,e⟩ => (nameData[i]!, typeData[i]!, moduleData[i]!, e)
  for (nm,tp,mod,emb) in embeddedData do
    handle.putStrLn <| Json.toLine <| Json.mkObj [
      ("name", toJson nm),
      ("type", toJson tp),
      ("module", toJson mod),
      ("embedding", toJson emb)
      ]
  IO.println s!"[Embed.generateTypes] Processed batch of size {batch.size}"

def generateNames : IO Unit := do
  if ← nameEmbeddings.pathExists then
    IO.println s!"{nameEmbeddings} file already exists. Aborting!"
    return
  IO.FS.withFile nameEmbeddings .write fun handle => do
    let mathlibContents ← IO.FS.readFile "Mathlib.lean"
    let ctx := Parser.mkInputContext mathlibContents "<Mathlib>"
    let (hdr, _, msgs) ← Parser.parseHeader ctx
    if msgs.toList.length != 0 then
      IO.println "Header parsing messages:"
      for m in msgs.msgs do
        IO.println <| ← m.toString
    initSearchPath (← findSysroot)
    let (env, msgs) ← Elab.processHeader hdr {} msgs ctx
    if msgs.toList.length != 0 then
      IO.println "Header processing messages:"
      for m in msgs.msgs do
        IO.println <| ← m.toString
    let mut batch : Array (Name × ConstantInfo) := #[]
    for (nm,c) in env.constants do
      -- TODO: Generalize using arbitrary filter.
      if !(!nm.isInternal && match c with | .thmInfo _ => true | _ => false) then
        continue
      batch := batch.push (nm,c)
      if batch.size == 2000 then
        process env handle batch
        batch := #[]
    process env handle batch
    IO.println "Finished generating name embeddings."
where
process (env handle batch) := do
  let nameData : Array Name := batch.map Prod.fst
  let typeData : Array String ← batch.mapM fun (_, c) =>
    (toString ∘ FormatWithInfos.fmt) <$> ppExprWithInfos { env := env } c.type
  let moduleData : Array Name ← batch.mapM fun (nm,_) => do
    let some moduleIdx := env.getModuleIdxFor? nm | return Name.anonymous
    return env.header.moduleNames[moduleIdx.toNat]!
  let embeddings ← EmbeddingM.getIndexedEmbeddingsRecursively
    (nameData.map toString) (trace := true) |>.run
  let embeddedData := embeddings.map fun ⟨i,e⟩ => (nameData[i]!, typeData[i]!, moduleData[i]!, e)
  for (nm,tp,mod,emb) in embeddedData do
    handle.putStrLn <| Json.toLine <| Json.mkObj [
      ("name", toJson nm),
      ("type", toJson tp),
      ("module", toJson mod),
      ("embedding", toJson emb)
      ]
  IO.println s!"[Embed.generateTypes] Processed batch of size {batch.size}"

def uploadTypes : IO Unit := do
  if !(← typeEmbeddings.pathExists) then
    IO.println s!"{typeEmbeddings} does not exist. Aborting!"
    return
  let gitRev := (← IO.Process.output {
    cmd := "git"
    args := #["rev-parse", "HEAD"]
  }).stdout |>.replace "¬" ""
  IO.FS.withFile typeEmbeddings .read fun handle => do
    let mut line := "START"
    let mut batch : Array (String × String × String × Array JsonNumber) := #[]
    while line != "" do
      line ← handle.getLine
      if line != "" then
        let .ok json := Json.parse line |
          throw <| .userError "Failed to parse line. Aborting!"
        let .ok name := json.getObjValAs? String "name" |
          throw <| .userError "Failed to parse name. Aborting!"
        let .ok type := json.getObjValAs? String "type" |
          throw <| .userError "Failed to parse type. Aborting!"
        let .ok module := json.getObjValAs? String "module" |
          throw <| .userError "Failed to parse module. Aborting!"
        let .ok embedding := json.getObjValAs? (Array JsonNumber) "embedding" |
          throw <| .userError "Failed to parse embedding. Aborting!"
        batch := batch.push (name, type, module, embedding)
      if batch.size == 100 then
        process gitRev batch 5
        batch := #[]
    process gitRev batch 5
where
process (gitRev batch gas) := do
  let mut result : Nat := 0
  let mut count : Nat := gas
  while result != batch.size && count > 0 do
    try
      result ← PineconeM.run <| PineconeM.upsert
        (batch.map fun (nm,tp,mdl,emb) => {
          id := toString nm.toName.hash,
          values := emb,
          metadata := Json.mkObj [
            ("name",nm),
            ("type",tp),
            ("module",mdl),
            ("rev",gitRev)
          ] }) "types"
    catch e =>
      IO.println e
      count := count - 1
      IO.println s!"Trying again with remaining gas {count}"
  if count == 0 then
    IO.println s!"Ran out of gas. Aborting this batch of size {batch.size}."
  else IO.println s!"Successfully uploaded {result} embeddings for batch of size {batch.size}."

def uploadNames : IO Unit := do
  if !(← nameEmbeddings.pathExists) then
    IO.println s!"{nameEmbeddings} does not exist. Aborting!"
    return
  let gitRev := (← IO.Process.output {
    cmd := "git"
    args := #["rev-parse", "HEAD"]
  }).stdout |>.replace "¬" ""
  IO.FS.withFile nameEmbeddings .read fun handle => do
    let mut line := "START"
    let mut batch : Array (String × String × String × Array JsonNumber) := #[]
    while line != "" do
      line ← handle.getLine
      if line != "" then
        let .ok json := Json.parse line |
          throw <| .userError "Failed to parse line. Aborting!"
        let .ok name := json.getObjValAs? String "name" |
          throw <| .userError "Failed to parse name. Aborting!"
        let .ok type := json.getObjValAs? String "type" |
          throw <| .userError "Failed to parse type. Aborting!"
        let .ok module := json.getObjValAs? String "module" |
          throw <| .userError "Failed to parse module. Aborting!"
        let .ok embedding := json.getObjValAs? (Array JsonNumber) "embedding" |
          throw <| .userError "Failed to parse embedding. Aborting!"
        batch := batch.push (name, type, module, embedding)
      if batch.size == 100 then
        process gitRev batch 5
        batch := #[]
    process gitRev batch 5
where
process (gitRev batch gas) := do
  let mut result : Nat := 0
  let mut count : Nat := gas
  while result != batch.size && count > 0 do
    try
      result ← PineconeM.run <| PineconeM.upsert
        (batch.map fun (nm,tp,mdl,emb) => {
          id := toString nm.toName.hash,
          values := emb,
          metadata := Json.mkObj [
            ("name",nm),
            ("type",tp),
            ("module",mdl),
            ("rev",gitRev)
          ] }) "names"
    catch e =>
      IO.println e
      count := count - 1
      IO.println s!"Trying again with remaining gas {count}"
  if count == 0 then
    IO.println s!"Ran out of gas. Aborting this batch of size {batch.size}."
  else IO.println s!"Successfully uploaded {result} embeddings for batch of size {batch.size}."

end Embed

def main (args : List String) : IO Unit :=
  match args with
  | "generate"::"types"::[] => Embed.generateTypes
  | "generate"::"names"::[] => Embed.generateNames
  | "generate"::"both"::[] => do Embed.generateTypes ; Embed.generateNames
  | "upload"::"types"::[] => Embed.uploadTypes
  | "upload"::"names"::[] => Embed.uploadNames
  | "upload"::"both"::[] => do Embed.uploadTypes ; Embed.uploadNames
  | "go"::[] => do
      Embed.generateTypes ; Embed.generateNames ; Embed.uploadTypes ; Embed.uploadNames
  | _ => IO.println "Usage:
Generate type embeddings:            lake exe embed generate types
Generate name embeddings:            lake exe embed generate names
Generate type and name embeddings:   lake exe embed generate both
Upload type embeddings:              lake exe embed upload types
Upload name embeddings:              lake exe embed upload names
Upload type and name embeddings:     lake exe embed upload both
Generate and upload types and names: lake exe embed go"
