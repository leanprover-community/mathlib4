import Embedding.Types

open Lean

namespace Embedding

def OPENAI_API_KEY : IO String := do
  let some key ← IO.getEnv "OPENAI_API_KEY" | throw <| .userError "OpenAI API key not found.
The OpenAI key must be set in the environment variable OPENAI_API_KEY"
  return key

def getRawEmbeddings (data : Array String) : IO (UInt32 × String × String) := do
  let child ← IO.Process.spawn {
    cmd := "curl"
    args := #[
      "https://api.openai.com/v1/embeddings",
      "-H", s!"Authorization: Bearer {← OPENAI_API_KEY}",
      "-H", "Content-Type: application/json",
      "--data-binary", "@-"
    ]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let (stdin, child) ← child.takeStdin
  stdin.putStr <| toString <| toJson <| Json.mkObj [
    ("model","text-embedding-ada-002"),
    ("input", toJson data)
  ]
  stdin.flush 
  let stdout ← IO.asTask child.stdout.readToEnd .dedicated
  let err ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode != 0 then 
    throw <| .userError err
  let out ← IO.ofExcept stdout.get
  return (exitCode, out, err)

partial def getEmbeddings (data : Array String) (gas : Nat := 10) (trace : Bool := false) : 
    IO (Array (Option (Array JsonNumber))) := do
  if gas == 0 then 
    if trace then IO.println "Out of gas."
    return data.map fun _ => none
  if data.size == 0 then 
    if trace then IO.println "Data is empty."
    return #[]
  let (_, rawRes, _) ← getRawEmbeddings data
  match parseResponse rawRes with 
  | .ok (.ok out) => 
    if trace then IO.println s!"Successfully obtained embeddings for data of size {data.size}."
    return out.qsort (fun i j => i.index ≤ j.index) |>.map fun e => some e.embedding
  | .ok (.error err) => 
    if err.isTokenLimit then 
      if data.size == 1 then 
        if trace then IO.println "Token limit reached with size 1. Omitting."
        return #[none]
      let size := data.size
      let newSize := size / 2
      if trace then IO.println s!"Token limit reached. Splitting to size {newSize}."
      return (← getEmbeddings data[:newSize] gas trace) ++ (← getEmbeddings data[newSize:] gas trace)
    else 
      if trace then IO.println s!"Unknown error\n{toJson err}\nRetrying with gas = {gas - 1}."
      getEmbeddings data (gas - 1) trace
  | .error err => 
    if trace then IO.println s!"Parse error:\n{err}\nRetrying with gas = {gas - 1}."
    getEmbeddings data (gas - 1) trace

def getDeclEmbeddings (data : Array Decl) (env : Environment) (gas : Nat := 10) (trace : Bool := false) : 
    IO (Array EmbeddedDecl) := do
  let names : Array String := data.map fun d => d.name.toString
  let types : Array String ← data.mapM fun d => (toString ∘ (·.fmt)) <$> ppExprWithInfos { env := env } d.type
  let nameEmbs ← getEmbeddings names gas trace
  let typeEmbs ← getEmbeddings types gas trace
  return (data.zip (nameEmbs.zip typeEmbs)).map fun d => { d.fst with nameEmb := d.snd.fst, typeEmb := d.snd.snd }

end Embedding