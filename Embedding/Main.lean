import Embedding.Basic

open Lean

namespace Lean

instance : ForM m ConstMap (Name × ConstantInfo) where
  forM M e := M.forM fun n c => e (n,c)

instance : ForIn m ConstMap (Name × ConstantInfo) where
  forIn := ForM.forIn 

namespace Environment

def getModuleNameFor? (env : Environment) (nm : Name) : Option Name := 
  env.getModuleIdxFor? nm >>= fun i => env.header.moduleNames[i.toNat]?

end Environment

end Lean

namespace Embedding

def getMathlibEnv : IO Environment := do
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
  return env

def mkDecl (nm : Name) (cinfo : ConstantInfo) (env : Environment) (rev : String) : Decl where
  name := nm
  type := cinfo.type
  module := env.getModuleNameFor? nm
  rev := rev

end Embedding

open Embedding

def main : IO Unit := IO.FS.withFile "embeddings.jsonl" .write fun handle => do
  let env ← Embedding.getMathlibEnv
  let rev ← IO.Process.output {
    cmd := "git"
    args := #["rev-parse","HEAD"]
  } 
  let rev := rev.stdout.trim
  let mut batch := #[]
  let totalSize : Nat := env.constants.toList.filter (fun (nm, _) => !nm.isInternal) |>.length
  IO.println s!"Starting to process {totalSize} declarations."
  let mut counter : Nat := 0
  for (nm,cinfo) in env.constants do 
    if nm.isInternal then continue
    counter := counter + 1
    batch := batch.push <| mkDecl nm cinfo env rev
    if batch.size == 2000 then 
      process handle env batch
      batch := #[]
    if counter % 2000 == 0 then IO.println s!"PROGRESS: {counter}:{totalSize}"
  process handle env batch
where
process (handle env batch) := do
  let embeddedDecls ← getDeclEmbeddings batch env (trace := true)
  for e in embeddedDecls do 
    handle.putStrLn <| (← e.json env).compress
  IO.println s!"Process complete with batch of size {batch.size}"
