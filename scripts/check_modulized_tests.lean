module
public import Cli.Basic
public import Lean

open Lean System Parser.Module

public def main : IO UInt32 := do
  let pathStrs ← FilePath.walkDir "MathlibTest"
  for pathStr in pathStrs do
    unless !(← pathStr.isDir) do continue
    let mut text ← IO.FS.readFile pathStr
    let inputCtx := Parser.mkInputContext text pathStr.toString
    let (header, parserState, msgs) ← Parser.parseHeader inputCtx
    if !msgs.toList.isEmpty then -- skip this file if there are parse errors
      msgs.forM fun msg => msg.toString >>= IO.println
      throw <| .userError "parse errors in file"
    let `(header| $[module%$moduleTk?]? $[prelude%$preludeTk?]? $imps:import*) := header
      | throw <| .userError s!"unexpected header syntax of {pathStr}"
    if moduleTk?.isSome then
      continue
    IO.println s!"not modulized: {pathStr}"
  return 0
