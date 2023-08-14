import Mathlib.Util.InfoTree.More
import Mathlib.Util.InfoTree.ToJson

open Lean Elab Meta

#eval show MetaM _ from do
  let (_, msgs, trees) ← compileModule `Mathlib.Init.ZeroOne
  for m in msgs do IO.println (← m.data.format)
  for t in trees do
    IO.println (← t.toJson none)
  return msgs.length
