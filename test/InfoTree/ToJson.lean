import Mathlib.Util.Frontend
import Mathlib.Util.InfoTree.ToJson

open Lean Elab IO Meta

#eval show MetaM _ from do
  let (_, msgs, trees) ← compileModule `Mathlib.Logic.Hydra
  for m in msgs do IO.println (← m.data.format)
  for t in trees do
    for t in t.retainTacticInfo do
      for t in t.retainOriginal do
        for t in t.retainSubstantive do
          IO.println (← t.toJson none)
  return msgs.length
