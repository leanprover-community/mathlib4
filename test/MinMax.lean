import Mathlib.Tactic.MinMax

open Mathlib.ToNatDegree

run_cmd Lean.Elab.Command.liftTermElabM do
  guard (splitUpper "SemilatticeSup" == ["Semilattice", "Sup"])

run_cmd Lean.Elab.Command.liftTermElabM do
  guard <| "hello I am `WithTop' α` and also `top'`" ==
    stringReplacements "hello I am `WithBot' α` and also `bot'`"

run_cmd Lean.Elab.Command.liftTermElabM do
  guard (["le", "inf"] == swapWords ["inf", "le"])

run_cmd Lean.Elab.Command.liftTermElabM do
  guard (splitUpper "NNRealHHi, but it's " ==
    ["NNReal", "HHi", ",", " ", "but", " ", "it", "'", "s", " "])
