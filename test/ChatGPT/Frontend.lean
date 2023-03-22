import Mathlib.Tactic.ChatGPT.Frontend

open Lean Elab Meta
namespace Mathlib.Tactic.ChatGPT

set_option trace.debug true

#eval show MetaM _ from do
  let (env, msgs, _) ← runFrontend "import Lean\ndef h : Nat := by sorry" {} "" default
  let some ci := env.find? `h | throwError "No declaration h"
  trace[debug] "{← ppExpr ci.type}"
  guard $ toString (← ppExpr ci.type) = "Nat"
  for msg in msgs do
    trace[debug] msg.data


#eval show MetaM _ from do
  let (_, msgs, _) ← runFrontend "def h : Nat := by\n\ndef g := 7" {} "" default
  for msg in msgs do
    trace[debug] (← msg.toString true)

def fghExample :=
"
import Lean
#eval 2 + 2
def f := 2
def g := ⟨f
def h : Nat := by sorry
"

#eval show MetaM _ from do
  let (_, msgs, trees) ← runFrontend fghExample {} "" default
  for msg in msgs do
    trace[debug] (← msg.toString true)
  for tree in trees do
    trace[debug] (← tree.format)

#eval show MetaM _ from do
  let (_, _, trees) ← runFrontend fghExample {} "" default
  for (ctx, g, pos, _) in trees.bind InfoTree.sorries do
      trace[debug] "The `sorry` at {pos} has goal:\n{← ctx.ppGoals [g]}"
