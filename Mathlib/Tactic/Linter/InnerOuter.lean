import Lean
import Lean.Parser.Term
import Batteries.Data.List.Matcher

open Lean Elab Command Linter

structure Config where
  outer : Name
  inner : Name
  projection : String

def isBadSyntax (c : Config) : Syntax → Bool
  | `(c.outer $_*) => true
  | stx => List.containsInfix (toString stx).toList c.projection.toList

def isTermApp : Syntax → Bool
  | `($_ $_*) => true
  | _ => false

partial
def containsOuter (c : Config) (e : Expr) : Bool :=
  if e.isAppOf c.outer then
    true
  else
    e.getAppArgs.any (fun e ↦ containsOuter c e)

def isValVal (c : Config) (e : Expr) : Bool :=
  e.isAppOf c.inner && e.getAppArgs.any (fun e ↦ containsOuter c e)

partial
def find (c : Config) : InfoTree → Array (TermInfo × Bool)
  | .node k args =>
    let kargs := (args.map (find c)).foldl (· ++ ·) #[]
    if let .ofTermInfo i := k then
      if isTermApp i.stx && (i.stx.find? (isBadSyntax c)).isSome then
        #[(i, (i.expr.find? (isValVal c)).isSome)] ++ kargs
      else
        #[(i, false)] ++ kargs
    else kargs
  | .context _ t => find c t
  | _ => default

register_option linter.innerOuter : Bool := {
  defValue := true
  descr := "enable the inner-outer linter"
}

def innerOuterLinter (c : Config) : Linter where
  run stx := do
    unless getLinterValue linter.innerOuter (← getLinterOptions) && (← getInfoState).enabled do
      return
    let trees ← getInfoTrees
    for tree in trees.map (find c) do
      for (info, relevant) in tree do
        unless relevant do continue
        Linter.logLintIf linter.innerOuter info.stx
          m!"{info.stx} uses explicit syntax for {c.inner} ({c.outer} ?_)"

def homBase : Config where
  outer := `AlgebraicGeometry.PresheafedSpace.Hom.base
  inner := `DFunLike.coe
  projection := ".base"

initialize addLinter (innerOuterLinter homBase)
