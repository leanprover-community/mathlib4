import Lean
import Lean.Parser.Term
import Batteries.Data.List.Matcher

open Lean Elab Command Linter

structure Config where
  chain : List Name
  projection : String

def isBadSyntax (c : Config) : Syntax → Bool
  | .ident _ s _ _ => List.containsInfix s.str.toList c.projection.toList
  | _ => false

def isTermApp : Syntax → Bool
  | `($_ $_*) => true
  | _ => false

def isValValAux (e : Expr) : List Name → Bool
  | [] => true
  | n :: ns => e.isAppOf n && e.getAppArgs.any (fun e ↦ isValValAux e ns)

def isValVal (c : Config) (e : Expr) : Bool :=
  isValValAux e c.chain

partial
def find (c : Config) : InfoTree → Array (Syntax × Bool)
  | .node k args =>
    if let .ofTermInfo i := k then
      if isTermApp i.stx then
        if List.containsInfix (toString i.stx).toList c.projection.toList then
          #[(i.stx, (i.expr.find? (isValVal c)).isSome)]
        else
          #[]
        --match i.stx.find? (isBadSyntax c) with
        --| some stx => #[(stx, (i.expr.find? (isValVal c)).isSome)]
        --| none => #[(i.stx, (i.expr.find? (isValVal c)).isSome)]
      else
        (args.map (find c)).foldl (· ++ ·) #[]
        -- kargs
    --else if let .ofFieldInfo i := k then
    --  #[(i.stx, (i.val.find? (isValVal c)).isSome)] ++ kargs
    --else if let .ofPartialTermInfo i := k then
    --  #[(i.stx, true)] ++ kargs
    else
      (args.map (find c)).foldl (· ++ ·) #[]
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
      for (stx, relevant) in tree do
        unless relevant do continue
        Linter.logLintIf linter.innerOuter stx
          m!"{stx} uses unwanted explicit syntax."

def homBase : Config where
  chain :=
    [`DFunLike.coe ,
     `CategoryTheory.ConcreteCategory.hom ,
     `AlgebraicGeometry.PresheafedSpace.Hom.base ,
     `AlgebraicGeometry.LocallyRingedSpace.Hom.toHom ,
     `AlgebraicGeometry.Scheme.Hom.toLRSHom']
  projection := "base"

initialize addLinter (innerOuterLinter homBase)
