import Lean

namespace Mathlib.Tactic.Symm
open Lean Meta

/-- Environment extensions for symm lemmas -/
initialize symmExtension : SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    name := `symm
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }
/--
matches to expressions of the form `r x y` with `r` a relation and returns the triple `(r, x, y)` if there is a match. Note that `r` may be obtained applying a function to arguments.
-/
def relationAppM? (expr : Expr) : MetaM (Option (Expr × Expr × Expr)) :=
  do
    if expr.isApp && (← inferType expr).isProp then
      let baseRel := expr.getAppFn
      let allArgs := expr.getAppArgs
      if allArgs.size < 2 then pure none
      else
        let lhs := allArgs[allArgs.size -2]!
        let rhs := allArgs[allArgs.size -1]!
        if ← isDefEq (← inferType lhs) (← inferType rhs) then
          let mut rel := baseRel
          for i in [0:allArgs.size - 2] do
            rel := mkApp rel allArgs[i]!
          return some (rel, lhs, rhs)
        else return none
    else pure none

/-- add symmetry attribute if valid -/
def symmAttr : AttributeImpl where
  name := `symm
  descr := "symmetric relation"
  add decl _ kind := do
    MetaM.run' do
      let declTy := (← getConstInfo decl).type
      let (xs, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
      if xs.size < 1 then
        throwError "@[symm] attribute only applies to lemmas proving x ∼ y → y ∼ x, got {declTy} with too few arguments"
      else
        let finalHyp ← inferType xs[xs.size -1]!
        match ← relationAppM? targetTy with
        | some (rel, lhs, rhs) =>
          let flip ←  mkAppM' rel #[rhs, lhs]
          unless (← isDefEq flip finalHyp) do
            throwError "@[symm] attribute only applies to lemmas proving x ∼ y → y ∼ x, got {declTy} with wrong penultimate argument {finalHyp} instead of {flip}"
          let key ← withReducible <| DiscrTree.mkPath rel
          symmExtension.add (decl, key) kind
        | none =>
          throwError "@[symm] attribute only applies to lemmas proving x ∼ y → y ∼ x, got {declTy}"

initialize registerBuiltinAttribute symmAttr

/-- look up symmetry lemmas -/
def symmLemmas (env : Environment) : DiscrTree Name :=
  symmExtension.getState env


open Lean.Elab.Tactic in

/-- This tactic applies to a goal whose target has the form `t ~ u` where `~` is a symmetric relation, that is, a relation which has a symmetry lemma tagged with the attribute [symm]. It replaces the target with `u ~ t`. -/
elab "symm" : tactic =>
  withMainContext do
  let tgt ← getMainTarget
  match ← relationAppM? tgt with
  | none =>
    throwError "symmetry lemmas only apply to binary relations, not{indentExpr tgt}"
  | some (rel, _, _) =>
    let s ← saveState
    for lem in ← (symmLemmas (← getEnv)).getMatch rel do
      try
        liftMetaTactic (apply · (← mkConstWithFreshMVarLevels lem))
        return
      catch _ =>
        s.restore
    throwError "no applicable symmetry lemma found for{indentExpr tgt}"
