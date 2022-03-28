import Lean

namespace Mathlib.Tactic.Symm
open Lean Meta

initialize symmExtension : SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    name := `symm
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

def relationAppM?(expr: Expr) : MetaM (Option (Expr × Expr × Expr)) :=
  do
    if expr.isApp then
      let baseRel := expr.getAppFn
      let allArgs := expr.getAppArgs
      if allArgs.size < 2 then pure none
      else
        let lhs := allArgs[allArgs.size -2]
        let rhs := allArgs[allArgs.size -1]
        let mut rel := baseRel
        for i in [0:allArgs.size -3] do
          rel := mkApp rel allArgs[i]
        return some (rel, lhs, rhs)
    else pure none

def symmAttribute : AttributeImpl where
  name := `symm
  descr := "Marks a lemma as symmetry lemma"
  add decl stx kind := do
    MetaM.run' do
      let declTy := (← getConstInfo decl).type
      let (xs, bis, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
      if xs.size < 1 then
        throwError "@[symm] attribute only applies to lemmas proving x ∼ y → y ∼ x, got {declTy} with two few arguments"
      else
        let finalHyp ← inferType xs[xs.size -1]
        match ← relationAppM? targetTy with
        | some (rel, lhs, rhs) =>
          let flip ←  mkAppM' rel #[rhs, lhs]
          unless (← isDefEq flip finalHyp) do
            throwError "@[symm] attribute only applies to lemmas proving x ∼ y → y ∼ x, got {declTy} with wrong penultimate argument {finalHyp} instead of {flip}"
          let key ← withReducible <| DiscrTree.mkPath lhs
          symmExtension.add (decl, key) kind
        | none =>
          throwError "@[symm] attribute only applies to lemmas proving x ∼ y → y ∼ x, got {declTy}"

initialize registerBuiltinAttribute symmAttribute

def symmLemmas (env : Environment) : DiscrTree Name :=
  symmExtension.getState env

open Lean.Elab.Tactic in
elab "symm" : tactic =>
  withMainContext do
  let tgt ← getMainTarget
  match ← relationAppM? tgt with
  | none =>
    throwError "applyExtLemma only applies to binary relations, not{indentExpr tgt}"
  | some (rel, lhs, rhs) =>
    let s ← saveState
    for lem in ← (symmLemmas (← getEnv)).getMatch lhs do
      try
        liftMetaTactic (apply · (← mkConstWithFreshMVarLevels lem))
        return
      catch e =>
        s.restore
    throwError "no applicable symmetry lemma found for{indentExpr tgt}"
