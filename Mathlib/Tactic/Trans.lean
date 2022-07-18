import Lean
import Mathlib.Tactic.Symm


namespace Mathlib.Tactic.Trans
open Lean Meta Elab
open Mathlib.Tactic.Symm

initialize transExtension : SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    name := `trans
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

def areTransHyps(rel x z xyHyp yzHyp : Expr) : MetaM Bool :=
  try
    let y ← mkFreshExprMVar (some <| ← inferType x)
    let modelPair ← mkAppM ``PProd.mk #[mkAppN rel #[x, y], mkAppN rel #[y, z]]
    let hypPair ← mkAppM ``PProd.mk #[xyHyp, yzHyp]
    isDefEq modelPair hypPair
    -- pure true
  catch _ => pure false

def transAttr : AttributeImpl where
  name := `trans
  descr := "transitive relation"
  add decl stx kind := do
    MetaM.run' do
      let declTy := (← getConstInfo decl).type
      let (xs, bis, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
      if xs.size < 2 then
        throwError "@[trans] attribute only applies to lemmas proving x ∼ y → y ∼ z → z ∼ x, got {declTy} with too few arguments"
      else
        match ← relationAppM? targetTy with
        | some (rel, x, z) =>
          let xyHyp ← inferType xs[xs.size -2]!
          let yzHyp ← inferType xs[xs.size -1]!
          let y ← mkFreshExprMVar (some <| ← inferType x)
          let modelPair ← mkAppM ``PProd.mk #[← mkAppM' rel #[x, y], ← mkAppM' rel #[y, z]]
          let hypPair ← mkAppM ``PProd.mk #[xyHyp, yzHyp]
          unless (← isDefEq hypPair modelPair) do
            throwError "@[trans] attribute only applies to lemmas proving x ∼ y → y ∼ z → z ∼ x, got {declTy}"
          let key ← withReducible <| DiscrTree.mkPath rel
          transExtension.add (decl, key) kind
        | none =>
          throwError "@[trans] attribute only applies to lemmas proving x ∼ y → y ∼ z → z ∼ x, got {declTy}"

initialize registerBuiltinAttribute transAttr

def transLemmas (env : Environment) : DiscrTree Name :=
  transExtension.getState env

def simpleTrans {rel : α → α → Prop}{a b c : α}[Trans rel rel rel] :
    rel a b → rel b c → rel a c  := trans

open Lean.Elab.Tactic
elab "trans" t?:(ppSpace (colGt term))? : tactic => do
match t? with
| none =>
  withMainContext do
  let tgt ← getMainTarget
  match ← relationAppM? tgt with
  | none =>
    throwError "transitivity lemmas only apply to binary relations, not {indentExpr tgt}"
  | some (rel, x, z) =>
    let s ← saveState
    let α ← inferType x
    let lemmas ← (transLemmas (← getEnv)).getUnify rel
    let lemmas := lemmas.push ``simpleTrans
    for lem in lemmas do
      try
        liftMetaTactic (apply · (← mkConstWithFreshMVarLevels lem))
        return
      catch e =>
        s.restore
    throwError "no applicable transitivity lemma found for {indentExpr tgt}"
| some t =>
  withMainContext do
  let tgt ← getMainTarget
  match ← relationAppM? tgt with
  | none =>
    throwError "transitivity lemmas only apply to binary relations, not {indentExpr tgt}"
  | some (rel, x, z) =>
    let s ← saveState
    let y ← elabTerm t none
    let α ← inferType y
    let lemmas ← (transLemmas (← getEnv)).getUnify rel
    let lemmas := lemmas.push ``simpleTrans
    for lem in lemmas do
      try
        -- let f ← mkConstWithFreshMVarLevels lem
        let r1 ←  mkAppM' rel #[x, y]
        let r2 ←  mkAppM' rel #[y, z]
        let l ←
          withLocalDecl `pf1 BinderInfo.default r1 fun pf1 =>
          withLocalDecl `pf2 BinderInfo.default r2 fun pf2 => do
            let pf3 ← mkAppM lem #[pf1, pf2]
            mkLambdaFVars #[pf1, pf2] pf3
        liftMetaTactic (apply · l)
        return
      catch e =>
        s.restore
        logInfo m!"Error in apply : {e.toMessageData}, rel: {rel}, lem: {lem}"
    throwError "no applicable transitivity lemma found for {indentExpr tgt}"
