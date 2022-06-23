/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import Lean
import Mathlib.Tactic.Cache
import Mathlib.Tactic.RCases

open Tactic

namespace Mathlib.Tactic.Ext
open Lean Meta

def withExtHyps (struct : Name) (k : Array Expr → (x y : Expr) → Array (Name × Expr) → MetaM α) : MetaM α := do
  unless isStructure (← getEnv) struct do throwError "not a structure: {struct}"
  let structC ← mkConstWithLevelParams struct
  forallTelescope (← inferType structC) fun params _ => do
  withNewBinderInfos (params.map (·.fvarId!, BinderInfo.implicit)) do
  withLocalDeclD `x (mkAppN structC params) fun x => do
  withLocalDeclD `y (mkAppN structC params) fun y => do
    let mut hyps := #[]
    for field in getStructureFieldsFlattened (← getEnv) struct (includeSubobjectFields := false) do
      let x_f ← mkProjection x field
      let y_f ← mkProjection y field
      if ← isProof x_f then
        pure ()
      else if ← isDefEq (← inferType x_f) (← inferType y_f) then
        hyps := hyps.push (field, ← mkEq x_f y_f)
      else
        hyps := hyps.push (field, ← mkHEq x_f y_f)
    k params x y hyps

scoped elab "ext_type%" struct:ident : term => do
  withExtHyps (← resolveGlobalConstNoOverload struct) fun params x y hyps => do
    let mut ty ← mkEq x y
    for (f, h) in hyps.reverse do
      ty := mkForall f BinderInfo.default h ty
    mkForallFVars (params |>.push x |>.push y) ty

def mkIff (p q : Expr) : Expr := mkApp2 (mkConst ``Iff) p q

def mkAndN : List Expr → Expr
  | [] => mkConst ``True
  | [p] => p
  | [p, q] => mkAnd p q
  | p :: ps => mkAnd p (mkAndN ps)

scoped elab "ext_iff_type%" struct:ident : term => do
  withExtHyps (← resolveGlobalConstNoOverload struct) fun params x y hyps => do
    mkForallFVars (params |>.push x |>.push y) <|
      mkIff (← mkEq x y) <| mkAndN (hyps.map (·.2)).toList

elab "subst_eqs" : tactic =>
  open Elab.Tactic in
  liftMetaTactic1 fun mvarId => substEqs mvarId

scoped macro "ext_proof%" : term =>
  `(fun {..} {..} => by intros; subst_eqs; rfl)

syntax "split_ands" : tactic
macro_rules | `(tactic| split_ands) => `(tactic| skip)
macro_rules | `(tactic| split_ands) => `(tactic| refine And.intro ?_ ?_ <;> split_ands)

macro_rules | `(tactic| rfl) => `(tactic| exact HEq.rfl)

scoped macro "ext_iff_proof%" : term => `(fun {..} {..} =>
  ⟨fun _ => by subst_eqs; split_ands <;> rfl,
   fun _ => by (repeat cases ‹_ ∧ _›); subst_eqs; rfl⟩)

scoped macro "declareExtTheoremsFor" struct:ident : command => do
  let extName := mkIdent <| struct.getId.eraseMacroScopes.mkStr "ext"
  let extIffName := mkIdent <| struct.getId.eraseMacroScopes.mkStr "ext_iff"
  `(@[ext] protected theorem $extName:ident : ext_type% $struct:ident := ext_proof%
    protected theorem $extIffName:ident : ext_iff_type% $struct:ident := ext_iff_proof%)

open Elab.Command MonadRecDepth in
def liftCommandElabM (k : CommandElabM α) : AttrM α := do
  let (a, commandState) ←
    k.run {
      fileName := (← getEnv).mainModule.toString,
      fileMap := default,
      tacticCache? := none,
    } |>.run {
      env := ← getEnv,
      maxRecDepth := ← getMaxRecDepth,
      scopes := [{ header := "", opts := ← getOptions }]
    }
  modify fun coreState => { coreState with
    traceState.traces := coreState.traceState.traces ++ commandState.traceState.traces
    env := commandState.env
  }
  if let some err := commandState.messages.msgs.toArray.find?
      (·.severity matches MessageSeverity.error) then
    throwError err.data
  pure a

initialize extExtension : SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    name := `ext
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

def extAttribute : AttributeImpl where
  name := `ext
  descr := "Marks a lemma as extensionality lemma"
  add decl _stx kind := do
    if isStructure (← getEnv) decl then
      liftCommandElabM do
        Elab.Command.elabCommand <|<- `(declareExtTheoremsFor $(mkIdent decl))
    else MetaM.run' do
      let declTy := (← getConstInfo decl).type
      let (_, _, declTy) ← withReducible <| forallMetaTelescopeReducing declTy
      if declTy.isAppOfArity ``Eq 3 && (declTy.getArg! 1).isMVar && (declTy.getArg! 2).isMVar then
        let ty := declTy.getArg! 0
        let key ←
          if (← withReducible <| whnf ty).isForall then
            pure #[DiscrTree.Key.star] -- FIXME: workaround
          else
            withReducible <| DiscrTree.mkPath ty
        extExtension.add (decl, key) kind
      else
        throwError "@[ext] attribute only applies to structures or lemmas proving x = y, got {declTy}"

initialize registerBuiltinAttribute extAttribute

def extLemmas (env : Environment) : DiscrTree Name :=
  extExtension.getState env

open Lean.Elab.Tactic in
elab "apply_ext_lemma" : tactic => do
  let tgt ← getMainTarget
  unless tgt.isAppOfArity ``Eq 3 do
    throwError "applyExtLemma only applies to equations, not{indentExpr tgt}"
  let ty := tgt.getArg! 0
  let s ← saveState
  for lem in ← (extLemmas (← getEnv)).getMatch ty do
    try
      liftMetaTactic (apply · (← mkConstWithFreshMVarLevels lem))
      return
    catch _ => s.restore
  throwError "no applicable extensionality lemma found for{indentExpr ty}"

scoped syntax "ext_or_skip" (ppSpace rintroPat)* : tactic
macro_rules | `(tactic| ext_or_skip) => `(tactic| skip)
macro_rules
| `(tactic| ext_or_skip $xs:rintroPat*) =>
  `(tactic| apply_ext_lemma; ext_or_skip $xs:rintroPat*)
macro_rules
| `(tactic| ext_or_skip $x:rintroPat $xs:rintroPat*) =>
  `(tactic| rintro $x:rintroPat; ext_or_skip $xs:rintroPat*)

-- TODO: support `ext : n`

syntax "ext" (colGt ppSpace rintroPat)* (" : " num)? : tactic
macro_rules
| `(tactic| ext) => do
  `(tactic| first | intro; ext | apply_ext_lemma; ext | skip)
macro_rules
| `(tactic| ext $xs:rintroPat*) =>
  `(tactic| apply_ext_lemma; ext_or_skip $xs:rintroPat*)

syntax "ext1" (colGt ppSpace rintroPat)* : tactic
macro_rules
| `(tactic| ext1 $xs:rintroPat*) =>
  `(tactic| apply_ext_lemma; rintro $xs:rintroPat*)

-- TODO
syntax "ext1?" (colGt ppSpace rintroPat)* : tactic
syntax "ext?" (colGt ppSpace rintroPat)* (" : " num)? : tactic
