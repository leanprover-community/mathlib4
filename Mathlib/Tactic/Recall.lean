/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Kyle Miller
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Command
public meta import Lean.Elab.DeclUtil
public meta import Lean.Meta.Tactic.TryThis
public meta import Lean.PrettyPrinter.Delaborator

/-!
# `recall` command
-/
set_option backward.defeqAttrib.useBackward true

public meta section

namespace Mathlib.Tactic.Recall

/--
The `recall` command redeclares a previous definition for illustrative purposes.
This can be useful for files that give an expository account of some theory in Lean.

The syntax of the command mirrors `def`, so all the usual bells and whistles work.
```
recall List.cons_append (a : α) (as bs : List α) : (a :: as) ++ bs = a :: (as ++ bs) := rfl
```
Also, one can leave out the body.
```
recall Nat.add_comm (n m : Nat) : n + m = m + n
```

The command verifies that the new definition type-checks and that the type and value
provided are definitionally equal to the original declaration. However, this does not
capture some details (like binders), so the following works without error.
```
recall Nat.add_comm {n m : Nat} : n + m = m + n
```

Docstrings are permitted but are ignored:
```
/-- The additive commutativity of natural numbers. -/
recall Nat.add_comm (n m : Nat) : n + m = m + n
```
-/
syntax (name := recall) (docComment)? "recall " ident ppIndent(optDeclSig) (declVal)? : command

/--
The `recall?` command looks up a previous definition and suggests the correct
`recall` statement for it.
```
recall? Nat.add_comm
-- Try this: recall Nat.add_comm (n m : Nat) : n + m = m + n
```
-/
syntax (name := recall?) "recall? " ident : command

open Lean Meta Elab Command Term

/-- Format a `recall` suggestion string for the given constant name.
Uses `delabConstWithSignature` with `universes := false` to produce the idiomatic
decomposed binder form without universe parameters on the name. -/
private def mkRecallSuggestion (declName : Name) : MetaM String := do
  let decl ← getConstInfo declName
  let e := Expr.const declName (decl.levelParams.map Level.param)
  let (stx, _) ← PrettyPrinter.delabCore e
    (delab := PrettyPrinter.Delaborator.delabConstWithSignature (universes := false))
  let sig := toString (← PrettyPrinter.ppTerm ⟨stx⟩)
  return s!"recall {sig}"

elab_rules : command
  | `(recall?%$tk $id) => withoutModifyingEnv do
    let declName := id.getId
    addConstInfo id declName
    let _ ← getConstInfo declName
    let suggestion ← liftTermElabM <| mkRecallSuggestion declName
    liftTermElabM <|
      Tactic.TryThis.addSuggestion tk (suggestion : String) (origSpan? := ← getRef)

elab_rules : command
  | `($[$_doc?:docComment]? recall $id $sig:optDeclSig $[$val?]?) =>
    -- `recall` doesn't introduce new definitions, so suppress the unused variable linter.
    withScope (fun sc => { sc with opts := sc.opts.set `linter.unusedVariables false }) <|
    withoutModifyingEnv do
    let declName ← resolveGlobalConstNoOverload id
    addConstInfo id declName
    let info ← getConstInfo declName
    let declConst : Expr := mkConst declName <| info.levelParams.map Level.param
    let stxRef ← getRef
    let recallName := Name.mkSimple
      s!"_recall_{(← liftTermElabM Lean.mkFreshId)}"
    let newId := mkIdentFrom id recallName
    if let some val := val? then
      let some infoVal := info.value? (allowOpaque := true)
        | throwErrorAt val "constant '{declName}' has no defined value"
      elabCommand <| ← `(noncomputable def $newId $sig:optDeclSig $val)
      let ns ← getCurrNamespace
      let some newInfo := (← getEnv).find? (ns ++ recallName)
        | return -- def already threw
      liftTermElabM do
        let mvs ← newInfo.levelParams.mapM fun _ => mkFreshLevelMVar
        let newType := newInfo.type.instantiateLevelParams newInfo.levelParams mvs
        unless (← isDefEq info.type newType) do
          let suggestion ← mkRecallSuggestion declName
          Tactic.TryThis.addSuggestion stxRef (suggestion : String) (origSpan? := stxRef)
          throwTypeMismatchError none info.type newInfo.type declConst
        let newVal := newInfo.value?.get!.instantiateLevelParams newInfo.levelParams mvs
        unless (← isDefEq infoVal newVal) do
          let err := m!"\
            value mismatch{indentExpr declConst}\nhas value{indentExpr newVal}\n\
            but is expected to have value{indentExpr infoVal}"
          throwErrorAt val err
    else
      let (binders, type?) := expandOptDeclSig sig
      if let some type := type? then
        runTermElabM fun vars => do
          withAutoBoundImplicit do
            elabBinders binders.getArgs fun xs => do
              let xs ← addAutoBoundImplicits xs none
              let type ← elabType type
              Term.synthesizeSyntheticMVarsNoPostponing
              let type ← mkForallFVars xs type
              let type ← mkForallFVars vars type (usedOnly := true)
              let infoType ← do
                let mvs ← info.levelParams.mapM fun _ => mkFreshLevelMVar
                pure <| info.type.instantiateLevelParams info.levelParams mvs
              unless (← isDefEq infoType type) do
                let suggestion ← mkRecallSuggestion declName
                Tactic.TryThis.addSuggestion stxRef (suggestion : String) (origSpan? := stxRef)
                throwTypeMismatchError none info.type type declConst
      else
        unless binders.getNumArgs == 0 do
          throwError "expected type after ':'"

end Mathlib.Tactic.Recall
