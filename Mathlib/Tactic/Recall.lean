/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Kyle Miller
-/
import Mathlib.Init
import Lean.Elab.Command
import Lean.Elab.DeclUtil

/-!
# `recall` command
-/

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
-/
syntax (name := recall) "recall " ident ppIndent(optDeclSig) (declVal)? : command

open Lean Meta Elab Command Term

elab_rules : command
  | `(recall $id $sig:optDeclSig $[$val?]?) => withoutModifyingEnv do
    let declName := id.getId
    let some info := (← getEnv).find? declName
      | throwError "unknown constant '{declName}'"
    let declConst : Expr := mkConst declName <| info.levelParams.map Level.param
    discard <| liftTermElabM <| addTermInfo id declConst
    let newId := ({ namePrefix := declName : DeclNameGenerator }.mkUniqueName (← getEnv) `recall).1
    let newId := mkIdentFrom id newId
    if let some val := val? then
      let some infoVal := info.value?
        | throwErrorAt val "constant '{declName}' has no defined value"
      elabCommand <| ← `(noncomputable def $newId $sig:optDeclSig $val)
      let some newInfo := (← getEnv).find? newId.getId | return -- def already threw
      liftTermElabM do
        let mvs ← newInfo.levelParams.mapM fun _ => mkFreshLevelMVar
        let newType := newInfo.type.instantiateLevelParams newInfo.levelParams mvs
        unless (← isDefEq info.type newType) do
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
              unless (← isDefEq info.type type) do
                throwTypeMismatchError none info.type type declConst
      else
        unless binders.getNumArgs == 0 do
          throwError "expected type after ':'"

end Mathlib.Tactic.Recall
