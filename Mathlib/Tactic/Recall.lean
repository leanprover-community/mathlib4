/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Kyle Miller
-/
import Lean.Elab.MutualDef
import Std.Tactic.OpenPrivate

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
open private elabHeaders from Lean.Elab.MutualDef

elab_rules : command
  | `(recall $id $sig:optDeclSig $[$val?]?) => withoutModifyingEnv do
    let some info := (← getEnv).find? id.getId
      | throwError "unknown constant '{id}'"
    runTermElabM fun _ => discard <| addTermInfo id (mkConst id.getId)
    let id' := mkIdentFrom id (← mkAuxName id.getId 1)
    if let some val := val? then
      let some infoVal := info.value?
        | throwErrorAt val "constant '{id}' has no defined value"
      elabCommand <| ← `(noncomputable def $id':declId $sig:optDeclSig $val)
      let some newInfo := (← getEnv).find? id'.getId | return -- def already threw
      runTermElabM fun _ => do
        let mvs ← newInfo.levelParams.mapM fun _ => mkFreshLevelMVar
        let newType := newInfo.type.instantiateLevelParams newInfo.levelParams mvs
        unless (← isDefEq info.type newType) do
          throwTypeMismatchError none info.type newInfo.type (mkConst id.getId)
        let newVal := newInfo.value?.get!.instantiateLevelParams newInfo.levelParams mvs
        unless (← isDefEq infoVal newVal) do
          let err :=
            m!"value mismatch{indentD id.getId}\nhas value{indentExpr newVal}\n" ++
            m!"but is expected to have value{indentExpr infoVal}"
          throwErrorAt val err
    else
      let (binders, type?) := expandOptDeclSig sig
      let views := #[{
        declId := id', binders, type?, value := .missing,
        ref := ← getRef, kind := default, modifiers := {}
      : DefView}]
      runTermElabM fun _ => do
        let elabView := (← elabHeaders views)[0]!
        unless (← isDefEq info.type elabView.type) do
          throwTypeMismatchError none info.type elabView.type (mkConst id.getId)
