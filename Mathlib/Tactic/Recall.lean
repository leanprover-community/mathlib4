/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Kyle Miller, Mario Carneiro
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
    let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let info ← getConstInfo declName
    let declConst : Expr := mkConst declName <| info.levelParams.map .param
    let newId ← liftCoreM <| mkFreshUserName `_recall
    let val := val?.getD (← `(Parser.Command.declVal| := lcUnreachable))
    elabCommand <| ← `(noncomputable unsafe def $(mkIdent newId) $sig:optDeclSig $val)
    if val?.isNone && sig.raw[1].isNone then return
    let valRef := match val? with
      | some val => if let `(Parser.Command.declVal| := $e) := val then e.raw else val
      | none => id
    let newInfo ← getConstInfoDefn ((← getCurrNamespace) ++ newId)
    liftTermElabM do
    let mvs ← newInfo.levelParams.mapM fun _ => mkFreshLevelMVar
    let newType := newInfo.type.instantiateLevelParams newInfo.levelParams mvs
    unless (← isDefEq info.type newType) do
      withRef (if sig.raw[1].isNone then valRef else sig.raw[1][0][1]) do
        throwTypeMismatchError none info.type newInfo.type declConst
    if val?.isNone then return
    let some infoVal := info.value?
      | throwErrorAt valRef "constant '{declName}' has no defined value"
    let newVal := newInfo.value.instantiateLevelParams newInfo.levelParams mvs
    unless (← isDefEq infoVal newVal) do
      let err := m!"\
        value mismatch{indentExpr declConst}\nhas value{indentExpr newVal}\n\
        but is expected to have value{indentExpr infoVal}"
      throwErrorAt valRef err

end Mathlib.Tactic.Recall
