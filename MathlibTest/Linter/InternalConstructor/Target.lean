module

public import Mathlib.Init
import MathlibTest.Linter.InternalConstructor.Source

open Lean Meta Elab Command
elab "test" cmd:command : command => do
  if ! (← getInfoState).enabled then
    logError "Info trees are disabled, can not use `#info_trees`."
  else
    elabCommand cmd
    let infoTrees := (← getInfoState).substituteLazy.get.trees
    for t in infoTrees do
      t.foldInfoM (init := ()) fun ctx info _ ↦ do
        let .ofTermInfo i := info | return
        logInfo m!"{i.elaborator}; {i.expr}"

/--
@ +1:16...19
error: `Foo._mkInternal` is an internal constructor and should not be used directly.

Note: This linter can be disabled with `set_option linter.internalConstructors false`
-/
#guard_msgs (positions := true) in
def e₁ : Foo := ⟨4⟩

/--
@ +1:16...31
error: `Foo._mkInternal` is an internal constructor and should not be used directly.

Note: This linter can be disabled with `set_option linter.internalConstructors false`
-/
#guard_msgs (positions := true) in
def e₂ : Foo := Foo._mkInternal 4
