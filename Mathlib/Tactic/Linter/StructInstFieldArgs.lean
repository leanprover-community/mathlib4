/-
Copyright (c) 2026 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
module

public import Lean.Data.Options

meta import Lean.Meta.Tactic.TryThis
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
## Structure Instance Field Arguments Linter

This linter discourages the pattern `:= fun x ↦ _` in structure instance fields
and suggest moving function binders to the left side of the `:=`.

This increases readability of the code while not changing functionality.

The linter prints a try-this-suggestion with an automated fix.

### Example

```lean4
-- offending
instance : Foo where
  foo_bar := fun x y ↦ x

-- conform
instance : A where
  foo_bar x y := x
```

## Implementation

Not all function arguments are moveable, for example `foo := fun ⟨x, y⟩ ↦ _`
cannot be changed as `foo ⟨x, y⟩ := _` is not valid syntax.

## Future extensions

- In repeated `fun` applications like `foo := fun x ↦ fun y ↦ x`, the linter
  only looks at the first `fun` syntax and thus suggests `foo x := fun y ↦ x`
  on which the linter will trigger again. The suggestion could directly suggest
  the conform version by going recursively into the function body, but for simplicity,
  this has not been implemented so far.
-/

open Lean Elab Linter
open Lean Elab Command Linter Meta Tactic.TryThis

namespace Mathlib.Linter.Style

/-- Helper function to format Syntax the way it is written in source code. -/
meta def srcText (stxs : Array Syntax) : Option String :=
  (mkNullNode stxs).reprint.map (·.trimAscii.copy)

/--
`fun` binders that can be moved before `:=` unchanged.
See the definition of `Lean.Parser.Term.funBinder`.
-/
meta def movableBinder (b : Syntax) : Bool :=
  b.isIdent || b.getKind ∈
    #[``Parser.Term.funStrictImplicitBinder,
      ``Parser.Term.funImplicitBinder,
      ``Parser.Term.instBinder,
      ``Parser.Term.hole,
      ``Parser.Term.typeAscription]

/--
The `structInstFieldArgs` linter flags values of structure instance fields which start with
`fun` and suggests to move the arguments before the `:=`.

Example: `foo a b := _` is preferred over `foo := fun a b ↦ _`.

The linter comes with a try-this-suggestion to automatically apply the fix.
-/
public meta register_option linter.style.structInstFieldArgs : Bool := {
  defValue := false
  descr := "enable the `structInstFieldArgs` linter"
}

@[inherit_doc linter.style.structInstFieldArgs]
meta def structInstFieldArgsLinter : Linter where run := withSetOptionIn fun stx => do
    unless getLinterValue linter.style.structInstFieldArgs (← getLinterOptions) do return
    if (← MonadState.get).messages.hasErrors then return
    for field in stx.topDown do
      -- check that the syntax is an instance field
      -- with at least one `fun` binder which should be moved
      -- to the front.
      if field.getKind != ``Lean.Parser.Term.structInstField then continue
      -- `defPart` contains `:=` and everything after
      let some defPart := field.find? (·.getKind == ``Parser.Term.structInstFieldDef) | continue
      -- `value` is value of the field after `:=`
      let value := defPart[defPart.getNumArgs - 1]
      if value.getKind != ``Parser.Term.fun then continue
      -- `funBody` is one of `basicFun <|> matchAlts`
      let funBody := value[1]
      unless funBody.getKind == ``Parser.Term.basicFun do continue
      let binders := funBody[0].getArgs
      let movableBinders := binders.takeWhile movableBinder
      if movableBinders.isEmpty then continue

      let assignStx := defPart.getArgs.pop -- the `:=`
      let optTypeStx :=  funBody[1] -- optional type annotation like `fun x y : Nat ↦ _`
      let arrowStx :=  funBody[2] -- the arrow `↦` or `=>`

      -- Extract some parts of the original source to make the suggestion
      let some assignTxt := srcText assignStx | continue
      let some movableBinderTxt := srcText movableBinders | continue
      let some optFunTypeTxt := if optTypeStx.isNone then
          some ""
        else
          (srcText #[optTypeStx]).map (" " ++ ·)
        | continue

      let suggestion ← if movableBinders.size == binders.size then
          -- if all binders are moveable, we suggest `foo x y := _`
          pure s!"{movableBinderTxt}{optFunTypeTxt} {assignTxt}"
        else
          -- if there ore non-moveable binders,
          -- we need to keep the `fun` syntax for the unmovable binders,
          -- e.g. `foo x y := fun ⟨a, b⟩ ↦ _`
          let remaining  := binders.extract movableBinders.size binders.size
          let funStx :=  value[0] -- the keyword `fun`
          let some funTxt := srcText #[funStx] | continue
          let some remainingTxt := srcText remaining | continue
          let some arrowTxt := srcText #[arrowStx] | continue
          pure s!"{movableBinderTxt} {assignTxt} {funTxt} {remainingTxt}{optFunTypeTxt} {arrowTxt}"

      let replacementSpan := mkNullNode <| assignStx ++ #[arrowStx]
      let msgSpan := mkNullNode <| movableBinders
      Linter.logLint linter.style.structInstFieldArgs msgSpan m!"Please move function binders \
        before the `:=`. The syntax `foo := fun x y ↦ _` can be written as  `foo x y := _` \
        which increases readability."
      liftTermElabM <| addSuggestion
        msgSpan
        suggestion
        (origSpan? := replacementSpan)
        (header := "Fix:")
        (diffGranularity := .word)

meta initialize addLinter structInstFieldArgsLinter

end Mathlib.Linter.Style
