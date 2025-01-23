/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro, Jon Eugster
-/
import Mathlib.Util.WithWeakNamespace

/-! # `scoped[NS]` syntax

This command is similar to `scoped`,
but it scopes the syntax in the specified namespace instead of the current namespace.
-/

namespace Mathlib.Tactic

open Lean

/--
`scoped[NS]` is similar to the `scoped` modifier on attributes, notations, macros and
other commands but it scopes the syntax in the specified namespace instead of the
current namespace.

Examples:

```
scoped[Matrix] postfix:1024 "ᵀ" => Matrix.transpose
```

declares `ᵀ` as a notation for matrix transposition
which is only accessible if you `open Matrix` or `open scoped Matrix`.

```
namespace Nat

scoped[Nat.Count] attribute [instance] CountSet.fintype
```

make the definition `Nat.CountSet.fintype` an instance,
but only if `Nat.Count` is open
-/
syntax (name := scopedNS) (docComment)? (Parser.Term.attributes)?
  "scoped" "[" ident "] " command : command
macro_rules
  | `(scoped[$ns] attribute [$[$attr:attr],*] $ids*) =>
    /- implementation for `Parser.Command.attribute` -/
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      attribute [$[scoped $attr:attr],*] $ids*)
  | `($[$docComment]? $(attributes)? scoped%$tk[$ns] $cmd) => do
    /-
    implementation for most common commands.

    These commands usually have few optional arguments at the beginning:

    - `optional docComment`: the doc-string
    - `optional Term.«attributes»`: e.g. `@[simp]`
    - `Term.attrKind`: is `scoped` or `local`

    We parse the command without these, then add `scoped` manually to control the namespace
    and add the other optional arguments back.
    -/
    let (docCommentPos, attributesPos, attrKindPos) ← match cmd.raw.getKind with
      | ``Parser.Command.notation
      | ``Parser.Command.macro_rules
      | ``Parser.Command.syntax
      | ``Parser.Command.macro
      | ``Parser.Command.elab_rules
      | ``Parser.Command.elab
      | ``Parser.Command.binderPredicate
      | ``Parser.Command.mixfix => pure (0, 1, 2)
      | _ => Macro.throwErrorAt tk "scoped[NS] is not implemented for this command!"

    -- parser `optional _` expects a `nullKind` node which
    -- has no children (case `none`) or one child (case `some _`)
    let docCommentNode : Syntax := match docComment with
      | none => Lean.mkNullNode
      | some doc => Lean.mkNullNode #[doc]
    let attributesNode : Syntax := match attributes with
      | none => Lean.mkNullNode
      | some attr => Lean.mkNullNode #[attr]

    -- assert the parsed sub-command does not have any of these optional arguments filled
    -- (e.g. to avoid `scoped[Test] /-- bad -/ local macro ...` from parsing)
    match cmd.raw[docCommentPos] with
    | Syntax.node .none `null #[] => pure ()
    | _ => Macro.throwErrorAt cmd.raw[docCommentPos]
            s!"unexpected docstring, move it in front of `scoped[NS]`!"
    match cmd.raw[attributesPos] with
    | Syntax.node .none `null #[] => pure ()
    | _ => Macro.throwErrorAt cmd.raw[docCommentPos]
            s!"unexpected attributes, move them in front of `scoped[NS]`!"
    let `(Parser.Term.attrKind|) := cmd.raw[attrKindPos]
      | Macro.throwErrorAt cmd.raw[attrKindPos] "This scoping directive conflicts with scoped[NS]"

    -- set the `attrKind` to `scoped`
    -- TODO: why did Mario have `Unhygienic.run` here?
    let attrKindNode ← `(Parser.Term.attrKind| scoped)

    -- insert the optional arguments and `scoped` into the command.
    let cmdNew : TSyntax `command := ⟨cmd.raw
      |>.setArg docCommentPos docCommentNode
      |>.setArg attributesPos attributesNode
      |>.setArg attrKindPos attrKindNode⟩

    -- wrap the generated command in `with_weak_namespace` to control the namespace
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId) $cmdNew)

end Mathlib.Tactic
