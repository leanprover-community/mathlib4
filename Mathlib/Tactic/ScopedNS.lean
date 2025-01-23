/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
import Mathlib.Util.WithWeakNamespace

/-! # `scoped[NS]` syntax

This is a replacement for the `localized` command in mathlib. It is similar to `scoped`,
but it scopes the syntax in the specified namespace instead of the current namespace.
-/

namespace Mathlib.Tactic
open Lean

/--
`scoped[NS]` is similar to the `scoped` modifier on attributes and notations,
but it scopes the syntax in the specified namespace instead of the current namespace.
```
scoped[Matrix] postfix:1024 "ᵀ" => Matrix.transpose
-- declares `ᵀ` as a notation for matrix transposition
-- which is only accessible if you `open Matrix` or `open scoped Matrix`.

namespace Nat

scoped[Nat.Count] attribute [instance] CountSet.fintype
-- make the definition Nat.CountSet.fintype an instance,
-- but only if `Nat.Count` is open
```
-/
syntax (name := scopedNS) (docComment)? (Parser.Term.attributes)?
  "scoped" "[" ident "] " command : command
macro_rules
  | `(scoped[$ns] attribute [$[$attr:attr],*] $ids*) =>
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      attribute [$[scoped $attr:attr],*] $ids*)
  | `($[$doc]? $(attr)? scoped%$tk[$ns] $cmd) => do
    let attrKindArg ← match cmd.raw.getKind with
      | ``Parser.Command.notation
      | ``Parser.Command.macro_rules
      | ``Parser.Command.syntax
      | ``Parser.Command.macro
      | ``Parser.Command.elab_rules
      | ``Parser.Command.elab
      | ``Parser.Command.binderPredicate
      | ``Parser.Command.mixfix => pure 2
      | _ => Macro.throwErrorAt tk "can't use scoped[NS] on this kind of command"
    let `(Parser.Term.attrKind|) := cmd.raw[attrKindArg]
      | Macro.throwErrorAt cmd.raw[attrKindArg] "This scoping directive conflicts with scoped[NS]"
    let cmd' := ⟨cmd.raw.setArg attrKindArg <| Unhygienic.run `(Parser.Term.attrKind| scoped)⟩
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId) $cmd':command)

end Mathlib.Tactic
