/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
import Lean.Parser.Command

/-!
# Support for `lemma` as a synonym for `theorem`.
-/

open Lean

/-- `lemma` means the same as `theorem`. It is used to denote "less important" theorems -/
syntax (name := lemma) declModifiers
  group("lemma " declId ppIndent(declSig) declVal) : command

/-- Implementation of the `lemma` command, by macro expansion to `theorem`. -/
@[macro «lemma»] def expandLemma : Macro := fun stx =>
  -- Not using a macro match, to be more resilient against changes to `lemma`.
  -- This implementation ensures that any future changes to `theorem` are reflected in `lemma`
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration
