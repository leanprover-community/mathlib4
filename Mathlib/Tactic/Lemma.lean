import Lean.Parser.Command

open Lean

/-- `lemma` means the same as `theorem`. It is used to denote "less important" theorems -/
syntax (name := lemma) declModifiers
  group("lemma " declId ppIndent(declSig) declVal Parser.Command.terminationSuffix) : command

/-- Implementation of the `lemma` command, by macro expansion to `theorem`. -/
@[macro «lemma»] def expandLemma : Macro := fun stx =>
  -- FIXME: this should be a macro match, but terminationSuffix is not easy to bind correctly.
  -- This implementation ensures that any future changes to `theorem` are reflected in `lemma`
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration
