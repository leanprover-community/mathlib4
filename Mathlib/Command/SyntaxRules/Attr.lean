/-
Copyright (c) 2024 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean

/-! # Attribute `syntax_rules_header_impl` for implementations using `syntax_rules`

TODO: more docs
-/

open Lean Meta Elab Parser Command Term Syntax

section data

/-- This data is inferred from the specific `syntaxRulesHeader` command using the
`syntax_rules_header_impl` attribute and used to guide elaboration.

TODO: docstring -/
structure SyntaxRulesData where
  /-- e.g. `Lean.Elab.Tactic`; the name of the type of the declaration. -/
  type : Name
  /-- e.g. ``fun alts => `(term|fun alts:matchAlts*)``. The result (e.g. `fun alts:matchAlts*`, in
  this case) is elaborated with type `type`. -/
  termOfAlts : Array (TSyntax ``Term.matchAlt) → CommandElabM Term
  /-- e.g. `term_elab`, used as `@[term_elab k]` -/
  attrName : Name
  /-- If `none`, simply use `@[attrName k]` as the attribute on the declaration, where `k` is  the
  `SyntaxNodeKind` of the matched-against syntax. If not `none`, use `← mkAttr attrName k` as the
  attribute syntax. This allows greater control over the parameters passed to the attribute if
  necessary. -/
  mkAttr : Option ((attr node : Name) → CommandElabM (TSyntax `attr)) := none
  /-- e.g. `` `(term|throwUnsupportedSyntax) ``. This will be the value for the universal fallback
  (`_`) branch, and will be wrapped in `no_error_if_unused%`. Note that `throwUnsupportedSyntax` is
  valid in any monad `m` with an instance of `MonadExceptOf Exception m`. -/
  fallbackTerm : CommandElabM Term
  /-- e.g. "elab_rules"; used for error messages. -/
  cmdName : String
  /-- e.g. `elabRules`; just helps keep things legible if you look at internals, no real effect. -/
  auxDefName : Name
  /-- Whether to unfold `type` if it's an `abbrev`. Usually this will be `true`. -/
  unfoldTypeAbbrev := true

--TODO: should `Syntax` be `TSyntax`?
/-- An abbreviation for `Syntax → CommandElabM SyntaxRulesData`. The input is the syntax of the
header of a `syntax_rules`-based command (e.g. the syntax `linting_rules : deprecation`), and the
output is the data necessary for implementing it in terms of `syntax_rules`. -/
abbrev ToSyntaxRulesData := Syntax → CommandElabM SyntaxRulesData

end data

section attr

-- TODO: this is not an elaborator, so the message constructed by `mkElabAttribute` using
-- `"syntax rules header data"` is not quite right
/-- An attribute for implementing `syntax_rules` headers. TODO: better docs -/
initialize syntaxRulesHeaderAttr : KeyedDeclsAttribute ToSyntaxRulesData ← unsafe
  (mkElabAttribute ToSyntaxRulesData .anonymous `syntax_rules_header_impl .anonymous
    ``ToSyntaxRulesData "syntax rules header data")

--TODO:? Should we cargo cult this from `expandNoKindMacroRulesAux`? Or not? No...
/-
if k.isStr && k.getString! == "antiquot" then
    k := k.getPrefix
-/

/-- Aux definition for `getSyntaxRulesData` -/
private def getSyntaxRulesDataAux (s : Command.State) (ref : Syntax) :
    List (KeyedDeclsAttribute.AttributeEntry ToSyntaxRulesData) → CommandElabM SyntaxRulesData
  | [] => throwError "No @[syntax_rules_header_impl] attribute found for{indentD ref}"
  | (toSyntaxRulesData::toSyntaxRulesDatas) =>
    catchInternalId unsupportedSyntaxExceptionId
      (toSyntaxRulesData.value ref)
      (fun _ => do set s; getSyntaxRulesDataAux s ref toSyntaxRulesDatas)

/-- Get the first `SyntaxRulesData` from declarations registered with `@[syntax_rules_header k]`-/
def getSyntaxRulesData (header : Syntax) : CommandElabM SyntaxRulesData := do
  let headerKind := header.getKind
  if headerKind == choiceKind then
    --TODO: handle choices by using `forM`? do we ever need to do that?
    throwError "ambiguous syntax node kind {headerKind} for{indentD header}"
  let vals := syntaxRulesHeaderAttr.getEntries (← getEnv) headerKind
  getSyntaxRulesDataAux (← get) header vals

end attr
