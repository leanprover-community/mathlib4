/-
Copyright (c) 2024 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean

/-! # Attribute `syntax_rules_header` for implementations using `syntax_rules`

TODO: more docs
-/

open Lean Meta Elab Parser Command Term Syntax

section data

/-- This data is inferred from the specific `syntaxRuleHeader` command using the
`syntax_rules_header` attribute and used to guide elaboration.

TODO: docstring -/
structure SyntaxRuleData where
  /-- e.g. `Lean.Elab.Tactic`; the name of the type of the declaration. -/
  type : Name
  /-- e.g. ``fun alts => `(term|fun alts:matchAlts*)``. The result (e.g. `fun alts:matchAlts*`, in
  this case) is elaborated with type `type`. -/
  termOfAlts : Array (TSyntax ``Term.matchAlt) → CommandElabM Term
  /-- e.g. `term_elab`, used as `@[term_elab k]` -/
  attrName : Name
  /- FIXME:? Sometimes you need to key by extra information, which currently can only be done by
  creating a corresponding name. E.g. to key by a pair of a category and syntax nodekind, one might
  use `some (fun n => return category ++ n)`. This is a little better than creating a whole new
  attribute for each category. -/
  /- TODO:? is this the best type signature? Using `Ident` lets us manage refs via e.g.
  `mkIdentFrom` but might be awkward. -/
  /-- If not `none`, transform the `SyntaxNodeKind` into some arbitrary `Ident` before using it as
  a key for `attrName`. -/
  mkKey : Option (Name → CommandElabM Ident) := none
  /-- e.g. "elab_rules"; used for error messages. -/
  cmdName : String
  /-- e.g. `elabRules`; just helps keep things legible if you look at internals, no real effect. -/
  auxDefName : Name

end data

section attr

--TODO: should `Syntax` be `TSyntax`?
/-- An abbreviation for `Syntax → CommandElabM SyntaxRuleData`. The input is the syntax of the
header of a `syntax_rules`-based command (e.g. the syntax `linting_rules : deprecation`), and the
output is the data necessary for implementing it in terms of `syntax_rules`. -/
abbrev ToSyntaxRuleData := Syntax → CommandElabM SyntaxRuleData

-- TODO: this is not an elaborator, so the message constructed by `mkElabAttribute` using
-- `"syntax rules header data"` is not quite right
/-- An attribute for implementing `syntax_rules` headers. TODO: better docs -/
initialize syntaxRulesHeaderAttr : KeyedDeclsAttribute ToSyntaxRuleData ← unsafe
  (mkElabAttribute ToSyntaxRuleData .anonymous `syntax_rules_header .anonymous ``ToSyntaxRuleData
    "syntax rules header data")

--TODO:? Should we cargo cult this from `expandNoKindMacroRulesAux`? Or not? No...
/-
if k.isStr && k.getString! == "antiquot" then
    k := k.getPrefix
-/

/-- Aux definition for `getSyntaxRuleData` -/
private def getSyntaxRuleDataAux (s : Command.State) (ref : Syntax) :
    List (KeyedDeclsAttribute.AttributeEntry ToSyntaxRuleData) → CommandElabM SyntaxRuleData
  | [] => throwError "No @[syntax_rules_header] attribute found for{indentD ref}"
  | (toSyntaxRuleData::toSyntaxRuleDatas) =>
    catchInternalId unsupportedSyntaxExceptionId
      (toSyntaxRuleData.value ref)
      (fun _ => do set s; getSyntaxRuleDataAux s ref toSyntaxRuleDatas)

/-- Get the first `SyntaxRuleData` from declarations registered with `@[syntax_rule_header k]`-/
def getSyntaxRuleData (header : Syntax) : CommandElabM SyntaxRuleData := do
  let headerKind := header.getKind
  if headerKind == choiceKind then
    --TODO: handle choices by using `forM`? do we ever need to do that?
    throwError "ambiguous syntax node kind {headerKind} for{indentD header}"
  let vals := syntaxRulesHeaderAttr.getEntries (← getEnv) headerKind
  getSyntaxRuleDataAux (← get) header vals

end attr
