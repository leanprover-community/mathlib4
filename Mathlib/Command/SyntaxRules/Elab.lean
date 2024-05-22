/-
Copyright (c) 2024 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean
import Mathlib.Command.SyntaxRules.Attr

/-! # Elaborate `syntax_rules_impl`

TODO: module doc
-/

open Lean Meta Elab
open Lean.Parser hiding mkIdent
open Command Term Syntax

section stx

/-- TODO: docstring -/
declare_syntax_cat syntaxRulesHeader

--FIXME: we need this since `matchAlts` has on optional argument, which makes it unusable in `stx`
private def matchAltsStx := Parser.Term.matchAlts

/-- TODO: docstring -/
syntax (name := syntaxRules) (docComment)? (Parser.Term.«attributes»)? Parser.Term.attrKind
  "syntax_rules_impl" " (" &"header" ":=" syntaxRulesHeader ")" optKind matchAltsStx : command

/-- TODO: docstring? -/
syntax (name := genericSyntaxRules) syntaxRulesHeader optKind matchAltsStx : command

/- TODO: explain -/
macro_rules
| `(genericSyntaxRules|$header:syntaxRulesHeader $[(kind := $k:ident)]? $alts:matchAlts) =>
  `(syntaxRules|syntax_rules_impl (header := $header:syntaxRulesHeader) $[(kind := $k:ident)]?
    $alts:matchAlts)

end stx

section elaborate

--TODO: scoped?
/-- Unfolds exactly one abbrevation. Does nothing if the elaborated term is not an `abbrev`. -/
syntax (name := unfoldAbbrev1) "unfold_abbrev1%" term : term

/-- Elaborator for `unfold_abbrev1% term`. -/
@[term_elab unfoldAbbrev1]
def elabUnfoldAbbrev : TermElab
  | stx, type? => do
    let t ← elabTerm stx[1] type?
    let some (name, _) := t.const? | return t
    let .defnInfo { hints := .abbrev , value .. } ← getConstInfo name | return t
    return value

/-- The main part of elaborating `syntax_rules_impl`. -/
def elabSyntaxRulesAux (doc? : Option (TSyntax ``docComment))
    (attrs? : Option (TSepArray ``attrInstance ",")) (attrKind : TSyntax ``attrKind)
    (k : SyntaxNodeKind) (alts : Array (TSyntax ``matchAlt)) :
    SyntaxRulesData → CommandElabM Syntax
  | { type, termOfAlts, attrName, mkAttr, cmdName, auxDefName, unfoldTypeAbbrev } => do
    let alts ← alts.mapM fun (alt : TSyntax ``matchAlt) => match alt with
      | `(matchAltExpr| | $pats,* => $rhs) => do
        let pat := pats.elemsAndSeps[0]!
        if !pat.isQuot then
          throwUnsupportedSyntax
        let quoted := getQuotContent pat
        let k' := quoted.getKind
        if checkRuleKind k' k then
          pure alt
        else if k' == choiceKind then
          match quoted.getArgs.find? fun quotAlt => checkRuleKind quotAlt.getKind k with
          | none        => throwErrorAt alt
            "invalid {cmdName} alternative, expected syntax node kind '{k}'"
          | some quoted =>
            let pat := pat.setArg 1 quoted
            let pats := ⟨pats.elemsAndSeps.set! 0 pat⟩
            `(matchAltExpr| | $pats,* => $rhs)
        else
          throwErrorAt alt
            "invalid {cmdName} alternative, unexpected syntax node kind '{k'}'"
      | _ => throwUnsupportedSyntax
    let alts := alts.push (← `(matchAltExpr| | _ => no_error_if_unused% throwUnsupportedSyntax))
    let attrs : (TSyntaxArray ``attrInstance) ← do
      let attr ← if let some mkAttr := mkAttr then
          `(attrInstance| $attrKind:attrKind $(← mkAttr attrName k):attr)
        else
          `(attrInstance| $attrKind:attrKind $(mkIdent attrName):ident $(← mkIdentFromRef k))
      trace[syntaxRules] "using attribute {attr}"
      pure <| match attrs? with
        | some attrs => attrs.getElems.push attr
        | none => #[attr]
    -- We still want the actual type to be `type`, so that the attribute doesn't get confused.
    if unfoldTypeAbbrev then
      `($[$doc?:docComment]? @[$attrs,*]
        aux_def $(mkIdent auxDefName) $(mkIdent k) : $(mkIdent type) :=
          show unfold_abbrev1% $(mkIdent type) from $(← termOfAlts alts))
    else
      `($[$doc?:docComment]? @[$attrs,*]
        aux_def $(mkIdent auxDefName) $(mkIdent k) : $(mkIdent type) := $(← termOfAlts alts))

--TODO: pass `tk` to elabSyntaxRules for error reporting?
/-- Elaborates `syntax_rules_impl`. -/
@[command_elab syntaxRules]
def elabSyntaxRules : CommandElab :=
  adaptExpander fun stx => match stx with
  | `(command|$[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
      syntax_rules_impl (header := $header:syntaxRulesHeader) $alts:matchAlt*) =>
    expandNoKindMacroRulesAux alts "syntax_rules_impl" fun kind? alts =>
      `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
        syntax_rules_impl (header := $header:syntaxRulesHeader) $[(kind := $(mkIdent <$> kind?))]?
        $alts:matchAlt*)
  | `(command|$[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind syntax_rules_impl
      (header := $header:syntaxRulesHeader)
      (kind := $kind) $alts:matchAlt*) => do
    let data ← getSyntaxRulesData header
    elabSyntaxRulesAux doc? attrs? attrKind (← resolveSyntaxKind kind.getId) alts data
  | _  => throwUnsupportedSyntax

end elaborate

initialize registerTraceClass `syntaxRules
