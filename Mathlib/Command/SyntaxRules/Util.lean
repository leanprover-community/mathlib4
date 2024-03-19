/-
Copyright (c) 2024 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean

/-!
# Utilities for commands based on `syntax_rules`

TODO: better docs throughout
-/

open Lean Meta Elab

/-! # Syntax nodes -/

/-- Resolves `k` to a `SyntaxNodeKind`. Like `Elab.syntaxNodeKindOfAttrParam`, but takes in a
`Name` argument instead of the whole `attr` syntax. -/
def SyntaxRules.syntaxNodeKindOfAttrParam (defaultParserNamespace : Name) (k : Name) :
    AttrM SyntaxNodeKind := do
  checkSyntaxNodeKindAtCurrentNamespaces k
  <|>
  checkSyntaxNodeKind (defaultParserNamespace ++ k)
  <|>
  throwError "invalid syntax node kind '{k}'"

/-- A helper function for providing `evalKey` for `KeyedDeclsAttribute.init` when `mkElabAttribute`
doesn't suffice. Largely inlined from `KeyedDeclsAttribute.init`. -/
def elabNodeKind (id : Ident) (parserNamespace := Name.anonymous) :
    AttrM SyntaxNodeKind := do
  let kind ← SyntaxRules.syntaxNodeKindOfAttrParam parserNamespace id.getId
  /- Recall that a `SyntaxNodeKind` is often the name of the parser, but this is not always true,
  and we must check it. -/
  if (← getEnv).contains kind && (← getInfoState).enabled then
    addConstInfo id kind none
  return kind

/-! # Name structure

The most common use of `syntax_rules` is to attach a `KeyedDeclsAttribute` to some declaration.
Such an attribute is keyed by a `Name`. This key is usually the `SyntaxNodeKind`, but sometimes we
want to key by other things as well (e.g. syntax node kind and a `category` specified by a
`foo_rules : category` command). In that case, we can use these utilities to systematically pack
multiple names in one.
-/

/-- Encode a pair of names in a single name. `delim` is assumed to be atomic and a string. Macro
scopes from `n₁` are erased. Note that this cannot be nested. -/
def mkSimpleNamePair (n₁ n₂ : Name) (delim := `_namePair) : Name :=
  n₁.eraseMacroScopes ++ delim.eraseMacroScopes ++ n₂

--FIXME?: propagate macro scopes to each pair?
/-- Unpacks an encoded name pair if `pair` is of the form `a ++ delim ++ b`. Assumes `delim` is a simple string (no dots or numbers). Returns `none` if `pair` is not actually a pair or if `delim` is of the wrong form. -/
def ofSimpleNamePair? (pair : Name) (delim := `_namePair) : Option (Name × Name) :=
  match delim with
  | .str .anonymous d => go d pair.eraseMacroScopes #[]
  | _ => none
where
  go (d : String) : Name → Array Name → Option (Name × Name)
  | .str a b, ns =>
    if b == d then some (a, ns.foldl (fun a b => b.append a) .anonymous) else go d a (ns.push b)
  | .num a b, ns => go d a (ns.push (.num .anonymous b))
  | .anonymous, _ => none
