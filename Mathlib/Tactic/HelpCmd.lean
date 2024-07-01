/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Syntax
import Lean.DocString

/-!

# The `#help` command

The `#help` command can be used to list all definitions in a variety of extensible aspects of lean.

* `#help option` lists options (used in `set_option myOption`)
* `#help attr` lists attributes (used in `@[myAttr] def foo := ...`)
* `#help cats` lists syntax categories (like `term`, `tactic`, `stx` etc)
* `#help cat C` lists elements of syntax category C
  * `#help term`, `#help tactic`, `#help conv`, `#help command`
    are shorthand for `#help cat term` etc.
  * `#help cat+ C` also shows `elab` and `macro` definitions associated to the syntaxes

All forms take an optional identifier to narrow the search; for example `#help option pp` shows
only `pp.*` options.

-/

namespace Mathlib.Tactic
open Lean Meta Elab Tactic Command

/--
The command `#help option` shows all options that have been defined in the current environment.
Each option has a format like:
```
option pp.all : Bool := false
  (pretty printer) display coercions, implicit parameters, proof terms, fully qualified names,
  universe, and disable beta reduction and notations during pretty printing
```
This says that `pp.all` is an option which can be set to a `Bool` value, and the default value is
`false`. If an option has been modified from the default using e.g. `set_option pp.all true`,
it will appear as a `(currently: true)` note next to the option.

The form `#help option id` will show only options that begin with `id`.
-/
syntax withPosition("#help " colGt &"option" (colGt ppSpace Parser.rawIdent)?) : command

private def elabHelpOption (id : Option Ident) : CommandElabM Unit := do
  let id := id.map (·.raw.getId.toString false)
  let mut decls : Lean.RBMap _ _ compare := {}
  for (name, decl) in show Lean.RBMap .. from ← getOptionDecls do
    let name := name.toString false
    if let some id := id then
      if !id.isPrefixOf name then
        continue
    decls := decls.insert name decl
  let mut msg := Format.nil
  let opts ← getOptions
  if decls.isEmpty then
    match id with
    | some id => throwError "no options start with {id}"
    | none => throwError "no options found (!)"
  for (name, decl) in decls do
    let mut msg1 := match decl.defValue with
    | .ofString val => s!"String := {repr val}"
    | .ofBool val => s!"Bool := {repr val}"
    | .ofName val => s!"Name := {repr val}"
    | .ofNat val => s!"Nat := {repr val}"
    | .ofInt val => s!"Int := {repr val}"
    | .ofSyntax val => s!"Syntax := {repr val}"
    if let some val := opts.find (.mkSimple name) then
      msg1 := s!"{msg1}  (currently: {val})"
    msg := msg ++ .nest 2 (f!"option {name} : {msg1}" ++ .line ++ decl.descr) ++ .line ++ .line
  logInfo msg

elab_rules : command | `(#help option $(id)?) => elabHelpOption id

/--
The command `#help attribute` (or the short form `#help attr`) shows all attributes that have been
defined in the current environment.
Each option has a format like:
```
[inline]: mark definition to always be inlined
```
This says that `inline` is an attribute that can be placed on definitions like
`@[inline] def foo := 1`. (Individual attributes may have restrictions on where they can be
applied; see the attribute's documentation for details.) Both the attribute's `descr` field as well
as the docstring will be displayed here.

The form `#help attr id` will show only attributes that begin with `id`.
-/
syntax withPosition("#help " colGt (&"attr" <|> &"attribute")
    (colGt ppSpace Parser.rawIdent)?) : command

private def elabHelpAttr (id : Option Ident) : CommandElabM Unit := do
  let id := id.map (·.raw.getId.toString false)
  let mut decls : Lean.RBMap _ _ compare := {}
  /-
  #adaptation_note
  On nightly-2024-06-21, added the `.toList` here:
  without it the requisite `ForIn` instance can't be found.
  -/
  for (name, decl) in (← attributeMapRef.get).toList do
    let name := name.toString false
    if let some id := id then
      if !id.isPrefixOf name then
        continue
    decls := decls.insert name decl
  let mut msg := Format.nil
  let env ← getEnv
  if decls.isEmpty then
    match id with
    | some id => throwError "no attributes start with {id}"
    | none => throwError "no attributes found (!)"
  for (name, decl) in decls do
    let mut msg1 := s!"[{name}]: {decl.descr}"
    if let some doc ← findDocString? env decl.ref then
      msg1 := s!"{msg1}\n{doc.trim}"
    msg := msg ++ .nest 2 msg1 ++ .line ++ .line
  logInfo msg

elab_rules : command
  | `(#help attr $(id)?) => elabHelpAttr id
  | `(#help attribute $(id)?) => elabHelpAttr id

/-- Gets the initial string token in a parser description. For example, for a declaration like
`syntax "bla" "baz" term : tactic`, it returns `some "bla"`. Returns `none` for syntax declarations
that don't start with a string constant. -/
partial def getHeadTk (e : Expr) : Option String :=
  match e.getAppFnArgs with
  | (``ParserDescr.node, #[_, _, p])
  | (``ParserDescr.trailingNode, #[_, _, _, p])
  | (``ParserDescr.unary, #[.app _ (.lit (.strVal "withPosition")), p])
  | (``ParserDescr.unary, #[.app _ (.lit (.strVal "atomic")), p])
  | (``ParserDescr.unary, #[.app _ (.lit (.strVal "ppRealGroup")), p])
  | (``ParserDescr.unary, #[.app _ (.lit (.strVal "ppRealFill")), p])
  | (``Parser.ppRealFill, #[p])
  | (``Parser.withAntiquot, #[_, p])
  | (``Parser.leadingNode, #[_, _, p])
  | (``Parser.trailingNode, #[_, _, _, p])
  | (``Parser.group, #[p])
  | (``Parser.withCache, #[_, p])
  | (``Parser.withResetCache, #[p])
  | (``Parser.withPosition, #[p])
  | (``Parser.withOpen, #[p])
  | (``Parser.withPositionAfterLinebreak, #[p])
  | (``Parser.suppressInsideQuot, #[p])
  | (``Parser.ppRealGroup, #[p])
  | (``Parser.ppIndent, #[p])
  | (``Parser.ppDedent, #[p])
    => getHeadTk p
  | (``ParserDescr.binary, #[.app _ (.lit (.strVal "andthen")), p, q])
  | (``HAndThen.hAndThen, #[_, _, _, _, p, .lam _ _ q _])
    => getHeadTk p <|> getHeadTk q
  | (``ParserDescr.nonReservedSymbol, #[.lit (.strVal tk), _])
  | (``ParserDescr.symbol, #[.lit (.strVal tk)])
  | (``Parser.nonReservedSymbol, #[.lit (.strVal tk), _])
  | (``Parser.symbol, #[.lit (.strVal tk)])
  | (``Parser.unicodeSymbol, #[.lit (.strVal tk), _])
    => pure tk
  | _ => none

/--
The command `#help cats` shows all syntax categories that have been defined in the
current environment.
Each syntax has a format like:
```
category command [Lean.Parser.initFn✝]
```
The name of the syntax category in this case is `command`, and `Lean.Parser.initFn✝` is the
name of the declaration that introduced it. (It is often an anonymous declaration like this,
but you can click to go to the definition.) It also shows the doc string if available.

The form `#help cats id` will show only syntax categories that begin with `id`.
-/
syntax withPosition("#help " colGt &"cats" (colGt ppSpace Parser.rawIdent)?) : command

private def elabHelpCats (id : Option Ident) : CommandElabM Unit := do
  let id := id.map (·.raw.getId.toString false)
  let mut decls : Lean.RBMap _ _ compare := {}
  for (name, cat) in (Parser.parserExtension.getState (← getEnv)).categories do
    let name := name.toString false
    if let some id := id then
      if !id.isPrefixOf name then
        continue
    decls := decls.insert name cat
  let mut msg := MessageData.nil
  let env ← getEnv
  if decls.isEmpty then
    match id with
    | some id => throwError "no syntax categories start with {id}"
    | none => throwError "no syntax categories found (!)"
  for (name, cat) in decls do
    let mut msg1 := m!"category {name} [{mkConst cat.declName}]"
    if let some doc ← findDocString? env cat.declName then
      msg1 := msg1 ++ Format.line ++ doc.trim
    msg := msg ++ .nest 2 msg1 ++ (.line ++ .line : Format)
  logInfo msg

elab_rules : command | `(#help cats $(id)?) => elabHelpCats id

/--
The command `#help cat C` shows all syntaxes that have been defined in syntax category `C` in the
current environment.
Each syntax has a format like:
```
syntax "first"... [Parser.tactic.first]
  `first | tac | ...` runs each `tac` until one succeeds, or else fails.
```
The quoted string is the leading token of the syntax, if applicable. It is followed by the full
name of the syntax (which you can also click to go to the definition), and the documentation.

* The form `#help cat C id` will show only attributes that begin with `id`.
* The form `#help cat+ C` will also show information about any `macro`s and `elab`s
  associated to the listed syntaxes.
-/
syntax withPosition("#help " colGt &"cat" "+"? colGt ident
    (colGt ppSpace (Parser.rawIdent <|> str))?) : command

private def elabHelpCat (more : Option Syntax) (catStx : Ident) (id : Option String) :
    CommandElabM Unit := do
  let mut decls : Lean.RBMap _ _ compare := {}
  let mut rest : Lean.RBMap _ _ compare := {}
  let catName := catStx.getId.eraseMacroScopes
  let some cat := (Parser.parserExtension.getState (← getEnv)).categories.find? catName
    | throwErrorAt catStx "{catStx} is not a syntax category"
  liftTermElabM <| Term.addCategoryInfo catStx catName
  let env ← getEnv
  for (k, _) in cat.kinds do
    let mut used := false
    if let some tk := do getHeadTk (← (← env.find? k).value?) then
      let tk := tk.trim
      if let some id := id then
        if !id.isPrefixOf tk then
          continue
      used := true
      decls := decls.insert tk ((decls.findD tk #[]).push k)
    if !used && id.isNone then
      rest := rest.insert (k.toString false) k
  let mut msg := MessageData.nil
  if decls.isEmpty && rest.isEmpty then
    match id with
    | some id => throwError "no {catName} declarations start with {id}"
    | none => throwError "no {catName} declarations found"
  let env ← getEnv
  let addMsg (k : SyntaxNodeKind) (msg msg1 : MessageData) : CommandElabM MessageData := do
    let mut msg1 := msg1
    if let some doc ← findDocString? env k then
      msg1 := msg1 ++ Format.line ++ doc.trim
    msg1 := .nest 2 msg1
    if more.isSome then
      let addElabs {α} (type : String) (attr : KeyedDeclsAttribute α)
          (msg : MessageData) : CommandElabM MessageData := do
        let mut msg := msg
        for e in attr.getEntries env k do
          let x := e.declName
          msg := msg ++ Format.line ++ m!"+ {type} {mkConst x}"
          if let some doc ← findDocString? env x then
            msg := msg ++ .nest 2 (Format.line ++ doc.trim)
        pure msg
      msg1 ← addElabs "macro" macroAttribute msg1
      match catName with
      | `term => msg1 ← addElabs "term elab" Term.termElabAttribute msg1
      | `command => msg1 ← addElabs "command elab" commandElabAttribute msg1
      | `tactic | `conv => msg1 ← addElabs "tactic elab" tacticElabAttribute msg1
      | _ => pure ()
    return msg ++ msg1 ++ (.line ++ .line : Format)
  for (name, ks) in decls do
    for k in ks do
      msg ← addMsg k msg m!"syntax {repr name}... [{mkConst k}]"
  for (_, k) in rest do
    msg ← addMsg k msg m!"syntax ... [{mkConst k}]"
  logInfo msg

elab_rules : command
  | `(#help cat $[+%$more]? $cat) => elabHelpCat more cat none
  | `(#help cat $[+%$more]? $cat $id:ident) => elabHelpCat more cat (id.getId.toString false)
  | `(#help cat $[+%$more]? $cat $id:str) => elabHelpCat more cat id.getString

/--
The command `#help term` shows all term syntaxes that have been defined in the current environment.
See `#help cat` for more information.
-/
syntax withPosition("#help " colGt &"term" "+"?
    (colGt ppSpace (Parser.rawIdent <|> str))?) : command
macro_rules
  | `(#help term%$tk $[+%$more]? $(id)?) =>
    `(#help cat$[+%$more]? $(mkIdentFrom tk `term) $(id)?)

/--
The command `#help tactic` shows all tactics that have been defined in the current environment.
See `#help cat` for more information.
-/
syntax withPosition("#help " colGt &"tactic" "+"?
    (colGt ppSpace (Parser.rawIdent <|> str))?) : command
macro_rules
  | `(#help tactic%$tk $[+%$more]? $(id)?) =>
    `(#help cat$[+%$more]? $(mkIdentFrom tk `tactic) $(id)?)

/--
The command `#help conv` shows all tactics that have been defined in the current environment.
See `#help cat` for more information.
-/
syntax withPosition("#help " colGt &"conv" "+"?
    (colGt ppSpace (Parser.rawIdent <|> str))?) : command
macro_rules
  | `(#help conv%$tk $[+%$more]? $(id)?) =>
    `(#help cat$[+%$more]? $(mkIdentFrom tk `conv) $(id)?)

/--
The command `#help command` shows all commands that have been defined in the current environment.
See `#help cat` for more information.
-/
syntax withPosition("#help " colGt &"command" "+"?
    (colGt ppSpace (Parser.rawIdent <|> str))?) : command
macro_rules
  | `(#help command%$tk $[+%$more]? $(id)?) =>
    `(#help cat$[+%$more]? $(mkIdentFrom tk `command) $(id)?)
