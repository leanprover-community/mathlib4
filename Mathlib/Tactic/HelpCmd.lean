/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Lean.Expr.Basic

/-!

# The `#help` command

The `#help` command can be used to list all definitions in a variety of extensible aspects of lean.

* `#help option` lists options (used in `set_option myOption`)
* `#help attr` lists attributes (used in `@[myAttr] def foo := ...`)
* `#help cats` lists syntax categories (like `term`, `tactic`, `stx` etc)
* `#help cat C` lists elements of syntax category C
  * `#help term`, `#help tactic`, `#help conv` are shorthand for `#help cat term` etc.

All forms take an optional identifier to narrow the search; for example `#help option pp` shows
only `pp.*` options.

-/

-- FIXME: polyfill for lean4#1391
namespace Std.PersistentHashMap

/-- `for` iteration for `PersistentHashMap`. -/
@[specialize] protected def forIn {_ : BEq α} {_ : Hashable α} [Monad m]
    (map : PersistentHashMap α β) (init : σ) (f : α × β → σ → m (ForInStep σ)) : m σ := do
  let intoError : ForInStep σ → Except σ σ
  | .done s => .error s
  | .yield s => .ok s
  let result ← foldlM (m := ExceptT σ m) map (init := init) fun s a b =>
    (intoError <$> f (a, b) s : m _)
  match result with
  | .ok s | .error s => pure s

instance {_ : BEq α} {_ : Hashable α} : ForIn m (PersistentHashMap α β) (α × β) where
  forIn := PersistentHashMap.forIn

end Std.PersistentHashMap

namespace Mathlib.Tactic
open Lean Meta Elab Tactic

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
elab "#help" &"option" id:(ident)? : command => do
  let id := id.map (·.getId.toString false)
  let mut decls : Std.RBMap _ _ compare := {}
  for (name, decl) in show Std.RBMap .. from ← getOptionDecls do
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
    if let some val := opts.find name then
      msg1 := s!"{msg1}  (currently: {val})"
    msg := msg ++ .nest 2 (f!"option {name} : {msg1}" ++ .line ++ decl.descr) ++ .line ++ .line
  logInfo msg

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
elab "#help" (&"attr" <|> &"attribute") id:(ident)? : command => do
  let id := id.map (·.getId.toString false)
  let mut decls : Std.RBMap _ _ compare := {}
  for (name, decl) in ← attributeMapRef.get do
    let name := name.toString false
    if let some id := id then
      if !id.isPrefixOf name then
        continue
    decls := decls.insert name decl
  let mut msg := Format.nil
  -- let env ← getEnv
  if decls.isEmpty then
    match id with
    | some id => throwError "no attributes start with {id}"
    | none => throwError "no attributes found (!)"
  for (name, decl) in decls do
    let mut msg1 := s!"[{name}]: {decl.descr}"
    -- FIXME: put back when lean4#1384 lands
    -- if let some doc ← findDocString? env decl.ref then
    --   msg1 := s!"{msg1}\n{doc.trim}"
    msg := msg ++ .nest 2 msg1 ++ .line ++ .line
  logInfo msg

/-- Gets the initial string token in a parser description. For example, for a declaration like
`syntax "bla" "baz" term : tactic`, it returns `some "bla"`. Returns `none` for syntax declarations
that don't start with a string constant. -/
partial def getHeadTk (e : Expr) : Option String :=
  match e.getAppFnArgs with
  | (``ParserDescr.node, #[_, _, p]) => getHeadTk p
  | (``ParserDescr.unary, #[.app _ (.lit (.strVal "withPosition")), p]) => getHeadTk p
  | (``ParserDescr.unary, #[.app _ (.lit (.strVal "atomic")), p]) => getHeadTk p
  | (``ParserDescr.binary, #[.app _ (.lit (.strVal "andthen")), p, _]) => getHeadTk p
  | (``ParserDescr.nonReservedSymbol, #[.lit (.strVal tk), _]) => some tk
  | (``ParserDescr.symbol, #[.lit (.strVal tk)]) => some tk
  | (``Parser.withAntiquot, #[_, p]) => getHeadTk p
  | (``Parser.leadingNode, #[_, _, p]) => getHeadTk p
  | (``HAndThen.hAndThen, #[_, _, _, _, p, _]) => getHeadTk p
  | (``Parser.nonReservedSymbol, #[.lit (.strVal tk), _]) => some tk
  | (``Parser.symbol, #[.lit (.strVal tk)]) => some tk
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
elab "#help" &"cats" id:(ident)? : command => do
  let id := id.map (·.getId.toString false)
  let mut decls : Std.RBMap _ _ compare := {}
  for (name, cat) in (Parser.parserExtension.getState (← getEnv)).categories do
    let name := name.toString false
    if let some id := id then
      if !id.isPrefixOf name then
        continue
    decls := decls.insert name cat
  let mut msg := MessageData.nil
  -- let env ← getEnv
  if decls.isEmpty then
    match id with
    | some id => throwError "no syntax categories start with {id}"
    | none => throwError "no syntax categories found (!)"
  for (name, _cat) in decls do
    -- FIXME: put back when lean4#1392 lands
    -- let mut msg1 := m!"category {name} [{mkConst cat.ref}]"
    -- if let some doc ← findDocString? env cat.ref then
    --   msg1 := msg1 ++ Format.line ++ doc.trim
    let msg1 := m!"category {name}"
    msg := msg ++ .nest 2 msg1 ++ (.line ++ .line : Format)
  logInfo msg

/- FIXME: these depend essentially on lean4#1392

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

The form `#help cat C id` will show only attributes that begin with `id`.
-/
elab "#help" &"cat" cat:ident id:(ident <|> str)? : command => do
  let id := id.map fun id => match id.raw with
    | .ident _ _ v _ => v.toString false
    | id => id.isStrLit?.get!
  let mut decls : Std.RBMap _ _ compare := {}
  let mut rest : Std.RBMap _ _ compare := {}
  let catName := cat.getId
  let some cat := (Parser.parserExtension.getState (← getEnv)).categories.find? catName
    | throwError "{cat} is not a syntax category"
  let env ← getEnv
  for (k, _) in cat.kinds do
    let mut used := false
    if let some tk := do getHeadTk (← (← env.find? k).value?) then
      if let some id := id then
        if !id.isPrefixOf tk then
          continue
      used := true
      decls := decls.insert tk k
    if !used && id.isNone then
      rest := rest.insert (k.toString false) k
  let mut msg := MessageData.nil
  if decls.isEmpty && rest.isEmpty then
    match id with
    | some id => throwError "no {catName} declarations start with {id}"
    | none => throwError "no {catName} declarations found"
  let env ← getEnv
  for (name, k) in decls do
    let mut msg1 := m!"syntax {repr name.trim}... [{mkConst k}]"
    if let some doc ← findDocString? env k then
      msg1 := msg1 ++ Format.line ++ doc.trim
    msg := msg ++ .nest 2 msg1 ++ (.line ++ .line : Format)
  for (_, k) in rest do
    let mut msg1 := m!"syntax ... [{mkConst k}]"
    if let some doc ← findDocString? env k then
      msg1 := msg1 ++ Format.line ++ doc.trim
    msg := msg ++ .nest 2 msg1 ++ (.line ++ .line : Format)
  logInfo msg

/--
The command `#help term` shows all term syntaxes that have been defined in the current environment.
See `#help cat` for more information.
-/
macro "#help" &"term" id:(ident <|> str)? : command =>
  set_option hygiene false in `(#help cat term $(id.map (⟨·.raw⟩))?)

/--
The command `#help tactic` shows all tactics that have been defined in the current environment.
See `#help cat` for more information.
-/
macro "#help" &"tactic" id:(ident <|> str)? : command =>
  set_option hygiene false in `(#help cat tactic $(id.map (⟨·.raw⟩))?)

/--
The command `#help conv` shows all tactics that have been defined in the current environment.
See `#help cat` for more information.
-/
macro "#help" &"conv" id:(ident <|> str)? : command =>
  set_option hygiene false in `(#help cat conv $(id.map (⟨·.raw⟩))?)
-/
