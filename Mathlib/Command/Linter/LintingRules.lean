/-
Copyright (c) 2024 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean
import Mathlib.Command.SyntaxRules

/-!

This file sets up the `linting_rules` command. This command can be used as:
```
linting_rules : <category>
| `(stx₁) => <result₁>
| `(stx₂) => <result₂>
...
```
where the type of `result` may depend on the linting category, but is usually
`CommandElabM MessageData`.

The implementation is in terms of `syntax_rules`.

We have to set up
* the syntax for `linting_rules`
* a declaration `@[syntax_rules_header lintingRules] toSyntaxRuleData : ToSyntaxRuleData` which
identifies the category, generates `LintingRulesCatImpl` from it, and produces `SyntaxRuleData`
* an internal attribute `@[linting_rule_category <categoryName>]` on definitions of type
`LintingRulesCatImpl`
* a command `registerLintingRuleCategory` which takes in a `LintingRuleData` specifying the option,
various handlers, etc., translates the relevant part into `LintingRulesCatImpl` (including creating
auxiliary defs) and stores it in the attribute. --Old: It also registers a whole new keyed decls
attribute for this category, which is attached to aux defs by `syntax_rules`. --TODO: make this
part of something like `@[linting_rules category k]`? Or use `@[linting_rules category ++ k]`?
Honestly let's go with the hack for now. Seems a bit better than a new attribute each category? But
we WILL have to change `mkElabAttribute` to first strip the prefix, then check the node. May as
well allow a custom message there I guess. sighhhhh.
* `LintingStep`, the return value in `CommandElabM` of any linter
* `runLintingRules`, the actual linter which runs rules.

TODO: do we want a "generic" category?

TODO:? we're technically hijacking the "no two decls with the same name" restriction to make sure
`register_linting_rules_cat` never registers two implementations for the same category. Ideally
we'd use the attribute `@[linting_rules_cat]` to check this.

TODO: naming: use `LintingRuleStep` instead of `LintingStep`? In general: `LintingRule` or
`LintingRules` everywhere

TODO: factor a bunch of this out as a "category `syntax_rules` builder"

TODO: register a specific "generic" category with no `: ident` syntax?
-/

open Lean Meta Elab Command

initialize registerTraceClass `lintingRules
initialize registerTraceClass `lintingRules.register
initialize registerTraceClass `lintingRules.run

section stx

/- TODO: be sure to note in tutorial that we do not register a command, and we do not include
`optKind`. That could change, maybe. But I think if you need to handle the kind specially, have a
macro from a command to an intermediate command of the form `syntaxRulesHeader optKind matchAlts`
or `syntax_rules ...` directly. -/
/-- `linting_rules : category` command. TODO: docstring -/
syntax (name := lintingRulesHeader) "linting_rules" ppSpace ":" ppSpace ident : syntaxRulesHeader

end stx

namespace LintingRules

section lintingflow

/-- Guides linting by `linting_rules`. -/
inductive LintingStep where
  -- TODO: do we need this?
  | /-- Do not continue linting with this linter at all. -/ done!
  -- TODO: bad name? `.stopDescending` instead?
  | /-- Do not continue linting with this linter while descending into the current subtree of
  syntax. (Do, however, lint adjacent syntax nodes.) -/ done
  | /-- Continue linting with this linter. -/ continue
deriving Inhabited, Repr

instance : ToMessageData LintingStep where
  toMessageData
  | .done => "done"
  | .done! => "done!"
  | .continue => "continue"

/-- `abbrev` for `Syntax → CommandElabM LintingStep` -/
abbrev RunLintingStep := Syntax → CommandElabM LintingStep

end lintingflow

/-- An encoded pair of a syntax nodekind and a category. Named arguments to help prevent typos. -/
private def mkLintingRuleKey (kind cat : Name) := mkSimpleNamePair kind cat

/-- Get the pair of a syntax nodekind and a category from an encoded pair. Named argument to
prevent typos. -/
private def ofLintingRuleKey? (kindCat : Name) := ofSimpleNamePair? kindCat

section attr

/-- The attribute implementing the `linting_rules` command. Keys are encoded name pairs
`(category, kind)` (via `mkSimpleNamePair`). -/
initialize lintingRulesAttr : KeyedDeclsAttribute RunLintingStep ←
  unsafe KeyedDeclsAttribute.init {
    builtinName   := .anonymous
    name          := `linting_rule
    descr         := "attribute implementing the linting_rules command"
    valueTypeName := ``RunLintingStep
    evalKey       := fun _ => fun
      | stx@`(attr|linting_rule $id:ident) => do
        let some (kind, cat) := ofLintingRuleKey? id.getId
          | throwError "unexpected key {id}: key is not a pair"
        let kind ← elabNodeKind (mkIdentFrom stx kind) -- adds const info, checks nodekind
        let key := mkLintingRuleKey kind cat
        trace[lintingRules] "adding key {key}"
        return key
      | _ => throwUnsupportedSyntax
    onAdded       := fun builtin declName => do
      --TODO: get rid of? We don't care about the builtin case...
      if builtin then
        if let some doc ← findDocString? (← getEnv) declName (includeBuiltin := false) then
          declareBuiltin (declName ++ `docString) (mkAppN (mkConst ``addBuiltinDocString)
            #[toExpr declName, toExpr doc])
        if let some declRanges ← findDeclarationRanges? declName then
          declareBuiltin (declName ++ `declRange) (mkAppN (mkConst ``addBuiltinDeclarationRanges)
            #[toExpr declName, toExpr declRanges])
  }

end attr

namespace Category

section data

/-FIXME: we need to currently use an aux def with `run` in the macro, because there's no way we can
create a term of arbitrary type `Out` in `runLintingRules`, and *then* apply `run`. -/

/-- Configuration for either registering a new option to control a linter or using an existing one.
-/
protected inductive LintingRulesCat.OptionConfig
  /-- Register a new option for controlling a linting_rules linter. By default, the name, group,
  and description are auto-generated. -/
  | new (defValue := true) (name : Option Name := none) (descr group : Option String := none)
  /-- Enable/disable this linting rules category with an existing option `opt`. -/
  | existing (opt : Lean.Option Bool)

/-- The data needed to register a new `linting_rules` category with `registerLintingRulesCat`. -/
structure LintingRulesCat where
  /-- The category name. Appears in syntax as `linting_rules : name`. -/
  name : Name := by exact decl_name%
  /-- The return value in `CommandElabM` expected after a syntax match. -/
  Out : Type -- := MessageData -- has to be `Type` not `Type u` because of `CommandElabM`
  /-- Responsible for translating `Out` to `CommandElabM LintingStep`. -/
  -- TODO: right type? use `withRef` and `getRef` if we want access to syntax?
  resolve : Out → CommandElabM LintingStep
  /-- If `.new ..`, create a new option for enabling/disabling the linter. If `.existing opt`, use
  `opt` to enable/disable the linter. -/
  opt : LintingRulesCat.OptionConfig := .new
  /-TODO: does the following field make sense? We could technically handle this in each categories'
  `resolve` by hand. But it's nice to not have to worry about it too much. -/
  --TODO: should it land in `CommandElabM Bool`?
  /-- If this returns `true`, we stop descending into the node. (Note: we do not run `startFn`
  after this.) By default, we do not lint quotations. -/
  stopFn : Syntax → Bool := (·.isQuot)
  --TODO: would the following be useful? E.g. only start linting inside certain tactics.
  /-- If this is not `none`, we only begin linting while descending into the node. -/
  startFn : Option (Syntax → Bool) := none

/- Genuinely not sure what to do about macro scopes...I guess it should be `kind ++ cat`? should
`kind` have macro scopes? `eraseMacroScopes` on category? -/

--TODO: is there a way to make this private without erroring later?
/-- The necessary data to form SyntaxRuleData with. -/
structure LintingRulesCatImpl where
  /-- The name of the `linting_rules` category. -/
  name : Name
  /-- A constant representing `Out`. -/
  OutConst : Name
  /-- A constant representing `resolve : Out → CommandElabM LintingStep`. -/
  resolveConst : Name
  /-- The option associated with this category. -/
  opt : Lean.Option Bool
  /-- `stopFn`, if there is one. -/
  stopFn : Syntax → Bool
  /-- `startFn`, if there is one. -/
  startFn : Option (Syntax → Bool)
deriving Inhabited

/- TODO: provide a function which validates that `type` referes to a type and `attrName` to an
attribute -/

--TODO: move

private def LintingRulesCatImpl.toSyntaxRuleData :
    LintingRulesCatImpl → SyntaxRuleData
  | { name, OutConst, resolveConst, .. } => {
    type := ``RunLintingStep
    /- recall that `Out : Type`, `resolveConst : Out → CommandElabM LintingStep`, and
    `RunLintingStep := Syntax → CommandElabM LintingStep` -/
    -- TODO: is `withRef` redundant here? Is it better somewhere else? E.g. in the `run` loop?
    termOfAlts := fun alts => `(term|fun stx => do
      let out ← show CommandElabM $(mkIdent OutConst) from match stx with $alts:matchAlt*
      $(mkIdent resolveConst):term out)
    attrName := `linting_rule -- We can't use an `s`, lest it conflict with the command.
    -- TODO: pass stx and use as ref? Or just return a `name`?
    mkKey := some fun kind => mkIdentFromRef <| mkLintingRuleKey kind name
    cmdName := "linting_rules"
    auxDefName := `lintingRules
  }

end data

section attr


/- TODO: Currently this is a tag attribute, and rather fragile.
Ideally, we would write `@[linting_rules_cat <catname>]` and check that we only ever added one
implementation for `<catname>` (including on import, though perhaps that's automatic).
Also, maybe a NameSet is not efficient to `fold` over. -/
/- TODO: After achieving the above, it would be a little better to factor this out for reuse to
more easily spin up syntax_rules commands that have a category. -/
/- TODO(perf): check if a label attribute is better. Better to flatten arrays on import instead of
each time the linter runs... -/
/-- An attribute we use to collect implementations of `linting_rules` categories. -/
register_label_attr linting_rules_cat

/-- Get labelled entries. (Does not require `CoreM`.) -/
def labelled (env : Environment) : IO (Array Name) :=
  return ((← labelExtensionMapRef.get).find? `linting_rules_cat).get!.getState env

-- initialize lintingRulesCatAttr : TagAttribute ←
--   registerTagAttribute
--     `linting_rules_cat
--     "An attribute for implmentations of linting rule categories."
--     -- This attribute should only be used internally, so we don't check much.
--     fun decl => do
--       unless (`LintingRules.Category).isPrefixOf decl do
--         throwError "{decl} must be in the LintingRules.Category namespace"
--       let info ← getConstInfo decl
--       unless info.type == mkConst ``LintingRulesCatImpl do
--         throwError "The type of {decl}:{indentD info.type}\nis expected to be 'SyntaxRuleData'."
--     -- TODO: this is cargo-culted, check it makes sense to change from the default.
--     (applicationTime := AttributeApplicationTime.afterCompilation)

syntax_rules_header
| `(lintingRulesHeader|linting_rules : $id:ident) => do
  /-TODO: we rather fragilely assume that the decl specifying the `SyntaxRuleData` is constructed
  as `` `LintingRules.Category ++ id ``. This is enforced by `registerLintingRuleCategory`.
  Ideally this would be a parameter to the attribute which would key the decl (or something like
  that). -/
  let decl := `LintingRules.Category ++ id.getId
  let .true := (← labelled (← getEnv)).contains decl -- lintingRulesCatAttr.hasTag (← getEnv) decl
    | throwErrorAt id "{id} is not a recognized linting_rules category."
  addConstInfo id decl -- show docstring provided for `register_linting_rules_cat ..` on `id`
  return (← unsafe evalConstCheck LintingRulesCatImpl ``LintingRulesCatImpl decl).toSyntaxRuleData

end attr

section register

/-- Each `linting_rules` category `foo` is controlled by the option `linter.cat` unless otherwise
specified. -/
def mkLintingRulesOptionName (cat : Name) := `linter ++ cat

--TODO: include doc comment? or inherit?
/-- Assumes `cat` has not been used to generate an option name already. -/
def registerLintingRulesCatOption (cat : Name) : LintingRulesCat.OptionConfig →
    CommandElabM (Lean.Option Bool)
  | .new defValue name descr group => do
    let name := name.getD (mkLintingRulesOptionName cat)
    let exists? ← try some <$> getOptionDecl name catch _ => pure none
    if let some { declName, .. } := exists? then
      throwError "Option {name} already exists, and cannot be registered.\n\
        Use opt := .existing {declName} if this is intentional."
    let descr := descr.getD <| "enable the '" ++ cat.toString ++ "' linter"
    let group := group.getD "lintingRules"
    elabCommand <|← `(command|
      register_option $(mkIdent name) : Bool := with_decl_name% $(mkIdent name) {
        defValue := $(quote defValue)
        descr := $(quote descr)
        group := $(quote group)
      }) -- TODO: include group or not? Is `quote` ok?
    trace[lintingRules.register] "registered option {name} with default value {defValue}"
    return { name, defValue }
  | .existing opt => do
    -- validate that the option exists
    let _ ← getOptionDecl opt.name
    trace[lintingRules.register] "not registering new option; using {opt.name}"
    return opt

open Term

/-- Create the name of the decl that will bear `@[linting_rules_cat]`. -/
private def mkCatDeclName (cat : Name) := `LintingRules.Category ++ cat.eraseMacroScopes

/-- Add a suffix to `cat`. -/
private def mkCatConstName (cat suffix : Name) := mkCatDeclName cat ++ suffix.eraseMacroScopes

/-- Implements `register_linting_rules_cat`. TODO: docstring -/
def registerLintingRulesCat (id : Ident) (data : Term)
    (doc : Option (TSyntax ``Parser.Command.docComment)) : CommandElabM Unit := withRef data do
  let cat := id.getId -- TODO: ensure no namespaces.
  -- TODO: include types?
  -- TODO: `quote` or `mkIdent`?
  let outName := mkCatConstName cat `_OutConst
  let resolveName := mkCatConstName cat `_resolveConst
  --TODO: do variables mess up the type? No, right?
  elabCommand <|← `(command|abbrev $(mkIdent outName) : Type := ($data:term).Out)
  elabCommand <|← `(command|abbrev $(mkIdent resolveName) := ($data:term).resolve)
  /- TODO: There's got to be a nicer way to do this next bit. I'm not fond of the unsafe bit. Can't
  we do the transformation within syntax or something? The issue is control flow, really: don't
  initialize if we've got an `existing` one.
  I would have just liked to eval `LintingRulesCat` instead of elaborating the term over and over
  if we were going to eval something, but `evalTerm`/the monad can't handle it because of the
  `Type` restriction.
  Maybe an intermediate `abbrev` just for `data` would be good?
  But we're not adding categories that often, so maybe that's premature optimization.
  Instead, we could possibly `reduce` and extract the data from `Expr`s if we *really* wanted to
  avoid something `unsafe`. But it's probably fine. -/
  let optCfg ← runTermElabM fun _ => do
    unsafe evalTerm LintingRulesCat.OptionConfig (mkConst ``LintingRulesCat.OptionConfig)
      (← `(term|($data:term).opt))
  let { name := optName, defValue } ← registerLintingRulesCatOption cat optCfg
  let catDeclId := mkIdentFrom id (mkCatDeclName cat)
  -- TODO: add any other attributes
  -- TODO: can't we add this attribute in meta code?
  elabCommand <|← `(command|
    $[$doc:docComment]?
    @[linting_rules_cat]
    def $catDeclId:ident : LintingRules.Category.LintingRulesCatImpl where
      name := $(quote cat)
      OutConst := $(quote outName)
      resolveConst := $(quote resolveName)
      opt := { name := $(quote optName), defValue := $(quote defValue) }
      stopFn := ($data).stopFn
      startFn := ($data).startFn)
  --TODO: improve trace by resolving constant so that hover works
  trace[lintingRules.register] "registered @[linting_rules_cat] {catDeclId} : LintingRulesCaptImpl"


/--

Specifically, this command:
* creates `LintingRulesCatImpl` of name `` `LintingRules.Category ++ catName `` and tags it with
`@[linting_rules_cat]`, using data from the given `LintingRulesCat`
* registers an option if no existing option is supplied

TODO: elaborate; mention trace? Include `?`?; mention that docstring will be shown on hover of
category.
-/
syntax (name := registerLintingRulesCatCommand)
  (docComment)? "register_linting_rules_cat " ident ppSpace ":=" ppSpace term : command

elab_rules : command
| `(registerLintingRulesCatCommand|
  $[$doc:docComment]? register_linting_rules_cat $id:ident := $data:term) => do
  -- make `data` a bit nicer to write
  let data ← withRef data
    `(term|with_decl_name% $id ($data : LintingRules.Category.LintingRulesCat))
  registerLintingRulesCat id data doc

end register

section run

--TODO: Have a `lintingRules.all` option?
-- register_option lintingRules.all : Bool := {
--   defValue := true
--   descr := "enable linting_rules linters by default" -- TODO: improve
-- }

-- --TODO: does this actually behave as expected? Do we even want it, or just use `linter.all`?
-- def getLintingRulesAll (o : Options) : Bool := Linter.getLinterValue lintingRules.all o

-- def getLintingRulesValue (opt : Lean.Option Bool) (o : Options) : Bool :=
--   o.get opt.name (getLintingRulesAll o)

/-- A short representation of syntax used in traces. -/
private def shortRepr : Syntax → MessageData
  | .node info kind args => m!"{kind} @{info.getPos?} #[<{args.size} args>]"
  | .ident _ raw .. => m!"ident {raw}"
  | .missing => m!"<missing>"
  | .atom _ val => m!"{val}"

/-- Trace messages are not preserved during linting. This emulates tracing. -/
private def lintTrace (opts : Options) (msg : MessageData) : CommandElabM Unit := do
  if opts.getBool `trace.lintingRules.run false then logInfo msg

/-- Runs a list of `RunLintingStep`s on `stx` with state `s` until one -/
private def runLintingSteps (s : Command.State) (stx : Syntax) :
    List RunLintingStep → CommandElabM LintingStep
  | [] => pure .continue
  | fn :: fns => do
    try
      catchInternalId unsupportedSyntaxExceptionId
        (fn stx) (fun _ => do set s; runLintingSteps s stx fns)
    catch ex =>
      logException ex --TODO?: Should we instead be trying the next `fns`?
      pure .continue

--TODO: handle `set_option` a la `withSetOptionIn`.
--TODO: use trace nodes.
--TODO(perf): try without: `startFn`; `stopFn`; parallel loops; `flatten` (use fold instead)
open Linter in
/-- Descend the top-level command syntax and run `linting_rules` rules on each syntax encountered .
-/
def runLintingRules (stx : Syntax) : CommandElabM Unit := do
  let opts ← getOptions
  let env ← getEnv
  let cats ← labelled env
    -- (lintingRulesCatAttr.ext.toEnvExtension.getState env).importedEntries.flatten ++
    -- (lintingRulesCatAttr.ext.getState env).toArray
  -- lintTrace opts m!"Using categories {cats}."
  -- let mut isDone := mkArray cats.size (some 0) -- if no `startFn`
  --TODO: see if it's better to extract the name and opt at this stage, or to use `.name` etc.
  --TODO: good placement of `unsafe` or not?
  let cats ← unsafe cats.mapM <| evalConst LintingRulesCatImpl
  let mut isDone : HashMap Name (LOption Nat) := {}
  -- let mut isDone := cats.map fun { startFn, .. } =>
  --   if startFn.isNone then LOption.some 0 else .undef
  for stx in stx.topDown do
    /- TODO: check efficiency? just do `i in [:cats.size]` and use array access instead? Also,
    destruct or use `.name`? -/
    -- lintTrace opts m!"Linting {shortRepr stx}." --TODO: does this increase reference count?
    if stx.getKind == `null then
      -- lintTrace opts m!"null nodekind; moving on."
      continue
    for h : i in [:cats.size] do
      match
        isDone.find? cats[i].name |>.getD (if cats[i].startFn.isNone then .some 0 else .undef) with
      | .some 0 =>
        -- lintTrace opts m!"Linting using {name}."
        if getLinterValue cats[i].opt opts then --TODO: use `withSetOptionIn` or something
          let key := mkLintingRuleKey stx.getKind cats[i].name -- TODO: is this efficient enough?
          -- lintTrace opts m!"Key: {key}"
          let step ← if cats[i].stopFn stx then
              pure .done
            else
              runLintingSteps (← get) stx (lintingRulesAttr.getValues env key)
          -- lintTrace opts m!"{step}"
          match step with
          | .continue => continue
          | .done =>
            isDone := isDone.insert cats[i].name (.some stx.getNumArgs)
          | .done! =>
            isDone := isDone.insert cats[i].name .none
      | .some (n+1) =>
        -- lintTrace opts m!"Done: {name}\n{n+1} ==> {n + stx.getNumArgs}"
        isDone := isDone.insert cats[i].name (.some (n + stx.getNumArgs))
      | .none => continue
      | .undef =>
        if let some .true := cats[i]!.startFn <*> stx then
          isDone := isDone.insert cats[i].name (.some 0)
        continue

initialize addLinter {
  name := `lintingRules
  run  := runLintingRules
}

end run
