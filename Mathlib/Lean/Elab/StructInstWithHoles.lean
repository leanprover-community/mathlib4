/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.FindExpr
import Lean.Parser.Term
import Lean.Meta.Structure
import Lean.Elab.App
import Lean.Elab.Binders

namespace Lean.Elab.Term.StructInstWithHoles --!!

open Meta
open TSyntax.Compat

--!! All instances of "missing" used to be "default", except in function names, where only `allDefault` was changed to `allMissing`.
/-
  # What this does

  This file defines a term elaboration for structure instances that include "variadic holes", i.e. holes of "variable length", which are represented via via the syntax `?..`, `?..!`, etc., e.g. `{ x := 0, ?.. }`. This serves to port the functionality of mathlib3's `refine_struct { .. }`, but via `refine` (e.g. `refine { ?.. }`).

  Lean currently already supports one form of variadic hole in structure instances, namely `..`, which fills all unspecified fields with natural metavariables and which is frequently used in pattern matching.

  Variadic holes that begin with a question mark are meant to parallel named holes (e.g. `?x`). Therefore, syntax like `{ x := 0, ?.. }` will fill all remaining fields with metavariables named by the field in question (e.g. `y := ?y`). Identifiers can optionally be provided to prefix the name; see below.

  Tests are performed in `Tests/StructInstWithHoles.lean`.

  At the end of this file, we implement `haveFieldProj` in analogy to `have_field` with some modifications. (This might be moved or eliminated.)

  ## Current specifics

  The following is subject to change.

  Several variants are supported to enable the choice between synthetic holes (`?`) and natural ones, and to enable the choice between filling all unspecified fields with holes (`!`) and synthesizing defaults where possible.

  Currently all four combinations are allowed. This is likely temporary; for example, `...` is certainly not expected to stick around, and more descriptive syntax might be used for whether to synthesize defaults or not (e.g. `?.. noDefaults`)

                synthesize defaults
                ┌──true──┬─false──┐
    named goals │ `?..`  │ `?..!` │
                ├────────┼────────┤
  unnamed goals │ `...`  │  `..!` │
                └────────┴────────┘

   Identifiers can be provided after the variadic hole syntax in the `?` case, e.g. `?..foo` and `?..!foo`

  # Overview of existing code

  This document began as `StructInst.lean`, then was modified as needed. The modifications are done in such a way as to (hopefully) make it easy for them to be absorbed into `StructInst.lean`, if that's where it ends up. The following details how the original `StructInst.lean` works (which is largely preserved).

  ## Short version

  The way this works is that we start with syntax, parse it into a bare-bones `Struct`, use `expandStruct` to expand that struct into another struct that has intermediate indicators (`FieldVal`s) holding raw syntax or accounting for its absence. We then `elabStruct` that struct into an `ElabStructResult` which has the potential result expression (an application of the structure's single constructor to its values, which may be metavariables if they weren't found in the syntax) plus info on the original struct. We then synthesize defaults using `propagate` to assign any metavariables standing in for default values, and then return the expression.

  ## Long version

  We start with turning the syntax into a struct. First we extract the sources (everything before the `with` and any variadic holes (`..` or similar)), then we feed this to `elabStructInstAux` along with the raw syntax and expected type. Inside `elabStructInstAux` we make the syntax into a Struct (`mkStructView`), then `expandStruct`.

  There's a "pre-expression scaffolding/framework/spine" set up early on in the process in the form of FieldVal's, which hold raw information: `.term stx` where `stx` is syntax, if a term was provided; a `.missing` value if it was missing; or a `.nested s` value where `s` is a `Struct` if a subobject relation obtains. The `FieldVal`s for a field might be modified as elaboration proceeds: for example, some might become `.nested`, or some defaults might turn into terms. This all happens during `expandStruct`.

  The `Struct` holds everything, and is updated throughout the process.

  One of its fields is `field`, which holds a list of `Field Struct`'s. (The appearance of `Struct` within `Field Struct` is to allow the `Struct`s to nest other `Struct`s when we have subobjects.)

  The fields of each element of the `field` field (got that?) are

  * `ref : Syntax`, which holds the `Syntax` found for that field
  * `lhs : FieldLHS`, which describes the name of the field in question
  * `val : FieldVal`, which holds the pre-expression `FieldVal`—either `.term stx` where `stx` is the syntax of the field's value, `.default` (now `.missing`) if no syntax was found, or `.nested s` if the field represents a subobject `s` of the structure (e.g. `toFoo`, produced by `extends`)
  * `expr? : Option Expr`, which holds the elaborated expression when it becomes available (or a metavariable, if the syntax is missing), and which begins at this stage as `none`.

  `elacStructInstAux` then calls `elabStruct` on the skeletal `Struct` (which has appropriate `FieldVal`s, but `none` for each field's `expr?`), which turns the `Struct` into an `ElabStructResult`.

  `elabStruct` elaborates everything but defaults, constructing the structure instance as an expression given by the application of the structure's constructor to the values it finds by elaborating the `stx` in any `.term stx` `FieldVal` while ensuring the appropriate type. (It's not quite true that no defaults are taken care of here: `autoparam`s are turned into `.term`s.) If the `FieldVal` is `.nested s`, it calls `elabStruct` on `s`; if it finds a `.default` (now renamed to `.missing`) `FieldVal`, it uses a fresh metavariable in place of an elaborated expression. As it does this, it stores any elaborated expressions in the `expr?` field of its fields and builds this constructor application expression, which is, in the resulting `ElabStructResult` structure, confusingly also named "val". Occasionally the `FieldVals` for each field are updated as well. Also returned in `ElabStructResult` is the updated Struct with all its new fields, and `instMVars`, an array of metavariables for dealing with typeclass instance synthesis.

  During `elabStruct`, defaults were inserted as metavariables into the constructed expression and into `expr?`, but they were also annotated with ``structInstDefault` to indicate that they represented a missing default value, and needed to be synthesized during the default loop. Indeed, the function `isMissingDefault?` checks that this metavariable is unassigned when deciding whether to return true or false. We finish our elaboration of the structure instance with the `propagate` loop, which iteratively synthesizes the defaults, as sometimes the default values of fields reference other fields which may also have a default value (etc.).

  # Modifications

  Changes from `StructInst.lean` are marked with `!!` in a comment (or with `!!/`, `!!\` surrounding a new or altered block).

  Existing comments are left unchanged, and new comments begin with "~~".

  ## Syntax

  We use the parser from `Term.lean`, but change `optional ".."` to our parseer for variadic holes, `variadicHole`

  ## Logic

  The original implementation of `..`, which creates a natural metavariable for each goal (and does not synthesize defaults) affects things early on, at the stage of `FieldVal`s. Instead of using a `.default` `FieldVal`, it makes a hole via syntax by providing a `.term (mkHole ref)` `FieldVal` for each missing field value.

  We preserve this behavior only for the `isSynthetic := false, useDefaults := false` case. Otherwise, we use the `.default` `FieldVal`—now renamed to `.missing` to reflect its changed function—and intervene mostly within the `ImplicitFields` namespace (previously the `DefaultFields` namespace), where defaults are synthesized. If the variadic hole syntax says not to, we don't propagate the default-synthesizing loop and therefore don't synthesize any defaults. Typically, when the default loop ends with some fields still annotated as missing, an error is thrown (`fields missing: ...`). However, if there's a variadic hole, we simply return from the loop without error; next (whether the loop has run or not) we assign those remaining annotated fields to *new* metavariables, which, in the `isSynthetic := true` case, are well-named and hold all of the metadata we want them to. These are ripe to be used in a `refine` statement.

  The only exception to this flow is how we handle `autoparam`s: autoparams are handled in `elabStruct`, so that's where we intervene as well.

  ## Style

  New code is often written in a "lookahead" fashion, to make it as easy as possible to move this to core, in case it would better belong there. Therefore some cases that don't occur in this elaboration are nonetheless accounted for—for example, the case where variadic hole syntax is absent (where the value of struct.source.implicit is none), and the case where `isSynthetic := false, useDefaults := false`, which is already accounted for by existing `..` syntax. We use a different token (`...`) only to show that this works.

  This modification of `StructInst.lean` also attempts to be "minimally invasive" by intervening in as few places as possible and leaving the existing flow of computation intact.

  ## Locations of changes

  The changes to existing definitions are localized to the following:

  ### Necessary parsing and syntax processing changes

  * The `structInst` term parser was modified to allow variadic hole syntax.

  * `expandStructInstFieldAbbrev`
    * update `$[..%$ell]?` syntax match to accommodate variadic holes

  * type of `implicit` in `Source` structure: `Option Syntax` ⇒ `Option VariadicHoleConfig`
    * originally this held the syntax `..` if present; now it holds information derived from the variadic hole syntax (if present) as opposed to the raw syntax

  * `getStructSource`
    * inserted `getVariadicHoleConfig?` in front of the raw `implicitSource` syntax to process it into a `VariadicHoleConfig`

  * `formatStruct`
    * instead of using a literal `".."` whenever `implicit.isSome`, use the syntax we encountered (stored as one of the fields of `VariadicHoleConfig`)

  ### Logic

  **Simple renamings**

  * The `.default` `FieldVal`, which was used to indicate that fields would be synthesized by the default loop, is renamed to `.missing` for clarity. Likewise `Struct.allDefault` is renamed to `Struct.allMissing` (since it simply checks these `FieldVal`s), and `formatField` formats `.missing` fields via `"<missing>"` instead of via `"<default>"`.

  * We rename the `DefaultFields` namespace to `ImplicitFields`, since this is now where we intervene to handle holes as well.

  **Setup changes**

  * `addMissingFields`, which is responsible for attaching `.missing` to unspecified fields, previously attached a `.term (mkHole stx)` to any missing field whenever `..` was present. Here, we only do so in the `isSynthetic := false, useDefaults := false` case, attaching `.missing` in all other cases (both when we exepct them to be synthesized as defaults and not).

  * `elabStruct` – this function uses `FieldVal`s to 1) generate `expr?`s for each field when possible and 2) apply the structure's constructor to the arguments it finds to build the instance expression. It stops short of synthesizing defaults, inserting a metavariable in both places when it encounters a `.missing` field. However, autoparams for `.missing` values are handled here. We therefore modify that section of the code so that
    * if the variadic hole says to use holes instead of defaults, we don't try the autoparam
    * if it says to use defaults, we try the autoparam in such a way that if it fails we use a hole instead
      * we also need to introduce a new optional `Bool` argument to the internal `cont` function that, when modified from its default, takes a different branch. Otherwise `cont` is untouched, and the original behavior is used when this argument is not specified.
    * if there's no variadic hole, use the original behavior

  **Default loop changes**

  * `propagateLoop` – this is a pass of the loop used for synthesizing defaults, and is responsible for throwing an error when too few fields are specified. If there is a variadic hole, it does not throw that error and simply returns.

  * `propagate` – this sets things up for the loop and executes it.
    * We check the variadic hole config and don't run `propagateLoop` if it says not to. (We start with a `do` to accommodate this.)
    * At the end, if there is a variadic hole, we run `assignRemainingDefaultsToHoles` (a new function which does what you expect)

  ## New Code

  The new functionality is in the `ImplicitFields` section to attach metadata to the goals produced. Currently, we attach the metadata as a `KVMap` to the type of the goal, but this may change. We use this metadata to resolve name conflicts, appending an appropriate index if any existing metavariable is from a structure that shares a field name. This is meant to improve clarity: for example, if `Foo` and `Bar` both have fields `x` and `y`, `refine ({ y := 0, ?.. : Foo}, { x := 1, ?.. : Bar})` will produce goals `x` and `y_1` to show that these are not from the same structure. (This may change if we decide to prefix each goal name with the name of the structure.)

  # Problems

  * Should `trySynthStructInstance?` be run even when `useDefaults` is `false`?

  * what about `bi == .instImplicit`?

  * should metadata be on the type, or somewhere else?

  * is the best way to get a unique id for a syntax instance via getPos? Do we need to do so anyway?

  * should utility-like functions be refactored into other files?

  * Can the docstrings of the original structure instance and `refine` be modified from "within mathlib" somehow?

  * Do I need to add to "authors" at the top or worry about the copyright?

  * What about the linting style?

-/

--!!/ We use parsers in anticipation of this possibly being merged into core.
def vH?dd        := leading_parser "?.." >> Parser.optional Parser.ident
def vH?dd!       := leading_parser "?..!" >> Parser.optional Parser.ident
def vHdd!        := leading_parser "..!"
def vHdd         := leading_parser "..."
def variadicHole := leading_parser (vH?dd <|> vH?dd! <|> vHdd! <|> vHdd)

open Lean.Parser Lean.Parser.Term in
/--
Structure instance. `{ x := e, ... }` assigns `e` to field `x`, which may be
inherited. If `e` is itself a variable called `x`, it can be elided:
`fun x => { x , y := 1 }`.
A *structure update* of an existing value can be given via `with`:
`{ point with x := 1 }`.
The structure type can be specified if not inferable:
`{ x := 1, y := 2 : Point }`.
`?..` will fill fields with automatically-named holes: `{ x := 1, ?.. : Point3D }` will create `?y`, `?z`.
-/
@[term_parser] def structInstWithHoles := leading_parser "{" >> ppHardSpace >> Lean.Parser.optional (atomic (sepBy1 termParser ", " >> " with "))
  >> sepByIndent (structInstFieldAbbrev <|> structInstField) ", " (allowTrailingSep := true)
  >> variadicHole --!! Only apply this elaboration to syntax that has one of these holes
  >> Lean.Parser.optional (" : " >> termParser) >> " }"
--!!\

--!! changed attr name and name
@[macro structInstWithHoles] def expandStructInstWithHolesExpectedType : Macro := fun stx =>
  let expectedArg := stx[4]
  if expectedArg.isNone then
    Macro.throwUnsupported
  else
    let expected := expectedArg[1]
    let stxNew   := stx.setArg 4 mkNullNode
    `(($stxNew : $expected))

--!! changed for WithHoles; would use $[$ell:variadicHole]? if built-in
/-- Expand field abbreviations. Example: `{ x, y := 0 }` expands to `{ x := x, y := 0 }` -/
@[macro structInstWithHoles] def expandStructInstWithHolesFieldAbbrev : Macro
  | `({ $[$srcs,* with]? $fields,* $ell:variadicHole $[: $ty]? }) =>
    if fields.getElems.raw.any (·.getKind == ``Lean.Parser.Term.structInstFieldAbbrev) then do
      let fieldsNew ← fields.getElems.mapM fun
        | `(Parser.Term.structInstFieldAbbrev| $id:ident) =>
          `(Parser.Term.structInstField| $id:ident := $id:ident)
        | field => return field
      `({ $[$srcs,* with]? $fieldsNew,* $ell $[: $ty]? })
    else
      Macro.throwUnsupported
  | _ => Macro.throwUnsupported

/--
  If `stx` is of the form `{ s₁, ..., sₙ with ... }` and `sᵢ` is not a local variable, expand into `let src := sᵢ; { ..., src, ... with ... }`.

  Note that this one is not a `Macro` because we need to access the local context.
-/
private def expandNonAtomicExplicitSources (stx : Syntax) : TermElabM (Option Syntax) := do
  let sourcesOpt := stx[1]
  if sourcesOpt.isNone then
    return none
  else
    let sources := sourcesOpt[0]
    if sources.isMissing then
      throwAbortTerm
    let sources := sources.getSepArgs
    if (← sources.allM fun source => return (← isLocalIdent? source).isSome) then
      return none
    if sources.any (·.isMissing) then
      throwAbortTerm
    return some (← go sources.toList #[])
where
  go (sources : List Syntax) (sourcesNew : Array Syntax) : TermElabM Syntax := do
    match sources with
    | [] =>
      let sources := Syntax.mkSep sourcesNew (mkAtomFrom stx ", ")
      return stx.setArg 1 (stx[1].setArg 0 sources)
    | source :: sources =>
      if (← isLocalIdent? source).isSome then
        go sources (sourcesNew.push source)
      else
        withFreshMacroScope do
          let sourceNew ← `(src)
          let r ← go sources (sourcesNew.push sourceNew)
          `(let src := $source; $r)

structure ExplicitSourceInfo where
  stx        : Syntax
  structName : Name
  deriving Inhabited

--!!/
structure VariadicHoleConfig where
  stx         : TSyntax ``variadicHole
  name        : Option Name := none
  isSynthetic : Bool
  useDefaults : Bool
  deriving Inhabited, Repr
--!!\

structure Source where
  explicit : Array ExplicitSourceInfo -- `s₁ ... sₙ with`
  implicit : Option VariadicHoleConfig --!!
  deriving Inhabited

def Source.isNone : Source → Bool
  | { explicit := #[], implicit := none } => true
  | _ => false

--!!/
def getVariadicHoleConfig? : TSyntax ``variadicHole → Option VariadicHoleConfig
| stx => match stx with
  | `(variadicHole|?..$[$x:ident]?) => some
    {stx, isSynthetic := true, useDefaults := true, name := x.map Syntax.getId}
  | `(variadicHole|?..!$[$x:ident]?) => some
    {stx, isSynthetic := true, useDefaults := false, name := x.map Syntax.getId}
  | `(variadicHole|...) => some
    {stx, isSynthetic := false, useDefaults := true}
  | `(variadicHole|..!) => some
    {stx, isSynthetic := false, useDefaults := false}
  | _ => none --~~? Should this be unreachable!?
--!!\

/-- `optional (atomic (sepBy1 termParser ", " >> " with ")` -/
private def mkSourcesWithSyntax (sources : Array Syntax) : Syntax :=
  let ref := sources[0]!
  let stx := Syntax.mkSep sources (mkAtomFrom ref ", ")
  mkNullNode #[stx, mkAtomFrom ref "with "]

private def getStructSource (structStx : Syntax) : TermElabM Source :=
  withRef structStx do
    let explicitSource := structStx[1]
    let implicitSource := structStx[3]
    let explicit ← if explicitSource.isNone then
      pure #[]
    else
      explicitSource[0].getSepArgs.mapM fun stx => do
        let some src ← isLocalIdent? stx | unreachable!
        addTermInfo' stx src
        let srcType ← whnf (← inferType src)
        tryPostponeIfMVar srcType
        let structName ← getStructureName srcType
        return { stx, structName }
    let implicit :=
      if implicitSource[0].isNone
      then none
      else getVariadicHoleConfig? implicitSource --!!
    return { explicit, implicit }

/--
  We say a `{ ... }` notation is a `modifyOp` if it contains only one
  ```
  def structInstArrayRef := leading_parser "[" >> termParser >>"]"
  ```
-/
private def isModifyOp? (stx : Syntax) : TermElabM (Option Syntax) := do
  let s? ← stx[2].getSepArgs.foldlM (init := none) fun s? arg => do
    /- arg is of the form `structInstFieldAbbrev <|> structInstField` -/
    if arg.getKind == ``Lean.Parser.Term.structInstField then
      /- Remark: the syntax for `structInstField` is
         ```
         def structInstLVal   := leading_parser (ident <|> numLit <|> structInstArrayRef) >> many (group ("." >> (ident <|> numLit)) <|> structInstArrayRef)
         def structInstField  := leading_parser structInstLVal >> " := " >> termParser
         ```
      -/
      let lval := arg[0]
      let k    := lval[0].getKind
      if k == ``Lean.Parser.Term.structInstArrayRef then
        match s? with
        | none   => return some arg
        | some s =>
          if s.getKind == ``Lean.Parser.Term.structInstArrayRef then
            throwErrorAt arg "invalid \{...} notation, at most one `[..]` at a given level"
          else
            throwErrorAt arg "invalid \{...} notation, can't mix field and `[..]` at a given level"
      else
        match s? with
        | none   => return some arg
        | some s =>
          if s.getKind == ``Lean.Parser.Term.structInstArrayRef then
            throwErrorAt arg "invalid \{...} notation, can't mix field and `[..]` at a given level"
          else
            return s?
    else
      return s?
  match s? with
  | none   => return none
  | some s => if s[0][0].getKind == ``Lean.Parser.Term.structInstArrayRef then return s? else return none

private def elabModifyOp (stx modifyOp : Syntax) (sources : Array ExplicitSourceInfo) (expectedType? : Option Expr) : TermElabM Expr := do
  if sources.size > 1 then
    throwError "invalid \{...} notation, multiple sources and array update is not supported."
  let cont (val : Syntax) : TermElabM Expr := do
    let lval := modifyOp[0][0]
    let idx  := lval[1]
    let self := sources[0]!.stx
    let stxNew ← `($(self).modifyOp (idx := $idx) (fun s => $val))
    trace[Elab.struct.modifyOp] "{stx}\n===>\n{stxNew}"
    withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
  let rest := modifyOp[0][1]
  if rest.isNone then
    cont modifyOp[2]
  else
    let s ← `(s)
    let valFirst  := rest[0]
    let valFirst  := if valFirst.getKind == ``Lean.Parser.Term.structInstArrayRef then valFirst else valFirst[1]
    let restArgs  := rest.getArgs
    let valRest   := mkNullNode restArgs[1:restArgs.size]
    let valField  := modifyOp.setArg 0 <| mkNode ``Parser.Term.structInstLVal #[valFirst, valRest]
    let valSource := mkSourcesWithSyntax #[s]
    let val       := stx.setArg 1 valSource
    let val       := val.setArg 2 <| mkNullNode #[valField]
    trace[Elab.struct.modifyOp] "{stx}\nval: {val}"
    cont val

/--
  Get structure name.
  This method tries to postpone execution if the expected type is not available.

  If the expected type is available and it is a structure, then we use it.
  Otherwise, we use the type of the first source. -/
private def getStructName (expectedType? : Option Expr) (sourceView : Source) : TermElabM Name := do
  tryPostponeIfNoneOrMVar expectedType?
  let useSource : Unit → TermElabM Name := fun _ => do
    unless sourceView.explicit.isEmpty do
      return sourceView.explicit[0]!.structName
    match expectedType? with
    | some expectedType => throwUnexpectedExpectedType expectedType
    | none => throwUnknownExpectedType
  match expectedType? with
  | none => useSource ()
  | some expectedType =>
    let expectedType ← whnf expectedType
    match expectedType.getAppFn with
    | Expr.const constName _ =>
      unless isStructure (← getEnv) constName do
        throwError "invalid \{...} notation, structure type expected{indentExpr expectedType}"
      return constName
    | _                      => useSource ()
where
  throwUnknownExpectedType :=
    throwError "invalid \{...} notation, expected type is not known"
  throwUnexpectedExpectedType type (kind := "expected") := do
    let type ← instantiateMVars type
    if type.getAppFn.isMVar then
      throwUnknownExpectedType
    else
      throwError "invalid \{...} notation, {kind} type is not of the form (C ...){indentExpr type}"

inductive FieldLHS where
  | fieldName  (ref : Syntax) (name : Name)
  | fieldIndex (ref : Syntax) (idx : Nat)
  | modifyOp   (ref : Syntax) (index : Syntax)
  deriving Inhabited

instance : ToFormat FieldLHS := ⟨fun lhs =>
  match lhs with
  | .fieldName _ n  => format n
  | .fieldIndex _ i => format i
  | .modifyOp _ i   => "[" ++ i.prettyPrint ++ "]"⟩

inductive FieldVal (σ : Type) where
  | term  (stx : Syntax) : FieldVal σ
  | nested (s : σ)       : FieldVal σ
  | missing              : FieldVal σ -- mark that field is missing
  deriving Inhabited

structure Field (σ : Type) where
  ref   : Syntax
  lhs   : List FieldLHS
  val   : FieldVal σ
  expr? : Option Expr := none
  deriving Inhabited

def Field.isSimple {σ} : Field σ → Bool
  | { lhs := [_], .. } => true
  | _                  => false

inductive Struct where
  /-- Remark: the field `params` is used for .missing value propagation. It is initially empty, and then set at `elabStruct`. -/
  | mk (ref : Syntax) (structName : Name) (params : Array (Name × Expr)) (fields : List (Field Struct)) (source : Source)
  deriving Inhabited

abbrev Fields := List (Field Struct)

def Struct.ref : Struct → Syntax
  | ⟨ref, _, _, _, _⟩ => ref

def Struct.structName : Struct → Name
  | ⟨_, structName, _, _, _⟩ => structName

def Struct.params : Struct → Array (Name × Expr)
  | ⟨_, _, params, _, _⟩ => params

def Struct.fields : Struct → Fields
  | ⟨_, _, _, fields, _⟩ => fields

def Struct.source : Struct → Source
  | ⟨_, _, _, _, s⟩ => s

/-- `true` iff all fields of the given structure are marked as `missing` -/
partial def Struct.allMissing (s : Struct) : Bool :=
  s.fields.all fun { val := val,  .. } => match val with
    | .term _   => false
    | .missing  => true
    | .nested s => allMissing s

def formatField (formatStruct : Struct → Format) (field : Field Struct) : Format :=
  Format.joinSep field.lhs " . " ++ " := " ++
    match field.val with
    | .term v   => v.prettyPrint
    | .nested s => formatStruct s
    | .missing  => "<missing>" --!!

partial def formatStruct : Struct → Format
  | ⟨_, _,          _, fields, source⟩ =>
    let fieldsFmt := Format.joinSep (fields.map (formatField formatStruct)) ", "
--!! changed to use stored syntax
    let implicitFmt := match source.implicit with
    | some v => format v.stx
    | none   => ""
    if source.explicit.isEmpty then
      "{" ++ fieldsFmt ++ implicitFmt ++ "}"
    else
      "{" ++ format (source.explicit.map (·.stx)) ++ " with " ++ fieldsFmt ++ implicitFmt ++ "}"

instance : ToFormat Struct := ⟨formatStruct⟩
instance : ToString Struct := ⟨toString ∘ format⟩

instance : ToFormat (Field Struct) := ⟨formatField formatStruct⟩
instance : ToString (Field Struct) := ⟨toString ∘ format⟩

/-
Recall that `structInstField` elements have the form
```
   def structInstField  := leading_parser structInstLVal >> " := " >> termParser
   def structInstLVal   := leading_parser (ident <|> numLit <|> structInstArrayRef) >> many (("." >> (ident <|> numLit)) <|> structInstArrayRef)
   def structInstArrayRef := leading_parser "[" >> termParser >>"]"
```
-/
-- Remark: this code relies on the fact that `expandStruct` only transforms `fieldLHS.fieldName`
def FieldLHS.toSyntax (first : Bool) : FieldLHS → Syntax
  | .modifyOp   stx _    => stx
  | .fieldName  stx name => if first then mkIdentFrom stx name else mkGroupNode #[mkAtomFrom stx ".", mkIdentFrom stx name]
  | .fieldIndex stx _    => if first then stx else mkGroupNode #[mkAtomFrom stx ".", stx]

def FieldVal.toSyntax : FieldVal Struct → Syntax
  | .term stx => stx
  | _         => unreachable!

def Field.toSyntax : Field Struct → Syntax
  | field =>
    let stx := field.ref
    let stx := stx.setArg 2 field.val.toSyntax
    match field.lhs with
    | first::rest => stx.setArg 0 <| mkNullNode #[first.toSyntax true, mkNullNode <| rest.toArray.map (FieldLHS.toSyntax false) ]
    | _ => unreachable!

private def toFieldLHS (stx : Syntax) : MacroM FieldLHS :=
  if stx.getKind == ``Lean.Parser.Term.structInstArrayRef then
    return FieldLHS.modifyOp stx stx[1]
  else
    -- Note that the representation of the first field is different.
    let stx := if stx.getKind == groupKind then stx[1] else stx
    if stx.isIdent then
      return FieldLHS.fieldName stx stx.getId.eraseMacroScopes
    else match stx.isFieldIdx? with
      | some idx => return FieldLHS.fieldIndex stx idx
      | none     => Macro.throwError "unexpected structure syntax"

private def mkStructView (stx : Syntax) (structName : Name) (source : Source) : MacroM Struct := do
  /- Recall that `stx` is of the form
     ```
     leading_parser "{" >> optional (atomic (sepBy1 termParser ", " >> " with "))
                 >> sepByIndent (structInstFieldAbbrev <|> structInstField) ...
                --!!
                 >> variadicHole
                 >> optional (" : " >> termParser)
                 >> " }"
     ```

     This method assumes that `structInstFieldAbbrev` had already been expanded.
  -/
  let fields ← stx[2].getSepArgs.toList.mapM fun fieldStx => do
    let val      := fieldStx[2]
    let first    ← toFieldLHS fieldStx[0][0]
    let rest     ← fieldStx[0][1].getArgs.toList.mapM toFieldLHS
    return { ref := fieldStx, lhs := first :: rest, val := FieldVal.term val : Field Struct }
  return ⟨stx, structName, #[], fields, source⟩

def Struct.modifyFieldsM {m : Type → Type} [Monad m] (s : Struct) (f : Fields → m Fields) : m Struct :=
  match s with
  | ⟨ref, structName, params, fields, source⟩ => return ⟨ref, structName, params, (← f fields), source⟩

def Struct.modifyFields (s : Struct) (f : Fields → Fields) : Struct :=
  Id.run <| s.modifyFieldsM f

def Struct.setFields (s : Struct) (fields : Fields) : Struct :=
  s.modifyFields fun _ => fields

def Struct.setParams (s : Struct) (ps : Array (Name × Expr)) : Struct :=
  match s with
  | ⟨ref, structName, _, fields, source⟩ => ⟨ref, structName, ps, fields, source⟩

private def expandCompositeFields (s : Struct) : Struct :=
  s.modifyFields fun fields => fields.map fun field => match field with
    | { lhs := .fieldName _ (.str Name.anonymous ..) :: _, .. } => field
    | { lhs := .fieldName ref n@(.str ..) :: rest, .. } =>
      let newEntries := n.components.map <| FieldLHS.fieldName ref
      { field with lhs := newEntries ++ rest }
    | _ => field

private def expandNumLitFields (s : Struct) : TermElabM Struct :=
  s.modifyFieldsM fun fields => do
    let env ← getEnv
    let fieldNames := getStructureFields env s.structName
    fields.mapM fun field => match field with
      | { lhs := .fieldIndex ref idx :: rest, .. } =>
        if idx == 0 then throwErrorAt ref "invalid field index, index must be greater than 0"
        else if idx > fieldNames.size then throwErrorAt ref "invalid field index, structure has only #{fieldNames.size} fields"
        else return { field with lhs := .fieldName ref fieldNames[idx - 1]! :: rest }
      | _ => return field

/-- For example, consider the following structures:
   ```
   structure A where
     x : Nat

   structure B extends A where
     y : Nat

   structure C extends B where
     z : Bool
   ```
   This method expands parent structure fields using the path to the parent structure.
   For example,
   ```
   { x := 0, y := 0, z := true : C }
   ```
   is expanded into
   ```
   { toB.toA.x := 0, toB.y := 0, z := true : C }
   ```
-/
private def expandParentFields (s : Struct) : TermElabM Struct := do
  let env ← getEnv
  s.modifyFieldsM fun fields => fields.mapM fun field => do match field with
    | { lhs := .fieldName ref fieldName :: _,    .. } =>
      addCompletionInfo <| CompletionInfo.fieldId ref fieldName (← getLCtx) s.structName
      match findField? env s.structName fieldName with
      | none => throwErrorAt ref "'{fieldName}' is not a field of structure '{s.structName}'"
      | some baseStructName =>
        if baseStructName == s.structName then pure field
        else match getPathToBaseStructure? env baseStructName s.structName with
          | some path =>
            let path := path.map fun funName => match funName with
              | .str _ s => .fieldName ref (Name.mkSimple s)
              | _        => unreachable!
            return { field with lhs := path ++ field.lhs }
          | _ => throwErrorAt ref "failed to access field '{fieldName}' in parent structure"
    | _ => return field

private abbrev FieldMap := HashMap Name Fields

private def mkFieldMap (fields : Fields) : TermElabM FieldMap :=
  fields.foldlM (init := {}) fun fieldMap field =>
    match field.lhs with
    | .fieldName _ fieldName :: _    =>
      match fieldMap.find? fieldName with
      | some (prevField::restFields) =>
        if field.isSimple || prevField.isSimple then
          throwErrorAt field.ref "field '{fieldName}' has already been specified"
        else
          return fieldMap.insert fieldName (field::prevField::restFields)
      | _ => return fieldMap.insert fieldName [field]
    | _ => unreachable!

private def isSimpleField? : Fields → Option (Field Struct)
  | [field] => if field.isSimple then some field else none
  | _       => none

private def getFieldIdx (structName : Name) (fieldNames : Array Name) (fieldName : Name) : TermElabM Nat := do
  match fieldNames.findIdx? fun n => n == fieldName with
  | some idx => return idx
  | none     => throwError "field '{fieldName}' is not a valid field of '{structName}'"

def mkProjStx? (s : Syntax) (structName : Name) (fieldName : Name) : TermElabM (Option Syntax) := do
  if (findField? (← getEnv) structName fieldName).isNone then
    return none
  return some <| mkNode ``Parser.Term.proj #[s, mkAtomFrom s ".", mkIdentFrom s fieldName]

def findField? (fields : Fields) (fieldName : Name) : Option (Field Struct) :=
  fields.find? fun field =>
    match field.lhs with
    | [.fieldName _ n] => n == fieldName
    | _                => false

mutual

  private partial def groupFields (s : Struct) : TermElabM Struct := do
    let env ← getEnv
    withRef s.ref do
    s.modifyFieldsM fun fields => do
      let fieldMap ← mkFieldMap fields
      fieldMap.toList.mapM fun ⟨fieldName, fields⟩ => do
        match isSimpleField? fields with
        | some field => pure field
        | none =>
          let substructFields := fields.map fun field => { field with lhs := field.lhs.tail! }
          let field := fields.head!
          match Lean.isSubobjectField? env s.structName fieldName with
          | some substructName =>
            let substruct := Struct.mk s.ref substructName #[] substructFields s.source
            let substruct ← expandStruct substruct
            pure { field with lhs := [field.lhs.head!], val := FieldVal.nested substruct }
          | none =>
            let updateSource (structStx : Syntax) : TermElabM Syntax := do
              let sourcesNew ← s.source.explicit.filterMapM fun source => mkProjStx? source.stx source.structName fieldName
              let explicitSourceStx := if sourcesNew.isEmpty then mkNullNode else mkSourcesWithSyntax sourcesNew
              let implicitSourceStx := s.source.implicit.map (·.stx) |>.getD mkNullNode --!!
              return (structStx.setArg 1 explicitSourceStx).setArg 3 implicitSourceStx
            let valStx := s.ref -- construct substructure syntax using s.ref as template
            let valStx := valStx.setArg 4 mkNullNode -- erase optional expected type
            let args   := substructFields.toArray.map (·.toSyntax)
            let valStx := valStx.setArg 2 (mkNullNode <| mkSepArray args (mkAtom ","))
            let valStx ← updateSource valStx
            return { field with lhs := [field.lhs.head!], val := FieldVal.term valStx }

  private partial def addMissingFields (s : Struct) : TermElabM Struct := do
    let env ← getEnv
    let fieldNames := getStructureFields env s.structName
    let ref := s.ref.mkSynthetic
--~~? does this mean that ref no longer functions as an identifier for the original instance?
    withRef ref do
      let fields ← fieldNames.foldlM (init := []) fun fields fieldName => do
        match findField? s.fields fieldName with
        | some field => return field::fields
        | none       =>
          let addField (val : FieldVal Struct) : TermElabM Fields := do
            return { ref, lhs := [FieldLHS.fieldName ref fieldName], val := val } :: fields
          match Lean.isSubobjectField? env s.structName fieldName with
          | some substructName =>
            -- If one of the sources has the subobject field, use it
            if let some val ← s.source.explicit.findSomeM? fun source => mkProjStx? source.stx source.structName fieldName then
              addField (FieldVal.term val)
            else
              let substruct := Struct.mk ref substructName #[] [] s.source
              let substruct ← expandStruct substruct
              addField (FieldVal.nested substruct)
          | none =>
            if let some val ← s.source.explicit.findSomeM? fun source => mkProjStx? source.stx source.structName fieldName then
              addField (FieldVal.term val)
            else
              --!!/ Use hole syntax as a term in the natural, no-defaults (..) case; otherwise add it as a missing field.
              match s.source.implicit with
              | some { isSynthetic := false, useDefaults := false, .. } =>
                addField (FieldVal.term (mkHole ref))
              | _ => addField FieldVal.missing
              --!!\
      return s.setFields fields.reverse

  private partial def expandStruct (s : Struct) : TermElabM Struct := do
    let s := expandCompositeFields s
    let s ← expandNumLitFields s
    let s ← expandParentFields s
    let s ← groupFields s
    addMissingFields s

end

structure CtorHeaderResult where
  ctorFn     : Expr
  ctorFnType : Expr
  instMVars  : Array MVarId
  params     : Array (Name × Expr)

private def mkCtorHeaderAux : Nat → Expr → Expr → Array MVarId → Array (Name × Expr) → TermElabM CtorHeaderResult
  | 0,   type, ctorFn, instMVars, params => return { ctorFn , ctorFnType := type, instMVars, params }
  | n+1, type, ctorFn, instMVars, params => do
    match (← whnfForall type) with
    | .forallE paramName d b c =>
      match c with
      | .instImplicit =>
        let a ← mkFreshExprMVar d .synthetic
        mkCtorHeaderAux n (b.instantiate1 a) (mkApp ctorFn a) (instMVars.push a.mvarId!) (params.push (paramName, a))
      | _ =>
        let a ← mkFreshExprMVar d
        mkCtorHeaderAux n (b.instantiate1 a) (mkApp ctorFn a) instMVars (params.push (paramName, a))
    | _ => throwError "unexpected constructor type"

private partial def getForallBody : Nat → Expr → Option Expr
  | i+1, .forallE _ _ b _ => getForallBody i b
  | _+1, _                => none
  | 0,   type             => type

private def propagateExpectedType (type : Expr) (numFields : Nat) (expectedType? : Option Expr) : TermElabM Unit := do
  match expectedType? with
  | none              => return ()
  | some expectedType =>
    match getForallBody numFields type with
      | none           => pure ()
      | some typeBody =>
        unless typeBody.hasLooseBVars do
          discard <| isDefEq expectedType typeBody

private def mkCtorHeader (ctorVal : ConstructorVal) (expectedType? : Option Expr) : TermElabM CtorHeaderResult := do
  let us ← mkFreshLevelMVars ctorVal.levelParams.length
  let val  := Lean.mkConst ctorVal.name us
  let type ← instantiateTypeLevelParams (ConstantInfo.ctorInfo ctorVal) us
  let r ← mkCtorHeaderAux ctorVal.numParams type val #[] #[]
  propagateExpectedType r.ctorFnType ctorVal.numFields expectedType?
  synthesizeAppInstMVars r.instMVars r.ctorFn
  return r

def markDefaultMissing (e : Expr) : Expr :=
  mkAnnotation `structInstDefault e

def defaultMissing? (e : Expr) : Option Expr :=
  annotation? `structInstDefault e

def throwFailedToElabField {α} (fieldName : Name) (structName : Name) (msgData : MessageData) : TermElabM α :=
  throwError "failed to elaborate field '{fieldName}' of '{structName}, {msgData}"

def trySynthStructInstance? (s : Struct) (expectedType : Expr) : TermElabM (Option Expr) := do
  if !s.allMissing then
    return none
  else
    try synthInstance? expectedType catch _ => return none

--!!/ By Mario Carneiro
def toSyntax (e : Expr) (type? : Option Expr := none) : TermElabM Syntax := withFreshMacroScope do
  let stx ← `(?a)
  let mvar ← elabTerm stx type?
  mvar.mvarId!.assign e
  pure stx
--!!\

structure ElabStructResult where
  val       : Expr
  struct    : Struct
  instMVars : Array MVarId

elab "faq_throw_error" : tactic =>
  Lean.Elab.Tactic.withMainContext do
let goal ← Lean.Elab.Tactic.getMainGoal
Lean.Meta.throwTacticEx `faq_throw_error goal "throwing an error at the current goal"

private partial def elabStruct (s : Struct) (expectedType? : Option Expr) : TermElabM ElabStructResult := withRef s.ref do
  let env ← getEnv
  let vhc? := s.source.implicit
  let ctorVal := getStructureCtor env s.structName
  if isPrivateNameFromImportedModule env ctorVal.name then
    throwError "invalid \{...} notation, constructor for `{s.structName}` is marked as private"
  -- We store the parameters at the resulting `Struct`. We use this information during default value propagation.
  let { ctorFn, ctorFnType, params, .. } ← mkCtorHeader ctorVal expectedType?
  let (e, _, fields, instMVars) ← s.fields.foldlM (init := (ctorFn, ctorFnType, [], #[])) fun (e, type, fields, instMVars) field => do
    match field.lhs with
    | [.fieldName ref fieldName] =>
      let type ← whnfForall type
      trace[Elab.struct] "elabStruct {field}, {type}"
      match type with
      | .forallE _ d b bi =>
      --!! added updateField argument
        let cont (val : Expr) (field : Field Struct) (instMVars := instMVars) (updateField := true) : TermElabM (Expr × Expr × Fields × Array MVarId) := do
          pushInfoTree <| InfoTree.node (children := {}) <| Info.ofFieldInfo {
            projName := s.structName.append fieldName, fieldName, lctx := (← getLCtx), val, stx := ref }
          let e     := mkApp e val
          let type  := b.instantiate1 val
          let field := if updateField then { field with expr? := some val } else field --!!
          return (e, type, field::fields, instMVars)
        match field.val with
        | .term stx =>
          cont (← elabTermEnsuringType stx d.consumeTypeAnnotations) field
        | .nested s  =>
          --~~? Should this remain in all cases? Should the definition be changed when useDefaults is false? When might it be encountered?
          let inst? := if vhc?.all (·.useDefaults) then
            (← trySynthStructInstance? s d) else none
          match inst? with
          | some val =>
            cont val { field with val := FieldVal.term (mkHole field.ref) }
          | none     =>
            let { val, struct := sNew, instMVars := instMVarsNew } ← elabStruct s (some d)
            let val ← ensureHasType d val
            cont val { field with val := FieldVal.nested sNew } (instMVars ++ instMVarsNew)
        | .missing  =>
        --~~? Should this be moved to the default section? Assuming not:
          match d.getAutoParamTactic? with
          | some (.const tacticDecl ..) =>
            let d := (d.getArg! 0).consumeTypeAnnotations
            if vhc?.all (·.useDefaults) then --!!
              match evalSyntaxConstant env (← getOptions) tacticDecl with
              | .error err       => throwError err
              | .ok tacticSyntax =>
              --~~? we need to be able to try the tactic and create a metavariable if it fails. but WHEN do we try the tactic, and how do we introduce it correctly? Timing might be tricky. Should we use syntax and a tactic which introduces a metavariable, or should we have a different way of introducing the metavariable by, say, amending the Expression in `cont` post `← elabTermEnsuringType ...`?
              --!!/
                if vhc?.isSome then
                  --~~?[...] need to do a couple things here. I think: make the tactic syntax the val, but also...hmmm. we need to use one in the expression and one in the field maybe? do tactics only get evaluated after?
                  let val := (← mkFreshExprMVar (some d) .synthetic)
                  let stx ← `(by first | $tacticSyntax | exact $(← toSyntax val)) --`(by first | $tacticSyntax | refine $(← toSyntax val))
                  cont (← elabTermEnsuringType stx d) {field with expr? := some (markDefaultMissing val)} (updateField := false)
                else
                --!!\
                  let stx ← `(by $tacticSyntax)
                  cont (← elabTermEnsuringType stx d) field
            --!!/
            else
              let val ← withRef field.ref <| mkFreshExprMVar (some d)
              cont (markDefaultMissing val) field
            --!!\
          | _ =>
            if bi == .instImplicit then
            --~~? When might this be encountered? Do we need to distinguish it somehow? OR adjust the timing of our metavariable creation?
            --~~? Why is it not some d?
              let val ← withRef field.ref <| mkFreshExprMVar d .synthetic
              trace[Elab.struct] ".instImplicit ({val})"
              cont val field (instMVars.push val.mvarId!)
            else
            --~ otherwise, make a metavariable and MARK AS DEFAULT.
              let val ← withRef field.ref <| mkFreshExprMVar (some d)
              cont (markDefaultMissing val) field
      | _ => withRef field.ref <| throwFailedToElabField fieldName s.structName m!"unexpected constructor type{indentExpr type}"
    | _ => throwErrorAt field.ref "unexpected unexpanded structure field"
  return { val := e, struct := s.setFields fields.reverse |>.setParams params, instMVars }

namespace ImplicitFields

structure Context where
  -- We must search for default values overriden in derived structures
  structs : Array Struct := #[]
  allStructNames : Array Name := #[]
  /--
  Consider the following example:
  ```
  structure A where
    x : Nat := 1

  structure B extends A where
    y : Nat := x + 1
    x := y + 1

  structure C extends B where
    z : Nat := 2*y
    x := z + 3
  ```
  And we are trying to elaborate a structure instance for `C`. There are default values for `x` at `A`, `B`, and `C`.
  We say the default value at `C` has distance 0, the one at `B` distance 1, and the one at `A` distance 2.
  The field `maxDistance` specifies the maximum distance considered in a round of Default field computation.
  Remark: since `C` does not set a default value of `y`, the default value at `B` is at distance 0.

  The fixpoint for setting default values works in the following way.
  - Keep computing default values using `maxDistance == 0`.
  - We increase `maxDistance` whenever we failed to compute a new default value in a round.
  - If `maxDistance > 0`, then we interrupt a round as soon as we compute some default value.
    We use depth-first search.
  - We sign an error if no progress is made when `maxDistance` == structure hierarchy depth (2 in the example above).
  -/
  maxDistance : Nat := 0

structure State where
  progress : Bool := false

partial def collectStructNames (struct : Struct) (names : Array Name) : Array Name :=
  let names := names.push struct.structName
  struct.fields.foldl (init := names) fun names field =>
    match field.val with
    | .nested struct => collectStructNames struct names
    | _ => names

partial def getHierarchyDepth (struct : Struct) : Nat :=
  struct.fields.foldl (init := 0) fun max field =>
    match field.val with
    | .nested struct => Nat.max max (getHierarchyDepth struct + 1)
    | _ => max

def isDefaultMissing? [Monad m] [MonadMCtx m] (field : Field Struct) : m Bool := do
  if let some expr := field.expr? then
    if let some (.mvar mvarId) := defaultMissing? expr then
      unless (← mvarId.isAssigned) do
        return true
  return false

partial def findDefaultMissing? [Monad m] [MonadMCtx m] (struct : Struct) : m (Option (Field Struct)) :=
  struct.fields.findSomeM? fun field => do
   match field.val with
   | .nested struct => findDefaultMissing? struct
   | _ => return if (← isDefaultMissing? field) then field else none

partial def allDefaultMissing [Monad m] [MonadMCtx m] (struct : Struct) : m (Array (Field Struct)) :=
  go struct *> get |>.run' #[]
where
  go (struct : Struct) : StateT (Array (Field Struct)) m Unit :=
    for field in struct.fields do
      if let .nested struct := field.val then
        go struct
      else if (← isDefaultMissing? field) then
        modify (·.push field)

def getFieldName (field : Field Struct) : Name :=
  match field.lhs with
  | [.fieldName _ fieldName] => fieldName
  | _ => unreachable!

abbrev M := ReaderT Context (StateRefT State TermElabM)

def isRoundDone : M Bool := do
  return (← get).progress && (← read).maxDistance > 0

def getFieldValue? (struct : Struct) (fieldName : Name) : Option Expr :=
  struct.fields.findSome? fun field =>
    if getFieldName field == fieldName then
      field.expr?
    else
      none

--!!/
--~~? Metadata on a metavariable should be able to be checked from wherever we like. So where should it be? Right now I put it on the type. Where else could it be? LocalInstances? Would that be better?
structure FieldHoleMData where
  index      : Nat
  structRef  : Syntax
  fieldRef   : Syntax
  structName : Name
  fieldName  : Name
  prefixName : Name

def mkFieldHoleMData (index : Nat) (field : Field Struct) (struct : Struct) : FieldHoleMData :=
  {
    index,
    structRef  := struct.ref
    fieldRef   := field.ref
    structName := struct.structName
    fieldName  := getFieldName field
    prefixName := match struct.source.implicit with
                  | some {name := some prefixName, ..} => prefixName
                  | _ => Name.anonymous
  }

open KVMap in
def getFieldHoleMDataFromMVar? (decl : MetavarDecl) : Option FieldHoleMData :=
  match decl.type with
  | .mdata md _ =>
    if getBool md `fieldHole then
      some
      {
        index      := getNat md `index
        structRef  := getSyntax md `structRef
        fieldRef   := getSyntax md `fieldRef
        structName := getName md `structName
        fieldName  := getName md `fieldName
        prefixName := getName md `prefixName
      }
    else none
  | _ => none

def isFieldHole (decl : MetavarDecl) : Bool :=
  match decl.type with
  | .mdata md _ => KVMap.getBool md `fieldHole
  | _           => false

/-- Merges two `KVMap`s, overwriting the value of any shared keys with the values given in the second `KVMap`.
-/
def mergeKVMap : KVMap → KVMap → KVMap :=
  fun m₀ m₁ => Id.run do
    let mut m := m₀
    for (name, data) in m₁ do
      m := KVMap.insert m name data
    return m
/-- Turns a list of key-value pairs (e.g. ``[(`a, ofBool true), (`b, ofNat 2), ...]``) into a `KVMap`.}-/
def toKVMap : List (Name × DataValue) → KVMap
| l => l.foldl (fun m (n, d) => KVMap.insert m n d) {}

open DataValue in
def mkFieldHoleMDataKVMap (f : FieldHoleMData) : KVMap :=
  toKVMap [
    (`fieldHole  , ofBool   true        ),
    (`index      , ofNat    f.index     ),
    (`structRef  , ofSyntax f.structRef ),
    (`fieldRef   , ofSyntax f.fieldRef  ),
    (`structName , ofName   f.structName),
    (`fieldName  , ofName   f.fieldName ),
    (`prefixName , ofName   f.prefixName)
  ]

/-- Creates a metavariable with `metadata` attached to its `type`. If there's any existing metadata on `type`, `metadata` is preferentially merged into it. -/
def mkFreshExprMVarWithMData (type : Expr) (metadata : KVMap) (kind : MetavarKind := default) (userName := Name.anonymous) :=
  let annotatedType :=
    match type with
    | .mdata m e =>
      let merge := mergeKVMap m metadata
      Expr.mdata merge e
    | _          =>
      Expr.mdata metadata type
  mkFreshExprMVar annotatedType (kind := kind) (userName := userName)

def mkFreshFieldNamedMVar (type : Expr) (index : Nat) (prefixName : Option Name) (field : Field Struct) (struct : Struct) :=
  let fieldHoleMData := mkFieldHoleMDataKVMap <| mkFieldHoleMData index field struct
  let name :=
    match prefixName with
    | some x => x ++ (getFieldName field)
    --~~? Prefix by struct name?
    | none   => /- struct.structName ++ -/ getFieldName field
  let name := if index == 0 then name else name.appendIndexAfter index
  mkFreshExprMVarWithMData type fieldHoleMData (kind := .syntheticOpaque) (userName := name)

def fieldsOverlap (env : Environment) (structName₀ : Name) (structName₁ : Name) : Bool :=
  let fields₀ := getStructureFieldsFlattened env structName₀ false
  let fields₁ := getStructureFieldsFlattened env structName₁ false
  fields₀.any (fun field => fields₁.contains field)

--~~ Monadic code for tracing:
def getConflictingIndex? (env : Environment) (s : Struct) (prefixName : Name) (decl : MetavarDecl) : TermElabM (Option Nat) := do
  let fieldHoleMData? := getFieldHoleMDataFromMVar? decl
  --~~ clean this up
  match fieldHoleMData? with
  | some fieldHoleMData =>
    --~~? Is it necessary to check if two goals come from the same `?..`? It seems so far like it's not.
    let cond1 := true --Lean.Syntax.getPos? s.ref != Lean.Syntax.getPos? fieldHoleMData.structRef
    let cond2 := prefixName == fieldHoleMData.prefixName
    let cond3 := fieldsOverlap env s.structName (fieldHoleMData.structName)
    trace[Elab.struct] "goal name conflict for {fieldHoleMData.structName}: {cond1} && {cond2} && {cond3}"
    if cond1 && cond2 && cond3
    then return some fieldHoleMData.index
    else return none
  | none => return none

def nextIndexGivenCollisions (env : Environment) (mctx : MetavarContext) (s : Struct) : TermElabM Nat := do
  let prefixName := match s.source.implicit with
  | some { name := some prefixName, .. } => prefixName
  | _ => Name.anonymous
  let conflictingIndex : (Option Nat) ← mctx.decls.foldl
    (fun i? _ decl => do
      let i'? ← getConflictingIndex? env s prefixName decl
      return (Option.merge max (← i?) i'?)) (pure none)
  match conflictingIndex with
  | some i => return i+1
  | none   => return 0

def assignRemainingDefaultsToHoles (struct : Struct) : TermElabM Unit :=
--~~? withRef?
--~~? If so, do we use a synthetic ref or not? What's with that?
  withRef struct.ref do
  match struct.source.implicit with
  | some vhc =>
    let index ← nextIndexGivenCollisions (← getEnv) (← getMCtx) struct
    --~~could refactor so that we get the mvarIds in the range along with the check that they exist in allDefaultMissing
    for field in (← allDefaultMissing struct) do
      match field.expr? with
      | some expr =>
        match defaultMissing? expr with
        | some (.mvar mvarId) =>
          let type := (← getMVarDecl mvarId).type
          --~~? should these be withRef? Why or why not?
          if vhc.isSynthetic then
            mvarId.assign (← withRef field.ref <| mkFreshFieldNamedMVar type index vhc.name field struct)
          else
          --~~? Do we need a new hole? Or can we just leave it as-is?
            let newHole ← withRef field.ref <| mkFreshExprMVar type (kind := .natural)
            mvarId.assign newHole
            registerMVarErrorHoleInfo newHole.mvarId! struct.ref
        | _ => unreachable!
      | none => unreachable!
  | none => return ()

-- def getConflictingIndex? (env : Environment) (s : Struct) (prefixName : Name) (decl : MetavarDecl) : Option Nat :=
--   let fieldHoleMData? := getFieldHoleMDataFromMVar? decl
--   --~~ clean this up
--   match fieldHoleMData? with
--   | some fieldHoleMData =>
--     if s.ref != fieldHoleMData.structRef
--       && prefixName == fieldHoleMData.prefixName
--       && (fieldsOverlap env s.structName (fieldHoleMData.structName))
--     then fieldHoleMData.index
--     else none
--   | none => none

-- def nextIndexGivenCollisions (env : Environment) (mctx : MetavarContext) (s : Struct) : Nat :=
--   let prefixName := match s.source.implicit with
--   | some { name := some prefixName, ..} => prefixName
--   | _ => Name.anonymous
--   let conflictingIndex := mctx.decls.foldl
--     (fun i? _ decl =>
--       Option.merge max i? (getConflictingIndex? env s prefixName decl)) none
--   match conflictingIndex with
--   | some i => i+1
--   | none   => 0

-- def assignRemainingDefaultsToHoles (struct : Struct) : TermElabM Unit :=
-- --~~? withRef?
-- --~~? If so, do we use a synthetic ref or not? What's with that?
--   withRef struct.ref do
--   match struct.source.implicit with
--   | some vhc =>
--     let index := nextIndexGivenCollisions (← getEnv) (← getMCtx) struct
--     --~~could refactor so that we get the mvarIds in the range along with the check that they exist in allDefaultMissing
--     for field in (← allDefaultMissing struct) do
--       match field.expr? with
--       | some expr =>
--         match defaultMissing? expr with
--         | some (.mvar mvarId) =>
--           let type := (← getMVarDecl mvarId).type
--           --~~? should these be withRef? Why or why not?
--           if vhc.isSynthetic then
--             mvarId.assign (← withRef field.ref <| mkFreshFieldNamedMVar type index vhc.name field struct)
--           else
--           --~~? Do we need a new hole?
--             let newHole ← withRef field.ref <| mkFreshExprMVar type (kind := .natural)
--             mvarId.assign newHole
--             registerMVarErrorHoleInfo newHole.mvarId! struct.ref
--         | _ => unreachable!
--       | none => unreachable!
--   | none => return ()
--!!\

partial def mkDefaultValueAux? (struct : Struct) : Expr → TermElabM (Option Expr)
  | .lam n d b c => withRef struct.ref do
    if c.isExplicit then
      let fieldName := n
      match getFieldValue? struct fieldName with
      | none     => return none
      | some val =>
        let valType ← inferType val
        if (← isDefEq valType d) then
          mkDefaultValueAux? struct (b.instantiate1 val)
        else
          return none
    else
      if let some (_, param) := struct.params.find? fun (paramName, _) => paramName == n then
        -- Recall that we did not use to have support for parameter propagation here.
        if (← isDefEq (← inferType param) d) then
          mkDefaultValueAux? struct (b.instantiate1 param)
        else
          return none
      else
        let arg ← mkFreshExprMVar d
        mkDefaultValueAux? struct (b.instantiate1 arg)
  | e =>
    if e.isAppOfArity ``id 2 then
      return some e.appArg!
    else
      return some e

def mkDefaultValue? (struct : Struct) (cinfo : ConstantInfo) : TermElabM (Option Expr) :=
  withRef struct.ref do
  let us ← mkFreshLevelMVarsFor cinfo
  mkDefaultValueAux? struct (← instantiateValueLevelParams cinfo us)

/-- Reduce default value. It performs beta reduction and projections of the given structures. -/
partial def reduce (structNames : Array Name) (e : Expr) : MetaM Expr := do
  match e with
  | .lam ..       => lambdaLetTelescope e fun xs b => do mkLambdaFVars xs (← reduce structNames b)
  | .forallE ..   => forallTelescope e fun xs b => do mkForallFVars xs (← reduce structNames b)
  | .letE ..      => lambdaLetTelescope e fun xs b => do mkLetFVars xs (← reduce structNames b)
  | .proj _ i b   =>
    match (← Meta.project? b i) with
    | some r => reduce structNames r
    | none   => return e.updateProj! (← reduce structNames b)
  | .app f .. =>
    match (← reduceProjOf? e structNames.contains) with
    | some r => reduce structNames r
    | none   =>
      let f := f.getAppFn
      let f' ← reduce structNames f
      if f'.isLambda then
        let revArgs := e.getAppRevArgs
        reduce structNames (f'.betaRev revArgs)
      else
        let args ← e.getAppArgs.mapM (reduce structNames)
        return mkAppN f' args
  | .mdata _ b =>
    let b ← reduce structNames b
    if (defaultMissing? e).isSome && !b.isMVar then
      return b
    else
      return e.updateMData! b
  | .mvar mvarId =>
    match (← getExprMVarAssignment? mvarId) with
    | some val => if val.isMVar then pure val else reduce structNames val
    | none     => return e
  | e => return e

partial def tryToSynthesizeDefault (structs : Array Struct) (allStructNames : Array Name) (maxDistance : Nat) (fieldName : Name) (mvarId : MVarId) : TermElabM Bool :=
  let rec loop (i : Nat) (dist : Nat) := do
    if dist > maxDistance then
      return false
    else if h : i < structs.size then
      let struct := structs.get ⟨i, h⟩
      match getDefaultFnForField? (← getEnv) struct.structName fieldName with
      | some defFn =>
        let cinfo ← getConstInfo defFn
        let mctx ← getMCtx
        match (← mkDefaultValue? struct cinfo) with
        | none     => setMCtx mctx; loop (i+1) (dist+1)
        | some val =>
          let val ← reduce allStructNames val
          match val.find? fun e => (defaultMissing? e).isSome with
          | some _ => setMCtx mctx; loop (i+1) (dist+1)
          | none   =>
            let mvarDecl ← getMVarDecl mvarId
            let val ← ensureHasType mvarDecl.type val
            mvarId.assign val
            return true
      | _ => loop (i+1) dist
    else
      return false
  loop 0 0

partial def step (struct : Struct) : M Unit :=
  unless (← isRoundDone) do
    withReader (fun ctx => { ctx with structs := ctx.structs.push struct }) do
      for field in struct.fields do
        match field.val with
        | .nested struct => step struct
        | _ => match field.expr? with
          | none      => unreachable!
          | some expr =>
            match defaultMissing? expr with
            | some (.mvar mvarId) =>
              unless (← mvarId.isAssigned) do
                let ctx ← read
                if (← withRef field.ref <| tryToSynthesizeDefault ctx.structs ctx.allStructNames ctx.maxDistance (getFieldName field) mvarId) then
                  modify fun _ => { progress := true }
            | _ => pure ()

partial def propagateLoop (hierarchyDepth : Nat) (d : Nat) (struct : Struct) : M Unit := do
  match (← findDefaultMissing? struct) with
  | none       => return () -- Done
  | some field =>
    trace[Elab.struct] "propagate [{d}] [field := {field}]: {struct}"
    if d > hierarchyDepth then
      let missingFields := (← allDefaultMissing struct).map getFieldName
      --!!/
      if struct.source.implicit.isSome then
        return ()
      else
      --!!\
        let missingFieldsWithoutDefault :=
        let env := (← getEnv)
        let structs := (← read).allStructNames
        missingFields.filter fun fieldName => structs.all fun struct =>
          (getDefaultFnForField? env struct fieldName).isNone
        let fieldsToReport :=
          if missingFieldsWithoutDefault.isEmpty then missingFields else missingFieldsWithoutDefault
        throwErrorAt field.ref "fields missing: {fieldsToReport.toList.map (s!"'{·}'") |> ", ".intercalate}"
    else withReader (fun ctx => { ctx with maxDistance := d }) do
      modify fun _ => { progress := false }
      step struct
      if (← get).progress then
        propagateLoop hierarchyDepth 0 struct
      else
        propagateLoop hierarchyDepth (d+1) struct

def propagate (struct : Struct) : TermElabM Unit := do --!! added do
  let hierarchyDepth := getHierarchyDepth struct
  let structNames := collectStructNames struct #[]
  let vhc? := struct.source.implicit --!!
  if vhc?.all (·.useDefaults) then --!!
    propagateLoop hierarchyDepth 0 struct { allStructNames := structNames } |>.run' {}
  if vhc?.isSome then --!!
    assignRemainingDefaultsToHoles struct --!!

end ImplicitFields

private def elabStructInstAux (stx : Syntax) (expectedType? : Option Expr) (source : Source) : TermElabM Expr := do
  let structName ← getStructName expectedType? source
  let struct ← liftMacroM <| mkStructView stx structName source
  let struct ← expandStruct struct
  trace[Elab.struct] "{struct}"
  /- We try to synthesize pending problems with `withSynthesize` combinator before trying to use default values.
     This is important in examples such as
      ```
      structure MyStruct where
          {α : Type u}
          {β : Type v}
          a : α
          b : β

      #check { a := 10, b := true : MyStruct }
      ```
     were the `α` will remain "unknown" until the default instance for `OfNat` is used to ensure that `10` is a `Nat`.

     TODO: investigate whether this design decision may have unintended side effects or produce confusing behavior.
  -/
  let { val := r, struct, instMVars } ← withSynthesize (mayPostpone := true) <| elabStruct struct expectedType?
  trace[Elab.struct] "before propagate {r}"
  ImplicitFields.propagate struct
  synthesizeAppInstMVars instMVars r
  return r

--!! changed attribute and name
@[term_elab structInstWithHoles] def elabStructInstWithHoles : TermElab := fun stx expectedType? => do
  match (← expandNonAtomicExplicitSources stx) with
  | some stxNew => withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
  | none =>
    let sourceView ← getStructSource stx
    if let some modifyOp ← isModifyOp? stx then
      if sourceView.explicit.isEmpty then
        throwError "invalid \{...} notation, explicit source is required when using '[<index>] := <value>'"
      elabModifyOp stx modifyOp sourceView.explicit expectedType?
    else
      elabStructInstAux stx expectedType? sourceView

section haveFieldProj

declare_syntax_cat asname
syntax "as" ident : asname

-- couldn't write elab "haveFieldProj" f:(ident)? x:("as" n:ident)? : tactic
/-- Once a goal has been created for a structure's field via `?..` syntax, `haveFieldProj` can be used equivalently to `have <field name>.proj := <projection function>`.
`haveFieldProj f as a` gets the field projection for the field `f` and names it `a`; `f` and `as a` can both be individually omitted.
-/
elab "haveFieldProj" f:(ident)? x:(asname)? : tactic => do
  let fieldHoleMData? := ImplicitFields.getFieldHoleMDataFromMVar? (← Tactic.getMainDecl)
  match fieldHoleMData? with
  | some fieldHoleMData =>
    let fieldName := match f with | some f' => f'.getId | none => fieldHoleMData.fieldName
    let some projname := (getProjFnForField? (← getEnv) fieldHoleMData.structName fieldName) | throwError "couldn't find projection function for field {fieldName} of structure {fieldHoleMData.structName}"
    let name := match x with
      | some stx => match stx with
        | `(asname|as $n:ident) => n
        --~~? Use ``fieldName ++ `proj``, `fieldName`, or just `projname`?
        | _ => mkIdent (fieldName ++ `proj)
      | none => mkIdent (fieldName ++ `proj)
    Tactic.evalTactic (←`(tactic|have $name := $(mkIdent projname)))
  | none => throwError "no field metadata found on the main goal"

end haveFieldProj
