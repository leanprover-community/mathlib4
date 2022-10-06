/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

-- import Mathlib.Lean.Expr
import Lean
import Mathlib.Data.List.Basic -- this should import the above file
import Std.Tactic.NoMatch
import Mathlib.Tactic.ToAdditive

/-!
# Stub for implementation of the `@[simps]` attribute.

This file is currently just a stub that creates a no-operation `@[simps]` attribute.
Without this, all declarations in the mathport output for mathlib3 that use `@[simps]` fail.
With the no-operation attribute, the declarations can succeed,
but of course all later proofs that rely on the existence of the automatically generated lemmas
will fail.

Partial progress to port the implementation from mathlib3.

OLD DOC:

# simps attribute

This file defines the `@[simps]` attribute, to automatically generate `simp` lemmas
reducing a definition when projections are applied to it.

## Implementation Notes

There are three attributes being defined here
* `@[simps]` is the attribute for objects of a structure or instances of a class. It will
  automatically generate simplification lemmas for each projection of the object/instance that
  contains data. See the doc strings for `simpsAttr` and `simpsCfg` for more details and
  configuration options.
* `@[simpsStructure]` is automatically added to structures that have been used in `@[simps]` at least
  once. This attribute contains the data of the projections used for this structure by all following
  invocations of `@[simps]`.
* `@[notation_class]` should be added to all classes that define notation, like `Mul` and
  `Zero`. This specifies that the projections that `@[simps]` used are the projections from
  these notation classes instead of the projections of the superclasses.
  Example: if `Mul` is tagged with `@[notation_class]` then the projection used for `Semigroup`
  will be `λ α hα, @Mul.mul α (@Semigroup.toMul α hα)` instead of `@Semigroup.mul`.

## Tags

structures, projections, simp, simplifier, generates declarations
-/

/-
ask:
- are there useful commands for compositions of structure projections?
- is _refl_lemma still a thing? -> probably, but I can call a function that should add it
- When a coercion is inserted into a term, how does that look? -> you never see coercions
- what is the Lean 4 equivalent of has_to_format/has_to_tactic_format?
- primitive projections -> you never see these normally

-- PR opportunity: dsimp using iff.rfl lemmas:
* In file `Tactic/Simp/SimpTheorems` we check whether a proof is `Eq.refl` to decide
whether this is a `rflTheorem`. This should also check for `Iff.rfl`
-/

-- move
namespace String

/-- `getRest s pre` returns `some post` if `s = pre ++ post`.
  If `pre` is not a prefix of `s`, it returns `none`.
  Note: this corresponds to `List.isPrefixOf?`-/
def getRest (s pre : String) : Option String :=
if startsWith s pre then some <| s.drop pre.length else none

end String

open Lean Meta Parser Elab Command

namespace Lean.Parser
namespace Attr

syntax (name := simps) "simps" (" (" &"config" " := " term ")")? (ppSpace ident)* : attr
syntax (name := simps?) "simps?" (" (" &"config" " := " term ")")? (ppSpace ident)* : attr

end Attr

namespace Command

syntax simpsRule.rename := ident " → " ident
syntax simpsRule.erase := "-" ident
syntax simpsRule := (simpsRule.rename <|> simpsRule.erase) &" as_prefix"?
syntax simpsProj := ident (" (" simpsRule,+ ")")?
syntax (name := initialize_simps_projections) "initialize_simps_projections"
  (ppSpace simpsProj) : command
syntax (name := initialize_simps_projections?) "initialize_simps_projections?"
  (ppSpace simpsProj) : command
/- question 1: can I replace the 2 syntaxes above by:
syntax (name := initialize_simps_projections2) "initialize_simps_projections" "?"?
  (ppSpace simpsProj) : command
-/
/- question 2: Am I doing tracing wrong? -/
/- question 3: what is a reasonable low number as second argument of `synthInstance`?
  What does this number measure?-/
/- Question 4: How to add an attribute? `attr.add "do a bunch of effort to write syntax here?"`-/
syntax (name := notation_class) "notation_class" : attr


end Command
end Lean.Parser

initialize registerTraceClass `simps.verbose
initialize registerTraceClass `simps.debug

/--
Projection data for a single projection of a structure, consisting of the following fields:
- the name used in the generated `simp` lemmas
- an Expression used by simps for the projection. It must be definitionally equal to an original
  projection (or a composition of multiple projections).
  These Expressions can contain the universe parameters specified in the first argument of
  `simpsStructure`.
- a list of natural numbers, which is the projection number(s) that have to be applied to the
  Expression. For example the list `[0, 1]` corresponds to applying the first projection of the
  structure, and then the second projection of the resulting structure (this assumes that the
  target of the first projection is a structure with at least two projections).
  The composition of these projections is required to be definitionally equal to the provided
  Expression.
- A boolean specifying whether `simp` lemmas are generated for this projection by default.
- A boolean specifying whether this projection is written as prefix.
-/
structure ProjectionData where
  name : Name -- todo: uncapitalize
  expr : Expr -- todo: uncapitalize
  projNrs : List ℕ
  isDefault : Bool
  isPrefix : Bool
  deriving Inhabited

instance : ToFormat ProjectionData := ⟨λ ⟨a, b, c, d, e⟩ => .group <| .nest 1 <|
  "⟨" ++ .joinSep [format a, format b, format c, format d, format e] ("," ++ .line) ++ "⟩"⟩

/-- The `@[simpsStructure]` attribute specifies the preferred projections of the given structure,
used by the `@[simps]` attribute.
- You can generate this with the command `initialize_simps_projections`.
- If not generated, the `@[simps]` attribute will generate this automatically.
- To change the default value, see Note [custom simps projection].
- You are strongly discouraged to add this attribute manually.
- The first argument is the list of names of the universe variables used in the structure
- The second argument is an array that consists of the projection data for each projection.
-/
initialize simpsStructure : NameMapExtension (List Name × Array ProjectionData) ←
  registerNameMapExtension (List Name × Array ProjectionData) `simpsStructure

/-- The `@[notation_class]` attribute specifies that this is a notation class,
  and this notation should be used instead of projections by @[simps].
  * The first argument `true` for notation classes and `false` for classes applied to the structure,
    like `CoeSort` and `CoeFun`
  * The second argument is the name of the projection (by default it is the first projection
    of the structure)
-/
initialize notationClassAttr : NameMapExtension Unit ← -- todo: should this be TagAttribute?
  registerNameMapAttribute {
    name  := `notation_class
    descr := "An attribute specifying that this is a notation class. Used by @[simps]."
    add   := fun
    | nm, `(attr|notation_class) => do
      if (getStructureInfo? (← getEnv) nm).isNone then
        throwError "@[notation_class] attribute can only be added to classes."
    | _, stx => throwError "unexpected notation_class syntax {stx}" }

/-- Temporary projection data parsed from `initialize_simps_projections` before the Expression
  matching this projection has been found. Only used internally in `simpsGetRawProjections`. -/
structure ParsedProjectionData where
  origName : Name  -- name for this projection used in the structure definition
  newName : Name   -- name for this projection used in the generated `simp` lemmas
  isDefault : Bool -- will simp lemmas be generated for with (without specifically naming this?)
  isPrefix : Bool  -- is the projection name a prefix?
  expr? : Option Expr := none -- projection expression
  projNrs : List Nat := [] -- the list of projection numbers this expression corresponds to
  isChanged : Bool := false -- is this a projection that is changed by the user?

def ParsedProjectionData.toProjectionData (p : ParsedProjectionData) : ProjectionData :=
⟨p.newName, p.expr?.getD default, p.projNrs, p.isDefault, p.isPrefix⟩

instance : ToFormat ParsedProjectionData := ⟨λ ⟨x₁, x₂, x₃, x₄, x₅, x₆, x₇⟩ => .group <| .nest 1 <|
  "⟨" ++ .joinSep [format x₁, format x₂, format x₃, format x₄, format x₅, format x₆, format x₇]
    ("," ++ .line) ++ "⟩"⟩

/-- The type of rules that specify how metadata for projections in changes.
  See `initialize_simps_projections`. -/
abbrev ProjectionRule :=
  (Name × Name ⊕ Name) × Bool

/-- Returns the projection information of a structure. -/
def projectionsInfo (l : List ProjectionData) (pref : String) (str : Name) : Format :=
  let ⟨defaults, nondefaults⟩ := l.partition (·.isDefault)
  let toPrint : List Format :=
    defaults.map fun s =>
      let prefixStr := if s.isPrefix then "(prefix) " else ""
      f!"Projection {prefixStr}{s.name}: {s.expr}"
  let print2 :=
    String.join <| (nondefaults.map fun nm : ProjectionData => toString nm.1).intersperse ", "
  let toPrint :=
    toPrint.map toString ++
      if nondefaults.isEmpty then [] else
      ["No lemmas are generated for the projections: " ++ print2 ++ "."]
  let toPrint := String.join <| toPrint.intersperse "\n        > "
  f! "[simps] > {pref } {str }:\n        > {toPrint}"

/-- Auxiliary function of `getCompositeOfProjections`. -/
partial def getCompositeOfProjectionsAux (str : Name) (proj : String) (x : Expr)
  (pos : List ℕ) (args : Array Expr) : MetaM (Expr × List ℕ) := do
    let env ← getEnv
    let projs := (getStructureInfo? env str).get!
    let projInfo := projs.fieldNames.toList.mapIdx
      fun n p => (fun x => (x, n, p)) <$> proj.getRest ("_" ++ p.getString!)
    if (projInfo.filterMap id).isEmpty then
      throwError "Failed to find constructor {proj.drop 1} in structure {str}."
    let (projRest, index, projName) := (projInfo.filterMap id).getLast!
    let strDecl := (env.find? str).get!
    let projExpr : Expr := mkConst (str ++ projName) <| strDecl.levelParams.map mkLevelParam
    let projDecl := (env.find? (str ++ projName)).get!
    let type ← inferType x
    let params := type.getAppArgs
    let newX := mkAppN (projExpr.instantiateLevelParams
      projDecl.levelParams type.getAppFn.constLevels!) <| params ++ [x]
    let newPos := pos ++ [index]
    if projRest.isEmpty then return (← mkLambdaFVars args newX, newPos)
      else do
        let type ← inferType newX
        forallTelescopeReducing type fun typeArgs tgt =>
          getCompositeOfProjectionsAux tgt.getAppFn.constName! projRest (mkAppN newX typeArgs)
            newPos (args ++ typeArgs)


/-- Given a structure `str` and a projection `proj`, that could be multiple nested projections
  (separated by `_`), returns an Expression that is the composition of these projections and a
  list of natural numbers, that are the projection numbers of the applied projections. -/
def getCompositeOfProjections (str : Name) (proj : String) : MetaM (Expr × List ℕ) := do
  let env ← getEnv
  let strDecl := (env.find? str).get!
  let strExpr : Expr := mkConst str <| strDecl.levelParams.map mkLevelParam
  let type ← inferType strExpr
  forallTelescopeReducing type fun typeArgs _ =>
  withLocalDeclD `x (mkAppN strExpr typeArgs) fun ex =>
  getCompositeOfProjectionsAux str ("_" ++ proj) ex [] <| typeArgs ++ [ex]

/-- Auxilliary function for `simpsGetRawProjections` that executes the projection renaming.

Figure out projections, including renamings. The information for a projection is (before we
figure out the `expr` of the projection):
`(original name, given name, is default, is prefix)`.
The first projections are always the actual projections of the structure, but `rules` could
specify custom projections that are compositions of multiple projections. -/
def simpsApplyProjectionRules (str : Name) (rules : Array ProjectionRule) :
  CoreM (Array ParsedProjectionData) := do
  let env ← getEnv
  if getStructureInfo? env str |>.isNone then
    throwError "Declaration {str} is not a structure."
  let projs := (getStructureInfo? env str).get!
  let projs : Array ParsedProjectionData := projs.fieldNames.map fun nm => ⟨nm, nm, true, false, none, [], false⟩
  let projs : Array ParsedProjectionData := rules.foldl (init := projs) fun projs rule =>
    match rule with
    | (.inl (oldName, newName), isPrefix) =>
      if (projs.map (·.newName)).contains oldName then
        projs.map fun proj => if proj.newName == oldName then
          { proj with newName := newName, isPrefix := isPrefix } else
          proj else
        projs.push ⟨oldName, newName, true, isPrefix, none, [], false⟩
    | (.inr nm, isPrefix) =>
      if (projs.map (·.newName)).contains nm then
        projs.map fun proj => if proj.newName = nm then
          { proj with isDefault := false, isPrefix := isPrefix } else
          proj else
        projs.push ⟨nm, nm, false, isPrefix, none, [], false⟩
  trace[simps.debug] "[simps] > Projection info after applying the rules: {projs}."
  if !(projs.map (·.newName)).toList.Nodup then throwError
    ("Invalid projection names. Two projections have the same name.\n{
    }This is likely because a custom composition of projections was given the same name as an {
    }existing projection. Solution: rename the existing projection (before naming the {
    }custom projection).")
  pure projs

/-- Auxilliary function for `simpsGetRawProjections`.
Find custom projections declared by the user. -/
def simpsFindCustomProjection (str : Name) (proj : ParsedProjectionData)
  (rawUnivs : List Level) (trc : Bool) : CoreM ParsedProjectionData := do
  let env ← getEnv
  let (rawExpr, nrs) ← MetaM.run' (getCompositeOfProjections str proj.origName.getString!)
  match env.find? (str ++ `simps ++ proj.newName) with
  | some d@(.defnInfo _) =>
    let customProj := d.instantiateValueLevelParams rawUnivs
    if trc then
      dbg_trace "[simps] > found custom projection for {proj.newName}:\n        > {customProj}"
    match (← MetaM.run' $ isDefEq customProj rawExpr) with
    | true => pure {proj with expr? := some customProj, projNrs := nrs, isChanged := true}
    | false =>
      -- if the type of the Expression is different, we show a different error message, because
      -- (in Lean 3) just stating that the expressions are different is quite unhelpful
      let customProjType ← MetaM.run' (inferType customProj)
      let rawExprType ← MetaM.run' (inferType rawExpr)
      if (← MetaM.run' (isDefEq customProjType rawExprType)) then throwError
        ("Invalid custom projection:\n  {customProj}\n{
        }Expression is not definitionally equal to {rawExpr}") else throwError
        ("Invalid custom projection:\n  {customProj}\n{
        }Expression has different type than {str ++ proj.origName}. Given type:\n{
        }  {customProjType}\nExpected type:\n  {rawExprType}\n{
        }Note: make sure order of implicit arguments is exactly the same.")
  | _ => pure {proj with expr? := some rawExpr, projNrs := nrs}

/-- Auxilliary function for `simpsGetRawProjections`.
Resolve a single notation class in `simpsFindAutomaticProjections`. -/
def simpsResolveNotationClass (projs : Array ParsedProjectionData)
  (className : Name) (args : Array Expr) (eStr : Expr) (rawUnivs : List Level) (trc : Bool) :
    MetaM (Array ParsedProjectionData) := do
  let env ← getEnv
  let classInfo := (getStructureInfo? env className).get!
  let projName := classInfo.fieldNames[0]!
  /- For this class, find the projection. `rawExpr` is the projection found applied to `args`,
      and `rawExprLambda` has the arguments `args` abstracted. -/
  let (relevantProj, rawExprLambda) ← do
    let eInstType := mkAppN (.const className rawUnivs) args
    withLocalDeclD `x eStr fun hyp => do
      let eInst ← synthInstance eInstType (some 10) -- reasonable, but low number
      let rawExpr ← mkAppM projName (args.push eInst)
      let rawExprLambda ← mkLambdaFVars (args.push hyp) rawExpr
      let rawExprWhnf ← whnf rawExpr
      let relevantProj ← lambdaTelescope rawExprWhnf fun _ body =>
        pure <| body.getAppFn.constName?
      dbg_trace (relevantProj, rawExprLambda)
      pure (relevantProj, rawExprLambda)
  match projs.findIdx? fun x => some x.1 == relevantProj with
  | none =>
    if trc then
      dbg_trace ("[simps] > Warning: The structure has an instance for {className}, {
        }but it is not definitionally equal to any projection.")
    throwError "" -- will be caught by <|> in `simpsFindAutomaticProjections`
  | some pos =>
    trace[simps.debug] "[simps] > The raw projection is:\n {rawExprLambda}"
    projs.mapIdxM fun nr x => if nr.1 = pos then do
      if x.isChanged then
        if trc then
          dbg_trace ("[simps] > Warning: Projection {relevantProj} is definitionally equal to\n  {
            rawExprLambda}\nHowever, this is not used since a custom simps projection is specified {
            }by the user.")
        pure x else
        if trc then
          dbg_trace ("[simps] > Using notation from {className} for projection {relevantProj}.")
        pure {x with expr? := some rawExprLambda} else
      pure x

/-- Auxilliary function for `simpsGetRawProjections`.
Find custom projections, automatically found by simps.
These come from algebraic notation classes, like `+`. -/
-- if performance becomes a problem, possible heuristic: use the names of the projections to
-- skip all classes that don't have the corresponding field.
def simpsFindAutomaticProjections (str : Name) (projs : Array ParsedProjectionData)
  (strType : Expr) (rawUnivs : List Level) (trc : Bool) : CoreM (Array ParsedProjectionData) := do
  let env ← getEnv
  MetaM.run' <| forallTelescope strType fun args _ => do
    let eStr := mkAppN (.const str rawUnivs) args
    let automaticProjs := notationClassAttr.getState env
    if args.size == 1 then -- can be wrong if additional type-class arguments??
      automaticProjs.foldM (init := projs) fun projs className _ =>
        simpsResolveNotationClass projs className args eStr rawUnivs trc <|>
        pure projs else
      pure projs


/--
Get the projections used by `simps` associated to a given structure `str`.

The returned information is also stored in a parameter of the attribute `@[simpsStructure]`, which
is given to `str`. If `str` already has this attribute, the information is read from this
attribute instead. See the documentation for this attribute for the data this tactic returns.

The returned universe levels are the universe levels of the structure. For the projections there
are three cases
* If the declaration `{StructureName}.simps.{projectionName}` has been declared, then the value
  of this declaration is used (after checking that it is definitionally equal to the actual
  projection. If you rename the projection name, the declaration should have the *new* projection
  name.
* You can also declare a custom projection that is a composite of multiple projections.
* Otherwise, for every class with the `notation_class` attribute, and the structure has an
  instance of that notation class, then the projection of that notation class is used for the
  projection that is definitionally equal to it (if there is such a projection).
  This means in practice that coercions to function types and sorts will be used instead of
  a projection, if this coercion is definitionally equal to a projection. Furthermore, for
  notation classes like `Mul` and `Zero` those projections are used instead of the
  corresponding projection.
  Projections for coercions and notation classes are not automatically generated if they are
  composites of multiple projections (for example when you use `extend` without the
  `oldStructureCmd` (does this exist?)).
* Otherwise, the projection of the structure is chosen.
  For example: ``simpsGetRawProjections env `prod`` gives the default projections
```
  ([u, v], [prod.fst.{u v}, prod.snd.{u v}])
```
    while ``simpsGetRawProjections env `equiv`` gives [todo: change example for Lean 4]
```
  ([u_1, u_2], [λ α β, Coe.coe, λ {α β} (e : α ≃ β), ⇑(e.symm), left_inv, right_inv])
```
    after declaring the coercion from `equiv` to function and adding the declaration
```
  def equiv.simps.invFun {α β} (e : α ≃ β) : β → α := e.symm
```

Optionally, this command accepts three optional arguments:
* If `traceIfExists` the command will always generate a trace message when the structure already
  has the attribute `@[simpsStructure]`.
* The `rules` argument accepts a list of pairs `sum.inl (oldName, newName)`. This is used to
  change the projection name `oldName` to the custom projection name `newName`. Example:
  for the structure `equiv` the projection `toFun` could be renamed `apply`. This name will be
  used for parsing and generating projection names. This argument is ignored if the structure
  already has an existing attribute. If an element of `rules` is of the form `sum.inr name`, this
  means that the projection `name` will not be applied by default.
* if `trc` is true, this tactic will trace information.
-/
def simpsGetRawProjections (str : Name) (traceIfExists : Bool := false)
  (rules : Array ProjectionRule := #[]) (trc := false) :
  CoreM (List Name × Array ProjectionData) := do
  let env ← getEnv
  let trc := trc || ((← getOptions) |>.getBool `trace.simps.verbose)
  -- to do: double check tracing
  match (simpsStructure.getState env).find? str with
  | some data =>
    -- We always print the projections when they already exists and are called by
    -- `initialize_simps_projections`.
    if traceIfExists || ((← getOptions) |>.getBool `trace.simps.verbose) then
      dbg_trace
        projectionsInfo data.2.toList "Already found projection information for structure" str
    return data
  | none =>
    if trc then
      dbg_trace "[simps] > generating projection information for structure {str}."
    trace[simps.debug] "[simps] > Applying the rules {rules}."
    if env.find? str |>.isNone then
      throwError "No such declaration {str}." -- maybe unreachable
    let strDecl := (env.find? str).get!
    let rawLevels := strDecl.levelParams
    let rawUnivs := rawLevels.map Level.param
    let projs ← simpsApplyProjectionRules str rules
    let projs ← projs.mapM fun proj => simpsFindCustomProjection str proj rawUnivs trc
    -- the following will not work properly with Lean 4-style structure bundling
    -- let projs ← simpsFindAutomaticProjections str projs strDecl.type rawUnivs trc
    let projs := projs.map (·.toProjectionData)
    -- make all proof non-default.
    let projs ← projs.mapM fun proj => do
      match (← MetaM.run' <| isProof proj.expr) with
      | true => pure { proj with isDefault := false }
      | false => pure proj
    if trc then
      dbg_trace (projectionsInfo projs.toList "generated projections for" str)
    simpsStructure.add str (rawLevels, projs)
    trace[simps.debug] "[simps] > Generated raw projection data:\n{(rawLevels, projs)}"
    return (rawLevels, projs)

library_note "custom simps projection"
/-- You can specify custom projections for the `@[simps]` attribute.
To do this for the projection `MyStructure.originalProjection` by adding a declaration
`MyStructure.simps.myProjection` that is definitionally equal to
`MyStructure.originalProjection` but has the projection in the desired (simp-normal) form.
Then you can call
```
initialize_simps_projections (originalProjection → myProjection, ...)
```
to register this projection. See `initializeSimpsProjectionsCmd` for more information.

You can also specify custom projections that are definitionally equal to a composite of multiple
projections. This is often desirable when extending structures (without `oldStructureCmd`).

`CoeFun` and notation class (like `Mul`) instances will be automatically used, if they
are definitionally equal to a projection of the structure (but not when they are equal to the
composite of multiple projections).
-/

/-- Parse a rule for `initialize_simps_projections`. It is either `<name>→<name>` or `-<name>`,
  possibly following by `as_prefix`.-/
def elabSimpsRule : Syntax → CommandElabM ProjectionRule
| `(simpsRule| $id1 → $id2 $[as_prefix%$tk]?) => pure (.inl (id1.getId, id2.getId), tk.isSome)
| `(simpsRule| - $id $[as_prefix%$tk]?) => pure (.inr id.getId, tk.isSome)
| _                    => Elab.throwUnsupportedSyntax


/--
This command specifies custom names and custom projections for the simp attribute `simpsAttr`.
* You can specify custom names by writing e.g.
  `initialize_simps_projections equiv (toFun → apply, invFun → symm_apply)`.
* See Note [custom simps projection] and the examples below for information how to declare custom
  projections.
* If no custom projection is specified, the projection will be `coe_fn`/`⇑` if a `CoeFun`
  instance has been declared, or the notation of a notation class (like `Mul`) if such an
  instance is available. If none of these cases apply, the projection itself will be used.
* You can disable a projection by default by running
  `initialize_simps_projections equiv (-invFun)`
  This will ensure that no simp lemmas are generated for this projection,
  unless this projection is explicitly specified by the user.
* If you want the projection name added as a prefix in the generated lemma name, you can add the
  `as_prefix` modifier:
  `initialize_simps_projections equiv (toFun → coe as_prefix)`
  Note that this does not influence the parsing of projection names: if you have a declaration
  `foo` and you want to apply the projections `snd`, `coe` (which is a prefix) and `fst`, in that
  order you can run `@[simps snd_coe_fst] def foo ...` and this will generate a lemma with the
  name `coe_foo_snd_fst`.
  * Run `initialize_simps_projections?` (or `set_option trace.simps.verbose true`)
  to see the generated projections.
* You can declare a new name for a projection that is the composite of multiple projections, e.g.
  ```
    structure A := (proj : ℕ)
    structure B extends A
    initialize_simps_projections? B (toA_proj → proj, -toA)
  ```
  You can also make your custom projection that is definitionally equal to a composite of
  projections. In this case, coercions and notation classes are not automatically recognized, and
  should be manually given by giving a custom projection.
  This is especially useful when extending a structure (without `oldStructureCmd`).
  In the above example, it is desirable to add `-toA`, so that `@[simps]` doesn't automatically
  apply the `B.toA` projection and then recursively the `A.proj` projection in the lemmas it
  generates. If you want to get both the `foo_proj` and `foo_toA` simp lemmas, you can use
  `@[simps, simps toA]`.
* Running `initialize_simps_projections MyStruc` without arguments is not necessary, it has the
  same effect if you just add `@[simps]` to a declaration.
* If you do anything to change the default projections, make sure to call either `@[simps]` or
  `initialize_simps_projections` in the same file as the structure declaration. Otherwise, you might
  have a file that imports the structure, but not your custom projections.

Some common uses:
* If you define a new homomorphism-like structure (like `MulHom`) you can just run
  `initialize_simps_projections` after defining the `CoeFun` instance
  ```
    instance {mM : Mul M} {mN : Mul N} : CoeFun (MulHom M N) := ...
    initialize_simps_projections MulHom (toFun → apply)
  ```
  This will generate `foo_apply` lemmas for each declaration `foo`.
* If you prefer `coe_foo` lemmas that state equalities between functions, use
  `initialize_simps_projections MulHom (toFun → coe as_prefix)`
  In this case you have to use `@[simps {fullyApplied := false}]` or equivalently `@[simps asFn]`
  whenever you call `@[simps]`.
* You can also initialize to use both, in which case you have to choose which one to use by default,
  by using either of the following
  ```
    initialize_simps_projections MulHom (toFun → apply, toFun → coe, -coe as_prefix)
    initialize_simps_projections MulHom (toFun → apply, toFun → coe as_prefix, -apply)
  ```
  In the first case, you can get both lemmas using `@[simps, simps coe asFn]` and in the second
  case you can get both lemmas using `@[simps asFn, simps apply]`.
* If your new homomorphism-like structure extends another structure (without `oldStructureCmd`)
  (like `relEmbedding`), then you have to specify explicitly that you want to use a coercion
  as a custom projection. For example
  ```
    def relEmbedding.simps.apply (h : r ↪r s) : α → β := h
    initialize_simps_projections relEmbedding (to_embedding_toFun → apply, -to_embedding)
  ```
* If you have an isomorphism-like structure (like `equiv`) you often want to define a custom
  projection for the inverse:
  ```
    def equiv.simps.symm_apply (e : α ≃ β) : β → α := e.symm
    initialize_simps_projections equiv (toFun → apply, invFun → symm_apply)
  ```
-/
def initializeSimpsProjectionsCmd (trc : Bool) (id : Ident)
  (stxs : Option (Syntax.TSepArray `Lean.Parser.Command.simpsRule ",")) : CommandElabM Unit := do
  let stxs := stxs.getD <| .mk #[]
  let rules ← stxs.getElems.raw.mapM elabSimpsRule
  let nm ← resolveGlobalConstNoOverload id
  _ ← liftCoreM <| simpsGetRawProjections nm true rules trc

/-- Elaborates an `initialize_simps_projections` command. -/
@[commandElab «initialize_simps_projections»] def elabInitializeSimpsProjections : CommandElab
| `(initialize_simps_projections $id $[($stxs,*)]?) => initializeSimpsProjectionsCmd false id stxs
| _ => throwUnsupportedSyntax

/-- Elaborates an `initialize_simps_projections?` command. -/
@[commandElab «initialize_simps_projections?»] def elabInitializeSimpsProjections? : CommandElab
| `(initialize_simps_projections? $id $[($stxs,*)]?) => initializeSimpsProjectionsCmd true id stxs
| _ => throwUnsupportedSyntax


structure SimpsCfg where
  attrs := [`simp]
  simpRhs := false
  typeMd := TransparencyMode.instances
  rhsMd := TransparencyMode.reducible -- was `none` in Lean 3
  fullyApplied := true
  notRecursive := [`prod, `pprod]
  trace := false
  debug := false
  addAdditive := @none Name
  deriving Inhabited

/-- A common configuration for `@[simps]`: generate equalities between functions instead equalities
  between fully applied Expressions. -/
def SimpsCfg.asFn : SimpsCfg where
  fullyApplied := false

/-- A common configuration for `@[simps]`: don't tag the generated lemmas with `@[simp]`. -/
def SimpsCfg.lemmasOnly : SimpsCfg where
  attrs := []

/-- `instantiateLambdasOrApps es e` instantiates lambdas in `e` by expressions from `es`.
If the length of `es` is larger than the number of lambdas in `e`,
then the term is applied to the remaining terms.
Also reduces head let-expressions in `e`, including those after instantiating all lambdas.

This is very similar to `expr.substs`, but this also reduces head let-expressions. -/
partial def Lean.Expr.instantiateLambdasOrApps (es : Array Expr) (e : Expr) : Expr :=
e.betaRev es.reverse true -- check if this is what I want

/-- Get the projections of a structure used by `@[simps]` applied to the appropriate arguments.
  Returns a list of tuples
  ```
  (corresponding right-hand-side, given projection name, projection Expression, projection numbers,
    used by default, is prefix)
  ```
  (where all fields except the first are packed in a `ProjectionData` structure)
  one for each projection. The given projection name is the name for the projection used by the user
  used to generate (and parse) projection names. For example, in the structure

  Example 1: ``simpsGetProjectionExprs env `(α × β) `(⟨x, y⟩)`` will give the output
  ```
    [(`(x), `fst, `(@prod.fst.{u v} α β), [0], true, false),
     (`(y), `snd, `(@prod.snd.{u v} α β), [1], true, false)]
  ```

  Example 2: ``simpsGetProjectionExprs env `(α ≃ α) `(⟨id, id, λ _, rfl, λ _, rfl⟩)``
  will give the output
  ```
    [(`(id), `apply, `(coe), [0], true, false),
     (`(id), `symm_apply, `(λ f, ⇑f.symm), [1], true, false),
     ...,
     ...]
  ```
-/
def simpsGetProjectionExprs (tgt : Expr) (rhs : Expr) (cfg : SimpsCfg) :
    CoreM <| Array <| Expr × ProjectionData := do
  -- the parameters of the structure
  let params := tgt.getAppArgs
  if cfg.debug && !(← MetaM.run' <| (params.zip rhs.getAppArgs).allM fun ⟨a, b⟩ => isDefEq a b) then
    throwError "unreachable code: parameters are not definitionally equal"
  let str := tgt.getAppFn.constName?.getD default
  -- the fields of the object
  let rhsArgs := rhs.getAppArgs.toList.drop params.size
  let (rawUnivs, projDeclata) ← simpsGetRawProjections str false #[] cfg.trace
  pure <|
    projDeclata.map fun proj =>
      (rhsArgs.getD (a₀ := default) proj.projNrs.head!,
        { proj with
            expr := (proj.expr.instantiateLevelParams rawUnivs
              tgt.getAppFn.constLevels!).instantiateLambdasOrApps params
            projNrs := proj.projNrs.tail })

/-- `getUnivLevel t` returns the universe level of a type `t` -/
def getUnivLevel (t : Expr) : MetaM Level := do
  let univ ← inferType t
  let Expr.sort u ← whnf univ | throwError "getUnivLevel error: argument is not a type."
  return u

/-- Add a lemma with `nm` stating that `lhs = rhs`. `type` is the type of both `lhs` and `rhs`,
  `args` is the list of local constants occurring, and `univs` is the list of universe variables. -/
def simpsAddProjection (nm : Name) (type lhs rhs : Expr) (args : Array Expr) (univs : List Name)
    (cfg : SimpsCfg) : MetaM Unit := do
  trace[simps.debug] "[simps] > Planning to add the equality\n        > {lhs} = ({rhs} : {type})"
  let env ← getEnv
  if (env.find? nm).isSome then -- diverging behavior from Lean 3
    throwError "simps tried to add lemma {nm} to the environment, but it already exists."
    -- simplify `rhs` if `cfg.simpRhs` is true
  let lvl ← getUnivLevel type
  let (rhs, prf) ← do
    if !cfg.simpRhs then
      pure (rhs, mkAppN (mkConst `Eq.refl [lvl]) #[type, lhs]) else
      let (rhs2, _) ← dsimp rhs {} -- { failIfUnchanged := false }
      if rhs != rhs2 then
        trace[simps.debug] "[simps] > `dsimp` simplified rhs to\n        > {rhs2}"
      let (result, _) ← simp rhs2 {} --{ failIfUnchanged := false }
      if rhs2 != result.expr then
        trace[simps.debug] "[simps] > `simp` simplified rhs to\n        > {result.expr}"
      pure (result.expr, result.proof?.getD _)
  let eqAp := mkAppN (mkConst `Eq [lvl]) #[type, lhs, rhs]
  let declName := nm
  let declType ← mkForallFVars args eqAp
  let declValue ← mkLambdaFVars args prf
  let decl := Declaration.thmDecl
    { name := nm
      levelParams := univs
      type := declType
      value := declValue }
  if cfg.trace then
    dbg_trace "[simps] > adding projection {declName}:\n        > {declType}"
  -- what is the best way to add some decoration to an error message?
  -- match (← getEnv).addDecl decl with
  -- | Except.ok    env => setEnv env
  -- | Except.error ex  => throwError
  --     "Failed to add projection lemma {declName}. Nested error:\n{ex.toMessageData (← getOptions)}"
  try addDecl decl
  catch ex =>
    throwError "Failed to add projection lemma {declName}. Nested error:\n{ex.toMessageData}"
  if (← isDefEq lhs rhs) ∧ `simp ∈ cfg.attrs then
     pure () --set_basic_attribute `_refl_lemma declName true
  -- cfg.attrs.mapM fun nm => setAttribute nm declName tt -- deal with attributes
  if cfg.addAdditive.isSome then
    ToAdditive.addToAdditiveAttr nm ⟨false, cfg.trace, cfg.addAdditive.get!, none, true⟩

/-!



/-- Derive lemmas specifying the projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  `toApply` is non-empty after a custom projection that is a composition of multiple projections
  was just used. In that case we need to apply these projections before we continue changing lhs. -/
def simpsAddProjections :
    ∀ e : environment nm : Name type lhs rhs : Expr args : List Expr univs : List Name mustBeStr : Bool cfg : SimpsCfg
      todo : List String toApply : List ℕ, tactic Unit
  | e, nm, type, lhs, rhs, args, univs, mustBeStr, cfg, todo, toApply => do
    -- we don't want to unfold non-reducible definitions (like `set`) to apply more arguments
        whenTracing
        `simps.debug
        (← do
          dbg_trace "[simps] > Type of the Expression before normalizing: {type}")
    let (typeArgs, tgt) ← open_pis_whnf type cfg.typeMd
    trace[simps.debug]
        (← do
          dbg_trace "[simps] > Type after removing pi's: {tgt}")
    let tgt ← whnf tgt
    trace[simps.debug]
        (← do
          dbg_trace "[simps] > Type after reduction: {tgt}")
    let newArgs := args ++ typeArgs
    let lhsAp := lhs.instantiateLambdasOrApps typeArgs
    let rhsAp := rhs.instantiateLambdasOrApps typeArgs
    let str := tgt.getAppFn.constName
    let-- We want to generate the current projection if it is in `todo`
    todoNext := todo.filter (· ≠ "")
    /- Don't recursively continue if `str` is not a structure or if the structure is in
            `notRecursive`. -/
        if e str ∧ ¬(todo = [] ∧ str ∈ cfg ∧ ¬mustBeStr) then do
        let [intro] ← return <| e str | throwError "unreachable code (3)"
        let rhsWhnf ← whnf rhsAp cfg
        let (rhsAp, todoNow)
          ←-- `todoNow` means that we still have to generate the current simp lemma
              if ¬isConstantOf rhsAp intro ∧ isConstantOf rhsWhnf intro then
              /- If this was a desired projection, we want to apply it before taking the whnf.
                          However, if the current field is an eta-expansion (see below), we first want
                          to eta-reduce it and only then construct the projection.
                          This makes the flow of this function messy. -/
                  when
                  ("" ∈ todo ∧ toApply = [])
                  (if cfg then simpsAddProjection nm tgt lhsAp rhsAp newArgs univs cfg
                  else simpsAddProjection nm type lhs rhs args univs cfg) >>
                return (rhsWhnf, false)
            else return (rhsAp, "" ∈ todo ∧ toApply = [])
        if isConstantOf (getAppFn rhsAp) intro then do
            let projInfo
              ←-- if the value is a constructor application
                  simpsGetProjectionExprs
                  e tgt rhsAp cfg
            trace[simps.debug]
                (← do
                  dbg_trace "[simps] > Raw projection information:
                      {projInfo}")
            let eta ← rhsAp
            let-- check whether `rhsAp` is an eta-expansion
            rhsAp := eta rhsAp
            -- eta-reduce `rhsAp`
                  /- As a special case, we want to automatically generate the current projection if `rhsAp`
                          was an eta-expansion. Also, when this was a desired projection, we need to generate the
                          current projection if we haven't done it above. -/
                  when
                  (todoNow ∨ todo = [] ∧ eta ∧ toApply = []) <|
                if cfg then simpsAddProjection nm tgt lhsAp rhsAp newArgs univs cfg
                else simpsAddProjection nm type lhs rhs args univs cfg
            -- If we are in the middle of a composite projection.
                  when
                  (toApply ≠ []) <|
                do
                let ⟨newRhs, proj, projExprxpr, projNrs, isDefault, isPrefix⟩ ← return <| projInfo toApply
                let newType ← inferType newRhs
                trace[simps.debug]
                    (← do
                      dbg_trace "[simps] > Applying a custom composite projection. Current lhs:\n        >  {lhsAp}")
                simpsAddProjections e nm newType lhsAp newRhs newArgs univs false cfg todo toApply
            /- We stop if no further projection is specified or if we just reduced an eta-expansion and we
                        automatically choose projections -/
                  when
                  ¬(toApply ≠ [] ∨ todo = [""] ∨ eta ∧ todo = []) <|
                do
                let projs : List Name := projInfo fun x => x
                let todo := if toApply = [] then todoNext else todo
                -- check whether all elements in `todo` have a projection as prefix
                      guardₓ
                      (todo fun x => projs fun proj => ("_" ++ proj).isPrefixOf x) <|>
                    let x := (todo fun x => projs fun proj => ¬("_" ++ proj).isPrefixOf x).iget
                    let simpLemma := nm x
                    let neededProj := (x '_').tail.head
                    throwError
                      "Invalid simp lemma {(←
                        simpLemma)}. Structure {str} does not have projection {(← neededProj)}.
                      The known projections are:
                        {projs}
                      You can also see this information by running
                        `initialize_simps_projections? {str}`.
                      Note: these projection names might not correspond to the projection names of the structure."
                projInfo fun projNr ⟨newRhs, proj, projExprxpr, projNrs, isDefault, isPrefix⟩ => do
                    let newType ← inferType newRhs
                    let new_todo := todo.filterMap fun x => x ("_" ++ proj)
                    -- we only continue with this field if it is non-propositional or mentioned in todo
                          when
                          (isDefault ∧ todo = [] ∨ new_todo ≠ []) <|
                        do
                        let newLhs := projExprxpr [lhsAp]
                        let newName := nm proj isPrefix
                        let new_cfg :=
                          { cfg with addAdditive := cfg fun nm => nm (toAdditive.guess_name proj) isPrefix }
                        trace[simps.debug]
                            (← do
                              dbg_trace "[simps] > Recursively add projections for:\n        >  {newLhs}")
                        simpsAddProjections e newName newType newLhs newRhs newArgs univs false new_cfg new_todo
                            projNrs
          else-- if I'm about to run into an error, try to set the transparency for `rhsMd` higher.
              if cfg = transparency.none ∧ (mustBeStr ∨ todoNext ≠ [] ∨ toApply ≠ []) then do
              when cfg
                  (← do
                    dbg_trace "[simps] > The given definition is not a constructor application:\n        >   {rhsAp}\n        > Retrying with the options \{ rhsMd := semireducible, simpRhs := true}.")
              simpsAddProjections e nm type lhs rhs args univs mustBeStr
                  { cfg with rhsMd := semireducible, simpRhs := true } todo toApply
            else do
              when (toApply ≠ []) <|
                  throwError "Invalid simp lemma {nm}.
                    The given definition is not a constructor application:
                      {rhsAp}"
              when mustBeStr <|
                  throwError "Invalid `simps` attribute. The body is not a constructor application:
                      {rhsAp}"
              when (todoNext ≠ []) <|
                  throwError "Invalid simp lemma {(← nm todoNext)}.
                    The given definition is not a constructor application:
                      {rhsAp}"
              if cfg then simpsAddProjection nm tgt lhsAp rhsAp newArgs univs cfg
                else simpsAddProjection nm type lhs rhs args univs cfg
      else do
        when mustBeStr <| throwError "Invalid `simps` attribute. Target {str} is not a structure"
        when (todoNext ≠ [] ∧ str ∉ cfg) <|
            let first_todo := todoNext
            throwError "Invalid simp lemma {(← nm first_todo)}.
              Projection {(first_todo '_').tail.head} doesn't exist, because target is not a structure."
        if cfg then simpsAddProjection nm tgt lhsAp rhsAp newArgs univs cfg
          else simpsAddProjection nm type lhs rhs args univs cfg

/-- `simpsTac` derives `simp` lemmas for all (nested) non-Prop projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  If `shortNm` is true, the generated names will only use the last projection name.
  If `trc` is true, trace as if `trace.simps.verbose` is true. -/
def simpsTac (nm : Name) (cfg : SimpsCfg := {  }) (todo : List String := []) (trc := false) : tactic Unit := do
  let env ← getEnv
  let d ← e.get nm
  let lhs : Expr := const d.name d.levelParams
  let todo := todo.dedup.map fun proj => "_" ++ proj
  let cfg := { cfg with trace := cfg.trace || ((← getOptions) |>.getBool `simps.verbose || trc }
  let b ← hasAttribute' `toAdditive nm
  let cfg ←
    if b then do
        let dict ← toAdditive.aux_attr.get_cache
        when cfg
            (← do
              dbg_trace "[simps] > @[toAdditive] will be added to all generated lemmas.")
        return { cfg with addAdditive := dict nm }
      else return cfg
  simpsAddProjections e nm d lhs d [] d true cfg todo []

/-- The parser for the `@[simps]` attribute. -/
def simpsParser : parser (Bool × List String × SimpsCfg) := do
  -- note: we don't check whether the user has written a nonsense namespace in an argument.
        Prod.mk <$>
        isSome <$> (tk "?")? <*>
      (Prod.mk <$> many (name.last <$> ident) <*> do
        let some e ← parser.pexpr? | return {  }
        evalPexpr SimpsCfg e)

/-- The `@[simps]` attribute automatically derives lemmas specifying the projections of this
declaration.

Example:
```lean
@[simps] def foo : ℕ × ℤ := (1, 2)
```
derives two `simp` lemmas:
```lean
@[simp] lemma foo_fst : foo.fst = 1
@[simp] lemma foo_snd : foo.snd = 2
```

* It does not derive `simp` lemmas for the prop-valued projections.
* It will automatically reduce newly created beta-redexes, but will not unfold any definitions.
* If the structure has a coercion to either sorts or functions, and this is defined to be one
  of the projections, then this coercion will be used instead of the projection.
* If the structure is a class that has an instance to a notation class, like `Mul`, then this
  notation is used instead of the corresponding projection.
* You can specify custom projections, by giving a declaration with name
  `{StructureName}.simps.{projectionName}`. See Note [custom simps projection].

  Example:
  ```lean
  def equiv.simps.invFun (e : α ≃ β) : β → α := e.symm
  @[simps] def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩
  ```
  generates
  ```
  @[simp] lemma equiv.trans_toFun : ∀ {α β γ} (e₁ e₂) (a : α), ⇑(e₁.trans e₂) a = (⇑e₂ ∘ ⇑e₁) a
  @[simp] lemma equiv.trans_invFun : ∀ {α β γ} (e₁ e₂) (a : γ),
    ⇑((e₁.trans e₂).symm) a = (⇑(e₁.symm) ∘ ⇑(e₂.symm)) a
  ```

* You can specify custom projection names, by specifying the new projection names using
  `initialize_simps_projections`.
  Example: `initialize_simps_projections equiv (toFun → apply, invFun → symm_apply)`.
  See `initializeSimpsProjectionsCmd` for more information.

* If one of the fields itself is a structure, this command will recursively create
  `simp` lemmas for all fields in that structure.
  * Exception: by default it will not recursively create `simp` lemmas for fields in the structures
    `prod` and `pprod`. You can give explicit projection names or change the value of
    `simpsCfg.notRecursive` to override this behavior.

  Example:
  ```lean
  structure MyProd (α β : Type*) := (fst : α) (snd : β)
  @[simps] def foo : prod ℕ ℕ × MyProd ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_snd_fst : foo.snd.fst = 3
  @[simp] lemma foo_snd_snd : foo.snd.snd = 4
  ```

* You can use `@[simps proj1 proj2 ...]` to only generate the projection lemmas for the specified
  projections.
* Recursive projection names can be specified using `proj1_proj2_proj3`.
  This will create a lemma of the form `foo.proj1.proj2.proj3 = ...`.

  Example:
  ```lean
  structure MyProd (α β : Type*) := (fst : α) (snd : β)
  @[simps fst fst_fst snd] def foo : prod ℕ ℕ × MyProd ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_fst_fst : foo.fst.fst = 1
  @[simp] lemma foo_snd : foo.snd = {fst := 3, snd := 4}
  ```
* If one of the values is an eta-expanded structure, we will eta-reduce this structure.

  Example:
  ```lean
  structure EquivPlusData (α β) extends α ≃ β := (data : bool)
  @[simps] def bar {α} : EquivPlusData α α := { data := true, ..equiv.refl α }
  ```
  generates the following:
  ```lean
  @[simp] lemma bar_toEquiv : ∀ {α : Sort*}, bar.toEquiv = equiv.refl α
  @[simp] lemma bar_data : ∀ {α : Sort*}, bar.data = tt
  ```
  This is true, even though Lean inserts an eta-expanded version of `equiv.refl α` in the
  definition of `bar`.
* For configuration options, see the doc string of `simpsCfg`.
* The precise syntax is `('simps' ident* e)`, where `e` is an Expression of type `simpsCfg`.
* `@[simps]` reduces let-expressions where necessary.
* When option `trace.simps.verbose` is true, `simps` will print the projections it finds and the
  lemmas it generates. The same can be achieved by using `@[simps?]`, except that in this case it
  will not print projection information.
* Use `@[toAdditive, simps]` to apply both `toAdditive` and `simps` to a definition, making sure
  that `simps` comes after `toAdditive`. This will also generate the additive versions of all
  `simp` lemmas.
-/
/- If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens, so is not included in the official doc). -/
@[user_attribute]
def simpsAttr : user_attribute Unit (Bool × List String × SimpsCfg) where
  Name := `simps
  descr := "Automatically derive lemmas specifying the projections of this declaration."
  parser := simpsParser
  after_set :=
    some fun n _ persistent => do
      guardₓ persistent <|> throwError "`simps` currently cannot be used as a local attribute"
      let (trc, todo, cfg) ← simpsAttr.get_param n
      simpsTac n cfg todo trc

add_tactic_doc { Name := "simps", category := DocCategory.attr, declNames := [`simpsAttr], tags := ["simplification"] }



-/


/--
  Defines the user attribute `simps` for automatic generation of `@[simp]` lemmas for projections.
-/
initialize simpsAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `simps
    descr := "Automatically derive lemmas specifying the projections of this declaration.",
    getParam := fun
    -- TODO implement support for `config := ...`
    | _, `(attr|simps $[$ids]*) => pure $ ids.map (·.getId.eraseMacroScopes)
    | _, stx => throwError "unexpected simps syntax {stx}"
  }

/-!
-- FROM LEAN 3

add_tactic_doc
{ name                     := "initialize_simps_projections",
  category                 := doc_category.cmd,
  declNames               := [`initializeSimpsProjectionsCmd],
  tags                     := ["simplification"] }

/--
  Configuration options for the `@[simps]` attribute.
  * `attrs` specifies the list of attributes given to the generated lemmas. Default: ``[`simp]``.
    The attributes can be either basic attributes, or user attributes without parameters.
    There are two attributes which `simps` might add itself:
    * If ``[`simp]`` is in the list, then ``[`_refl_lemma]`` is added automatically if appropriate.
    * If the definition is marked with `@[toAdditive ...]` then all generated lemmas are marked
      with `@[toAdditive]`. This is governed by the `addAdditive` configuration option.
  * if `simpRhs` is `true` then the right-hand-side of the generated lemmas will be put in
    simp-normal form. More precisely: `dsimp, simp` will be called on all these Expressions.
    See note [dsimp, simp].
  * `typeMd` specifies how aggressively definitions are unfolded in the type of Expressions
    for the purposes of finding out whether the type is a function type.
    Default: `instances`. This will unfold coercion instances (so that a coercion to a function type
    is recognized as a function type), but not declarations like `set`.
  * `rhsMd` specifies how aggressively definition in the declaration are unfolded for the purposes
    of finding out whether it is a constructor.
    Default: `reducible`
    Exception: `@[simps]` will automatically add the options
    `{rhsMd := semireducible, simpRhs := true}` if the given definition is not a constructor with
    the given reducibility setting for `rhsMd`.
  * If `fullyApplied` is `false` then the generated `simp` lemmas will be between non-fully applied
    terms, i.e. equalities between functions. This does not restrict the recursive behavior of
    `@[simps]`, so only the "final" projection will be non-fully applied.
    However, it can be used in combination with explicit field names, to get a partially applied
    intermediate projection.
  * The option `notRecursive` contains the list of names of types for which `@[simps]` doesn't
    recursively apply projections. For example, given an equivalence `α × β ≃ β × α` one usually
    wants to only apply the projections for `equiv`, and not also those for `×`. This option is
    only relevant if no explicit projection names are given as argument to `@[simps]`.
  * The option `trace` is set to `true` when you write `@[simps?]`. In this case, the attribute will
    print all generated lemmas. It is almost the same as setting the option `trace.simps.verbose`,
    except that it doesn't print information about the found projections.
  * if `addAdditive` is `some nm` then `@[toAdditive]` is added to the generated lemma. This
    option is automatically set to `true` when the original declaration was tagged with
    `@[toAdditive, simps]` (in that order), where `nm` is the additive name of the original
    declaration.
-/
@[derive [has_reflect, inhabited]] structure simpsCfg :=
(attrs         := [`simp])
(simpRhs      := false)
(typeMd       := transparency.instances)
(rhsMd        := transparency.none)
(fullyApplied := true)
(notRecursive := [`prod, `pprod])
(trace         := false)
(addAdditive  := @none name)

/-- A common configuration for `@[simps]`: generate equalities between functions instead equalities
  between fully applied Expressions. -/
def asFn : simpsCfg := {fullyApplied := false}
/-- A common configuration for `@[simps]`: don't tag the generated lemmas with `@[simp]`. -/
def lemmas_only : simpsCfg := {attrs := []}

/--
  Get the projections of a structure used by `@[simps]` applied to the appropriate arguments.
  Returns a list of tuples
  ```
  (corresponding right-hand-side, given projection name, projection Expression, projection numbers,
    used by default, is prefix)
  ```
  (where all fields except the first are packed in a `ProjectionData` structure)
  one for each projection. The given projection name is the name for the projection used by the user
  used to generate (and parse) projection names. For example, in the structure

  Example 1: ``simpsGetProjectionExprs env `(α × β) `(⟨x, y⟩)`` will give the output
  ```
    [(`(x), `fst, `(@prod.fst.{u v} α β), [0], true, false),
     (`(y), `snd, `(@prod.snd.{u v} α β), [1], true, false)]
  ```

  Example 2: ``simpsGetProjectionExprs env `(α ≃ α) `(⟨id, id, λ _, rfl, λ _, rfl⟩)``
  will give the output
  ```
    [(`(id), `apply, `(coe), [0], true, false),
     (`(id), `symm_apply, `(λ f, ⇑f.symm), [1], true, false),
     ...,
     ...]
  ```
-/
meta def simpsGetProjectionExprs (e : environment) (tgt : Expr)
  (rhs : Expr) (cfg : simpsCfg) : tactic $ list $ Expr × ProjectionData := do
  let params := getAppArgs tgt, -- the parameters of the structure
  (params.zip $ (getAppArgs rhs).take params.length).mmap' (λ ⟨a, b⟩, isDefEq a b)
    <|> throwError "unreachable code (1)",
  let str := tgt.getAppFn.constName,
  let rhsArgs := (getAppArgs rhs).drop params.length, -- the fields of the object
  (rawUnivs, projDeclata) ← simpsGetRawProjections e str false [] cfg.trace,
  let univs := rawUnivs.zip tgt.getAppFn.levelParams,
  let newProjDeclata : list $ Expr × ProjectionData := projDeclata.map $
    λ proj, (rhsArgs.inth proj.projNrs.head,
      { Expr := (proj.expr.instantiateUnivParams univs).instantiateLambdasOrApps params,
        projNrs := proj.projNrs.tail,
        .. proj }),
  return newProjDeclata

/-- Add a lemma with `nm` stating that `lhs = rhs`. `type` is the type of both `lhs` and `rhs`,
  `args` is the list of local constants occurring, and `univs` is the list of universe variables. -/
meta def simpsAddProjection (nm : name) (type lhs rhs : Expr) (args : list Expr)
  (univs : list name) (cfg : simpsCfg) : tactic unit := do
  trace[simps.debug] trace!
    "[simps] > Planning to add the equality\n        > {lhs} = ({rhs} : {type})",
  lvl ← getUnivLevel type,
  -- simplify `rhs` if `cfg.simpRhs` is true
  (rhs, prf) ← do { guard cfg.simpRhs,
    rhs' ← rhs.dsimp {fail_if_unchanged := false},
    trace[simps.debug] $ when (rhs ≠ rhs') trace!
      "[simps] > `dsimp` simplified rhs to\n        > {rhs'}",
    (rhsprf1, rhsprf2, ns) ← rhs'.simp {fail_if_unchanged := false},
    trace[simps.debug] $ when (rhs' ≠ rhsprf1) trace!
      "[simps] > `simp` simplified rhs to\n        > {rhsprf1}",
    return (prod.mk rhsprf1 rhsprf2) }
    <|> return (rhs, const `eq.refl [lvl] type lhs),
  let eqAp := const `eq [lvl] type lhs rhs,
  declName ← get_unused_declName nm,
  let declType := eqAp.pis args,
  let declValue := prf.lambdas args,
  let decl := declaration.thm declName univs declType (pure declValue),
  when cfg.trace trace!
    "[simps] > adding projection {declName}:\n        > {declType}",
  decorate_error ("Failed to add projection lemma " ++ declName.to_string ++ ". Nested error:") $
    add_decl decl,
  b ← succeeds $ isDefEq lhs rhs,
  when (b ∧ `simp ∈ cfg.attrs) (set_basic_attribute `_refl_lemma declName true),
  cfg.attrs.mmap' $ λ nm, set_attribute nm declName true,
  when cfg.addAdditive.isSome $
    toAdditive.attr.set declName ⟨false, cfg.trace, cfg.addAdditive.iget, none, true⟩ tt

/-- Derive lemmas specifying the projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  `toApply` is non-empty after a custom projection that is a composition of multiple projections
  was just used. In that case we need to apply these projections before we continue changing lhs. -/
meta def simpsAddProjections : Π (e : environment) (nm : name)
  (type lhs rhs : Expr) (args : list Expr) (univs : list name) (mustBeStr : bool)
  (cfg : simpsCfg) (todo : list string) (toApply : list ℕ), tactic unit
| e nm type lhs rhs args univs mustBeStr cfg todo toApply := do
  -- we don't want to unfold non-reducible definitions (like `set`) to apply more arguments
  trace[simps.debug] trace!
    "[simps] > Type of the Expression before normalizing: {type}",
  (typeArgs, tgt) ← open_pis_whnf type cfg.typeMd,
  trace[simps.debug] trace!"[simps] > Type after removing pi's: {tgt}",
  tgt ← whnf tgt,
  trace[simps.debug] trace!"[simps] > Type after reduction: {tgt}",
  let newArgs := args ++ typeArgs,
  let lhsAp := lhs.instantiateLambdasOrApps typeArgs,
  let rhsAp := rhs.instantiateLambdasOrApps typeArgs,
  let str := tgt.getAppFn.constName,
  /- We want to generate the current projection if it is in `todo` -/
  let todoNext := todo.filter (≠ ""),
  /- Don't recursively continue if `str` is not a structure or if the structure is in
    `notRecursive`. -/
  if e.is_structure str ∧ ¬(todo = [] ∧ str ∈ cfg.notRecursive ∧ ¬mustBeStr) then do
    [intro] ← return $ e.constructors_of str | throwError "unreachable code (3)",
    rhsWhnf ← whnf rhsAp cfg.rhsMd,
    (rhsAp, todoNow) ← -- `todoNow` means that we still have to generate the current simp lemma
      if ¬ isConstantOf rhsAp.getAppFn intro ∧
        isConstantOf rhsWhnf.getAppFn intro then
      /- If this was a desired projection, we want to apply it before taking the whnf.
        However, if the current field is an eta-expansion (see below), we first want
        to eta-reduce it and only then construct the projection.
        This makes the flow of this function messy. -/
      when ("" ∈ todo ∧ toApply = []) (if cfg.fullyApplied then
        simpsAddProjection nm tgt lhsAp rhsAp newArgs univs cfg else
        simpsAddProjection nm type lhs rhs args univs cfg) >>
      return (rhsWhnf, false) else
      return (rhsAp, "" ∈ todo ∧ toApply = []),
    if isConstantOf (getAppFn rhsAp) intro then do -- if the value is a constructor application
      projInfo ← simpsGetProjectionExprs e tgt rhsAp cfg,
      trace[simps.debug] trace!"[simps] > Raw projection information:\n  {projInfo}",
      eta ← rhsAp.is_eta_expansion, -- check whether `rhsAp` is an eta-expansion
      let rhsAp := eta.lhoare rhsAp, -- eta-reduce `rhsAp`
      /- As a special case, we want to automatically generate the current projection if `rhsAp`
        was an eta-expansion. Also, when this was a desired projection, we need to generate the
        current projection if we haven't done it above. -/
      when (todoNow ∨ (todo = [] ∧ eta.isSome ∧ toApply = [])) $
        if cfg.fullyApplied then
          simpsAddProjection nm tgt lhsAp rhsAp newArgs univs cfg else
          simpsAddProjection nm type lhs rhs args univs cfg,
      /- If we are in the middle of a composite projection. -/
      when (toApply ≠ []) $ do
      { ⟨newRhs, proj, projExprxpr, projNrs, isDefault, isPrefix⟩ ←
          return $ projInfo.inth toApply.head,
        newType ← inferType newRhs,
        trace[simps.debug]
          trace!"[simps] > Applying a custom composite projection. Current lhs:
        >  {lhsAp}",
        simpsAddProjections e nm newType lhsAp newRhs newArgs univs false cfg todo
          toApply.tail },
      /- We stop if no further projection is specified or if we just reduced an eta-expansion and we
      automatically choose projections -/
      when ¬(toApply ≠ [] ∨ todo = [""] ∨ (eta.isSome ∧ todo = [])) $ do
        let projs : list name := projInfo.map $ λ x, x.snd.name,
        let todo := if toApply = [] then todoNext else todo,
        -- check whether all elements in `todo` have a projection as prefix
        guard (todo.all $ λ x, projs.any $ λ proj, ("_" ++ proj.last).isPrefix_of x) <|>
          let x := (todo.find $ λ x, projs.all $ λ proj, ¬ ("_" ++ proj.last).isPrefix_of x).iget,
            simpLemma := nm.append_suffix x,
            neededProj := (x.split_on '_').tail.head in
          fail!
"Invalid simp lemma {simpLemma}. Structure {str} does not have projection {neededProj}.
The known projections are:
  {projs}
You can also see this information by running
  `initialize_simps_projections? {str}`.
Note: these projection names might not correspond to the projection names of the structure.",
        projInfo.mmap_with_index' $
          λ projNr ⟨newRhs, proj, projExprxpr, projNrs, isDefault, isPrefix⟩, do
          newType ← inferType newRhs,
          let new_todo :=
            todo.filterMap $ λ x, x.get_rest ("_" ++ proj.last),
          -- we only continue with this field if it is non-propositional or mentioned in todo
          when ((isDefault ∧ todo = []) ∨ new_todo ≠ []) $ do
            let newLhs := projExprxpr.instantiateLambdasOrApps [lhsAp],
            let newName := nm.append_to_last proj.last isPrefix,
            let new_cfg := { addAdditive := cfg.addAdditive.map $
              λ nm, nm.append_to_last (toAdditive.guess_name proj.last) isPrefix, ..cfg },
            trace[simps.debug] trace!"[simps] > Recursively add projections for:
        >  {newLhs}",
            simpsAddProjections e newName newType newLhs newRhs newArgs univs
              false new_cfg new_todo projNrs
    -- if I'm about to run into an error, try to set the transparency for `rhsMd` higher.
    else if cfg.rhsMd = transparency.none ∧ (mustBeStr ∨ todoNext ≠ [] ∨ toApply ≠ []) then do
      when cfg.trace trace!
        "[simps] > The given definition is not a constructor application:
        >   {rhsAp}
        > Retrying with the options {{ rhsMd := semireducible, simpRhs := true}.",
      simpsAddProjections e nm type lhs rhs args univs mustBeStr
        { rhsMd := semireducible, simpRhs := true, ..cfg} todo toApply
    else do
      when (toApply ≠ []) $
        fail!"Invalid simp lemma {nm}.
The given definition is not a constructor application:\n  {rhsAp}",
      when mustBeStr $
        fail!"Invalid `simps` attribute. The body is not a constructor application:\n  {rhsAp}",
      when (todoNext ≠ []) $
        fail!"Invalid simp lemma {nm.append_suffix todoNext.head}.
The given definition is not a constructor application:\n  {rhsAp}",
      if cfg.fullyApplied then
        simpsAddProjection nm tgt lhsAp rhsAp newArgs univs cfg else
        simpsAddProjection nm type lhs rhs args univs cfg
  else do
    when mustBeStr $
      fail!"Invalid `simps` attribute. Target {str} is not a structure",
    when (todoNext ≠ [] ∧ str ∉ cfg.notRecursive) $
        let first_todo := todoNext.head in
        fail!"Invalid simp lemma {nm.append_suffix first_todo}.
Projection {(first_todo.split_on '_').tail.head} doesn't exist, because target is not a structure.",
    if cfg.fullyApplied then
      simpsAddProjection nm tgt lhsAp rhsAp newArgs univs cfg else
      simpsAddProjection nm type lhs rhs args univs cfg

/-- `simpsTac` derives `simp` lemmas for all (nested) non-Prop projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  If `shortNm` is true, the generated names will only use the last projection name.
  If `trc` is true, trace as if `trace.simps.verbose` is true. -/
meta def simpsTac (nm : name) (cfg : simpsCfg := {}) (todo : list string := []) (trc := false) :
  tactic unit := do
  e ← getEnv,
  d ← e.get nm,
  let lhs : Expr := const d.name d.levelParams,
  let todo := todo.dedup.map $ λ proj, "_" ++ proj,
  let cfg := { trace := cfg.trace || ((← getOptions) |>.getBool `simps.verbose || trc, ..cfg },
  b ← hasAttribute' `toAdditive nm,
  cfg ← if b then do
  { dict ← toAdditive.aux_attr.get_cache,
    when cfg.trace
      trace!"[simps] > @[toAdditive] will be added to all generated lemmas.",
    return { addAdditive := dict.find nm, ..cfg } } else
    return cfg,
  simpsAddProjections e nm d.type lhs d.value [] d.univ_params true cfg todo []

/-- The parser for the `@[simps]` attribute. -/
meta def simpsParser : parser (bool × list string × simpsCfg) := do
/- note: we don't check whether the user has written a nonsense namespace in an argument. -/
prod.mk <$> isSome <$> (tk "?")? <*>
  (prod.mk <$> many (name.last <$> ident) <*>
  (do some e ← parser.pexpr? | return {}, evalPexpr simpsCfg e))

/--
The `@[simps]` attribute automatically derives lemmas specifying the projections of this
declaration.

Example:
```lean
@[simps] def foo : ℕ × ℤ := (1, 2)
```
derives two `simp` lemmas:
```lean
@[simp] lemma foo_fst : foo.fst = 1
@[simp] lemma foo_snd : foo.snd = 2
```

* It does not derive `simp` lemmas for the prop-valued projections.
* It will automatically reduce newly created beta-redexes, but will not unfold any definitions.
* If the structure has a coercion to either sorts or functions, and this is defined to be one
  of the projections, then this coercion will be used instead of the projection.
* If the structure is a class that has an instance to a notation class, like `Mul`, then this
  notation is used instead of the corresponding projection.
* You can specify custom projections, by giving a declaration with name
  `{StructureName}.simps.{projectionName}`. See Note [custom simps projection].

  Example:
  ```lean
  def equiv.simps.invFun (e : α ≃ β) : β → α := e.symm
  @[simps] def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩
  ```
  generates
  ```
  @[simp] lemma equiv.trans_toFun : ∀ {α β γ} (e₁ e₂) (a : α), ⇑(e₁.trans e₂) a = (⇑e₂ ∘ ⇑e₁) a
  @[simp] lemma equiv.trans_invFun : ∀ {α β γ} (e₁ e₂) (a : γ),
    ⇑((e₁.trans e₂).symm) a = (⇑(e₁.symm) ∘ ⇑(e₂.symm)) a
  ```

* You can specify custom projection names, by specifying the new projection names using
  `initialize_simps_projections`.
  Example: `initialize_simps_projections equiv (toFun → apply, invFun → symm_apply)`.
  See `initializeSimpsProjectionsCmd` for more information.

* If one of the fields itself is a structure, this command will recursively create
  `simp` lemmas for all fields in that structure.
  * Exception: by default it will not recursively create `simp` lemmas for fields in the structures
    `prod` and `pprod`. You can give explicit projection names or change the value of
    `simpsCfg.notRecursive` to override this behavior.

  Example:
  ```lean
  structure MyProd (α β : Type*) := (fst : α) (snd : β)
  @[simps] def foo : prod ℕ ℕ × MyProd ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_snd_fst : foo.snd.fst = 3
  @[simp] lemma foo_snd_snd : foo.snd.snd = 4
  ```

* You can use `@[simps proj1 proj2 ...]` to only generate the projection lemmas for the specified
  projections.
* Recursive projection names can be specified using `proj1_proj2_proj3`.
  This will create a lemma of the form `foo.proj1.proj2.proj3 = ...`.

  Example:
  ```lean
  structure MyProd (α β : Type*) := (fst : α) (snd : β)
  @[simps fst fst_fst snd] def foo : prod ℕ ℕ × MyProd ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_fst_fst : foo.fst.fst = 1
  @[simp] lemma foo_snd : foo.snd = {fst := 3, snd := 4}
  ```
* If one of the values is an eta-expanded structure, we will eta-reduce this structure.

  Example:
  ```lean
  structure EquivPlusData (α β) extends α ≃ β := (data : bool)
  @[simps] def bar {α} : EquivPlusData α α := { data := true, ..equiv.refl α }
  ```
  generates the following:
  ```lean
  @[simp] lemma bar_toEquiv : ∀ {α : Sort*}, bar.toEquiv = equiv.refl α
  @[simp] lemma bar_data : ∀ {α : Sort*}, bar.data = tt
  ```
  This is true, even though Lean inserts an eta-expanded version of `equiv.refl α` in the
  definition of `bar`.
* For configuration options, see the doc string of `simpsCfg`.
* The precise syntax is `('simps' ident* e)`, where `e` is an Expression of type `simpsCfg`.
* `@[simps]` reduces let-expressions where necessary.
* When option `trace.simps.verbose` is true, `simps` will print the projections it finds and the
  lemmas it generates. The same can be achieved by using `@[simps?]`, except that in this case it
  will not print projection information.
* Use `@[toAdditive, simps]` to apply both `toAdditive` and `simps` to a definition, making sure
  that `simps` comes after `toAdditive`. This will also generate the additive versions of all
  `simp` lemmas.
-/
/- If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens, so is not included in the official doc). -/
@[user_attribute] meta def simpsAttr : user_attribute unit (bool × list string × simpsCfg) :=
{ name := `simps,
  descr := "Automatically derive lemmas specifying the projections of this declaration.",
  parser := simpsParser,
  after_set := some $
    λ n _ persistent, do
      guard persistent <|> throwError "`simps` currently cannot be used as a local attribute",
      (trc, todo, cfg) ← simpsAttr.get_param n,
      simpsTac n cfg todo trc }

add_tactic_doc
{ name                     := "simps",
  category                 := doc_category.attr,
  declNames               := [`simpsAttr],
  tags                     := ["simplification"] }

-/


/-!

MAYBE NEEDED


unsafe instance : has_to_tactic_format ProjectionData :=
  ⟨fun ⟨a, b, c, d, e⟩ =>
    (fun x =>
        group <|
          nest 1 <|
            to_fmt "⟨" ++ to_fmt a ++ to_fmt "," ++ line ++ x ++ to_fmt "," ++ line ++ to_fmt c ++ to_fmt "," ++ line ++
                      to_fmt d ++
                    to_fmt "," ++
                  line ++
                to_fmt e ++
              to_fmt "⟩") <$>
      pp b⟩

unsafe instance : has_to_format ParsedProjectionData :=
  ⟨fun ⟨a, b, c, d⟩ =>
    group <|
      nest 1 <|
        to_fmt "⟨" ++ to_fmt a ++ to_fmt "," ++ line ++ to_fmt b ++ to_fmt "," ++ line ++ to_fmt c ++ to_fmt "," ++
              line ++
            to_fmt d ++
          to_fmt "⟩"⟩


-/
