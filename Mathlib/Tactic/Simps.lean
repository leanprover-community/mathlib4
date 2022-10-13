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

Partial progress to port the `@[simps]` attribute implementation from mathlib3.

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

## Changes w.r.t. Lean 3

There are some small changes in the attribute. None of them should have great effects
* The attribute will now raise an error if it tries to generate a lemma when there already exists
  a lemma with that name (in Lean 3 it would generate a different unique name)
* `transparency.none` has been replaced by `TransparencyMode.reducible`
* The `attr` configuration option has been split into `isSimp` and `attrs` (for extra attributes)
  (todo)

## Tags

structures, projections, simp, simplifier, generates declarations
-/

/-
Questions
- are there useful commands for compositions of structure projections?
- is _refl_lemma still a thing? -> probably, but I can call a function that should add it
- When a coercion is inserted into a term, how does that look? -> you never see coercions
- what is the Lean 4 equivalent of has_to_format/has_to_tactic_format?
- primitive projections -> you never see these normally
-/

/- Question: How to deal with all the different kinds of attributes? Is there a uniform
  "add attribute A to declaration X" or "check whether X has attribute A"?
  Can I add an attribute without constructing a complicated `Syntax` object? -/
/- question: Is there a reason `TransparencyMode.none` is not a thing anymore? (not super important) -/
/- question: what is a reasonable low number as second argument of `synthInstance`?
  What does this number measure?-/


/-
-- PR opportunity: dsimp using iff.rfl lemmas:
* In file `Tactic/Simp/SimpTheorems` we check whether a proof is `Eq.refl` to decide
whether this is a `rflTheorem`. This should also check for `Iff.rfl`
-/

-- move
namespace String

/-- `isPrefixOf? s pre` returns `some post` if `s = pre ++ post`.
  If `pre` is not a prefix of `s`, it returns `none`. -/
def isPrefixOf? (s pre : String) : Option String :=
if startsWith s pre then some <| s.drop pre.length else none

end String

open Lean Meta Parser Elab Term Command

-- move
namespace Lean.Meta
open Tactic Simp
/- make simp context giving data instead of Syntax. Doesn't support arguments.
Intended to be very similar to `Lean.Elab.Tactic.mkSimpContext`
Todo: support arguments. -/
def mkSimpContextResult (cfg : Meta.Simp.Config := {}) (simpOnly := false) (kind := SimpKind.simp)
  (dischargeWrapper := DischargeWrapper.default) (hasStar := false) :
  MetaM MkSimpContextResult := do
  match dischargeWrapper with
  | .default => pure ()
  | _ =>
    if kind == SimpKind.simpAll then
      throwError "'simp_all' tactic does not support 'discharger' option"
    if kind == SimpKind.dsimp then
      throwError "'dsimp' tactic does not support 'discharger' option"
  let simpTheorems ← if simpOnly then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  else
    getSimpTheorems
  let congrTheorems ← getSimpCongrTheorems
  let ctx : Simp.Context ← pure {
    config      := cfg
    simpTheorems := #[simpTheorems], congrTheorems
  }
  if !hasStar then
    return { ctx, dischargeWrapper }
  else
    let mut simpTheorems := ctx.simpTheorems
    let hs ← getPropHyps
    for h in hs do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    let ctx := { ctx with simpTheorems }
    return { ctx, dischargeWrapper }

def mkSimpContext (cfg : Meta.Simp.Config := {}) (simpOnly := false) (kind := SimpKind.simp)
  (dischargeWrapper := DischargeWrapper.default) (hasStar := false) :
  MetaM Simp.Context := do
  let data ← mkSimpContextResult cfg simpOnly kind dischargeWrapper hasStar
  return data.ctx

end Lean.Meta

def hasSimpAttribute (env : Environment) (declName : Name) : Bool :=
  simpExtension.getState env |>.lemmaNames.contains <| .decl declName


namespace Lean.Parser
namespace Attr

syntax simpsArgsRest := (" (" &"config" " := " term ")")? (ppSpace ident)*

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
  See `elabInitializeSimpsProjections` for more information.

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
syntax (name := simps) "simps" "?"? simpsArgsRest : attr

@[inheritDoc simps]
macro "simps?" rest:simpsArgsRest : attr => `(attr| simps ? $rest)

end Attr

namespace Command

syntax simpsRule.rename := ident " → " ident
syntax simpsRule.erase := "-" ident
syntax simpsRule := (simpsRule.rename <|> simpsRule.erase) &" as_prefix"?
syntax simpsProj := (ppSpace ident (" (" simpsRule,+ ")")?)


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
syntax (name := initialize_simps_projections)
  "initialize_simps_projections" "?"? simpsProj : command

@[inheritDoc «initialize_simps_projections»]
macro "initialize_simps_projections?" rest:simpsProj : command =>
  `(initialize_simps_projections ? $rest)


/-- The `@[notation_class]` attribute specifies that this is a notation class,
  and this notation should be used instead of projections by @[simps].
  * The first argument `true` for notation classes and `false` for classes applied to the structure,
    like `CoeSort` and `CoeFun`
  * The second argument is the name of the projection (by default it is the first projection
    of the structure)
-/
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

/- todo: should this be TagAttribute? Can we "initialize" TagAttribute with a certain cache? -/
initialize notationClassAttr : NameMapExtension Unit ←
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
-- todo: use `MessageData` properly in the definition
def projectionsInfo (l : List ProjectionData) (pref : String) (str : Name) : MessageData :=
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
      fun n p => (fun x => (x, n, p)) <$> proj.isPrefixOf? ("_" ++ p.getString!)
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
    if projRest.isEmpty then pure (← mkLambdaFVars args newX, newPos)
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
  trace[simps.debug] "Projection info after applying the rules: {projs}."
  unless (projs.map (·.newName)).toList.Nodup do throwError
    "Invalid projection names. Two projections have the same name.\n{""
    }This is likely because a custom composition of projections was given the same name as an {""
    }existing projection. Solution: rename the existing projection (before naming the {""
    }custom projection)."
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
      logInfo m!"[simps] > found custom projection for {proj.newName}:\n        > {customProj}"
    match (← MetaM.run' $ isDefEq customProj rawExpr) with
    | true => pure {proj with expr? := some customProj, projNrs := nrs, isChanged := true}
    | false =>
      -- if the type of the Expression is different, we show a different error message, because
      -- (in Lean 3) just stating that the expressions are different is quite unhelpful
      let customProjType ← MetaM.run' (inferType customProj)
      let rawExprType ← MetaM.run' (inferType rawExpr)
      if (← MetaM.run' (isDefEq customProjType rawExprType)) then throwError -- todo: indentExpr doesn't work here?
        "Invalid custom projection:\n  {customProj}\n{""
        }Expression is not definitionally equal to {rawExpr}" else throwError
        "Invalid custom projection:\n  {customProj}\n{""
        }Expression has different type than {str ++ proj.origName}. Given type:\n{""
        }  {customProjType}\nExpected type:\n  {rawExprType}\n{""
        }Note: make sure order of implicit arguments is exactly the same."
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
      trace[simps.debug] "info: (relevantProj, rawExprLambda)"
      pure (relevantProj, rawExprLambda)
  match projs.findIdx? fun x => some x.origName == relevantProj with
  | none =>
    if trc then
      logInfo m!"[simps] > Warning: The structure has an instance for {className}, {""
        }but it is not definitionally equal to any projection."
    throwError "" -- will be caught by <|> in `simpsFindAutomaticProjections`
  | some pos =>
    trace[simps.debug] "The raw projection is:\n {rawExprLambda}"
    projs.mapIdxM fun nr x => if nr.1 = pos then do
      if x.isChanged then
        if trc then
          logInfo m!"[simps] > Warning: Projection {relevantProj} is definitionally equal to\n  {""
            }{rawExprLambda}\nHowever, this is not used since a custom simps projection is {""
            }specified by the user."
        pure x else
        if trc then
          logInfo m!"[simps] > Using notation from {className} for projection {relevantProj}."
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
  let trc := trc || (← getOptions).getBool `trace.simps.verbose
  -- to do: double check tracing
  match (simpsStructure.getState env).find? str with
  | some data =>
    -- We always print the projections when they already exists and are called by
    -- `initialize_simps_projections`.
    if traceIfExists || (← getOptions).getBool `trace.simps.verbose then
      logInfo <|
        projectionsInfo data.2.toList "Already found projection information for structure" str
    pure data
  | none =>
    if trc then
      logInfo m!"[simps] > generating projection information for structure {str}."
    trace[simps.debug] "Applying the rules {rules}."
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
      logInfo <| projectionsInfo projs.toList "generated projections for" str
    simpsStructure.add str (rawLevels, projs)
    trace[simps.debug] "Generated raw projection data:\n{(rawLevels, projs)}"
    pure (rawLevels, projs)

library_note "custom simps projection"
/-- You can specify custom projections for the `@[simps]` attribute.
To do this for the projection `MyStructure.originalProjection` by adding a declaration
`MyStructure.simps.myProjection` that is definitionally equal to
`MyStructure.originalProjection` but has the projection in the desired (simp-normal) form.
Then you can call
```
initialize_simps_projections (originalProjection → myProjection, ...)
```
to register this projection. See `elabInitializeSimpsProjections` for more information.

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

@[commandElab «initialize_simps_projections»] def elabInitializeSimpsProjections : CommandElab
| `(initialize_simps_projections $[?%$trc]? $id $[($stxs,*)]?) => do
  let stxs := stxs.getD <| .mk #[]
  let rules ← stxs.getElems.raw.mapM elabSimpsRule
  let nm ← resolveGlobalConstNoOverload id
  _ ← liftCoreM <| simpsGetRawProjections nm true rules trc.isSome
| _ => throwUnsupportedSyntax

structure Simps.Config where
  isSimp := true
  attrs : List Name := [] -- todo
  simpRhs := false
  typeMd := TransparencyMode.instances
  rhsMd := TransparencyMode.reducible -- was `none` in Lean 3
  fullyApplied := true
  notRecursive := [`Prod, `PProd]
  trace := false
  debug := false -- adds a few checks (not used much)
  addAdditive := @none Name
  deriving Inhabited

/-- Function elaborating Simps.Config -/
declare_config_elab elabSimpsConfig Simps.Config

/-- A common configuration for `@[simps]`: generate equalities between functions instead equalities
  between fully applied Expressions. -/
def Simps.Config.asFn : Simps.Config where
  fullyApplied := false

/-- A common configuration for `@[simps]`: don't tag the generated lemmas with `@[simp]`. -/
def Simps.Config.lemmasOnly : Simps.Config where
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
def simpsGetProjectionExprs (tgt : Expr) (rhs : Expr) (cfg : Simps.Config) :
    MetaM <| Array <| Expr × ProjectionData := do
  -- the parameters of the structure
  let params := tgt.getAppArgs
  if cfg.debug && !(← (params.zip rhs.getAppArgs).allM fun ⟨a, b⟩ => isDefEq a b) then
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
  pure u

/-- Add a lemma with `nm` stating that `lhs = rhs`. `type` is the type of both `lhs` and `rhs`,
  `args` is the list of local constants occurring, and `univs` is the list of universe variables. -/
def simpsAddProjection (ref : Syntax) (declName : Name) (type lhs rhs : Expr) (args : Array Expr)
  (univs : List Name) (cfg : Simps.Config) : MetaM Unit := do
  trace[simps.debug] "Planning to add the equality\n        > {lhs} = ({rhs} : {type})"
  let env ← getEnv
  if (env.find? declName).isSome then -- diverging behavior from Lean 3
    throwError "simps tried to add lemma {declName} to the environment, but it already exists."
    -- simplify `rhs` if `cfg.simpRhs` is true
  let lvl ← getUnivLevel type
  let (rhs, prf) ← do
    let defaultPrf := mkAppN (mkConst `Eq.refl [lvl]) #[type, lhs]
    if !cfg.simpRhs then
      pure (rhs, defaultPrf) else
      let ctx ← mkSimpContext
      let (rhs2, _) ← dsimp rhs ctx
      if rhs != rhs2 then
        trace[simps.debug] "`dsimp` simplified rhs to\n        > {rhs2}" else
        trace[simps.debug] "`dsimp` failed to simplify rhs"
      let (result, _) ← simp rhs2 ctx
      if rhs2 != result.expr then
        trace[simps.debug] "`simp` simplified rhs to\n        > {result.expr}" else
        trace[simps.debug] "`simp` failed to simplify rhs"
      pure (result.expr, result.proof?.getD defaultPrf)
  let eqAp := mkAppN (mkConst `Eq [lvl]) #[type, lhs, rhs]
  let declType ← mkForallFVars args eqAp
  let declValue ← mkLambdaFVars args prf
  let decl := Declaration.thmDecl
    { name := declName
      levelParams := univs
      type := declType
      value := declValue }
  if cfg.trace then
    logInfo m!"[simps] > adding projection {declName}:\n        > {declType}"
  -- what is the best way to add some decoration to an error message?
  -- match (← getEnv).addDecl decl with
  -- | Except.ok    env => setEnv env
  -- | Except.error ex  => throwError
  --     "Failed to add projection lemma {declName}. Nested error:\n{ex.toMessageData (← getOptions)}"
  try addDecl decl
  catch ex =>
    throwError "Failed to add projection lemma {declName}. Nested error:\n{ex.toMessageData}"
  if cfg.isSimp then
    addSimpTheorem simpExtension declName true false .global <| eval_prio default
  -- cfg.attrs.mapM fun nm => setAttribute nm declName tt -- todo: deal with attributes
  if cfg.addAdditive.isSome then
    ToAdditive.addToAdditiveAttr declName ⟨false, cfg.trace, cfg.addAdditive.get!, none, true, ref⟩

/-- Update the last component of a name. -/
def Lean.Name.updateLast (f : String → String) : Name → Name
| (.str n s) => .str n (f s)
| n          => n

/-- `updateName nm s is_prefix` adds `s` to the last component of `nm`,
  either as prefix or as suffix (specified by `isPrefix`), separated by `_`.
  Used by `simps_add_projections`. -/
def updateName (nm : Name) (s : String) (isPrefix : Bool) : Name :=
nm.updateLast λ s' => if isPrefix then s ++ "_" ++ s' else s' ++ "_" ++ s

def Lean.Name.getString : Name → String
| .str _ s => s
| _       => ""


/-- Derive lemmas specifying the projections of the declaration.
  `nm`: name of the lemma
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  `toApply` is non-empty after a custom projection that is a composition of multiple projections
  was just used. In that case we need to apply these projections before we continue changing `lhs`.
  `simpLemmas`: names of the simp lemmas added so far.(simpLemmas : Array Name)
  -/
partial def simpsAddProjections (env : Environment) (ref : Syntax) (nm : Name) (type lhs rhs : Expr)
  (args : Array Expr) (univs : List Name) (mustBeStr : Bool) (cfg : Simps.Config) (todo : List String)
  (toApply : List ℕ) : MetaM (Array Name) := do
  -- we don't want to unfold non-reducible definitions (like `set`) to apply more arguments
  trace[simps.debug] "Type of the Expression before normalizing: {type}"
  withTransparency cfg.typeMd <| forallTelescopeReducing type fun typeArgs tgt =>
    withTransparency .default <| do
  trace[simps.debug] "Type after removing pi's: {tgt}"
  let tgt ← whnfD tgt
  trace[simps.debug] "Type after reduction: {tgt}"
  let newArgs := args ++ typeArgs
  let lhsAp := lhs.instantiateLambdasOrApps typeArgs
  let rhsAp := rhs.instantiateLambdasOrApps typeArgs
  let str := tgt.getAppFn.constName
  -- We want to generate the current projection if it is in `todo`
  let todoNext := todo.filter (· ≠ "")
  let strInfo? := getStructureInfo? env str
  /- Don't recursively continue if `str` is not a structure or if the structure is in
  `notRecursive`. -/
  if strInfo?.isNone || (todo.isEmpty && str ∈ cfg.notRecursive && !mustBeStr) then
    if mustBeStr then
      throwError "Invalid `simps` attribute. Target {str} is not a structure"
    if !todoNext.isEmpty && str ∉ cfg.notRecursive then
      let firstTodo := todoNext.head!
      throwError "Invalid simp lemma {nm.appendAfter firstTodo}.\nProjection {""
        }{(firstTodo.splitOn "_").tail.head!} doesn't exist, because target is not a structure."
    if cfg.fullyApplied then
      simpsAddProjection ref nm tgt lhsAp rhsAp newArgs univs cfg else
      simpsAddProjection ref nm type lhs rhs args univs cfg
    pure #[nm] else
  let some (.inductInfo info) ← pure <| env.find? str | throwError "unreachable"
  let [ctor] ← pure info.ctors | throwError "unreachable"
  trace[simps.debug] "{str} is a structure with constructor {ctor}."
  let rhsWhnf ← withTransparency cfg.rhsMd <| whnf rhsAp
  trace[simps.debug] "The right-hand-side {indentExpr rhsAp}\n reduces to {indentExpr rhsWhnf}"
  -- `todoNow` means that we still have to generate the current simp lemma
  let (rhsAp, todoNow) ←
    if !rhsAp.getAppFn.isConstOf ctor ∧ rhsWhnf.getAppFn.isConstOf ctor then
      /- If this was a desired projection, we want to apply it before taking the whnf.
      However, if the current field is an eta-expansion (see below), we first want
      to eta-reduce it and only then construct the projection.
      This makes the flow of this function messy. -/
      if "" ∈ todo && toApply.isEmpty then
        if cfg.fullyApplied then
          simpsAddProjection ref nm tgt lhsAp rhsAp newArgs univs cfg else
          simpsAddProjection ref nm type lhs rhs args univs cfg
      pure (rhsWhnf, false) else
      pure (rhsAp, "" ∈ todo && toApply.isEmpty)
  trace[simps.debug] "Continuing with {indentExpr rhsAp}"
  if !rhsAp.getAppFn.isConstOf ctor then
    -- if I'm about to run into an error, try to set the transparency for `rhsMd` higher.
    if cfg.rhsMd == .reducible && (mustBeStr || !todoNext.isEmpty || !toApply.isEmpty) then
      if cfg.trace then
        logInfo m!"[simps] > The given definition is not a constructor {""
          }application:\n        >   {rhsAp}\n        > Retrying with the options {""
          }\{rhs_md := semireducible, simp_rhs := tt}."
      simpsAddProjections env ref nm type lhs rhs args univs mustBeStr
        { cfg with rhsMd := .default, simpRhs := true } todo toApply else
    if !toApply.isEmpty then
      throwError "Invalid simp lemma {nm}.\nThe given definition is not a constructor {""
        }application:{indentExpr rhsAp}"
    if mustBeStr then
      throwError "Invalid `simps` attribute. The body is not a constructor application:{indentExpr rhsAp}"
    if !todoNext.isEmpty then
      throwError "Invalid simp lemma {nm.appendAfter todoNext.head!}.\n{""
        }The given definition is not a constructor application:{indentExpr rhsAp}"
    if cfg.fullyApplied then
      simpsAddProjection ref nm tgt lhsAp rhsAp newArgs univs cfg else
      simpsAddProjection ref nm type lhs rhs args univs cfg
    pure #[nm] else
  -- if the value is a constructor application
  trace[simps.debug] "Generating raw projection information..."
  let projInfo ← simpsGetProjectionExprs tgt rhsAp cfg
  trace[simps.debug] "Raw projection information:\n  {projInfo}"
  -- If we are in the middle of a composite projection.
  if !toApply.isEmpty then do
    let ⟨newRhs, _⟩ ←
      match projInfo[toApply.head!]? with
      | none => throwError "unreachable: index of composite projection is out of bounds."
      | some x => pure x
    let newType ← inferType newRhs
    trace[simps.debug] "Applying a custom composite projection. Current {""
      }lhs:\n        >   {lhsAp}"
    simpsAddProjections env ref nm newType lhsAp newRhs newArgs univs false cfg todo toApply else
  -- check whether `rhsAp` is an eta-expansion
  let eta : Option Expr := none -- todo: support eta-reduction of structures (still useful, because we care about syntactic equality!?)
  -- let eta ← rhsAp.isEtaExpansion
  let rhsAp := eta.getD rhsAp -- eta-reduce `rhsAp`
  /- As a special case, we want to automatically generate the current projection if `rhsAp`
  was an eta-expansion. Also, when this was a desired projection, we need to generate the
  current projection if we haven't done it above. -/
  if todoNow || (todo.isEmpty && eta.isSome) then
    if cfg.fullyApplied then
      simpsAddProjection ref nm tgt lhsAp rhsAp newArgs univs cfg else
      simpsAddProjection ref nm type lhs rhs args univs cfg
  /- We stop if no further projection is specified or if we just reduced an eta-expansion and we
  automatically choose projections -/
  if !(todo == [""] || eta.isSome || todo.isEmpty) then pure #[] else
  let projs : Array Name := projInfo.map fun x => x.2.name
  let todo := if toApply.isEmpty then todoNext else todo
  -- check whether all elements in `todo` have a projection as prefix
  match todo.find? fun x => projs.all fun proj => !("_" ++ proj.getString).isPrefixOf x with
  | some x =>
    let simpLemma := nm.appendAfter x
    let neededProj := (x.splitOn "_").tail.head!
    throwError "Invalid simp lemma {simpLemma}. Structure {str} does not have projection {""
      }{neededProj}.\nThe known projections are:\n  {projs}\nYou can also see this information {""
      }by running\n  `initialize_simps_projections? {str}`.\nNote: these projection names might {""
      }be customly defined for `simps`, and differ from the projection names of the structure."
  | none =>
    let l ← projInfo.mapM fun ⟨newRhs, proj, projExpr, projNrs, isDefault, isPrefix⟩ => do
      let newType ← inferType newRhs
      let new_todo := todo.filterMap fun x => x.isPrefixOf? ("_" ++ proj.getString)
      -- we only continue with this field if it is default or mentioned in todo
      if !(isDefault && todo.isEmpty) && new_todo.isEmpty then pure #[] else
      let newLhs := projExpr.instantiateLambdasOrApps #[lhsAp]
      let newName := updateName nm proj.getString isPrefix
      let new_cfg :=
        { cfg with addAdditive := cfg.addAdditive.map fun nm =>
          updateName nm (ToAdditive.guessName proj.getString) isPrefix }
      trace[simps.debug] "Recursively add projections for:\n        >  {newLhs}"
      simpsAddProjections env ref newName newType newLhs newRhs newArgs univs false new_cfg new_todo
        projNrs
    pure l.flatten

/-- `simpsTac` derives `simp` lemmas for all (nested) non-Prop projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  If `shortNm` is true, the generated names will only use the last projection name.
  If `trc` is true, trace as if `trace.simps.verbose` is true. -/
def simpsTac (ref : Syntax) (nm : Name) (cfg : Simps.Config := {}) (todo : List String := [])
  (trc := false) : AttrM (Array Name) := do
  let env ← getEnv
  let some d ← pure <| env.find? nm | throwError "Declaration {nm} doesn't exist."
  let lhs : Expr := mkConst d.name <| d.levelParams.map Level.param
  let todo := todo.eraseDup.map fun proj => "_" ++ proj
  let cfg :=
    { cfg with trace := cfg.trace || (← getOptions).getBool `trace.simps.verbose || trc }
  let cfg ← match ToAdditive.findTranslation? env nm with
  | none => pure cfg
  | some additiveName =>
    if cfg.trace then
      logInfo m!"[simps] > @[toAdditive] will be added to all generated lemmas."
    pure { cfg with addAdditive := additiveName }
  MetaM.run' <| simpsAddProjections env ref nm d.type lhs (d.value?.getD default) #[] d.levelParams
      (mustBeStr := true) cfg todo []

initialize simpsAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `simps
    descr := "Automatically derive lemmas specifying the projections of this declaration.",
    getParam := fun
    | nm, stx@`(attr|simps $[?%$trc]? $[(config := $c)]? $[$ids]*) => do
      let ids := ids.map (·.getId.eraseMacroScopes.getString)
      let cfg ← match c with
        | none => pure {}
        | some c => MetaM.run' <| TermElabM.run' <| elabSimpsConfig c
      simpsTac stx nm cfg ids.toList trc.isSome
    | _, stx => throwError "unexpected simps syntax {stx}"
  }
