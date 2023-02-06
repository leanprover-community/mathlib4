/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import Mathlib.Init.Data.Nat.Notation
import Mathlib.Lean.Message
import Mathlib.Lean.Expr.Basic
import Mathlib.Data.String.Defs
import Mathlib.Data.KVMap
import Mathlib.Tactic.Simps.NotationClass
import Std.Classes.Dvd
import Std.Util.LibraryNote

/-!
# Simps attribute

This file defines the `@[simps]` attribute, to automatically generate `simp` lemmas
reducing a definition when projections are applied to it.

## Implementation Notes

There are three attributes being defined here
* `@[simps]` is the attribute for objects of a structure or instances of a class. It will
  automatically generate simplification lemmas for each projection of the object/instance that
  contains data. See the doc strings for `Lean.Parser.Attr.simps` and `Simps.Config`
  for more details and configuration options.
* `simpsStructure` (just an environment extension, not actually an attribute)
  is automatically added to structures that have been used in `@[simps]`
  at least once. This attribute contains the data of the projections used for this structure
  by all following invocations of `@[simps]`.
* `@[notation_class]` should be added to all classes that define notation, like `Mul` and
  `Zero`. This specifies that the projections that `@[simps]` used are the projections from
  these notation classes instead of the projections of the superclasses.
  Example: if `Mul` is tagged with `@[notation_class]` then the projection used for `Semigroup`
  will be `fun α hα ↦ @Mul.mul α (@Semigroup.toMul α hα)` instead of `@Semigroup.mul`.

## Unimplemented Features

* Correct interaction with heterogenous operations like `HAdd` and `HMul`
* structure-Eta-reducing subexpressions
  * still useful, since we don't want to recurse into something like `{fst := x.fst, snd := x.snd}`
    obtained by `{ x with ... }`
* Adding custom simp-attributes / other attributes

### Improvements
* If multiple declarations are generated from a `simps` without explicit projection names, then
  only the first one is shown when mousing over `simps`.
* Double check output of simps (especially in combination with to_additive).

## Changes w.r.t. Lean 3

There are some small changes in the attribute. None of them should have great effects
* The attribute will now raise an error if it tries to generate a lemma when there already exists
  a lemma with that name (in Lean 3 it would generate a different unique name)
* `transparency.none` has been replaced by `TransparencyMode.reducible`
* The `attr` configuration option has been split into `isSimp` and `attrs` (for extra attributes)
  (todo)
* Because Lean 4 uses bundled structures, this means that `simps` applied to anything that
  implements a notation class will almost certainly require a user-provided custom simps projection.

## Tags

structures, projections, simp, simplifier, generates declarations
-/

open Lean Meta Parser Elab Term Command

/-- `updateName nm s is_prefix` adds `s` to the last component of `nm`,
  either as prefix or as suffix (specified by `isPrefix`), separated by `_`.
  Used by `simps_add_projections`. -/
def updateName (nm : Name) (s : String) (isPrefix : Bool) : Name :=
  nm.updateLast fun s' ↦ if isPrefix then s ++ "_" ++ s' else s' ++ "_" ++ s

-- move
namespace Lean.Meta
open Tactic Simp
/-- Make `MkSimpContextResult` giving data instead of Syntax. Doesn't support arguments.
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
  let ctx : Simp.Context := {
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

/-- Make `Simp.Context` giving data instead of Syntax. Doesn't support arguments.
Intended to be very similar to `Lean.Elab.Tactic.mkSimpContext`
Todo: support arguments. -/
def mkSimpContext (cfg : Meta.Simp.Config := {}) (simpOnly := false) (kind := SimpKind.simp)
    (dischargeWrapper := DischargeWrapper.default) (hasStar := false) :
    MetaM Simp.Context := do
  let data ← mkSimpContextResult cfg simpOnly kind dischargeWrapper hasStar
  return data.ctx

end Lean.Meta

/-- Tests whether `declName` has the `@[simp]` attribute in `env`. -/
def hasSimpAttribute (env : Environment) (declName : Name) : Bool :=
  simpExtension.getState env |>.lemmaNames.contains <| .decl declName

namespace Lean.Parser
namespace Attr


/-! Declare notation classes. -/
attribute [notation_class]
  Add Mul Neg Sub Div Dvd Mod LE LT Append Pow HasEquiv

-- attribute [notation_class]
--   Zero One Inv HasAndthen HasUnion HasInter HasSdiff
--   HasEquiv HasSubset HasSsubset HasEmptyc HasInsert HasSingleton HasSep HasMem

/-- arguments to `@[simps]` attribute. -/
syntax simpsArgsRest := (Tactic.config)? (ppSpace ident)*

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
* If the structure is a class that has an instance to a notation class, like `Neg`, then this
  notation is used instead of the corresponding projection.
  [TODO: not yet implemented for heterogenous operations like `HMul` and `HAdd`]
* You can specify custom projections, by giving a declaration with name
  `{StructureName}.Simps.{projectionName}`. See Note [custom simps projection].

  Example:
  ```lean
  def Equiv.Simps.invFun (e : α ≃ β) : β → α := e.symm
  @[simps] def Equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩
  ```
  generates
  ```
  @[simp] lemma Equiv.trans_toFun : ∀ {α β γ} (e₁ e₂) (a : α), ⇑(e₁.trans e₂) a = (⇑e₂ ∘ ⇑e₁) a
  @[simp] lemma Equiv.trans_invFun : ∀ {α β γ} (e₁ e₂) (a : γ),
    ⇑((e₁.trans e₂).symm) a = (⇑(e₁.symm) ∘ ⇑(e₂.symm)) a
  ```

* You can specify custom projection names, by specifying the new projection names using
  `initialize_simps_projections`.
  Example: `initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)`.
  See `initialize_simps_projections` for more information.

* If one of the fields itself is a structure, this command will recursively create
  `simp` lemmas for all fields in that structure.
  * Exception: by default it will not recursively create `simp` lemmas for fields in the structures
    `Prod` and `PProd`. You can give explicit projection names or change the value of
    `Simps.Config.notRecursive` to override this behavior.

  Example:
  ```lean
  structure MyProd (α β : Type _) := (fst : α) (snd : β)
  @[simps] def foo : Prod ℕ ℕ × MyProd ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
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
  structure MyProd (α β : Type _) := (fst : α) (snd : β)
  @[simps fst fst_fst snd] def foo : Prod ℕ ℕ × MyProd ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_fst_fst : foo.fst.fst = 1
  @[simp] lemma foo_snd : foo.snd = {fst := 3, snd := 4}
  ```
* [TODO] If one of the values is an eta-expanded structure, we will eta-reduce this structure.

  Example:
  ```lean
  structure EquivPlusData (α β) extends α ≃ β where
    data : Bool
  @[simps] def EquivPlusData.rfl {α} : EquivPlusData α α := { Equiv.refl α with data := true }
  ```
  generates the following:
  ```lean
  @[simp] lemma bar_toEquiv : ∀ {α : Sort*}, bar.toEquiv = Equiv.refl α
  @[simp] lemma bar_data : ∀ {α : Sort*}, bar.data = tt
  ```
  This is true, even though Lean inserts an eta-expanded version of `Equiv.refl α` in the
  definition of `bar`.
* For configuration options, see the doc string of `Simps.Config`.
* The precise syntax is `simps (config := e)? ident*`, where `e : Expr` is an expression of type
  `Simps.Config` and `ident*` is a list of desired projection names.
* `@[simps]` reduces let-expressions where necessary.
* When option `trace.simps.verbose` is true, `simps` will print the projections it finds and the
  lemmas it generates. The same can be achieved by using `@[simps?]`.
* Use `@[to_additive (attr := simps)]` to apply both `to_additive` and `simps` to a definition
  This will also generate the additive versions of all `simp` lemmas.
-/
/- If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens, so is not included in the official doc). -/
syntax (name := simps) "simps" "?"? simpsArgsRest : attr

@[inherit_doc simps]
macro "simps?" rest:simpsArgsRest : attr => `(attr| simps ? $rest)

end Attr

namespace Command

/-- Syntax for renaming a projection in `initialize_simps_projections`. -/
syntax simpsRule.rename := ident " → " ident
/-- Syntax for making a  projection non-default in `initialize_simps_projections`. -/
syntax simpsRule.erase := "-" ident
/-- Syntax for a single rule in `initialize_simps_projections`. -/
syntax simpsRule := (simpsRule.rename <|> simpsRule.erase) &" as_prefix"?
/-- Syntax for `initialize_simps_projections`. -/
syntax simpsProj := (ppSpace ident (" (" simpsRule,+ ")")?)

/--
This command specifies custom names and custom projections for the simp attribute `simpsAttr`.
* You can specify custom names by writing e.g.
  `initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)`.
* See Note [custom simps projection] and the examples below for information how to declare custom
  projections.
* For algebraic structures, we will automatically use the notation (like `Mul`) for the projections
  if such an instance is available. [TODO: support heterogenous operations]
* You can disable a projection by default by running
  `initialize_simps_projections Equiv (-invFun)`
  This will ensure that no simp lemmas are generated for this projection,
  unless this projection is explicitly specified by the user.
* If you want the projection name added as a prefix in the generated lemma name, you can add the
  `as_prefix` modifier:
  `initialize_simps_projections Equiv (toFun → coe as_prefix)`
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
  projections. In this case, notation classes are not automatically recognized, and should be
  manually given by giving a custom projection.
  This is especially useful when extending a structure
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
    initialize_simps_projections MulHom (toFun → apply, toFun → coe as_prefix, -coe)
    initialize_simps_projections MulHom (toFun → apply, toFun → coe as_prefix, -apply)
  ```
  In the first case, you can get both lemmas using `@[simps, simps coe asFn]` and in the second
  case you can get both lemmas using `@[simps asFn, simps apply]`.
* If your new homomorphism-like structure extends another structure (like `RelEmbedding`),
  then you have to specify explicitly that you want to use a coercion
  as a custom projection. For example
  ```
    def relEmbedding.Simps.apply (h : r ↪r s) : α → β := h
    initialize_simps_projections relEmbedding (to_embedding_toFun → apply, -to_embedding)
  ```
* If you have an isomorphism-like structure (like `Equiv`) you often want to define a custom
  projection for the inverse:
  ```
    def Equiv.Simps.symm_apply (e : α ≃ β) : β → α := e.symm
    initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)
  ```
-/
syntax (name := initialize_simps_projections)
  "initialize_simps_projections" "?"? simpsProj : command

@[inherit_doc «initialize_simps_projections»]
macro "initialize_simps_projections?" rest:simpsProj : command =>
  `(initialize_simps_projections ? $rest)

end Command
end Lean.Parser

initialize registerTraceClass `simps.verbose
initialize registerTraceClass `simps.debug

/-- Projection data for a single projection of a structure -/
structure ProjectionData where
  /-- The name used in the generated `simp` lemmas -/
  name : Name
  /-- An Expression used by simps for the projection. It must be definitionally equal to an original
  projection (or a composition of multiple projections).
  These Expressions can contain the universe parameters specified in the first argument of
  `simpsStructure`. -/
  expr : Expr
  /-- A list of natural numbers, which is the projection number(s) that have to be applied to the
  Expression. For example the list `[0, 1]` corresponds to applying the first projection of the
  structure, and then the second projection of the resulting structure (this assumes that the
  target of the first projection is a structure with at least two projections).
  The composition of these projections is required to be definitionally equal to the provided
  Expression. -/
  projNrs : List ℕ
  /-- A boolean specifying whether `simp` lemmas are generated for this projection by default. -/
  isDefault : Bool
  /-- A boolean specifying whether this projection is written as prefix. -/
  isPrefix : Bool
  deriving Inhabited

instance : ToMessageData ProjectionData where toMessageData
  | ⟨a, b, c, d, e⟩ => .group <| .nest 1 <|
    "⟨" ++ .joinSep [toMessageData a, toMessageData b, toMessageData c, toMessageData d,
      toMessageData e] ("," ++ Format.line) ++ "⟩"

/--
The `simpsStructure` environment extension specifies the preferred projections of the given
structure, used by the `@[simps]` attribute.
- You can generate this with the command `initialize_simps_projections`.
- If not generated, the `@[simps]` attribute will generate this automatically.
- To change the default value, see Note [custom simps projection].
- The first argument is the list of names of the universe variables used in the structure
- The second argument is an array that consists of the projection data for each projection.
-/
initialize simpsStructure : NameMapExtension (List Name × Array ProjectionData) ←
  registerNameMapExtension (List Name × Array ProjectionData)

/-- Temporary projection data parsed from `initialize_simps_projections` before the Expression
  matching this projection has been found. Only used internally in `simpsGetRawProjections`. -/
structure ParsedProjectionData where
  /-- name and syntax for this projection used in the structure definition -/
  origName : Name × Syntax
  /-- name and syntax for this projection used in the generated `simp` lemmas -/
  newName : Name × Syntax
  /-- will simp lemmas be generated for with (without specifically naming this?) -/
  isDefault : Bool
  /-- is the projection name a prefix? -/
  isPrefix : Bool
  /-- projection expression -/
  expr? : Option Expr := none
  /-- the list of projection numbers this expression corresponds to -/
  projNrs : Array Nat := #[]
  /-- is this a projection that is changed by the user? -/
  isChanged : Bool := false

/-- Turn `ParsedProjectionData` into `ProjectionData`. -/
def ParsedProjectionData.toProjectionData (p : ParsedProjectionData) : ProjectionData :=
  { p with name := p.newName.1, expr := p.expr?.getD default, projNrs := p.projNrs.toList }

instance : ToMessageData ParsedProjectionData where toMessageData
  | ⟨x₁, x₂, x₃, x₄, x₅, x₆, x₇⟩ => .group <| .nest 1 <|
    "⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂, toMessageData x₃, toMessageData x₄,
      toMessageData x₅, toMessageData x₆, toMessageData x₇]
    ("," ++ Format.line) ++ "⟩"

/-- The type of rules that specify how metadata for projections in changes.
  See `initialize_simps_projections`. -/
structure ProjectionRule where
  /-- A projection rule is either a renaming rule `before→after` or a hiding rule `-hideMe`.
    Each name comes with the syntax used to write the rule,
    which is used to declare hover information. -/
  rule : (Name × Syntax) × (Name × Syntax) ⊕ (Name × Syntax)
  /-- Either rule can optionally be followed by `as_prefix` to write the projection as prefix.
  This is uncommon for hiding rules, but not completely useless, since if a user manually wants
  to generate such a projection, it will be written using a prefix. -/
  asPrefix : Bool

instance : ToMessageData ProjectionRule where toMessageData
  | ⟨x₁, x₂⟩ => .group <| .nest 1 <|
    "⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂] ("," ++ Format.line) ++ "⟩"

/-- Returns the projection information of a structure. -/
def projectionsInfo (l : List ProjectionData) (pref : String) (str : Name) : MessageData :=
  let ⟨defaults, nondefaults⟩ := l.partition (·.isDefault)
  let toPrint : List MessageData :=
    defaults.map fun s ↦
      let prefixStr := if s.isPrefix then "(prefix) " else ""
      m!"Projection {prefixStr}{s.name}: {s.expr}"
  let print2 : MessageData :=
    String.join <| (nondefaults.map fun nm : ProjectionData ↦ toString nm.1).intersperse ", "
  let toPrint :=
    toPrint ++
      if nondefaults.isEmpty then [] else
      [("No lemmas are generated for the projections: " : MessageData) ++ print2 ++ "."]
  let toPrint := MessageData.joinSep toPrint ("\n" : MessageData)
  m! "{pref} {str}:\n{toPrint}"

/-- Auxiliary function of `getCompositeOfProjections`. -/
partial def getCompositeOfProjectionsAux (stx : Syntax) (str : Name) (proj : String) (x : Expr)
    (pos : Array ℕ) (args : Array Expr) : MetaM (Expr × Array ℕ) := do
  let env ← getEnv
  let projs := (getStructureInfo? env str).get!
  let projInfo := projs.fieldNames.toList.mapIdx fun n p ↦
    return (← ("_" ++ p.getString!).isPrefixOf? proj, n, p)
  let some (projRest, index, projName) := (projInfo.filterMap id).getLast?
    | throwError "Failed to find constructor {proj.drop 1} in structure {str}."
  let strDecl := (env.find? str).get!
  let projExpr := Expr.const (str ++ projName) <| strDecl.levelParams.map mkLevelParam
  let projDecl := (env.find? (str ++ projName)).get!
  let type ← inferType x
  let params := type.getAppArgs
  let newX := mkAppN (projExpr.instantiateLevelParams
    projDecl.levelParams type.getAppFn.constLevels!) <| params ++ [x]
  let newPos := pos.push index
  if projRest.isEmpty then
    let newE ← mkLambdaFVars args newX
    if !stx.isMissing then
      discard <| TermElabM.run' <| addTermInfo stx newE
    return (newE, newPos)
  let type ← inferType newX
  forallTelescopeReducing type fun typeArgs tgt ↦
    getCompositeOfProjectionsAux stx tgt.getAppFn.constName! projRest (mkAppN newX typeArgs)
      newPos (args ++ typeArgs)


/-- Given a structure `str` and a projection `proj`, that could be multiple nested projections
  (separated by `_`), returns an Expression that is the composition of these projections and a
  list of natural numbers, that are the projection numbers of the applied projections. -/
def getCompositeOfProjections (str : Name) (proj : String) (stx : Syntax) :
  MetaM (Expr × Array ℕ) := do
  let env ← getEnv
  let strDecl := (env.find? str).get!
  let strExpr : Expr := mkConst str <| strDecl.levelParams.map mkLevelParam
  let type ← inferType strExpr
  forallTelescopeReducing type fun typeArgs _ ↦
  withLocalDeclD `x (mkAppN strExpr typeArgs) fun ex ↦
  getCompositeOfProjectionsAux stx str ("_" ++ proj) ex #[] <| typeArgs.push ex

/-- Auxilliary function for `simpsGetRawProjections` that executes the projection renaming.

Figure out projections, including renamings. The information for a projection is (before we
figure out the `expr` of the projection):
`(original name, given name, is default, is prefix)`.
The first projections are always the actual projections of the structure, but `rules` could
specify custom projections that are compositions of multiple projections. -/
def simpsApplyProjectionRules (str : Name) (rules : Array ProjectionRule) :
  CoreM (Array ParsedProjectionData) := do
  let env ← getEnv
  let some projs := getStructureInfo? env str
    | throwError "Declaration {str} is not a structure."
  let projs : Array ParsedProjectionData := projs.fieldNames.map
    fun nm ↦ ⟨(nm, .missing), (nm, .missing), true, false, none, #[], false⟩
  let projs : Array ParsedProjectionData := rules.foldl (init := projs) fun projs rule ↦
    match rule with
    | ⟨.inl (oldName, newName), isPrefix⟩ =>
      if (projs.map (·.newName.1)).contains oldName.1 then
        projs.map fun proj ↦ if proj.newName.1 == oldName.1 then
          { proj with
            newName := newName, isPrefix := isPrefix,
            origName.2 := if proj.origName.2.isMissing then oldName.2 else proj.origName.2 } else
          proj else
        projs.push ⟨oldName, newName, true, isPrefix, none, #[], false⟩
    | ⟨.inr nm, isPrefix⟩ =>
      if (projs.map (·.newName.1)).contains nm.1 then
        projs.map fun proj ↦ if proj.newName.1 = nm.1 then
          { proj with
            isDefault := false, isPrefix := isPrefix,
            origName.2 := if proj.origName.2.isMissing then nm.2 else proj.origName.2 } else
          proj else
        projs.push ⟨nm, nm, false, isPrefix, none, #[], false⟩
  trace[simps.debug] "Projection info after applying the rules: {projs}."
  unless (projs.map (·.newName.1)).toList.Nodup do throwError
    "Invalid projection names. Two projections have the same name.\n{""
    }This is likely because a custom composition of projections was given the same name as an {""
    }existing projection. Solution: rename the existing projection (before naming the {""
    }custom projection)."
  pure projs

/-- Auxilliary function for `simpsGetRawProjections`.
TODO: we can use something similar to `getStructureFieldsFlattened` to simplify the notation for
this
Find custom projections declared by the user. -/
def simpsFindCustomProjection (str : Name) (proj : ParsedProjectionData)
  (rawUnivs : List Level) : CoreM ParsedProjectionData := do
  let env ← getEnv
  let (rawExpr, nrs) ← MetaM.run' <|
    getCompositeOfProjections str proj.origName.1.getString! proj.origName.2
  let customName := str ++ `Simps ++ proj.newName.1
  match env.find? customName with
  | some d@(.defnInfo _) =>
    let customProj := d.instantiateValueLevelParams! rawUnivs
    trace[simps.verbose] "found custom projection for {proj.newName.1}:{indentExpr customProj}"
    match (← MetaM.run' $ isDefEq customProj rawExpr) with
    | true =>
      discard <| MetaM.run' <| TermElabM.run' <| addTermInfo proj.newName.2 <|
        ← mkConstWithLevelParams customName
      pure { proj with expr? := some customProj, projNrs := nrs, isChanged := true }
    | false =>
      -- if the type of the Expression is different, we show a different error message, because
      -- (in Lean 3) just stating that the expressions are different is quite unhelpful
      let customProjType ← MetaM.run' (inferType customProj)
      let rawExprType ← MetaM.run' (inferType rawExpr)
      if (← MetaM.run' (isDefEq customProjType rawExprType)) then
        throwError "Invalid custom projection:{indentExpr customProj}\n{""
          }Expression is not definitionally equal to {indentExpr rawExpr}" else
        throwError "Invalid custom projection:\n  {customProj}\n{""
          }Expression has different type than {str ++ proj.origName.1}. Given type:{
          indentExpr customProjType}\nExpected type:{indentExpr rawExprType
          }\nNote: make sure order of implicit arguments is exactly the same."
  | _ =>
    discard <| MetaM.run' <| TermElabM.run' <| addTermInfo proj.newName.2 rawExpr
    pure {proj with expr? := some rawExpr, projNrs := nrs}

/-- Auxilliary function for `simpsGetRawProjections`.
Resolve a single notation class in `simpsFindAutomaticProjections`. -/
-- currently unused
def simpsResolveNotationClass (projs : Array ParsedProjectionData)
    (className : Name) (args : Array Expr) (eStr : Expr) (rawUnivs : List Level) :
    MetaM (Array ParsedProjectionData) := do
  let env ← getEnv
  let classInfo := (getStructureInfo? env className).get!
  let projName := classInfo.fieldNames[0]!
  /- For this class, find the projection. `rawExpr` is the projection found applied to `args`,
      and `rawExprLambda` has the arguments `args` abstracted. -/
  let (relevantProj, rawExprLambda) ← do
    let eInstType := mkAppN (.const className rawUnivs) args
    withLocalDeclD `x eStr fun hyp ↦ do
      -- todo: instead of instance search, traverse through parent structures for a notation class
      -- (that way we also deal with composite projections)
      let eInst ← synthInstance eInstType (some 10)
      let rawExpr ← mkAppM projName (args.push eInst)
      let rawExprLambda ← mkLambdaFVars (args.push hyp) rawExpr
      let rawExprWhnf ← whnf rawExpr
      let relevantProj ← lambdaTelescope rawExprWhnf fun _ body ↦
        pure <| body.getAppFn.constName?
      trace[simps.debug] "info: ({relevantProj}, {rawExprLambda})"
      pure (relevantProj, rawExprLambda)
  let some pos := projs.findIdx? fun x ↦ some x.origName.1 == relevantProj | do
    trace[simps.verbose] "Warning: The structure has an instance for {className}, {""
        }but it is not definitionally equal to any projection."
    failure -- will be caught by `simpsFindAutomaticProjections`
  trace[simps.debug] "The raw projection is:{indentExpr rawExprLambda}"
  projs.mapIdxM fun nr x ↦ do
    unless nr.1 = pos do return x
    if x.isChanged then
      trace[simps.verbose] "Warning: Projection {relevantProj} is definitionally equal to{
          indentExpr rawExprLambda}\nHowever, this is not used since a custom simps projection is {
            ""}specified by the user."
      return x
    trace[simps.verbose] "Using notation from {className} for projection {relevantProj}."
    return { x with expr? := some rawExprLambda }

/-- Auxilliary function for `simpsGetRawProjections`.
Find custom projections, automatically found by simps.
These come from algebraic notation classes, like `+`. -/
-- todo: just navigate all projections and check if there is one called "add"/"mul" etc.
-- currently unused
def simpsFindAutomaticProjections (str : Name) (projs : Array ParsedProjectionData)
  (strType : Expr) (rawUnivs : List Level) : CoreM (Array ParsedProjectionData) := do
  let env ← getEnv
  MetaM.run' <| forallTelescope strType fun args _ ↦ do
    let eStr := mkAppN (.const str rawUnivs) args
    let automaticProjs := notationClassAttr.getState env
    let mut projs := projs
    if args.size == 1 then -- can be wrong if additional type-class arguments??
      for (className, _) in automaticProjs do
        try projs ← simpsResolveNotationClass projs className args eStr rawUnivs
        catch _ => pure ()
    return projs


/--
Get the projections used by `simps` associated to a given structure `str`.

The returned information is also stored in a parameter of the attribute `@[simpsStructure]`, which
is given to `str`. If `str` already has this attribute, the information is read from this
attribute instead. See the documentation for this attribute for the data this tactic returns.

The returned universe levels are the universe levels of the structure. For the projections there
are three cases
* If the declaration `{StructureName}.Simps.{projectionName}` has been declared, then the value
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
  For example: ``simpsGetRawProjections env `Prod`` gives the default projections.
```
  ([u, v], [(`fst, `(Prod.fst.{u v}), [0], true, false),
     (`snd, `(@Prod.snd.{u v}), [1], true, false)])
```

Optionally, this command accepts three optional arguments:
* If `traceIfExists` the command will always generate a trace message when the structure already
  has the attribute `@[simpsStructure]`.
* The `rules` argument specifies whether projections should be added, renamed, used as prefix, and
  not used by default.
* if `trc` is true, this tactic will trace information just as if
  `set_option trace.simps.verbose true` was set.
-/
def simpsGetRawProjections (str : Name) (traceIfExists : Bool := false)
  (rules : Array ProjectionRule := #[]) (trc := false) :
  CoreM (List Name × Array ProjectionData) := do
  withOptions (· |>.updateBool `trace.simps.verbose (trc || ·)) <| do
  let env ← getEnv
  if let some data := (simpsStructure.getState env).find? str then
    -- We always print the projections when they already exists and are called by
    -- `initialize_simps_projections`.
    withOptions (· |>.updateBool `trace.simps.verbose (traceIfExists || ·)) <| do
      trace[simps.verbose]
        projectionsInfo data.2.toList "Already found projection information for structure" str
    return data
  trace[simps.verbose] "generating projection information for structure {str}."
  trace[simps.debug] "Applying the rules {rules}."
  let some strDecl := env.find? str
    | throwError "No such declaration {str}." -- maybe unreachable
  let rawLevels := strDecl.levelParams
  let rawUnivs := rawLevels.map Level.param
  let projs ← simpsApplyProjectionRules str rules
  let projs ← projs.mapM fun proj ↦ simpsFindCustomProjection str proj rawUnivs
  -- todo: find and use coercions to functions here
  -- let projs ← simpsFindAutomaticProjections str projs strDecl.type rawUnivs
  let projs := projs.map (·.toProjectionData)
  -- make all proofs non-default.
  let projs ← projs.mapM fun proj ↦ do
    match (← MetaM.run' <| isProof proj.expr) with
    | true => pure { proj with isDefault := false }
    | false => pure proj
  trace[simps.verbose] projectionsInfo projs.toList "generated projections for" str
  simpsStructure.add str (rawLevels, projs)
  trace[simps.debug] "Generated raw projection data:{indentD m!"(rawLevels, projs)"}}"
  pure (rawLevels, projs)

library_note "custom simps projection"/--
You can specify custom projections for the `@[simps]` attribute.
To do this for the projection `MyStructure.originalProjection` by adding a declaration
`MyStructure.Simps.myProjection` that is definitionally equal to
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
| `(simpsRule| $id1 → $id2 $[as_prefix%$tk]?) =>
  pure ⟨.inl ((id1.getId, id1.raw), (id2.getId, id2.raw)), tk.isSome⟩
| `(simpsRule| - $id $[as_prefix%$tk]?) =>
  pure ⟨.inr (id.getId, id.raw), tk.isSome⟩
| _                    => Elab.throwUnsupportedSyntax

/-- Function elaborating `initialize_simps_projections`. -/
@[command_elab «initialize_simps_projections»] def elabInitializeSimpsProjections : CommandElab
| `(initialize_simps_projections $[?%$trc]? $id $[($stxs,*)]?) => do
  let stxs := stxs.getD <| .mk #[]
  let rules ← stxs.getElems.raw.mapM elabSimpsRule
  let nm ← resolveGlobalConstNoOverload id
  discard <| liftTermElabM <| addTermInfo id.raw <| ← mkConstWithLevelParams nm
  _ ← liftCoreM <| simpsGetRawProjections nm true rules trc.isSome
| _ => throwUnsupportedSyntax

/-- Configuration options for `@[simps]` -/
structure Simps.Config where
  /-- Make generated lemmas simp lemmas -/
  isSimp := true
  /-- [TODO] Other attributes to apply to generated lemmas -/
  attrs : List Name := []
  /-- simplify the right-hand side of generated simp-lemmas using `dsimp, simp`. -/
  simpRhs := false
  /-- TransparencyMode used to reduce the type in order to detect whether it is a structure. -/
  typeMd := TransparencyMode.instances
  /-- TransparencyMode used to reduce the right-hand side in order to detect whether it is a
  constructor. Note: was `none` in Lean 3 -/
  rhsMd := TransparencyMode.reducible
  /-- Generated lemmas that are fully applied, i.e. generates equalities between applied functions.
  Set this to `false` to generate equalities between functions. -/
  fullyApplied := true
  /-- List of types in which we are not recursing to generate simplification lemmas.
  E.g. if we write `@[simps] def e : α × β ≃ β × α := ...` we will generate `e_apply` and not
  `e_apply_fst`. -/
  notRecursive := [`Prod, `PProd]
  /-- Output debug messages. Not used much, use `set_option simps.debug true` instead. -/
  debug := false
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
  (corresponding right-hand-side, given projection name, projection Expression,
    future projection numbers, used by default, is prefix)
  ```
  (where all fields except the first are packed in a `ProjectionData` structure)
  one for each projection. The given projection name is the name for the projection used by the user
  used to generate (and parse) projection names. For example, in the structure

  Example 1: ``simpsGetProjectionExprs env `(α × β) `(⟨x, y⟩)`` will give the output
  ```
    [(`(x), `fst, `(@Prod.fst.{u v} α β), [], true, false),
     (`(y), `snd, `(@Prod.snd.{u v} α β), [], true, false)]
  ```

  Example 2: ``simpsGetProjectionExprs env `(α ≃ α) `(⟨id, id, fun _ ↦ rfl, fun _ ↦ rfl⟩)``
  will give the output
  ```
    [(`(id), `apply, (Equiv.toFun), [], true, false),
     (`(id), `symm_apply, (fun e ↦ e.symm.toFun), [], true, false),
     ...,
     ...]
  ```
-/
def simpsGetProjectionExprs (tgt : Expr) (rhs : Expr) (cfg : Simps.Config) :
    MetaM <| Array <| Expr × ProjectionData := do
  -- the parameters of the structure
  let params := tgt.getAppArgs
  if cfg.debug && !(← (params.zip rhs.getAppArgs).allM fun ⟨a, b⟩ ↦ isDefEq a b) then
    throwError "unreachable code: parameters are not definitionally equal"
  let str := tgt.getAppFn.constName?.getD default
  -- the fields of the object
  let rhsArgs := rhs.getAppArgs.toList.drop params.size
  let (rawUnivs, projDeclata) ← simpsGetRawProjections str
  return projDeclata.map fun proj ↦
    (rhsArgs.getD (a₀ := default) proj.projNrs.head!,
      { proj with
        expr := (proj.expr.instantiateLevelParams rawUnivs
          tgt.getAppFn.constLevels!).instantiateLambdasOrApps params
        projNrs := proj.projNrs.tail })

variable (ref : Syntax) (univs : List Name)

/-- Add a lemma with `nm` stating that `lhs = rhs`. `type` is the type of both `lhs` and `rhs`,
  `args` is the list of local constants occurring, and `univs` is the list of universe variables. -/
def simpsAddProjection (declName : Name) (type lhs rhs : Expr) (args : Array Expr)
    (cfg : Simps.Config) : MetaM Unit := do
  trace[simps.debug] "Planning to add the equality{indentD m!"{lhs} = ({rhs} : {type})"}"
  let env ← getEnv
  if (env.find? declName).isSome then -- diverging behavior from Lean 3
    throwError "simps tried to add lemma {declName} to the environment, but it already exists."
  -- simplify `rhs` if `cfg.simpRhs` is true
  let lvl ← getLevel type
  let mut (rhs, prf) := (rhs, mkAppN (mkConst `Eq.refl [lvl]) #[type, lhs])
  if cfg.simpRhs then
    let ctx ← mkSimpContext
    let (rhs2, _) ← dsimp rhs ctx
    if rhs != rhs2 then
      trace[simps.debug] "`dsimp` simplified rhs to{indentExpr rhs2}"
    else
      trace[simps.debug] "`dsimp` failed to simplify rhs"
    let (result, _) ← simp rhs2 ctx
    if rhs2 != result.expr then
      trace[simps.debug] "`simp` simplified rhs to{indentExpr result.expr}"
    else
      trace[simps.debug] "`simp` failed to simplify rhs"
    rhs := result.expr
    prf := result.proof?.getD prf
  let eqAp := mkApp3 (mkConst `Eq [lvl]) type lhs rhs
  let declType ← mkForallFVars args eqAp
  let declValue ← mkLambdaFVars args prf
  trace[simps.verbose] "adding projection {declName}:{indentExpr declType}"
  try
    addDecl <| .thmDecl {
      name := declName
      levelParams := univs
      type := declType
      value := declValue }
  catch ex =>
    throwError "Failed to add projection lemma {declName}. Nested error:\n{ex.toMessageData}"
  addDeclarationRanges declName {
    range := ← getDeclarationRange (← getRef)
    selectionRange := ← getDeclarationRange ref }
  discard <| MetaM.run' <| TermElabM.run' <| addTermInfo (isBinder := true) ref <|
    ← mkConstWithLevelParams declName
  if cfg.isSimp then
    addSimpTheorem simpExtension declName true false .global <| eval_prio default
  -- cfg.attrs.mapM fun nm ↦ setAttribute nm declName tt -- todo: deal with attributes

/--
Perform head-structure-eta-reduction on expression `e`. That is, if `e` is of the form
`⟨f.1, f.2, ..., f.n⟩` with `f` definitionally equal to `e`, then
`headStructureEtaReduce e = headStructureEtaReduce f` and `headStructureEtaReduce e = e` otherwise.
-/
partial def headStructureEtaReduce (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let (ctor, args) := e.getAppFnArgs
  let some (.ctorInfo { induct := struct, numParams, ..}) := env.find? ctor | pure e
  let some { fieldNames, .. } := getStructureInfo? env struct | pure e
  let (params, fields) := args.toList.splitAt numParams -- fix if `Array.take` / `Array.drop` exist
  trace[simps.debug]
    "rhs is constructor application with params{indentD params}\nand fields {indentD fields}"
  let field0 :: fieldsTail := fields | return e
  let fieldName0 :: fieldNamesTail := fieldNames.toList | return e
  let (fn0, fieldArgs0) := field0.getAppFnArgs
  unless fn0 == struct ++ fieldName0 do
    trace[simps.debug] "{fn0} ≠ {struct ++ fieldName0}"
    return e
  let (params', reduct :: _) := fieldArgs0.toList.splitAt numParams | unreachable!
  unless params' == params do
    trace[simps.debug] "{params'} ≠ {params}"
    return e
  trace[simps.debug] "Potential structure-eta-reduct:{indentExpr e}\nto{indentExpr reduct}"
  let allArgs := params.toArray.push reduct
  let isEta ← (fieldsTail.zip fieldNamesTail).allM fun (field, fieldName) ↦
    if field.getAppFnArgs == (struct ++ fieldName, allArgs) then pure true else isProof field
  unless isEta do return e
  trace[simps.debug] "Structure-eta-reduce:{indentExpr e}\nto{indentExpr reduct}"
  headStructureEtaReduce reduct

/-- Derive lemmas specifying the projections of the declaration.
  `nm`: name of the lemma
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  `toApply` is non-empty after a custom projection that is a composition of multiple projections
  was just used. In that case we need to apply these projections before we continue changing `lhs`.
  `simpLemmas`: names of the simp lemmas added so far.(simpLemmas : Array Name)
  -/
partial def simpsAddProjections (nm : Name) (type lhs rhs : Expr)
  (args : Array Expr) (mustBeStr : Bool) (cfg : Simps.Config)
  (todo : List (String × Syntax)) (toApply : List ℕ) : MetaM (Array Name) := do
  -- we don't want to unfold non-reducible definitions (like `set`) to apply more arguments
  trace[simps.debug] "Type of the Expression before normalizing: {type}"
  withTransparency cfg.typeMd <| forallTelescopeReducing type fun typeArgs tgt ↦ withDefault do
  trace[simps.debug] "Type after removing pi's: {tgt}"
  let tgt ← whnfD tgt
  trace[simps.debug] "Type after reduction: {tgt}"
  let newArgs := args ++ typeArgs
  let lhsAp := lhs.instantiateLambdasOrApps typeArgs
  let rhsAp := rhs.instantiateLambdasOrApps typeArgs
  let str := tgt.getAppFn.constName
  trace[simps.debug] "todo: {todo}"
  -- We want to generate the current projection if it is in `todo`
  let todoNext := todo.filter (·.1 ≠ "")
  let env ← getEnv
  let stx? := todo.find? (·.1 == "") |>.map (·.2)
  /- The syntax object associated to the projection we're making now (if any).
  Note that we use `ref[0]` so that with `simps (config := ...)` we associate it to the word `simps`
  instead of the application of the attribute to arguments. -/
  let stxProj := stx?.getD ref[0]
  let strInfo? := getStructureInfo? env str
  /- Don't recursively continue if `str` is not a structure or if the structure is in
  `notRecursive`. -/
  if strInfo?.isNone || (todo.isEmpty && str ∈ cfg.notRecursive && !mustBeStr) then
    if mustBeStr then
      throwError "Invalid `simps` attribute. Target {str} is not a structure"
    if !todoNext.isEmpty && str ∉ cfg.notRecursive then
      let firstTodo := todoNext.head!.1
      throwError "Invalid simp lemma {nm.appendAfter firstTodo}.\nProjection {
        (firstTodo.splitOn "_").tail.head!} doesn't exist, because target {str} is not a structure."
    if cfg.fullyApplied then
      simpsAddProjection stxProj univs nm tgt lhsAp rhsAp newArgs cfg
    else
      simpsAddProjection stxProj univs nm type lhs rhs args cfg
    return #[nm]
  -- if the type is a structure
  let some (.inductInfo { isRec := false, ctors := [ctor], .. }) := env.find? str | unreachable!
  trace[simps.debug] "{str} is a structure with constructor {ctor}."
  let rhsEta ← headStructureEtaReduce rhsAp
  -- did the user ask to add this projection?
  let addThisProjection := stx?.isSome && toApply.isEmpty
  if addThisProjection then
    -- we pass the precise argument of simps as syntax argument to `simpsAddProjection`
    if cfg.fullyApplied then
      simpsAddProjection stxProj univs nm tgt lhsAp rhsEta newArgs cfg
    else
      simpsAddProjection stxProj univs nm type lhs rhs args cfg
  let rhsWhnf ← withTransparency cfg.rhsMd <| whnf rhsEta
  trace[simps.debug] "The right-hand-side {indentExpr rhsAp}\n reduces to {indentExpr rhsWhnf}"
  if !rhsWhnf.getAppFn.isConstOf ctor then
    -- if I'm about to run into an error, try to set the transparency for `rhsMd` higher.
    if cfg.rhsMd == .reducible && (mustBeStr || !todoNext.isEmpty || !toApply.isEmpty) then
      trace[simps.verbose] "[simps] > The given definition is not a constructor {""
          }application:\n        >   {rhsWhnf}\n        > Retrying with the options {""
          }\{rhsMd := semireducible, simpRhs := tt}."
      let nms ← simpsAddProjections nm type lhs rhs args mustBeStr
        { cfg with rhsMd := .default, simpRhs := true } todo toApply
      return if addThisProjection then nms.push nm else nms
    if !toApply.isEmpty then
      throwError "Invalid simp lemma {nm}.\nThe given definition is not a constructor {""
        }application:{indentExpr rhsWhnf}"
    if mustBeStr then
      throwError "Invalid `simps` attribute. The body is not a constructor application:{
        indentExpr rhsWhnf}"
    if !todoNext.isEmpty then
      throwError "Invalid simp lemma {nm.appendAfter todoNext.head!.1}.\n{""
        }The given definition is not a constructor application:{indentExpr rhsWhnf}"
    if !addThisProjection then
      if cfg.fullyApplied then
        simpsAddProjection stxProj univs nm tgt lhsAp rhsEta newArgs cfg
      else
        simpsAddProjection stxProj univs nm type lhs rhs args cfg
    return #[nm]
  -- if the value is a constructor application
  trace[simps.debug] "Generating raw projection information..."
  let projInfo ← simpsGetProjectionExprs tgt rhsWhnf cfg
  trace[simps.debug] "Raw projection information:{indentD m!"{projInfo}"}"
  -- If we are in the middle of a composite projection.
  if let idx :: rest := toApply then
    let some ⟨newRhs, _⟩ := projInfo[idx]?
      | throwError "unreachable: index of composite projection is out of bounds."
    let newType ← inferType newRhs
    trace[simps.debug] "Applying a custom composite projection. Todo: {toApply}. Current lhs:{
      indentExpr lhsAp}"
    return ← simpsAddProjections nm newType lhsAp newRhs newArgs false cfg todo rest
  trace[simps.debug] "Not in the middle of applying a custom composite projection"
  /- We stop if no further projection is specified or if we just reduced an eta-expansion and we
  automatically choose projections -/
  if todo.length == 1 && todo.head!.1 == "" then return #[nm]
  let projs : Array Name := projInfo.map fun x ↦ x.2.name
  let todo := todoNext
  trace[simps.debug] "Next todo: {todoNext}"
  -- check whether all elements in `todo` have a projection as prefix
  if let some (x, _) := todo.find? fun (x, _) ↦ projs.all
    fun proj ↦ !("_" ++ proj.getString).isPrefixOf x then
    let simpLemma := nm.appendAfter x
    let neededProj := (x.splitOn "_").tail.head!
    throwError "Invalid simp lemma {simpLemma}. Structure {str} does not have projection {""
      }{neededProj}.\nThe known projections are:\n  {projs}\nYou can also see this information {""
      }by running\n  `initialize_simps_projections? {str}`.\nNote: these projection names might {""
      }be customly defined for `simps`, and could differ from the projection names of the {""
      }structure."
  let nms ← projInfo.concatMapM fun ⟨newRhs, proj, projExpr, projNrs, isDefault, isPrefix⟩ ↦ do
    let newType ← inferType newRhs
    let newTodo := todo.filterMap
      fun (x, stx) ↦ (("_" ++ proj.getString).isPrefixOf? x).map (·, stx)
    -- we only continue with this field if it is default or mentioned in todo
    if !(isDefault && todo.isEmpty) && newTodo.isEmpty then return #[]
    let newLhs := projExpr.instantiateLambdasOrApps #[lhsAp]
    let newName := updateName nm proj.getString isPrefix
    trace[simps.debug] "Recursively add projections for:{indentExpr newLhs}"
    simpsAddProjections newName newType newLhs newRhs newArgs false cfg newTodo projNrs
  return if addThisProjection then nms.push nm else nms

/-- `simpsTac` derives `simp` lemmas for all (nested) non-Prop projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  If `shortNm` is true, the generated names will only use the last projection name.
  If `trc` is true, trace as if `trace.simps.verbose` is true. -/
def simpsTac (ref : Syntax) (nm : Name) (cfg : Simps.Config := {})
    (todo : List (String × Syntax) := []) (trc := false) : AttrM (Array Name) :=
  withOptions (· |>.updateBool `trace.simps.verbose (trc || ·)) <| do
  let env ← getEnv
  let some d := env.find? nm | throwError "Declaration {nm} doesn't exist."
  let lhs : Expr := mkConst d.name <| d.levelParams.map Level.param
  let todo := todo.pwFilter (·.1 ≠ ·.1) |>.map fun (proj, stx) ↦ ("_" ++ proj, stx)
  let mut cfg := cfg
  MetaM.run' <| simpsAddProjections ref d.levelParams
    nm d.type lhs (d.value?.getD default) #[] (mustBeStr := true) cfg todo []

/-- same as `simpsTac`, but taking syntax as an argument. -/
def simpsTacFromSyntax (nm : Name) (stx : Syntax) : AttrM (Array Name) :=
  match stx with
  | `(attr| simps $[?%$trc]? $[(config := $c)]? $[$ids]*) => do
    let cfg ← MetaM.run' <| TermElabM.run' <| withSaveInfoContext <| elabSimpsConfig stx[2][0]
    let ids := ids.map fun x => (x.getId.eraseMacroScopes.getString, x.raw)
    simpsTac stx nm cfg ids.toList trc.isSome
  | _ => throwUnsupportedSyntax

/-- `simps` attribute. -/
initialize simpsAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `simps
    descr := "Automatically derive lemmas specifying the projections of this declaration.",
    getParam := simpsTacFromSyntax }
