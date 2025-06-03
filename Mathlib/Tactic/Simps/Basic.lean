/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Lean.Elab.Tactic.Simp
import Lean.Elab.App
import Mathlib.Tactic.Simps.NotationClass
import Mathlib.Lean.Expr.Basic

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
* `structureExt` (just an environment extension, not actually an attribute)
  is automatically added to structures that have been used in `@[simps]`
  at least once. This attribute contains the data of the projections used for this structure
  by all following invocations of `@[simps]`.
* `@[notation_class]` should be added to all classes that define notation, like `Mul` and
  `Zero`. This specifies that the projections that `@[simps]` used are the projections from
  these notation classes instead of the projections of the superclasses.
  Example: if `Mul` is tagged with `@[notation_class]` then the projection used for `Semigroup`
  will be `fun α hα ↦ @Mul.mul α (@Semigroup.toMul α hα)` instead of `@Semigroup.mul`.
  [this is not correctly implemented in Lean 4 yet]

### Possible Future Improvements
* If multiple declarations are generated from a `simps` without explicit projection names, then
  only the first one is shown when mousing over `simps`.

## Changes w.r.t. Lean 3

There are some small changes in the attribute. None of them should have great effects
* The attribute will now raise an error if it tries to generate a lemma when there already exists
  a lemma with that name (in Lean 3 it would generate a different unique name)
* `transparency.none` has been replaced by `TransparencyMode.reducible`
* The `attr` configuration option has been split into `isSimp` and `attrs` (for extra attributes)
* Because Lean 4 uses bundled structures, this means that `simps` applied to anything that
  implements a notation class will almost certainly require a user-provided custom simps projection.

## Tags

structures, projections, simp, simplifier, generates declarations
-/
open Lean Elab Parser Command
open Meta hiding Config
open Elab.Term hiding mkConst

/-- An internal representation of a name to be used for a generated lemma. -/
private structure NameStruct where
  /-- The namespace that the final name will reside in. -/
  parent : Name
  /-- A list of pieces to be joined by `toName`. -/
  components : List String

/-- Join the components with `_`, or append `_def` if there is only one component. -/
private def NameStruct.toName (n : NameStruct) : Name :=
  Name.mkStr n.parent <|
    match n.components with
    | [] => ""
    | [x] => s!"{x}_def"
    | e => "_".intercalate e

instance : Coe NameStruct Name where coe := NameStruct.toName

/-- `update nm s isPrefix` adds `s` to the last component of `nm`,
either as prefix or as suffix (specified by `isPrefix`).
Used by `simps_add_projections`. -/
private def NameStruct.update (nm : NameStruct) (s : String) (isPrefix : Bool := false) :
    NameStruct :=
  { nm with components := if isPrefix then s :: nm.components else nm.components ++ [s] }

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
  let simprocs := #[← if simpOnly then pure {} else Simp.getSimprocs]
  let congrTheorems ← getSimpCongrTheorems
  let ctx : Simp.Context ← Simp.mkContext cfg
    (simpTheorems := #[simpTheorems])
    (congrTheorems := congrTheorems)
  if !hasStar then
    return { ctx, simprocs, dischargeWrapper }
  else
    let mut simpTheorems := ctx.simpTheorems
    let hs ← getPropHyps
    for h in hs do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    let ctx := ctx.setSimpTheorems simpTheorems
    return { ctx, simprocs, dischargeWrapper }

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
attribute [notation_class add] HAdd
attribute [notation_class mul] HMul
attribute [notation_class sub] HSub
attribute [notation_class div] HDiv
attribute [notation_class mod] HMod
attribute [notation_class append] HAppend
attribute [notation_class pow Simps.copyFirst] HPow
attribute [notation_class andThen] HAndThen
attribute [notation_class] Neg Dvd LE LT HasEquiv HasSubset HasSSubset Union Inter SDiff Insert
  Singleton Sep Membership
attribute [notation_class one Simps.findOneArgs] OfNat
attribute [notation_class zero Simps.findZeroArgs] OfNat

/-- arguments to `@[simps]` attribute. -/
syntax simpsArgsRest := Tactic.optConfig (ppSpace ident)*

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
* If the structure is a class that has an instance to a notation class, like `Neg` or `Mul`,
  then this notation is used instead of the corresponding projection.
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
    `Prod`, `PProd`, and `Opposite`. You can give explicit projection names or change the value of
    `Simps.Config.notRecursive` to override this behavior.

  Example:
  ```lean
  structure MyProd (α β : Type*) := (fst : α) (snd : β)
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
  structure MyProd (α β : Type*) := (fst : α) (snd : β)
  @[simps fst fst_fst snd] def foo : Prod ℕ ℕ × MyProd ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
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
  structure EquivPlusData (α β) extends α ≃ β where
    data : Bool
  @[simps] def EquivPlusData.rfl {α} : EquivPlusData α α := { Equiv.refl α with data := true }
  ```
  generates the following:
  ```lean
  @[simp] lemma bar_toEquiv : ∀ {α : Sort*}, bar.toEquiv = Equiv.refl α
  @[simp] lemma bar_data : ∀ {α : Sort*}, bar.data = true
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
syntax (name := simps) "simps" "!"? "?"? simpsArgsRest : attr

@[inherit_doc simps] macro "simps?"  rest:simpsArgsRest : attr => `(attr| simps   ? $rest)
@[inherit_doc simps] macro "simps!"  rest:simpsArgsRest : attr => `(attr| simps !   $rest)
@[inherit_doc simps] macro "simps!?" rest:simpsArgsRest : attr => `(attr| simps ! ? $rest)
@[inherit_doc simps] macro "simps?!" rest:simpsArgsRest : attr => `(attr| simps ! ? $rest)

end Attr

/-- Linter to check that `simps!` is used when needed -/
register_option linter.simpsNoConstructor : Bool := {
  defValue := true
  descr := "Linter to check that `simps!` is used" }

/-- Linter to check that no unused custom declarations are declared for simps. -/
register_option linter.simpsUnusedCustomDeclarations : Bool := {
  defValue := true
  descr := "Linter to check that no unused custom declarations are declared for simps" }

namespace Command

/-- Syntax for renaming a projection in `initialize_simps_projections`. -/
syntax simpsRule.rename := ident " → " ident
/-- Syntax for making a projection non-default in `initialize_simps_projections`. -/
syntax simpsRule.erase := "-" ident
/-- Syntax for making a projection default in `initialize_simps_projections`. -/
syntax simpsRule.add := "+" ident
/-- Syntax for making a projection prefix. -/
syntax simpsRule.prefix := &"as_prefix " ident
/-- Syntax for a single rule in `initialize_simps_projections`. -/
syntax simpsRule := simpsRule.prefix <|> simpsRule.rename <|> simpsRule.erase <|> simpsRule.add
/-- Syntax for `initialize_simps_projections`. -/
syntax simpsProj := ppSpace ident (" (" simpsRule,+ ")")?

/--
This command allows customisation of the lemmas generated by `simps`.

By default, tagging a definition of an element `myObj` of a structure `MyStruct` with `@[simps]`
generates one `@[simp]` lemma `myObj_myProj` for each projection `myProj` of `MyStruct`. There are a
few exceptions to this general rule:
* For algebraic structures, we will automatically use the notation (like `Mul`)
  for the projections if such an instance is available.
* By default, the projections to parent structures are not default projections,
  but all the data-carrying fields are (including those in parent structures).

This default behavior is customisable as such:
* You can disable a projection by default by running
  `initialize_simps_projections MulEquiv (-invFun)`
  This will ensure that no simp lemmas are generated for this projection,
  unless this projection is explicitly specified by the user (as in
  `@[simps invFun] def myEquiv : MulEquiv _ _ := _`).
* Conversely, you can enable a projection by default by running
  `initialize_simps_projections MulEquiv (+toEquiv)`.
* You can specify custom names by writing e.g.
  `initialize_simps_projections MulEquiv (toFun → apply, invFun → symm_apply)`.
* If you want the projection name added as a prefix in the generated lemma name, you can use
  `as_prefix fieldName`:
  `initialize_simps_projections MulEquiv (toFun → coe, as_prefix coe)`
  Note that this does not influence the parsing of projection names: if you have a declaration
  `foo` and you want to apply the projections `snd`, `coe` (which is a prefix) and `fst`, in that
  order you can run `@[simps snd_coe_fst] def foo ...` and this will generate a lemma with the
  name `coe_foo_snd_fst`.

Here are a few extra pieces of information:
  * Run `initialize_simps_projections?` (or `set_option trace.simps.verbose true`)
  to see the generated projections.
* Running `initialize_simps_projections MyStruct` without arguments is not necessary, it has the
  same effect if you just add `@[simps]` to a declaration.
* It is recommended to call `@[simps]` or `initialize_simps_projections` in the same file as the
  structure declaration. Otherwise, the projections could be generated multiple times in different
  files.

Some common uses:
* If you define a new homomorphism-like structure (like `MulHom`) you can just run
  `initialize_simps_projections` after defining the `DFunLike` instance (or instance that implies
  a `DFunLike` instance).
  ```
    instance {mM : Mul M} {mN : Mul N} : FunLike (MulHom M N) M N := ...
    initialize_simps_projections MulHom (toFun → apply)
  ```
  This will generate `foo_apply` lemmas for each declaration `foo`.
* If you prefer `coe_foo` lemmas that state equalities between functions, use
  `initialize_simps_projections MulHom (toFun → coe, as_prefix coe)`
  In this case you have to use `@[simps -fullyApplied]` whenever you call `@[simps]`.
* You can also initialize to use both, in which case you have to choose which one to use by default,
  by using either of the following
  ```
    initialize_simps_projections MulHom (toFun → apply, toFun → coe, as_prefix coe, -coe)
    initialize_simps_projections MulHom (toFun → apply, toFun → coe, as_prefix coe, -apply)
  ```
  In the first case, you can get both lemmas using `@[simps, simps -fullyApplied coe]` and in
  the second case you can get both lemmas using `@[simps -fullyApplied, simps apply]`.
* If you declare a new homomorphism-like structure (like `RelEmbedding`),
  then `initialize_simps_projections` will automatically find any `DFunLike` coercions
  that will be used as the default projection for the `toFun` field.
  ```
    initialize_simps_projections relEmbedding (toFun → apply)
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

namespace Simps

/-- Projection data for a single projection of a structure -/
structure ProjectionData where
  /-- The name used in the generated `simp` lemmas -/
  name : Name
  /-- An Expression used by simps for the projection. It must be definitionally equal to an original
  projection (or a composition of multiple projections).
  These Expressions can contain the universe parameters specified in the first argument of
  `structureExt`. -/
  expr : Expr
  /-- A list of natural numbers, which is the projection number(s) that have to be applied to the
  Expression. For example the list `[0, 1]` corresponds to applying the first projection of the
  structure, and then the second projection of the resulting structure (this assumes that the
  target of the first projection is a structure with at least two projections).
  The composition of these projections is required to be definitionally equal to the provided
  Expression. -/
  projNrs : List Nat
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
The `Simps.structureExt` environment extension specifies the preferred projections of the given
structure, used by the `@[simps]` attribute.
- You can generate this with the command `initialize_simps_projections`.
- If not generated, the `@[simps]` attribute will generate this automatically.
- To change the default value, see Note [custom simps projection].
- The first argument is the list of names of the universe variables used in the structure
- The second argument is an array that consists of the projection data for each projection.
-/
initialize structureExt : NameMapExtension (List Name × Array ProjectionData) ←
  registerNameMapExtension (List Name × Array ProjectionData)

/-- Projection data used internally in `getRawProjections`. -/
structure ParsedProjectionData where
  /-- name for this projection used in the structure definition -/
  strName : Name
  /-- syntax that might have provided `strName` -/
  strStx : Syntax := .missing
  /-- name for this projection used in the generated `simp` lemmas -/
  newName : Name
  /-- syntax that provided `newName` -/
  newStx : Syntax := .missing
  /-- will simp lemmas be generated for with (without specifically naming this?) -/
  isDefault : Bool := true
  /-- is the projection name a prefix? -/
  isPrefix : Bool := false
  /-- projection expression -/
  expr? : Option Expr := none
  /-- the list of projection numbers this expression corresponds to -/
  projNrs : Array Nat := #[]
  /-- is this a projection that is changed by the user? -/
  isCustom : Bool := false

/-- Turn `ParsedProjectionData` into `ProjectionData`. -/
def ParsedProjectionData.toProjectionData (p : ParsedProjectionData) : ProjectionData :=
  { p with name := p.newName, expr := p.expr?.getD default, projNrs := p.projNrs.toList }

instance : ToMessageData ParsedProjectionData where toMessageData
  | ⟨x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈, x₉⟩ => .group <| .nest 1 <|
    "⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂, toMessageData x₃, toMessageData x₄,
      toMessageData x₅, toMessageData x₆, toMessageData x₇, toMessageData x₈, toMessageData x₉]
    ("," ++ Format.line) ++ "⟩"

/-- The type of rules that specify how metadata for projections in changes.
See `initialize_simps_projections`. -/
inductive ProjectionRule where
  /-- A renaming rule `before→after` or
    Each name comes with the syntax used to write the rule,
    which is used to declare hover information. -/
  | rename (oldName : Name) (oldStx : Syntax) (newName : Name) (newStx : Syntax) :
      ProjectionRule
  /-- An adding rule `+fieldName` -/
  | add : Name → Syntax → ProjectionRule
  /-- A hiding rule `-fieldName` -/
  | erase : Name → Syntax → ProjectionRule
  /-- A prefix rule `prefix fieldName` -/
  | prefix : Name → Syntax → ProjectionRule

instance : ToMessageData ProjectionRule where toMessageData
  | .rename x₁ x₂ x₃ x₄ => .group <| .nest 1 <|
    "rename ⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂, toMessageData x₃, toMessageData x₄]
      ("," ++ Format.line) ++ "⟩"
  | .add x₁ x₂ => .group <| .nest 1 <|
    "+⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂] ("," ++ Format.line) ++ "⟩"
  | .erase x₁ x₂ => .group <| .nest 1 <|
    "-⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂] ("," ++ Format.line) ++ "⟩"
  | .prefix x₁ x₂ => .group <| .nest 1 <|
    "prefix ⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂] ("," ++ Format.line) ++ "⟩"

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
  m!"{pref} {str}:\n{toPrint}"

/-- Find the indices of the projections that need to be applied to elaborate `$e.$projName`.
Example: If `e : α ≃+ β` and ``projName = `invFun`` then this returns `[0, 1]`, because the first
projection of `MulEquiv` is `toEquiv` and the second projection of `Equiv` is `invFun`. -/
def findProjectionIndices (strName projName : Name) : MetaM (List Nat) := do
  let env ← getEnv
  let .some baseStr := findField? env strName projName |
    throwError "{strName} has no field {projName} in parent structure"
  let .some fullProjName := getProjFnForField? env baseStr projName |
    throwError "no such field {projName}"
  let .some pathToField := getPathToBaseStructure? env baseStr strName |
    throwError "no such field {projName}"
  let allProjs := pathToField ++ [fullProjName]
  return allProjs.map (env.getProjectionFnInfo? · |>.get!.i)

/--
A variant of `Substring.dropPrefix?` that does not consider `toFoo` to be a prefix to `toFoo_1`.
This is checked by inspecting whether the first character of the remaining part is a digit.

We use this variant because the latter is often a different field with an auto-generated name.
-/
private def dropPrefixIfNotNumber? (s : String) (pre : String) : Option Substring := do
  let ret ← s.dropPrefix? pre
  -- flag is true when the remaining part is nonempty and starts with a digit.
  let flag := ret.toString.data.head?.elim false Char.isDigit
  if flag then none else some ret

/-- A variant of `String.isPrefixOf` that does not consider `toFoo` to be a prefix to `toFoo_1`. -/
private def isPrefixOfAndNotNumber (s p : String) : Bool := (dropPrefixIfNotNumber? p s).isSome

/-- A variant of `String.splitOn` that does not split `toFoo_1` into `toFoo` and `1`. -/
private def splitOnNotNumber (s delim : String) : List String :=
  (process (s.splitOn delim).reverse "").reverse where
    process (arr : List String) (tail : String) := match arr with
      | [] => []
      | (x :: xs) =>
        -- flag is true when this segment is nonempty and starts with a digit.
        let flag := x.data.head?.elim false Char.isDigit
        if flag then
          process xs (tail ++ delim ++ x)
        else
          List.cons (x ++ tail) (process xs "")

/-- Auxiliary function of `getCompositeOfProjections`. -/
partial def getCompositeOfProjectionsAux (proj : String) (e : Expr) (pos : Array Nat)
    (args : Array Expr) : MetaM (Expr × Array Nat) := do
  let env ← getEnv
  let .const structName _ := (← whnf (← inferType e)).getAppFn |
    throwError "{e} doesn't have a structure as type"
  let projs := getStructureFieldsFlattened env structName
  let projInfo := projs.toList.map fun p ↦ do
    ((← dropPrefixIfNotNumber? proj (p.lastComponentAsString ++ "_")).toString, p)
  let some (projRest, projName) := projInfo.reduceOption.getLast? |
    throwError "Failed to find constructor {proj.dropRight 1} in structure {structName}."
  let newE ← mkProjection e projName
  let newPos := pos ++ (← findProjectionIndices structName projName)
  -- we do this here instead of in a recursive call in order to not get an unnecessary eta-redex
  if projRest.isEmpty then
    let newE ← mkLambdaFVars args newE
    return (newE, newPos)
  let type ← inferType newE
  forallTelescopeReducing type fun typeArgs _tgt ↦ do
    getCompositeOfProjectionsAux projRest (mkAppN newE typeArgs) newPos (args ++ typeArgs)

/-- Suppose we are given a structure `str` and a projection `proj`, that could be multiple nested
projections (separated by `_`), where each projection could be a projection of a parent structure.
This function returns an expression that is the composition of these projections and a
list of natural numbers, that are the projection numbers of the applied projections.
Note that this function is similar to elaborating dot notation, but it can do a little more.

Example: if we do
```
structure gradedFun (A : ℕ → Type*) where
  toFun := ∀ i j, A i →+ A j →+ A (i + j)
initialize_simps_projections (toFun_toFun_toFun → myMul)
```
we will be able to generate the "projection"
  `fun {A} (f : gradedFun A) (x : A i) (y : A j) ↦ ↑(↑(f.toFun i j) x) y`,
which projection notation cannot do. -/
def getCompositeOfProjections (structName : Name) (proj : String) : MetaM (Expr × Array Nat) := do
  let strExpr ← mkConstWithLevelParams structName
  let type ← inferType strExpr
  forallTelescopeReducing type fun typeArgs _ ↦
  withLocalDeclD `x (mkAppN strExpr typeArgs) fun e ↦
  getCompositeOfProjectionsAux (proj ++ "_") e #[] <| typeArgs.push e

/-- Get the default `ParsedProjectionData` for structure `str`.
It first returns the direct fields of the structure in the right order, and then
all (non-subobject fields) of all parent structures. The subobject fields are precisely the
non-default fields. -/
def mkParsedProjectionData (structName : Name) : CoreM (Array ParsedProjectionData) := do
  let env ← getEnv
  let projs := getStructureFields env structName
  if projs.size == 0 then
    throwError "Declaration {structName} is not a structure."
  let projData := projs.map fun fieldName ↦ {
    strName := fieldName, newName := fieldName,
    isDefault := isSubobjectField? env structName fieldName |>.isNone }
  let parentProjs := getStructureFieldsFlattened env structName false
  let parentProjs := parentProjs.filter (!projs.contains ·)
  let parentProjData := parentProjs.map fun nm ↦
    {strName := nm, newName := nm}
  return projData ++ parentProjData

/-- Execute the projection renamings (and turning off projections) as specified by `rules`. -/
def applyProjectionRules (projs : Array ParsedProjectionData) (rules : Array ProjectionRule) :
    CoreM (Array ParsedProjectionData) := do
  let projs : Array ParsedProjectionData := rules.foldl (init := projs) fun projs rule ↦
    match rule with
    | .rename strName strStx newName newStx =>
      if (projs.map (·.newName)).contains strName then
        projs.map fun proj ↦ if proj.newName == strName then
          { proj with
            newName,
            newStx,
            strStx := if proj.strStx.isMissing then strStx else proj.strStx } else
          proj else
        projs.push {strName, strStx, newName, newStx}
    | .erase nm stx =>
      if (projs.map (·.newName)).contains nm then
        projs.map fun proj ↦ if proj.newName = nm then
          { proj with
            isDefault := false,
            strStx := if proj.strStx.isMissing then stx else proj.strStx } else
          proj else
        projs.push {strName := nm, newName := nm, strStx := stx, newStx := stx, isDefault := false}
    | .add nm stx =>
      if (projs.map (·.newName)).contains nm then
        projs.map fun proj ↦ if proj.newName = nm then
          { proj with
            isDefault := true,
            strStx := if proj.strStx.isMissing then stx else proj.strStx } else
          proj else
        projs.push {strName := nm, newName := nm, strStx := stx, newStx := stx}
    | .prefix nm stx =>
      if (projs.map (·.newName)).contains nm then
        projs.map fun proj ↦ if proj.newName = nm then
          { proj with
            isPrefix := true,
            strStx := if proj.strStx.isMissing then stx else proj.strStx } else
          proj else
        projs.push {strName := nm, newName := nm, strStx := stx, newStx := stx, isPrefix := true}
  trace[simps.debug] "Projection info after applying the rules: {projs}."
  unless (projs.map (·.newName)).toList.Nodup do throwError "\
    Invalid projection names. Two projections have the same name.\n\
    This is likely because a custom composition of projections was given the same name as an \
    existing projection. Solution: rename the existing projection (before naming the \
    custom projection)."
  pure projs

/-- Auxiliary function for `getRawProjections`.
Generates the default projection, and looks for a custom projection declared by the user,
and replaces the default projection with the custom one, if it can find it. -/
def findProjection (str : Name) (proj : ParsedProjectionData)
    (rawUnivs : List Level) : CoreM ParsedProjectionData := do
  let env ← getEnv
  let (rawExpr, nrs) ← MetaM.run' <|
    getCompositeOfProjections str proj.strName.lastComponentAsString
  if !proj.strStx.isMissing then
    _ ← MetaM.run' <| TermElabM.run' <| addTermInfo proj.strStx rawExpr
  trace[simps.debug] "Projection {proj.newName} has default projection {rawExpr} and
    uses projection indices {nrs}"
  let customName := str ++ `Simps ++ proj.newName
  match env.find? customName with
  | some d@(.defnInfo _) =>
    let customProj := d.instantiateValueLevelParams! rawUnivs
    trace[simps.verbose] "found custom projection for {proj.newName}:{indentExpr customProj}"
    match (← MetaM.run' <| isDefEq customProj rawExpr) with
    | true =>
      _ ← MetaM.run' <| TermElabM.run' <| addTermInfo proj.newStx <|
        ← mkConstWithLevelParams customName
      pure { proj with expr? := some customProj, projNrs := nrs, isCustom := true }
    | false =>
      -- if the type of the Expression is different, we show a different error message, because
      -- (in Lean 3) just stating that the expressions are different is quite unhelpful
      let customProjType ← MetaM.run' (inferType customProj)
      let rawExprType ← MetaM.run' (inferType rawExpr)
      if (← MetaM.run' (isDefEq customProjType rawExprType)) then
        throwError "Invalid custom projection:{indentExpr customProj}\n\
          Expression is not definitionally equal to {indentExpr rawExpr}"
      else
        throwError "Invalid custom projection:{indentExpr customProj}\n\
          Expression has different type than {str ++ proj.strName}. Given type:\
          {indentExpr customProjType}\nExpected type:{indentExpr rawExprType}\n\
          Note: make sure order of implicit arguments is exactly the same."
  | _ =>
    _ ← MetaM.run' <| TermElabM.run' <| addTermInfo proj.newStx rawExpr
    pure {proj with expr? := some rawExpr, projNrs := nrs}

/-- Checks if there are declarations in the current file in the namespace `{str}.Simps` that are
not used. -/
def checkForUnusedCustomProjs (stx : Syntax) (str : Name) (projs : Array ParsedProjectionData) :
    CoreM Unit := do
  let nrCustomProjections := projs.toList.countP (·.isCustom)
  let env ← getEnv
  let customDeclarations := env.constants.map₂.foldl (init := #[]) fun xs nm _ =>
    if (str ++ `Simps).isPrefixOf nm && !nm.isInternalDetail && !isReservedName env nm then
      xs.push nm
    else
      xs
  if nrCustomProjections < customDeclarations.size then
    Linter.logLintIf linter.simpsUnusedCustomDeclarations stx m!"\
      Not all of the custom declarations {customDeclarations} are used. Double check the \
      spelling, and use `?` to get more information."

/-- If a structure has a field that corresponds to a coercion to functions or sets, or corresponds
  to notation, find the custom projection that uses this coercion or notation.
  Returns the custom projection and the name of the projection used.

We catch most errors this function causes, so that we don't fail if an unrelated projection has
an applicable name. (e.g. `Iso.inv`)

Implementation note: getting rid of TermElabM is tricky, since `Expr.mkAppOptM` doesn't allow to
keep metavariables around, which are necessary for `OutParam`. -/
def findAutomaticProjectionsAux (str : Name) (proj : ParsedProjectionData) (args : Array Expr) :
    TermElabM <| Option (Expr × Name) := do
  if let some ⟨className, isNotation, findArgs⟩ :=
    notationClassAttr.find? (← getEnv) proj.strName then
    let findArgs ← unsafe evalConst findArgType findArgs
    let classArgs ← try findArgs str className args
    catch ex =>
      trace[simps.debug] "Projection {proj.strName} is likely unrelated to the projection of \
        {className}:\n{ex.toMessageData}"
      return none
    let classArgs ← classArgs.mapM fun e => match e with
      | none => mkFreshExprMVar none
      | some e => pure e
    let classArgs := classArgs.map Arg.expr
    let projName := (getStructureFields (← getEnv) className)[0]!
    let projName := className ++ projName
    let eStr := mkAppN (← mkConstWithLevelParams str) args
    let eInstType ←
      try withoutErrToSorry (elabAppArgs (← Term.mkConst className) #[] classArgs none true false)
      catch ex =>
        trace[simps.debug] "Projection doesn't have the right type for the automatic projection:\n\
          {ex.toMessageData}"
        return none
    return ← withLocalDeclD `self eStr fun instStr ↦ do
      trace[simps.debug] "found projection {proj.strName}. Trying to synthesize {eInstType}."
      let eInst ← try synthInstance eInstType
      catch ex =>
        trace[simps.debug] "Didn't find instance:\n{ex.toMessageData}"
        return none
      let projExpr ← elabAppArgs (← Term.mkConst projName) #[] (classArgs.push <| .expr eInst)
        none true false
      let projExpr ← mkLambdaFVars (if isNotation then args.push instStr else args) projExpr
      let projExpr ← instantiateMVars projExpr
      return (projExpr, projName)
  return none

/-- Auxiliary function for `getRawProjections`.
Find custom projections, automatically found by simps.
These come from `DFunLike` and `SetLike` instances. -/
def findAutomaticProjections (str : Name) (projs : Array ParsedProjectionData) :
    CoreM (Array ParsedProjectionData) := do
  let strDecl ← getConstInfo str
  trace[simps.debug] "debug: {projs}"
  MetaM.run' <| TermElabM.run' (s := {levelNames := strDecl.levelParams}) <|
  forallTelescope strDecl.type fun args _ ↦ do
  let projs ← projs.mapM fun proj => do
    if let some (projExpr, projName) := ← findAutomaticProjectionsAux str proj args then
      unless ← isDefEq projExpr proj.expr?.get! do
        throwError "The projection {proj.newName} is not definitionally equal to an application \
          of {projName}:{indentExpr proj.expr?.get!}\nvs{indentExpr projExpr}"
      if proj.isCustom then
        trace[simps.verbose] "Warning: Projection {proj.newName} is given manually by the user, \
          but it can be generated automatically."
        return proj
      trace[simps.verbose] "Using {indentExpr projExpr}\nfor projection {proj.newName}."
      return { proj with expr? := some projExpr }
    return proj
  return projs

/--
Get the projections used by `simps` associated to a given structure `str`.

The returned information is also stored in the environment extension `Simps.structureExt`, which
is given to `str`. If `str` already has this attribute, the information is read from this
extension instead. See the documentation for this extension for the data this tactic returns.

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
  For example: ``getRawProjections env `Prod`` gives the default projections.
```
  ([u, v], [(`fst, `(Prod.fst.{u v}), [0], true, false),
     (`snd, `(@Prod.snd.{u v}), [1], true, false)])
```

Optionally, this command accepts three optional arguments:
* If `traceIfExists` the command will always generate a trace message when the structure already
  has an entry in `structureExt`.
* The `rules` argument specifies whether projections should be added, renamed, used as prefix, and
  not used by default.
* if `trc` is true, this tactic will trace information just as if
  `set_option trace.simps.verbose true` was set.
-/
def getRawProjections (stx : Syntax) (str : Name) (traceIfExists : Bool := false)
  (rules : Array ProjectionRule := #[]) (trc := false) :
  CoreM (List Name × Array ProjectionData) := do
  withOptions (· |>.updateBool `trace.simps.verbose (trc || ·)) <| do
  let env ← getEnv
  if let some data := (structureExt.getState env).find? str then
    -- We always print the projections when they already exists and are called by
    -- `initialize_simps_projections`.
    withOptions (· |>.updateBool `trace.simps.verbose (traceIfExists || ·)) <| do
      trace[simps.verbose]
        projectionsInfo data.2.toList "The projections for this structure have already been \
        initialized by a previous invocation of `initialize_simps_projections` or `@[simps]`.\n\
        Generated projections for" str
    return data
  trace[simps.verbose] "generating projection information for structure {str}."
  trace[simps.debug] "Applying the rules {rules}."
  let strDecl ← getConstInfo str
  let rawLevels := strDecl.levelParams
  let rawUnivs := rawLevels.map Level.param
  let projs ← mkParsedProjectionData str
  let projs ← applyProjectionRules projs rules
  let projs ← projs.mapM fun proj ↦ findProjection str proj rawUnivs
  checkForUnusedCustomProjs stx str projs
  let projs ← findAutomaticProjections str projs
  let projs := projs.map (·.toProjectionData)
  -- make all proofs non-default.
  let projs ← projs.mapM fun proj ↦ do
    match (← MetaM.run' <| isProof proj.expr) with
    | true => pure { proj with isDefault := false }
    | false => pure proj
  trace[simps.verbose] projectionsInfo projs.toList "generated projections for" str
  structureExt.add str (rawLevels, projs)
  trace[simps.debug] "Generated raw projection data:{indentD <| toMessageData (rawLevels, projs)}"
  pure (rawLevels, projs)

library_note "custom simps projection" /--
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

/-- Parse a rule for `initialize_simps_projections`. It is `<name>→<name>`, `-<name>`, `+<name>`
or `as_prefix <name>`. -/
def elabSimpsRule : Syntax → CommandElabM ProjectionRule
  | `(simpsRule| $id1 → $id2)   => return .rename id1.getId id1.raw id2.getId id2.raw
  | `(simpsRule| - $id)         => return .erase id.getId id.raw
  | `(simpsRule| + $id)         => return .add id.getId id.raw
  | `(simpsRule| as_prefix $id) => return .prefix id.getId id.raw
  | _                           => Elab.throwUnsupportedSyntax

/-- Function elaborating `initialize_simps_projections`. -/
@[command_elab «initialize_simps_projections»] def elabInitializeSimpsProjections : CommandElab
  | stx@`(initialize_simps_projections $[?%$trc]? $id $[($stxs,*)]?) => do
    let stxs := stxs.getD <| .mk #[]
    let rules ← stxs.getElems.raw.mapM elabSimpsRule
    let nm ← resolveGlobalConstNoOverload id
    _ ← liftTermElabM <| addTermInfo id.raw <| ← mkConstWithLevelParams nm
    _ ← liftCoreM <| getRawProjections stx nm true rules trc.isSome
  | _ => throwUnsupportedSyntax

/-- Configuration options for `@[simps]` -/
structure Config where
  /-- Make generated lemmas simp lemmas -/
  isSimp := true
  /-- Other simp-attributes to apply to generated lemmas.
  Attributes that are currently not simp-attributes are not supported. -/
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
  notRecursive := [`Prod, `PProd, `Opposite, `PreOpposite]
  /-- Output debug messages. Not used much, use `set_option simps.debug true` instead. -/
  debug := false
  /-- The stem to use for the projection names. If `none`, the default, use the suffix of the
  current declaration name, or the empty string if the declaration is an instance and the instance
  is named according to the `inst` convention. -/
  nameStem : Option String := none
  deriving Inhabited

/-- Function elaborating `Config` -/
declare_command_config_elab elabSimpsConfig Config

/-- A common configuration for `@[simps]`: generate equalities between functions instead equalities
between fully applied Expressions. Replaced by `@[simps -fullyApplied]`. -/
@[deprecated "use `-fullyApplied` instead" (since := "2025-03-10")]
def Config.asFn : Simps.Config where
  fullyApplied := false

/-- A common configuration for `@[simps]`: don't tag the generated lemmas with `@[simp]`.
Replaced by `@[simps -isSimp]`. -/
@[deprecated "use `-isSimp` instead" (since := "2025-03-10")]
def Config.lemmasOnly : Config where
  isSimp := false

/-- `instantiateLambdasOrApps es e` instantiates lambdas in `e` by expressions from `es`.
If the length of `es` is larger than the number of lambdas in `e`,
then the term is applied to the remaining terms.
Also reduces head let-expressions in `e`, including those after instantiating all lambdas.

This is very similar to `expr.substs`, but this also reduces head let-expressions. -/
partial def _root_.Lean.Expr.instantiateLambdasOrApps (es : Array Expr) (e : Expr) : Expr :=
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

  Example 1: ``getProjectionExprs env `(α × β) `(⟨x, y⟩)`` will give the output
  ```
    [(`(x), `fst, `(@Prod.fst.{u v} α β), [], true, false),
     (`(y), `snd, `(@Prod.snd.{u v} α β), [], true, false)]
  ```

  Example 2: ``getProjectionExprs env `(α ≃ α) `(⟨id, id, fun _ ↦ rfl, fun _ ↦ rfl⟩)``
  will give the output
  ```
    [(`(id), `apply, (Equiv.toFun), [], true, false),
     (`(id), `symm_apply, (fun e ↦ e.symm.toFun), [], true, false),
     ...,
     ...]
  ```
-/
def getProjectionExprs (stx : Syntax) (tgt : Expr) (rhs : Expr) (cfg : Config) :
    MetaM <| Array <| Expr × ProjectionData := do
  -- the parameters of the structure
  let params := tgt.getAppArgs
  if cfg.debug && !(← (params.zip rhs.getAppArgs).allM fun ⟨a, b⟩ ↦ isDefEq a b) then
    throwError "unreachable code: parameters are not definitionally equal"
  let str := tgt.getAppFn.constName?.getD default
  -- the fields of the object
  let rhsArgs := rhs.getAppArgs.toList.drop params.size
  let (rawUnivs, projDeclata) ← getRawProjections stx str
  projDeclata.mapM fun proj ↦ do
    let expr := proj.expr.instantiateLevelParams rawUnivs tgt.getAppFn.constLevels!
    -- after instantiating universes, we have to check again whether the expression is a proof.
    let proj := if ← isProof expr
      then { proj with isDefault := false }
      else proj
    return (rhsArgs.getD (fallback := default) proj.projNrs.head!,
      { proj with
        expr := expr.instantiateLambdasOrApps params
        projNrs := proj.projNrs.tail })

variable (ref : Syntax) (univs : List Name)

/-- Add a lemma with `nm` stating that `lhs = rhs`. `type` is the type of both `lhs` and `rhs`,
`args` is the list of local constants occurring, and `univs` is the list of universe variables. -/
def addProjection (declName : Name) (type lhs rhs : Expr) (args : Array Expr)
    (cfg : Config) : MetaM Unit := do
  trace[simps.debug] "Planning to add the equality{indentD m!"{lhs} = ({rhs} : {type})"}"
  let env ← getEnv
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
  if (env.find? declName).isSome then -- diverging behavior from Lean 3
    throwError "simps tried to add lemma{indentD m!"{.ofConstName declName} : {declType}"}\n\
      to the environment, but it already exists."
  trace[simps.verbose] "adding projection {declName}:{indentExpr declType}"
  try
    addDecl <| .thmDecl {
      name := declName
      levelParams := univs
      type := declType
      value := declValue }
  catch ex =>
    throwError "Failed to add projection lemma {declName}. Nested error:\n{ex.toMessageData}"
  addDeclarationRangesFromSyntax declName (← getRef) ref
  _ ← MetaM.run' <| TermElabM.run' <| addTermInfo (isBinder := true) ref <|
    ← mkConstWithLevelParams declName
  if cfg.isSimp then
    addSimpTheorem simpExtension declName true false .global <| eval_prio default
  _ ← cfg.attrs.mapM fun simpAttr ↦ do
    let .some simpDecl ← getSimpExtension? simpAttr |
      throwError "{simpAttr} is not a simp-attribute."
    addSimpTheorem simpDecl declName true false .global <| eval_prio default

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
partial def addProjections (nm : NameStruct) (type lhs rhs : Expr)
  (args : Array Expr) (mustBeStr : Bool) (cfg : Config)
  (todo : List (String × Syntax)) (toApply : List Nat) : MetaM (Array Name) := do
  -- we don't want to unfold non-reducible definitions (like `Set`) to apply more arguments
  trace[simps.debug] "Type of the Expression before normalizing: {type}"
  withTransparency cfg.typeMd <| forallTelescopeReducing type fun typeArgs tgt ↦ withDefault do
  trace[simps.debug] "Type after removing pi's: {tgt}"
  let tgt ← whnfD tgt
  trace[simps.debug] "Type after reduction: {tgt}"
  let newArgs := args ++ typeArgs
  let lhsAp := lhs.instantiateLambdasOrApps typeArgs
  let rhsAp := rhs.instantiateLambdasOrApps typeArgs
  let str := tgt.getAppFn.constName
  trace[simps.debug] "todo: {todo}, toApply: {toApply}"
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
  if strInfo?.isNone ||
    (todo.isEmpty && str ∈ cfg.notRecursive && !mustBeStr && toApply.isEmpty) then
    if mustBeStr then
      throwError "Invalid `simps` attribute. Target {str} is not a structure"
    if !todoNext.isEmpty && str ∉ cfg.notRecursive then
      let firstTodo := todoNext.head!.1
      throwError "Invalid simp lemma {nm.update firstTodo false |>.toName}.\nProjection \
        {(splitOnNotNumber firstTodo "_")[1]!} doesn't exist, \
        because target {str} is not a structure."
    if cfg.fullyApplied then
      addProjection stxProj univs nm.toName tgt lhsAp rhsAp newArgs cfg
    else
      addProjection stxProj univs nm.toName type lhs rhs args cfg
    return #[nm.toName]
  -- if the type is a structure
  let some (.inductInfo { isRec := false, ctors := [ctor], .. }) := env.find? str | unreachable!
  trace[simps.debug] "{str} is a structure with constructor {ctor}."
  let rhsEta ← headStructureEtaReduce rhsAp
  -- did the user ask to add this projection?
  let addThisProjection := stx?.isSome && toApply.isEmpty
  if addThisProjection then
    -- we pass the precise argument of simps as syntax argument to `addProjection`
    if cfg.fullyApplied then
      addProjection stxProj univs nm.toName tgt lhsAp rhsEta newArgs cfg
    else
      addProjection stxProj univs nm.toName type lhs rhs args cfg
  let rhsWhnf ← withTransparency cfg.rhsMd <| whnf rhsEta
  trace[simps.debug] "The right-hand-side {indentExpr rhsAp}\n reduces to {indentExpr rhsWhnf}"
  if !rhsWhnf.getAppFn.isConstOf ctor then
    -- if I'm about to run into an error, try to set the transparency for `rhsMd` higher.
    if cfg.rhsMd == .reducible && (mustBeStr || !todoNext.isEmpty || !toApply.isEmpty) then
      trace[simps.debug] "Using relaxed reducibility."
      Linter.logLintIf linter.simpsNoConstructor ref m!"\
        The definition {nm.toName} is not a constructor application. \
        Please use `@[simps!]` instead.\n\
        \n\
        Explanation: `@[simps]` uses the definition to find what the simp lemmas should \
        be. If the definition is a constructor, then this is easy, since the values of the \
        projections are just the arguments to the constructor. If the definition is not a \
        constructor, then `@[simps]` will unfold the right-hand side until it has found a \
        constructor application, and uses those values.\n\n\
        This might not always result in the simp-lemmas you want, so you are advised to use \
        `@[simps?]` to double-check whether `@[simps]` generated satisfactory lemmas.\n\
        Note 1: `@[simps!]` also calls the `simp` tactic, and this can be expensive in certain \
        cases.\n\
        Note 2: `@[simps!]` is equivalent to `@[simps (config := \{rhsMd := .default, \
        simpRhs := true})]`. You can also try `@[simps (config := \{rhsMd := .default})]` \
        to still unfold the definitions, but avoid calling `simp` on the resulting statement.\n\
        Note 3: You need `simps!` if not all fields are given explicitly in this definition, \
        even if the definition is a constructor application. For example, if you give a \
        `MulEquiv` by giving the corresponding `Equiv` and the proof that it respects \
        multiplication, then you need to mark it as `@[simps!]`, since the attribute needs to \
        unfold the corresponding `Equiv` to get to the `toFun` field."
      let nms ← addProjections nm type lhs rhs args mustBeStr
        { cfg with rhsMd := .default, simpRhs := true } todo toApply
      return if addThisProjection then nms.push nm.toName else nms
    if !toApply.isEmpty then
      throwError "Invalid simp lemma {nm.toName}.\nThe given definition is not a constructor \
        application:{indentExpr rhsWhnf}"
    if mustBeStr then
      throwError "Invalid `simps` attribute. The body is not a constructor application:\
        {indentExpr rhsWhnf}"
    if !todoNext.isEmpty then
      throwError "Invalid simp lemma {nm.update todoNext.head!.1 false |>.toName}.\n\
        The given definition is not a constructor application:{indentExpr rhsWhnf}"
    if !addThisProjection then
      if cfg.fullyApplied then
        addProjection stxProj univs nm.toName tgt lhsAp rhsEta newArgs cfg
      else
        addProjection stxProj univs nm.toName type lhs rhs args cfg
    return #[nm.toName]
  -- if the value is a constructor application
  trace[simps.debug] "Generating raw projection information..."
  let projInfo ← getProjectionExprs ref tgt rhsWhnf cfg
  trace[simps.debug] "Raw projection information:{indentD m!"{projInfo}"}"
  -- If we are in the middle of a composite projection.
  if let idx :: rest := toApply then
    let some ⟨newRhs, _⟩ := projInfo[idx]?
      | throwError "unreachable: index of composite projection is out of bounds."
    let newType ← inferType newRhs
    trace[simps.debug] "Applying a custom composite projection. Todo: {toApply}. Current lhs:\
      {indentExpr lhsAp}"
    return ← addProjections nm newType lhsAp newRhs newArgs false cfg todo rest
  trace[simps.debug] "Not in the middle of applying a custom composite projection"
  /- We stop if no further projection is specified or if we just reduced an eta-expansion and we
  automatically choose projections -/
  if todo.length == 1 && todo.head!.1 == "" then return #[nm.toName]
  let projs : Array Name := projInfo.map fun x ↦ x.2.name
  let todo := todoNext
  trace[simps.debug] "Next todo: {todoNext}"
  -- check whether all elements in `todo` have a projection as prefix
  if let some (x, _) := todo.find? fun (x, _) ↦ projs.all
    fun proj ↦ !isPrefixOfAndNotNumber (proj.lastComponentAsString ++ "_") x then
    let simpLemma := nm.update x |>.toName
    let neededProj := (splitOnNotNumber x "_")[0]!
    throwError "Invalid simp lemma {simpLemma}. \
      Structure {str} does not have projection {neededProj}.\n\
      The known projections are:\
      {indentD <| toMessageData projs}\n\
      You can also see this information by running\
      \n  `initialize_simps_projections? {str}`.\n\
      Note: these projection names might be customly defined for `simps`, \
      and could differ from the projection names of the structure."
  let nms ← projInfo.flatMapM fun ⟨newRhs, proj, projExpr, projNrs, isDefault, isPrefix⟩ ↦ do
    let newType ← inferType newRhs
    let newTodo := todo.filterMap
      fun (x, stx) ↦ (dropPrefixIfNotNumber? x (proj.lastComponentAsString ++ "_")).map
        (·.toString, stx)
    -- we only continue with this field if it is default or mentioned in todo
    if !(isDefault && todo.isEmpty) && newTodo.isEmpty then return #[]
    let newLhs := projExpr.instantiateLambdasOrApps #[lhsAp]
    let newName := nm.update proj.lastComponentAsString isPrefix
    trace[simps.debug] "Recursively add projections for:{indentExpr newLhs}"
    addProjections newName newType newLhs newRhs newArgs false cfg newTodo projNrs
  return if addThisProjection then nms.push nm.toName else nms

end Simps
open Simps

/-- `simpsTac` derives `simp` lemmas for all (nested) non-Prop projections of the declaration.
If `todo` is non-empty, it will generate exactly the names in `todo`.
If `shortNm` is true, the generated names will only use the last projection name.
If `trc` is true, trace as if `trace.simps.verbose` is true. -/
def simpsTac (ref : Syntax) (nm : Name) (cfg : Config := {})
    (todo : List (String × Syntax) := []) (trc := false) : AttrM (Array Name) :=
  withOptions (· |>.updateBool `trace.simps.verbose (trc || ·)) <| do
  let env ← getEnv
  let some d := env.find? nm | throwError "Declaration {nm} doesn't exist."
  let lhs : Expr := mkConst d.name <| d.levelParams.map Level.param
  let todo := todo.eraseDups |>.map fun (proj, stx) ↦ (proj ++ "_", stx)
  let mut cfg := cfg
  let nm : NameStruct :=
    { parent := nm.getPrefix
      components :=
        if let .some n := cfg.nameStem then
          if n == "" then [] else [n]
        else
          let s := nm.lastComponentAsString
          if (← isInstance nm) ∧ s.startsWith "inst" then [] else [s]}
  MetaM.run' <| addProjections ref d.levelParams
    nm d.type lhs (d.value?.getD default) #[] (mustBeStr := true) cfg todo []

/-- elaborate the syntax and run `simpsTac`. -/
def simpsTacFromSyntax (nm : Name) (stx : Syntax) : AttrM (Array Name) :=
  match stx with
  | `(attr| simps $[!%$bang]? $[?%$trc]? $c:optConfig $[$ids]*) => do
    let cfg ← liftCommandElabM <| elabSimpsConfig c
    let cfg := if bang.isNone then cfg else { cfg with rhsMd := .default, simpRhs := true }
    let ids := ids.map fun x => (x.getId.eraseMacroScopes.lastComponentAsString, x.raw)
    simpsTac stx nm cfg ids.toList trc.isSome
  | _ => throwUnsupportedSyntax

/-- The `simps` attribute. -/
initialize simpsAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `simps
    /- So as to be run _after_ the `instance` attribute, as this handler uses
    `Lean.Meta.isInstance`, which requires the `instance` handler to have
    already run. -/
    applicationTime := .afterCompilation
    descr := "Automatically derive lemmas specifying the projections of this declaration.",
    getParam := simpsTacFromSyntax }
