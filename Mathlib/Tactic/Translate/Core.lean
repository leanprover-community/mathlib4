/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn, Jon Eugster, Bryan Gin-ge Chen,
Jovan Gerbscheid
-/
import Batteries.Tactic.Trans
import Lean.Compiler.NoncomputableAttr
import Lean.Elab.Tactic.Ext
import Lean.Meta.Tactic.Rfl
import Lean.Meta.Tactic.Symm
import Mathlib.Data.Array.Defs
import Mathlib.Data.Nat.Notation
import Mathlib.Lean.Expr.ReplaceRec
import Mathlib.Lean.Meta.Simp
import Mathlib.Lean.Name
import Mathlib.Tactic.Eqns -- just to copy the attribute
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.Translate.GuessName

/-!
# The translation attribute.

Implementation of the translation attribute. This is used for `@[to_additive]` and `@[to_dual]`.
See the docstring of `to_additive` for more information
-/

open Lean Meta Elab Command Std

namespace Mathlib.Tactic.Translate
open Translate -- currently needed to enable projection notation

/-- `(attr := ...)` applies the given attributes to the original and the translated declaration.
In the case of `to_additive`, we may want to apply it multiple times,
(such as in `a ^ n` -> `n • a` -> `n +ᵥ a`). In this case, you should use the syntax
`to_additive (attr := some_other_attr, to_additive)`, which will apply `some_other_attr` to all
three generated declarations.
 -/
syntax attrOption := &"attr" " := " Parser.Term.attrInstance,*
/--
`(reorder := ...)` reorders the arguments/hypotheses in the generated declaration.
It uses cycle notation. For example `(reorder := 1 2, 5 6)` swaps the first two
arguments with each other and the fifth and the sixth argument and `(reorder := 3 4 5)` will move
the fifth argument before the third argument. This is used in `to_dual` to swap the arguments in
`≤`, `<` and `⟶`. It is also used in `to_additive` to translate from `^` to `•`.
-/
syntax reorderOption := &"reorder" " := " (num+),+
/--
the `(relevant_arg := ...)` option tells which argument to look at to determine whether to
translate this constant. This is inferred automatically using the function `findRelevantArg`,
but it can also be overwritten using this syntax.

If there are multiple possible arguments, we typically tag the first one.
If this argument contains a fixed type, this declaration will not be translated.
See the Heuristics section of the `to_additive` doc-string for more details.

If a declaration is not tagged, it is presumed that the first argument is relevant.

To indicate that there is no relevant argument, set it to a number that is out of bounds,
i.e. larger than the number of arguments, e.g. `(relevant_arg := 100)`.

Implementation note: we only allow exactly 1 relevant argument, even though some declarations
(like `Prod.instGroup`) have multiple relevant argument.
The reason is that whether we translate a declaration is an all-or-nothing decision, and
we will not be able to translate declarations that (e.g.) talk about multiplication on `ℕ × α`
anyway.
-/
syntax relevantArgOption := &"relevant_arg" " := " num
/--
`(dont_translate := ...)` takes a list of type variables (separated by spaces) that should not be
considered for translation. For example in
```
lemma foo {α β : Type} [Group α] [Group β] (a : α) (b : β) : a * a⁻¹ = 1 ↔ b * b⁻¹ = 1
```
we can choose to only translate `α` by writing `to_additive (dont_translate := β)`.
-/
syntax dontTranslateOption := &"dont_translate" " := " ident+
syntax bracketedOption := "(" attrOption <|> reorderOption <|>
  relevantArgOption <|> dontTranslateOption ")"
/-- A hint for where to find the translated declaration (`existing` or `self`) -/
syntax existingNameHint := (ppSpace (&"existing" <|> &"self"))?
syntax attrArgs :=
  existingNameHint (ppSpace bracketedOption)* (ppSpace ident)? (ppSpace (str <|> docComment))?

-- We omit a doc-string on these syntaxes to instead show the `to_additive` or `to_dual` doc-string
attribute [nolint docBlame] attrArgs bracketedOption

/-- An attribute that stores all the declarations that deal with numeric literals on variable types.

Numeral literals occur in expressions without type information, so in order to decide whether `1`
needs to be changed to `0`, the context around the numeral is relevant.
Most numerals will be in an `OfNat.ofNat` application, though tactics can add numeral literals
inside arbitrary functions. By default we assume that we do not change numerals, unless it is
in a function application with the `translate_change_numeral` attribute.

`@[translate_change_numeral n₁ ...]` should be added to all functions that take one or more
numerals as argument that should be changed if `shouldTranslate` succeeds on the first argument,
i.e. when the numeral is only translated if the first argument is a variable
(or consists of variables).
The arguments `n₁ ...` are the positions of the numeral arguments (starting counting from 1). -/
syntax (name := translate_change_numeral) "translate_change_numeral" (ppSpace num)* : attr

initialize registerTraceClass `translate
initialize registerTraceClass `translate_detail

/-- Linter, mostly used by translate attributes, that checks that the source declaration doesn't
have certain attributes -/
register_option linter.existingAttributeWarning : Bool := {
  defValue := true
  descr := "Linter, mostly used by translate attributes, that checks that the source declaration \
    doesn't have certain attributes" }

/-- Linter used by translate attributes that checks if the given declaration name is
    equal to the automatically generated name -/
register_option linter.translateGenerateName : Bool := {
  defValue := true
  descr := "Linter used by translate attributes that checks if the given declaration name is \
    equal to the automatically generated name" }

/-- Linter to check whether the user correctly specified that the translated declaration already
exists -/
register_option linter.translateExisting : Bool := {
  defValue := true
  descr := "Linter used by translate attributes that checks whether the user correctly specified
    that the translated declaration already exists" }

@[inherit_doc translate_change_numeral]
initialize changeNumeralAttr : NameMapExtension (List Nat) ←
  registerNameMapAttribute {
    name := `translate_change_numeral
    descr :=
      "Auxiliary attribute for `to_additive` that stores functions that have numerals as argument."
    add := fun
    | _, `(attr| translate_change_numeral $[$arg]*) =>
      pure <| arg.map (·.1.isNatLit?.get!.pred) |>.toList
    | _, _ => throwUnsupportedSyntax }

/-- `TranslateData` is a structure that holds all data required for a translation attribute. -/
structure TranslateData : Type where
  /-- An attribute that tells that certain arguments of this definition are not
  involved when translating.
  This helps the translation heuristic by also transforming definitions if `ℕ` or another
  fixed type occurs as one of these arguments. -/
  ignoreArgsAttr : NameMapExtension (List Nat)
  /-- `reorderAttr` stores the declarations that need their arguments reordered when translating.
  This is specified using the `(reorder := ...)` syntax. -/
  reorderAttr : NameMapExtension (List <| List Nat)
  relevantArgAttr : NameMapExtension Nat
  /-- The global `dont_translate` attribute specifies that operations on the given type
  should not be translated. This can be either for types that are translated,
  such as `MonoidAlgebra` -> `AddMonoidAlgebra`, or for fixed types, such as `Fin n`/`ZMod n`.

  Note: The name generation is not aware that the operations on this type should not be translated,
    so you generally have to specify a name manually, if some part should not be translated.
  -/
  dontTranslateAttr : NameMapExtension Unit
  /-- `translations` stores all of the constants that have been tagged with this attribute,
  and maps them to their translation. -/
  translations : NameMapExtension Name
  /-- The name of the attribute, for example `to_additive` or `to_dual`. -/
  attrName : Name
  /-- If `changeNumeral := true`, then try to translate the number `1` to `0`. -/
  changeNumeral : Bool
  /-- When `isDual := true`, every translation `A → B` will also give a translation `B → A`. -/
  isDual : Bool
  guessNameData : GuessName.GuessNameData

attribute [inherit_doc relevantArgOption] TranslateData.relevantArgAttr
attribute [inherit_doc GuessName.GuessNameData] TranslateData.guessNameData

/-- Get the translation for the given name. -/
def findTranslation? (env : Environment) (t : TranslateData) : Name → Option Name :=
  (t.translations.getState env).find?

/-- Get the translation for the given name,
falling back to translating a prefix of the name if the full name can't be translated.
This allows translating automatically generated declarations such as `IsRegular.casesOn`. -/
def findPrefixTranslation (env : Environment) (nm : Name) (t : TranslateData) : Name :=
  nm.mapPrefix (findTranslation? env t)

/-- Add a name translation to the translations map. -/
def insertTranslation (t : TranslateData) (src tgt : Name) (failIfExists := true) : CoreM Unit := do
  if let some tgt' := findTranslation? (← getEnv) t src then
    if failIfExists then
      throwError "The translation {src} ↦ {tgt'} already exists"
    else
      trace[translate] "The translation {src} ↦ {tgt'} already exists"
      return
  modifyEnv (t.translations.addEntry · (src, tgt))
  trace[translate] "Added translation {src} ↦ {tgt}"
  -- For an attribute like `to_dual`, we also insert the reverse direction of the translation
  if t.isDual && src != tgt then
    if let some src' := findTranslation? (← getEnv) t tgt then
      if failIfExists then
        throwError "The translation {tgt} ↦ {src'} already exists"
      else
        trace[translate] "The translation {tgt} ↦ {src'} already exists"
        return
    modifyEnv (t.translations.addEntry · (tgt, src))
    trace[translate] "Also added translation {tgt} ↦ {src}"

/-- `ArgInfo` stores information about how a constant should be translated. -/
structure ArgInfo where
  /-- The arguments that should be reordered when translating, using cycle notation. -/
  reorder : List (List Nat) := []
  /-- The argument used to determine whether this constant should be translated. -/
  relevantArg : Nat := 0

/-- Add a name translation to the translations map and add the `argInfo` information to `src`. -/
def insertTranslationAndInfo (t : TranslateData) (src tgt : Name) (argInfo : ArgInfo)
    (failIfExists := true) : CoreM Unit := do
  insertTranslation t src tgt failIfExists
  if argInfo.reorder != [] then
    trace[translate] "@[{t.attrName}] will reorder the arguments of {tgt} by {argInfo.reorder}."
    t.reorderAttr.add src argInfo.reorder
  if argInfo.relevantArg != 0 then
    trace[translate_detail] "Setting relevant_arg for {src} to be {argInfo.relevantArg}."
    t.relevantArgAttr.add src argInfo.relevantArg

/-- `Config` is the type of the arguments that can be provided to `to_additive`. -/
structure Config : Type where
  /-- View the trace of the translation procedure.
  Equivalent to `set_option trace.translate true`. -/
  trace : Bool := false
  /-- The given name of the target. -/
  tgt : Name := Name.anonymous
  /-- An optional doc string. -/
  doc : Option String := none
  /-- If `allowAutoName` is `false` (default) then
  we check whether the given name can be auto-generated. -/
  allowAutoName : Bool := false
  /-- The arguments that should be reordered when translating, using cycle notation. -/
  reorder : List (List Nat) := []
  /-- The argument used to determine whether this constant should be translated. -/
  relevantArg? : Option Nat := none
  /-- The attributes which we want to give to the original and translated declaration.
  For `simps` this will also add generated lemmas to the translation dictionary. -/
  attrs : Array Syntax := #[]
  /-- A list of type variables that should not be translated. -/
  dontTranslate : List Ident := []
  /-- The `Syntax` element corresponding to the translation attribute,
  which we need for adding definition ranges, and for logging messages. -/
  ref : Syntax
  /-- An optional flag stating that the translated declaration already exists.
  If this flag is wrong about whether the translated declaration exists, we raise a linter error.
  Note: the linter will never raise an error for inductive types and structures. -/
  existing : Bool := false
  /-- An optional flag stating that the target of the translation is the target itself.
  This can be used to reorder arguments, such as in
  `attribute [to_dual self (reorder := 3 4)] LE.le`.
  It can also be used to give a hint to `shouldTranslate`, such as in
  `attribute [to_additive self] Unit`.
  If `self := true`, we should also have `existing := true`. -/
  self : Bool := false
  deriving Repr

-- See https://github.com/leanprover/lean4/issues/10295
attribute [nolint unusedArguments] instReprConfig.repr

/-- Eta expands `e` at most `n` times. -/
def etaExpandN (n : Nat) (e : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType e) (some n) fun xs _ ↦ mkLambdaFVars xs (mkAppN e xs)

/-- `e.expand` eta-expands all expressions that have as head a constant `n` in `reorder`.
They are expanded until they are applied to one more argument than the maximum in `reorder.find n`.
It also expands all kernel projections that have as head a constant `n` in `reorder`. -/
def expand (t : TranslateData) (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let reorderFn : Name → List (List ℕ) := fun nm ↦ (t.reorderAttr.find? env nm |>.getD [])
  let e₂ ← Lean.Meta.transform (input := e) (skipConstInApp := true)
    (post := fun e => return .done e) fun e ↦
    e.withApp fun f args ↦ do
    match f with
    | .proj n i s =>
      let some info := getStructureInfo? (← getEnv) n | return .continue -- e.g. if `n` is `Exists`
      let some projName := info.getProjFn? i | unreachable!
      -- if `projName` has a translation, replace `f` with the application `projName s`
      -- and then visit `projName s args` again.
      if findTranslation? env t projName |>.isNone then
        return .continue
      return .visit <| (← whnfD (← inferType s)).withApp fun sf sargs ↦
        mkAppN (mkApp (mkAppN (.const projName sf.constLevels!) sargs) s) args
    | .const c _ =>
      let reorder := reorderFn c
      if reorder.isEmpty then
        -- no need to expand if nothing needs reordering
        return .continue
      let needed_n := reorder.flatten.foldr Nat.max 0 + 1
      if needed_n ≤ args.size then
        return .continue
      else
        -- in this case, we need to reorder arguments that are not yet
        -- applied, so first η-expand the function.
        let e' ← etaExpandN (needed_n - args.size) e
        trace[translate_detail] "expanded {e} to {e'}"
        return .continue e'
    | _ => return .continue
  if e != e₂ then
    trace[translate_detail] "expand:\nBefore: {e}\nAfter: {e₂}"
  return e₂

/-- Implementation function for `shouldTranslate`.
Failure means that in that subexpression there is no constant that blocks `e` from being translated.
We cache previous applications of the function, using an expression cache using ptr equality
to avoid visiting the same subexpression many times. Note that we only need to cache the
expressions without taking the value of `inApp` into account, since `inApp` only matters when
the expression is a constant. However, for this reason we have to make sure that we never
cache constant expressions, so that's why the `if`s in the implementation are in this order.

Note that this function is still called many times by `applyReplacementFun`
and we're not remembering the cache between these calls. -/
private unsafe def shouldTranslateUnsafe (env : Environment) (t : TranslateData) (e : Expr)
    (dontTranslate : Array FVarId) : Option (Name ⊕ FVarId) :=
  let rec visit (e : Expr) (inApp := false) : OptionT (StateM (PtrSet Expr)) (Name ⊕ FVarId) := do
    if e.isConst then
      if (t.dontTranslateAttr.find? env e.constName).isNone &&
        (inApp || (findTranslation? env t e.constName).isSome) then
        failure
      else
        return .inl e.constName
    if (← get).contains e then
      failure
    modify fun s => s.insert e
    match e with
    | x@(.app e a)       =>
        visit e true <|> do
          -- make sure that we don't treat `(fun x => α) (n + 1)` as a type that depends on `Nat`
          guard !x.isConstantApplication
          if let some n := e.getAppFn.constName? then
            if let some l := t.ignoreArgsAttr.find? env n then
              if e.getAppNumArgs + 1 ∈ l then
                failure
          visit a
    | .lam _ _ t _       => visit t
    | .forallE _ _ t _   => visit t
    | .letE _ _ e body _ => visit e <|> visit body
    | .mdata _ b         => visit b
    | .proj _ _ b        => visit b
    | .fvar fvarId       => if dontTranslate.contains fvarId then return .inr fvarId else failure
    | _                  => failure
  Id.run <| (visit e).run' mkPtrSet

/-- `shouldTranslate e` tests whether the expression `e` contains a constant
`nm` that is not applied to any arguments, and such that `translations.find?[nm] = none`.
This is used for deciding which subexpressions to translate: we only translate
constants if `shouldTranslate` applied to their relevant argument returns `true`.
This means we will replace expression applied to e.g. `α` or `α × β`, but not when applied to
e.g. `ℕ` or `ℝ × α`.
We ignore all arguments specified by the `ignore` `NameMap`. -/
def shouldTranslate (env : Environment) (t : TranslateData) (e : Expr)
    (dontTranslate : Array FVarId := #[]) : Option (Name ⊕ FVarId) :=
  unsafe shouldTranslateUnsafe env t e dontTranslate

/-- Swap the first two elements of a list -/
def List.swapFirstTwo {α : Type*} : List α → List α
  | []      => []
  | [x]     => [x]
  | x::y::l => y::x::l

/-- Change the numeral `nat_lit 1` to the numeral `nat_lit 0`.
Leave all other expressions unchanged. -/
def changeNumeral : Expr → Expr
  | .lit (.natVal 1) => mkRawNatLit 0
  | e                => e

/--
`applyReplacementFun e` replaces the expression `e` with its tranlsation.
It translates each identifier (inductive type, defined function etc) in an expression, unless
* The identifier occurs in an application with first argument `arg`; and
* `test arg` is false.
However, if `f` is in the dictionary `relevant`, then the argument `relevant.find f`
is tested, instead of the first argument.

It will also reorder arguments of certain functions, using `reorderFn`:
e.g. `g x₁ x₂ x₃ ... xₙ` becomes `g x₂ x₁ x₃ ... xₙ` if `reorderFn g = some [1]`.
-/
def applyReplacementFun (t : TranslateData) (e : Expr) (dontTranslate : Array FVarId := #[]) :
    MetaM Expr := do
  let e' := aux (← getEnv) (← getBoolOption `trace.translate_detail) (← expand t e)
  -- Make sure any new reserved names in the expr are realized; this needs to be done outside of
  -- `aux` as it is monadic.
  e'.forEach fun
    | .const n .. => do
      if !(← hasConst (skipRealize := false) n) && isReservedName (← getEnv) n then
        executeReservedNameAction n
    | _ => pure ()
  return e'
where /-- Implementation of `applyReplacementFun`. -/
  aux (env : Environment) (trace : Bool) : Expr → Expr :=
  let reorderFn : Name → List (List ℕ) := fun nm ↦ (t.reorderAttr.find? env nm |>.getD [])
  let relevantArg : Name → ℕ := fun nm ↦ (t.relevantArgAttr.find? env nm).getD 0
  Lean.Expr.replaceRec fun r e ↦ Id.run do
    if trace then
      dbg_trace s!"replacing at {e}"
    match e with
    | .const n₀ ls₀ => do
      let n₁ := findPrefixTranslation env n₀ t
      let ls₁ : List Level := if 0 ∈ (reorderFn n₀).flatten then ls₀.swapFirstTwo else ls₀
      if trace then
        if n₀ != n₁ then
          dbg_trace s!"changing {n₀} to {n₁}"
        if 0 ∈ (reorderFn n₀).flatten then
          dbg_trace s!"reordering the universe variables from {ls₀} to {ls₁}"
      return some <| .const n₁ ls₁
    | .app g x => do
      let mut gf := g.getAppFn
      if gf.isBVar && x.isLit then
        if trace then
          dbg_trace s!"applyReplacementFun: Variables applied to numerals are not changed {g.app x}"
        return some <| g.app x
      let mut gAllArgs := e.getAppArgs
      let some nm := gf.constName? | return mkAppN (← r gf) (← gAllArgs.mapM r)
      -- e = `(nm y₁ .. yₙ x)
      /- Test if the head should not be replaced. -/
      let relevantArgId := relevantArg nm
      if h : relevantArgId < gAllArgs.size then
        if let some fxd := shouldTranslate env t gAllArgs[relevantArgId] dontTranslate then
          if trace then
            match fxd with
            | .inl fxd => dbg_trace s!"The application of {nm} contains the fixed type \
              {fxd}, so it is not changed."
            | .inr _ => dbg_trace s!"The application of {nm} contains a fixed \
              variable so it is not changed."
        else
          gf ← r gf
          /- Test if arguments should be reordered. -/
          let reorder := reorderFn nm
          if !reorder.isEmpty then
            gAllArgs := gAllArgs.permute! reorder
            if trace then
              dbg_trace s!"reordering the arguments of {nm} using the cyclic permutations {reorder}"
      else
        gf ← r gf
      /- Do not replace numerals in specific types. -/
      if let some changedArgNrs := changeNumeralAttr.find? env nm then
        let firstArg := gAllArgs[0]!
        if shouldTranslate env t firstArg dontTranslate |>.isNone then
          if trace then
            dbg_trace s!"applyReplacementFun: We change the numerals in this expression. \
              However, we will still recurse into all the non-numeral arguments."
          -- In this case, we still update all arguments of `g` that are not numerals,
          -- since all other arguments can contain subexpressions like
          -- `(fun x ↦ ℕ) (1 : G)`, and we have to update the `(1 : G)` to `(0 : G)`
          gAllArgs := gAllArgs.mapIdx fun argNr arg ↦
            if changedArgNrs.contains argNr then
              changeNumeral arg
            else
              arg
      return mkAppN gf (← gAllArgs.mapM r)
    | .proj n₀ idx e => do
      let n₁ := findPrefixTranslation env n₀ t
      if trace then
        dbg_trace s!"applyReplacementFun: in projection {e}.{idx} of type {n₀}, \
          replace type with {n₁}"
      return some <| .proj n₁ idx <| ← r e
    | _ => return none

/-- Rename binder names in pi type. -/
def renameBinderNames (t : TranslateData) (src : Expr) : Expr :=
  src.mapForallBinderNames fun
    | .str p s => .str p (GuessName.guessName t.guessNameData s)
    | n => n

/-- Reorder pi-binders. See doc of `reorderAttr` for the interpretation of the argument -/
def reorderForall (reorder : List (List Nat)) (src : Expr) : MetaM Expr := do
  if let some maxReorder := reorder.flatten.max? then
    forallBoundedTelescope src (some (maxReorder + 1)) fun xs e => do
      if xs.size = maxReorder + 1 then
        mkForallFVars (xs.permute! reorder) e
      else
        throwError "the permutation\n{reorder}\nprovided by the `(reorder := ...)` option is \
          out of bounds, the type{indentExpr src}\nhas only {xs.size} arguments"
  else
    return src

/-- Reorder lambda-binders. See doc of `reorderAttr` for the interpretation of the argument -/
def reorderLambda (reorder : List (List Nat)) (src : Expr) : MetaM Expr := do
  if let some maxReorder := reorder.flatten.max? then
    let maxReorder := maxReorder + 1
    lambdaBoundedTelescope src maxReorder fun xs e => do
      if xs.size = maxReorder then
        mkLambdaFVars (xs.permute! reorder) e
      else
        -- we don't have to consider the case where the given permutation is out of bounds,
        -- since `reorderForall` applied to the type would already have failed in that case.
        forallBoundedTelescope (← inferType e) (maxReorder - xs.size) fun ys _ => do
          mkLambdaFVars ((xs ++ ys).permute! reorder) (mkAppN e ys)
  else
    return src

/-- Run `applyReplacementFun` on an expression `∀ x₁ .. xₙ, e`,
making sure not to translate type-classes on `xᵢ` if `i` is in `dontTranslate`. -/
def applyReplacementForall (t : TranslateData) (dontTranslate : List Nat) (e : Expr) :
    MetaM Expr := do
  if let some maxDont := dontTranslate.max? then
    forallBoundedTelescope e (some (maxDont + 1)) fun xs e => do
      let xs := xs.map (·.fvarId!)
      let dontTranslate := dontTranslate.filterMap (xs[·]?) |>.toArray
      let mut e ← applyReplacementFun t e dontTranslate
      for x in xs.reverse do
        let decl ← x.getDecl
        let xType ← applyReplacementFun t decl.type dontTranslate
        e := .forallE decl.userName xType (e.abstract #[.fvar x]) decl.binderInfo
      return e
  else
    applyReplacementFun t e #[]

/-- Run `applyReplacementFun` on an expression `fun x₁ .. xₙ ↦ e`,
making sure not to translate type-classes on `xᵢ` if `i` is in `dontTranslate`. -/
def applyReplacementLambda (t : TranslateData) (dontTranslate : List Nat) (e : Expr) :
    MetaM Expr := do
  if let some maxDont := dontTranslate.max? then
    lambdaBoundedTelescope e (maxDont + 1) fun xs e => do
      let xs := xs.map (·.fvarId!)
      let dontTranslate := dontTranslate.filterMap (xs[·]?) |>.toArray
      let mut e ← applyReplacementFun t e dontTranslate
      for x in xs.reverse do
        let decl ← x.getDecl
        let xType ← applyReplacementFun t decl.type dontTranslate
        e := .lam decl.userName xType (e.abstract #[.fvar x]) decl.binderInfo
      return e
  else
    applyReplacementFun t e #[]

/-- Unfold auxlemmas in the type and value. -/
def declUnfoldAuxLemmas (decl : ConstantInfo) : MetaM ConstantInfo := do
  let mut decl := decl
  decl := decl.updateType <| ← unfoldAuxLemmas decl.type
  if let some v := decl.value? then
    trace[translate] "value before unfold:{indentExpr v}"
    decl := decl.updateValue <| ← unfoldAuxLemmas v
    trace[translate] "value after unfold:{indentExpr decl.value!}"
  else if let .opaqueInfo info := decl then -- not covered by `value?`
    decl := .opaqueInfo { info with value := ← unfoldAuxLemmas info.value }
  return decl

/--
Given a list of variable local identifiers that shouldn't be translated,
determine the arguments that shouldn't be translated.

TODO: Currently, this function doesn't deduce any `dont_translate` types from `type`.
In the future we would like that the presence of `MonoidAlgebra k G` will automatically
flag `k` as a type to not be translated.
-/
def getDontTranslates (given : List Ident) (type : Expr) : MetaM (List Nat) := do
  forallTelescope type fun xs _ => do
    given.mapM fun id => withRef id.raw <| do
      let fvarId ← getFVarFromUserName id.getId
      return (xs.idxOf? fvarId).get!

/-- Run applyReplacementFun on the given `srcDecl` to make a new declaration with name `tgt` -/
def updateDecl (t : TranslateData) (tgt : Name) (srcDecl : ConstantInfo)
    (reorder : List (List Nat)) (dont : List Ident) : MetaM ConstantInfo := do
  let mut decl := srcDecl.updateName tgt
  if 0 ∈ reorder.flatten then
    decl := decl.updateLevelParams decl.levelParams.swapFirstTwo
  let dont ← getDontTranslates dont srcDecl.type
  decl := decl.updateType <| ← reorderForall reorder <| ← applyReplacementForall t dont <|
    renameBinderNames t decl.type
  if let some v := decl.value? then
    decl := decl.updateValue <| ← reorderLambda reorder <| ← applyReplacementLambda t dont v
  else if let .opaqueInfo info := decl then -- not covered by `value?`
    decl := .opaqueInfo { info with
      value := ← reorderLambda reorder <| ← applyReplacementLambda t dont info.value }
  return decl

/-- Abstracts the nested proofs in the value of `decl` if it is a def. -/
def declAbstractNestedProofs (decl : ConstantInfo) : MetaM ConstantInfo := do
  if decl matches .defnInfo _ then
    return decl.updateValue <| ← withDeclNameForAuxNaming decl.name do
      Meta.abstractNestedProofs decl.value!
  else
    return decl

/-- Find the target name of `pre` and all created auxiliary declarations. -/
def findTargetName (env : Environment) (t : TranslateData) (src pre tgt_pre : Name) : CoreM Name :=
  /- This covers auxiliary declarations like `match_i` and `proof_i`. -/
  if let some post := pre.isPrefixOf? src then
    return tgt_pre ++ post
  /- This covers equation lemmas (for other declarations). -/
  else if let some post := privateToUserName? src then
    match findTranslation? env t post.getPrefix with
    -- this is an equation lemma for a declaration without a translation. We will skip this.
    | none => return src
    -- this is an equation lemma for a declaration with a translation. We will translate this.
    -- Note: if this errors we could do this instead by calling `getEqnsFor?`
    | some addName => return src.updatePrefix <| mkPrivateName env addName
  else if src.hasMacroScopes then
    mkFreshUserName src.eraseMacroScopes
  else
    throwError "internal @[{t.attrName}] error."

/-- Returns a `NameSet` of all auxiliary constants in `e` that might have been generated
when adding `pre` to the environment.
Examples include `pre.match_5` and
`_private.Mathlib.MyFile.someOtherNamespace.someOtherDeclaration._eq_2`.
The last two examples may or may not have been generated by this declaration.
The last example may or may not be the equation lemma of a declaration with a translation attribute.
We will only translate it if it has a translation attribute.

Note that this function would return `proof_nnn` aux lemmas if
we hadn't unfolded them in `declUnfoldAuxLemmas`.
-/
def findAuxDecls (e : Expr) (pre : Name) : NameSet :=
  e.foldConsts ∅ fun n l ↦
    if n.getPrefix == pre || isPrivateName n || n.hasMacroScopes then
      l.insert n
    else
      l

/-- Transform the declaration `src` and all declarations `pre._proof_i` occurring in `src`
using the transforms dictionary.

`replace_all`, `trace`, `ignore` and `reorder` are configuration options.

`pre` is the declaration that got the translation attribute and `tgt_pre` is the target of this
declaration. -/
partial def transformDeclAux (t : TranslateData) (cfg : Config) (pre tgt_pre : Name) :
    Name → CoreM Unit := fun src ↦ do
  let env ← getEnv
  trace[translate_detail] "visiting {src}"
  -- if we have already translated this declaration, we do nothing.
  if (findTranslation? env t src).isSome && src != pre then
      return
  -- if this declaration is not `pre` and not an internal declaration, we return an error,
  -- since we should have already translated this declaration.
  if src != pre && !src.isInternalDetail then
    throwError "The declaration {pre} depends on the declaration {src} which is in the namespace \
      {pre}, but does not have the `@[{t.attrName}]` attribute. This is not supported.\n\
      Workaround: move {src} to a different namespace."
  -- we find, or guess, the translated name of `src`
  let tgt ← findTargetName env t src pre tgt_pre
  -- we skip if we already transformed this declaration before.
  if env.contains tgt then
    if tgt == src then
      -- Note: this can happen for equation lemmas of declarations without a translation.
      trace[translate_detail] "Auxiliary declaration {src} will be translated to itself."
    else
      trace[translate_detail] "Already visited {tgt} as translation of {src}."
    return
  let srcDecl ← getConstInfo src
  -- we first unfold all auxlemmas, since they are not always able to be translated on their own
  let srcDecl ← MetaM.run' do declUnfoldAuxLemmas srcDecl
  -- we then transform all auxiliary declarations generated when elaborating `pre`
  for n in findAuxDecls srcDecl.type pre do
    transformDeclAux t cfg pre tgt_pre n
  if let some value := srcDecl.value? then
    for n in findAuxDecls value pre do
      transformDeclAux t cfg pre tgt_pre n
  if let .opaqueInfo {value, ..} := srcDecl then
    for n in findAuxDecls value pre do
      transformDeclAux t cfg pre tgt_pre n
  -- if the auxiliary declaration doesn't have prefix `pre`, then we have to add this declaration
  -- to the translation dictionary, since otherwise we cannot translate the name.
  if !pre.isPrefixOf src then
    insertTranslation t src tgt
  -- now transform the source declaration
  let trgDecl : ConstantInfo ← MetaM.run' <|
    if src == pre then
      updateDecl t tgt srcDecl cfg.reorder cfg.dontTranslate
    else
      updateDecl t tgt srcDecl [] []
  let value ← match trgDecl with
    | .thmInfo { value, .. } | .defnInfo { value, .. } | .opaqueInfo { value, .. } => pure value
    | _ => throwError "Expected {tgt} to have a value."
  trace[translate] "generating\n{tgt} : {trgDecl.type} :=\n  {value}"
  try
    -- make sure that the type is correct,
    -- and emit a more helpful error message if it fails
    MetaM.run' <| check value
  catch
    | Exception.error _ msg => throwError "@[{t.attrName}] failed. \
      The translated value is not type correct. For help, see the docstring \
      of `to_additive`, section `Troubleshooting`. \
      Failed to add declaration\n{tgt}:\n{msg}"
    | _ => panic! "unreachable"
  -- "Refold" all the aux lemmas that we unfolded.
  let trgDecl ← MetaM.run' <| declAbstractNestedProofs trgDecl
  /- If `src` is explicitly marked as `noncomputable`, then add the new decl as a declaration but
  do not compile it, and mark is as noncomputable. Otherwise, only log errors in compiling if `src`
  has executable code.

  Note that `noncomputable section` does not explicitly mark noncomputable definitions as
  `noncomputable`, but simply abstains from logging compilation errors.

  This is not a perfect solution, as ideally we *should* complain when `src` should
  produce executable code but fails to do so (e.g. outside of `noncomputable section`). However,
  the `messages` and `infoState` are reset before this runs, so we cannot check for compilation
  errors on `src`. The scope set by `noncomputable` section lives in the `CommandElabM` state
  (which is inaccessible here), so we cannot test for `noncomputable section` directly. See [Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/to_additive.20and.20noncomputable/with/310541981). -/
  if isNoncomputable env src then
    addDecl trgDecl.toDeclaration!
    setEnv <| addNoncomputable (← getEnv) tgt
  else
    addAndCompile trgDecl.toDeclaration! (logCompileErrors := (IR.findEnvDecl env src).isSome)
  if let .defnDecl { hints := .abbrev, .. } := trgDecl.toDeclaration! then
    if (← getReducibilityStatus src) == .reducible then
      setReducibilityStatus tgt .reducible
    if Compiler.getInlineAttribute? (← getEnv) src == some .inline then
      MetaM.run' <| Meta.setInlineAttribute tgt
  -- now add declaration ranges so jump-to-definition works
  -- note: we currently also do this for auxiliary declarations, while they are not normally
  -- generated for those. We could change that.
  addDeclarationRangesFromSyntax tgt (← getRef) cfg.ref
  if isProtected (← getEnv) src then
    setEnv <| addProtected (← getEnv) tgt
  if defeqAttr.hasTag (← getEnv) src then
    defeqAttr.setTag tgt
  if let some matcherInfo ← getMatcherInfo? src then
    /-
    Use `Match.addMatcherInfo tgt matcherInfo`
    once https://github.com/leanprover/lean4/pull/5068 is in
    -/
    modifyEnv fun env => Match.Extension.addMatcherInfo env tgt matcherInfo
  -- necessary so that e.g. match equations can be generated for `tgt`
  enableRealizationsForConst tgt

/-- Copy the instance attribute in a `to_additive`

[todo] it seems not to work when the `to_additive` is added as an attribute later. -/
def copyInstanceAttribute (src tgt : Name) : CoreM Unit := do
  if let some prio ← getInstancePriority? src then
    let attr_kind := (← getInstanceAttrKind? src).getD .global
    trace[translate_detail] "Making {tgt} an instance with priority {prio}."
    addInstance tgt attr_kind prio |>.run'

/-- Warn the user when the declaration has an attribute. -/
def warnAttrCore (stx : Syntax) (f : Environment → Name → Bool)
    (thisAttr attrName src tgt : Name) : CoreM Unit := do
  if f (← getEnv) src then
    Linter.logLintIf linter.existingAttributeWarning stx <|
      m!"The source declaration {src} was given attribute {attrName} before calling @[{thisAttr}]. \
         The preferred method is to use `@[{thisAttr} (attr := {attrName})]` to apply the \
         attribute to both {src} and the target declaration {tgt}." ++
      if thisAttr == `to_additive then
        m!"\nSpecial case: If this declaration was generated by @[to_additive] \
          itself, you can use @[to_additive (attr := to_additive, {attrName})] on the original \
          declaration."
      else ""

/-- Warn the user when the declaration has a simple scoped attribute. -/
def warnAttr {α β : Type} [Inhabited β] (stx : Syntax) (attr : SimpleScopedEnvExtension α β)
    (f : β → Name → Bool) (thisAttr attrName src tgt : Name) : CoreM Unit :=
  warnAttrCore stx (f <| attr.getState ·) thisAttr attrName src tgt

/-- Warn the user when the declaration has a parametric attribute. -/
def warnParametricAttr {β : Type} [Inhabited β] (stx : Syntax) (attr : ParametricAttribute β)
    (thisAttr attrName src tgt : Name) : CoreM Unit :=
  warnAttrCore stx (attr.getParam? · · |>.isSome) thisAttr attrName src tgt

/-- `translateLemmas names argInfo desc t` runs `t` on all elements of `names`
and adds translations between the generated lemmas (the output of `t`).
`names` must be non-empty. -/
def translateLemmas {m : Type → Type} [Monad m] [MonadError m] [MonadLiftT CoreM m]
    (t : TranslateData) (names : Array Name) (argInfo : ArgInfo) (desc : String)
    (runAttr : Name → m (Array Name)) : m Unit := do
  let auxLemmas ← names.mapM runAttr
  let nLemmas := auxLemmas[0]!.size
  for (nm, lemmas) in names.zip auxLemmas do
    unless lemmas.size == nLemmas do
      throwError "{names[0]!} and {nm} do not generate the same number of {desc}."
  for (srcLemmas, tgtLemmas) in auxLemmas.zip <| auxLemmas.eraseIdx! 0 do
    for (srcLemma, tgtLemma) in srcLemmas.zip tgtLemmas do
      insertTranslationAndInfo t srcLemma tgtLemma argInfo

/--
Find the argument of `nm` that appears in the first translatable (type-class) argument.
Returns 1 if there are no types with a translatable class as arguments.
E.g. `Prod.instGroup` returns 1, and `Pi.instOne` returns 2.
Note: we only consider the relevant argument (`(relevant_arg := ...)`) of each type-class.
E.g. `[Pow A N]` is a translatable type-class on `A`, not on `N`.
-/
def findRelevantArg (t : TranslateData) (nm : Name) : MetaM Nat := do
  forallTelescopeReducing (← getConstInfo nm).type fun xs ty ↦ do
    let env ← getEnv
    -- check if `tgt` has a translatable type argument, and if so,
    -- find the index of a type from `xs` appearing in there
    let relevantArg? (tgt : Expr) : Option Nat := do
      let c ← tgt.getAppFn.constName?
      guard (findTranslation? env t c).isSome
      let relevantArg := (t.relevantArgAttr.find? env c).getD 0
      let arg ← tgt.getArg? relevantArg
      xs.findIdx? (arg.containsFVar ·.fvarId!)
    -- run the above check on all hypotheses and on the conclusion
    let arg ← OptionT.run <| xs.firstM fun x ↦ OptionT.mk do
        forallTelescope (← inferType x) fun _ys tgt ↦ return relevantArg? tgt
    let arg := arg <|> relevantArg? ty
    trace[translate_detail] "findRelevantArg: {arg}"
    return arg.getD 0

/-- Return the provided target name or autogenerate one if one was not provided. -/
def targetName (t : TranslateData) (cfg : Config) (src : Name) : CoreM Name := do
  if cfg.self then
    if cfg.tgt != .anonymous then
      logWarning m!"`{t.attrName} self` ignores the provided name {cfg.tgt}"
    return src
  let .str pre s := src | throwError "{t.attrName}: can't transport {src}"
  trace[translate_detail] "The name {s} splits as {open GuessName in s.splitCase}"
  let tgt_auto := GuessName.guessName t.guessNameData s
  let depth := cfg.tgt.getNumParts
  let pre := findPrefixTranslation (← getEnv) pre t
  let (pre1, pre2) := pre.splitAt (depth - 1)
  let res := if cfg.tgt == .anonymous then pre.str tgt_auto else pre1 ++ cfg.tgt
  if res == src then
    throwError "{t.attrName}: the generated translated name equals the original name '{src}'.\n\
    If this is intentional, use the `@[{t.attrName} self]` syntax.\n\
    Otherwise, check that your declaration name is correct \
    (if your declaration is an instance, try naming it)\n\
    or provide a translated name using the `@[{t.attrName} my_add_name]` syntax."
  if cfg.tgt == pre2.str tgt_auto && !cfg.allowAutoName then
    Linter.logLintIf linter.translateGenerateName cfg.ref m!"\
      `{t.attrName}` correctly autogenerated target name for {src}.\n\
      You may remove the explicit argument {cfg.tgt}."
  if cfg.tgt != .anonymous then
    trace[translate_detail] "The automatically generated name would be {pre.str tgt_auto}"
  return res

/-- if `f src = #[a_1, ..., a_n]` and `f tgt = #[b_1, ... b_n]` then `proceedFieldsAux src tgt f`
will insert translations from `a_i` to `b_i`. -/
def proceedFieldsAux (t : TranslateData) (src tgt : Name) (argInfo : ArgInfo)
    (f : Name → Array Name) : CoreM Unit := do
  let srcFields := f src
  let tgtFields := f tgt
  if srcFields.size != tgtFields.size then
    throwError "Failed to map fields of {src}, {tgt} with {srcFields} ↦ {tgtFields}.\n \
      Lengths do not match."
  for srcField in srcFields, tgtField in tgtFields do
    insertTranslationAndInfo t srcField tgtField argInfo

/-- Add the structure fields of `src` to the translations dictionary
so that they will be translated correctly. -/
def proceedFields (t : TranslateData) (src tgt : Name) (argInfo : ArgInfo) : CoreM Unit := do
  let env ← getEnv
  let aux := proceedFieldsAux t src tgt argInfo
  -- add translations for the structure fields
  aux fun declName ↦
    if isStructure env declName then
      let info := getStructureInfo env declName
      Array.ofFn (n := info.fieldNames.size) (info.getProjFn? · |>.get!)
    else
      #[]
  -- add translations for the automatically generated instances with `extend`.
  aux fun declName ↦
    if isStructure env declName then
      getStructureInfo env declName |>.parentInfo
        |>.filterMap fun c ↦ if !c.subobject then c.projFn else none
    else
      #[]
  -- add translations for the constructors of an inductive type
  aux fun declName ↦ match env.find? declName with
    | some (ConstantInfo.inductInfo { ctors, .. }) => ctors.toArray
    | _ => #[]

/-- Elaboration of the configuration options for a translation attribute. It is assumed that
- `stx[0]` is the attribute (e.g. `to_additive`)
- `stx[1]` is the optional tracing `?`
- `stx[2]` is the remaining `attrArgs` -/
def elabTranslationAttr (stx : Syntax) : CoreM Config :=
  match stx[2] with
  | `(attrArgs| $existing? $[$opts:bracketedOption]* $[$tgt]? $[$doc]?) => do
    let mut attrs := #[]
    let mut reorder := []
    let mut relevantArg? := none
    let mut dontTranslate := []
    for opt in opts do
      match opt with
      | `(bracketedOption| (attr := $[$stxs],*)) =>
        attrs := attrs ++ stxs
      | `(bracketedOption| (reorder := $[$[$reorders:num]*],*)) =>
        for cycle in reorders do
          if h : cycle.size = 1 then
            throwErrorAt cycle[0] "\
              invalid cycle `{cycle[0]}`, a cycle must have at least 2 elements.\n\
              `(reorder := ...)` uses cycle notation to specify a permutation.\n\
              For example `(reorder := 1 2, 5 6)` swaps the first two arguments with each other \
              and the fifth and the sixth argument and `(reorder := 3 4 5)` will move \
              the fifth argument before the third argument."
          let cycle ← cycle.toList.mapM fun n => match n.getNat with
            | 0 => throwErrorAt n "invalid position `{n}`, positions are counted starting from 1."
            | n+1 => pure n
          reorder := cycle :: reorder
      | `(bracketedOption| (relevant_arg := $n)) =>
        if let some arg := relevantArg? then
          throwErrorAt opt "cannot specify `relevant_arg` multiple times"
        else
          relevantArg? := n.getNat.pred
      | `(bracketedOption| (dont_translate := $[$types:ident]*)) =>
        dontTranslate := dontTranslate ++ types.toList
      | _ => throwUnsupportedSyntax
    let (existing, self) := match existing? with
      | `(existingNameHint| existing) => (true, false)
      | `(existingNameHint| self) => (true, true)
      | _ => (false, false)
    if self && !attrs.isEmpty then
      throwError "invalid `(attr := ...)` after `self`, \
        as there is only one declaration for the attributes.\n\
        Instead, you can write the attributes in the usual way."
    trace[translate_detail] "attributes: {attrs}; reorder arguments: {reorder}"
    let doc ← doc.mapM fun
      | `(str|$doc:str) => open Linter in do
        -- Deprecate `str` docstring syntax (since := "2025-08-12")
        if getLinterValue linter.deprecated (← getLinterOptions) then
          let hintSuggestion := {
            diffGranularity := .none
            toTryThisSuggestion := { suggestion := "/-- " ++ doc.getString.trim ++ " -/" }
          }
          let sugg ← Hint.mkSuggestionsMessage #[hintSuggestion] doc
            (codeActionPrefix? := "Update to: ") (forceList := false)
          logWarningAt doc <| .tagged ``Linter.deprecatedAttr
            m!"String syntax for `to_additive` docstrings is deprecated: Use \
              docstring syntax instead (e.g. `@[to_additive /-- example -/]`)\n\
              \n\
              Update deprecated syntax to:{sugg}"
        return doc.getString
      | `(docComment|$doc:docComment) => do
        -- TODO: rely on `addDocString`s call to `validateDocComment` after removing `str` support
        /-
        #adaptation_note
        Without understanding the consequences, I am commenting out the next line,
        as `validateDocComment` is now in `TermElabM` which is not trivial to reach from here.
        Perhaps the existing comments here suggest it is no longer needed, anyway?
        -/
        -- validateDocComment doc
        /- Note: the following replicates the behavior of `addDocString`. However, this means that
        trailing whitespace might appear in docstrings added via `docComment` syntax when compared
        to those added via `str` syntax. See this [Zulip thread](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Why.20do.20docstrings.20include.20trailing.20whitespace.3F/with/533553356). -/
        return (← getDocStringText doc).removeLeadingSpaces
      | _ => throwUnsupportedSyntax
    return {
      trace := !stx[1].isNone
      tgt := match tgt with | some tgt => tgt.getId | none => Name.anonymous
      doc, attrs, reorder, relevantArg?, dontTranslate, existing, self
      ref := match tgt with | some tgt => tgt.raw | none => stx[0] }
  | _ => throwUnsupportedSyntax

mutual
/-- Apply attributes to the original and translated declarations. -/
partial def applyAttributes (t : TranslateData) (stx : Syntax) (rawAttrs : Array Syntax)
    (src tgt : Name) (argInfo : ArgInfo) : TermElabM (Array Name) := do
  -- we only copy the `instance` attribute, since it is nice to directly tag `instance` declarations
  copyInstanceAttribute src tgt
  -- Warn users if the original declaration has an attributee
  if src != tgt && linter.existingAttributeWarning.get (← getOptions) then
    let appliedAttrs ← getAllSimpAttrs src
    if appliedAttrs.size > 0 then
      let appliedAttrs := ", ".intercalate (appliedAttrs.toList.map toString)
      -- Note: we're not bothering to print the correct attribute arguments.
      Linter.logLintIf linter.existingAttributeWarning stx m!"\
        The source declaration {src} was given the simp-attribute(s) {appliedAttrs} before \
        calling @[{t.attrName}].\nThe preferred method is to use something like \
        `@[{t.attrName} (attr := {appliedAttrs})]`\nto apply the attribute to both \
        {src} and the target declaration {tgt}."
    warnAttr stx Lean.Meta.Ext.extExtension
      (fun b n => (b.tree.values.any fun t => t.declName = n)) t.attrName `ext src tgt
    warnAttr stx Lean.Meta.Rfl.reflExt (·.values.contains ·) t.attrName `refl src tgt
    warnAttr stx Lean.Meta.Symm.symmExt (·.values.contains ·) t.attrName `symm src tgt
    warnAttr stx Batteries.Tactic.transExt (·.values.contains ·) t.attrName `trans src tgt
    warnAttr stx Lean.Meta.coeExt (·.contains ·) t.attrName `coe src tgt
    warnParametricAttr stx Lean.Linter.deprecatedAttr t.attrName `deprecated src tgt
    -- the next line also warns for `@[to_additive, simps]`, because of the application times
    warnParametricAttr stx simpsAttr t.attrName `simps src tgt
    warnAttrCore stx Term.elabAsElim.hasTag t.attrName `elab_as_elim src tgt
  -- add attributes
  -- the following is similar to `Term.ApplyAttributesCore`, but we hijack the implementation of
  -- `simps` and `to_additive`.
  let attrs ← elabAttrs rawAttrs
  let (additiveAttrs, attrs) := attrs.partition (·.name == t.attrName)
  let nestedDecls ←
    match h : additiveAttrs.size with
    | 0 => pure #[]
    | 1 =>
      let cfg ← elabTranslationAttr additiveAttrs[0].stx
      addTranslationAttr t tgt cfg additiveAttrs[0].kind
    | _ => throwError "cannot apply {t.attrName} multiple times."
  let allDecls := #[src, tgt] ++ nestedDecls
  if attrs.size > 0 then
    trace[translate_detail] "Applying attributes {attrs.map (·.stx)} to {allDecls}"
  for attr in attrs do
    withRef attr.stx do withLogging do
    if attr.name == `simps then
      translateLemmas t allDecls argInfo "simps lemmas" (simpsTacFromSyntax · attr.stx)
      return
    let env ← getEnv
    match getAttributeImpl env attr.name with
    | Except.error errMsg => throwError errMsg
    | Except.ok attrImpl =>
      let runAttr := do
        for decl in allDecls do
          attrImpl.add decl attr.stx attr.kind
      -- not truly an elaborator, but a sensible target for go-to-definition
      let elaborator := attrImpl.ref
      if (← getInfoState).enabled && (← getEnv).contains elaborator then
        withInfoContext (mkInfo := return .ofCommandInfo { elaborator, stx := attr.stx }) do
          try runAttr
          finally if attr.stx[0].isIdent || attr.stx[0].isAtom then
            -- Add an additional node over the leading identifier if there is one
            -- to make it look more function-like.
            -- Do this last because we want user-created infos to take precedence
            pushInfoLeaf <| .ofCommandInfo { elaborator, stx := attr.stx[0] }
      else
        runAttr
  return nestedDecls

/--
Copies equation lemmas and attributes from `src` to `tgt`
-/
partial def copyMetaData (t : TranslateData) (cfg : Config) (src tgt : Name) (argInfo : ArgInfo) :
    CoreM (Array Name) := do
  if let some eqns := eqnsAttribute.find? (← getEnv) src then
    unless (eqnsAttribute.find? (← getEnv) tgt).isSome do
      for eqn in eqns do
        _ ← addTranslationAttr t eqn cfg
      eqnsAttribute.add tgt (eqns.map (findTranslation? (← getEnv) t · |>.get!))
  else
    /- We need to generate all equation lemmas for `src` and `tgt`, even for non-recursive
    definitions. If we don't do that, the equation lemma for `src` might be generated later
    when doing a `rw`, but it won't be generated for `tgt`. -/
    translateLemmas t #[src, tgt] argInfo "equation lemmas" fun nm ↦
      (·.getD #[]) <$> MetaM.run' (getEqnsFor? nm)
  MetaM.run' <| Elab.Term.TermElabM.run' <|
    (applyAttributes t cfg.ref cfg.attrs src tgt) argInfo

/--
Make a new copy of a declaration, replacing fragments of the names of identifiers in the type and
the body using the `translations` dictionary.
-/
partial def transformDecl (t : TranslateData) (cfg : Config) (src tgt : Name)
    (argInfo : ArgInfo := {}) : CoreM (Array Name) := do
  transformDeclAux t cfg src tgt src
  copyMetaData t cfg src tgt argInfo

/-- Verify that the type of given `srcDecl` translates to that of `tgtDecl`. -/
partial def checkExistingType (t : TranslateData) (src tgt : Name) (reorder : List (List Nat))
    (dont : List Ident) : MetaM Unit := do
  let mut srcDecl ← getConstInfo src
  let tgtDecl ← getConstInfo tgt
  if 0 ∈ reorder.flatten then
    srcDecl := srcDecl.updateLevelParams srcDecl.levelParams.swapFirstTwo
  unless srcDecl.levelParams.length == tgtDecl.levelParams.length do
    throwError "`{t.attrName}` validation failed:\n  expected {srcDecl.levelParams.length} \
      universe levels, but '{tgt}' has {tgtDecl.levelParams.length} universe levels"
  -- instantiate both types with the same universes. `instantiateLevelParams` applies some
  -- normalization, so we have to apply it to both types.
  let type := srcDecl.type.instantiateLevelParams
    srcDecl.levelParams (tgtDecl.levelParams.map mkLevelParam)
  let tgtType := tgtDecl.type.instantiateLevelParams
    tgtDecl.levelParams (tgtDecl.levelParams.map mkLevelParam)
  let dont ← getDontTranslates dont type
  let type  ← reorderForall reorder <| ← applyReplacementForall t dont <| ← unfoldAuxLemmas type
  -- `instantiateLevelParams` normalizes universes, so we have to normalize both expressions
  unless ← withReducible <| isDefEq type tgtType do
    throwError "`{t.attrName}` validation failed: expected{indentExpr type}\nbut '{tgt}' has \
      type{indentExpr tgtType}"

/-- `addTranslationAttr src cfg` adds a translation attribute to `src` with configuration `cfg`.
See the attribute implementation for more details.
It returns an array with names of translated declarations (usually 1, but more if there are nested
`to_additive` calls). -/
partial def addTranslationAttr (t : TranslateData) (src : Name) (cfg : Config)
    (kind := AttributeKind.global) : AttrM (Array Name) := do
  if (kind != AttributeKind.global) then
    throwError "`{t.attrName}` can only be used as a global attribute"
  withOptions (· |>.updateBool `trace.translate (cfg.trace || ·)) <| do
  if let some tgt := findTranslation? (← getEnv) t src then
    -- we allow `(reorder := ...)` or `(relevant_arg := ...)` syntax
    -- for updating this information on constants that are already tagged
    -- for example, this is necessary for `HPow.hPow`
    if cfg.reorder != [] then
      modifyEnv (t.reorderAttr.addEntry · (src, cfg.reorder))
      return #[tgt]
    if let some relevantArg := cfg.relevantArg? then
      modifyEnv (t.relevantArgAttr.addEntry · (src, relevantArg))
      return #[tgt]
  let tgt ← targetName t cfg src
  let alreadyExists := (← getEnv).contains tgt
  if cfg.existing != alreadyExists && !(← isInductive src) && !cfg.self then
    Linter.logLintIf linter.translateExisting cfg.ref <|
      if alreadyExists then
        m!"The translated declaration already exists. Please specify this explicitly using \
           `@[{t.attrName} existing]`."
      else
        "The translated declaration doesn't exist. Please remove the option `existing`."
  if alreadyExists then
    MetaM.run' <| checkExistingType t src tgt cfg.reorder cfg.dontTranslate
  let relevantArg ← cfg.relevantArg?.getDM <| MetaM.run' <| findRelevantArg t src
  let argInfo := { reorder := cfg.reorder, relevantArg }
  insertTranslationAndInfo t src tgt argInfo alreadyExists
  let nestedNames ←
    if alreadyExists then
      -- since `tgt` already exists, we just need to copy metadata and
      -- add translations `src.x ↦ tgt.x'` for any subfields.
      trace[translate_detail] "declaration {tgt} already exists."
      proceedFields t src tgt argInfo
      copyMetaData t cfg src tgt argInfo
    else
      -- tgt doesn't exist, so let's make it
      transformDecl t cfg src tgt argInfo
  -- add pop-up information when mousing over the given translated name
  -- (the information will be over the attribute if no translated name is given)
  pushInfoLeaf <| .ofTermInfo {
    elaborator := .anonymous, lctx := {}, expectedType? := none, isBinder := !alreadyExists,
    stx := cfg.ref, expr := ← mkConstWithLevelParams tgt }
  if let some doc := cfg.doc then
    addDocStringCore tgt doc
  return nestedNames.push tgt

end

end Mathlib.Tactic.Translate
