/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn, Jon Eugster, Bryan Gin-ge Chen,
Jovan Gerbscheid
-/
module

public meta import Lean.Compiler.NoncomputableAttr
public meta import Lean.Elab.Tactic.Ext
public meta import Lean.Meta.Tactic.Rfl
public meta import Lean.Meta.Tactic.Symm
public meta import Mathlib.Lean.Meta.Simp
public meta import Mathlib.Tactic.Simps.Basic
public meta import Lean.Meta.CoeAttr
public import Batteries.Lean.NameMapAttribute
public import Batteries.Tactic.Trans
public import Mathlib.Tactic.Eqns
public import Mathlib.Tactic.Simps.Basic
public import Mathlib.Tactic.Translate.GuessName
public import Mathlib.Tactic.Translate.Reorder
public import Mathlib.Tactic.Translate.UnfoldBoundary

/-!
# The translation attribute.

Implementation of the translation attribute. This is used for `@[to_additive]` and `@[to_dual]`.
See the docstring of `to_additive` for more information
-/

public meta section

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

syntax reorderOption := &"reorder" " := " translateReorder
attribute [inherit_doc reorder] reorderOption

/--
the `(relevant_arg := ...)` option tells which argument to look at to determine whether to
translate this constant. This is inferred automatically,
but it can also be overwritten using this syntax.

If there are multiple possible arguments, we typically tag the first one.
If this argument contains a fixed type, this declaration will not be translated.
See the Heuristics section of the `to_additive` doc-string for more details.

When it cannot be inferred automatically, it is presumed that the first argument is relevant.

Use `(relevant_arg := _)` to indicate that there is no relevant argument.

Implementation note: we only allow exactly 1 relevant argument, even though some declarations
(like `Prod.instGroup`) have multiple relevant arguments.
The reason is that whether we translate a declaration is an all-or-nothing decision, and
we will not be able to translate declarations that (e.g.) talk about multiplication on `ℕ × α`
anyway.
-/

syntax relevantArgOption := &"relevant_arg" " := " hole <|> ident <|> num
/--
`(dont_translate := ...)` takes a list of type variables (separated by spaces) that should not be
considered for translation. For example in
```
lemma foo {α β : Type} [Group α] [Group β] (a : α) (b : β) : a * a⁻¹ = 1 ↔ b * b⁻¹ = 1
```
we can choose to only translate `α` by writing `to_additive (dont_translate := β)`.
-/

syntax dontTranslateOption := &"dont_translate" " := " (ident <|> num)+

syntax bracketedOption := "(" attrOption <|> reorderOption <|>
  relevantArgOption <|> dontTranslateOption ")"

/-- A hint about the translated declaration

- `existing` indicates that the translated form of the declaration is a pre-existing declaration.
  This is useful when the value cannot be translated, either because of a limitation in the
  translation heuristics, or because the value/proof is genuinely different.

- `self` indicates that the declaration translates to itself, up to some reordering of arguments.
  If no arguments are reordered then the attribute is redundant, which the `translateRedundant`
  linter will warn about.

- `none` indicates that the translated declaration should not get a user-facing name,
  instead being named like an auxiliary declaration. This is particularly useful for `to_dual` when
  using the `reassoc` attribute, because the dual of a right associated term is left associated,
  but we only want user-facing lemmas with right associated terms.
-/
syntax translationHint := (ppSpace (&"existing" <|> &"self" <|> &"none"))?

syntax attrArgs :=
  translationHint (ppSpace bracketedOption)* (ppSpace ident)? (ppSpace (str <|> docComment))?

-- We omit a doc-string on these syntaxes to instead show the `to_additive` or `to_dual` doc-string
attribute [nolint docBlame] attrArgs bracketedOption

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

/-- Linter used by translate attributes that checks if the given reorder is
    equal to the automatically generated name -/
register_option linter.translateReorder : Bool := {
  defValue := true
  descr := "Linter used by translate attributes that checks if the given reorder is \
    equal to the automatically generated one" }

/-- Linter used by translate attributes that checks if the relevant_arg is
automatically generated. -/
register_option linter.translateRelevantArg : Bool := {
  defValue := true
  descr := "Linter used by translate attributes that checks if the relevant_arg is \
    automatically generated" }

/-- Linter used by translate attributes that checks if the attribute was already applied -/
register_option linter.translateOverwrite : Bool := {
  defValue := true
  descr := "Linter used by translate attributes that checks if the attribute was already applied" }

/-- Linter used by translate attributes that checks if the attribute is redundant -/
register_option linter.translateRedundant : Bool := {
  defValue := true
  descr := "Linter used by translate attributes that checks if the attribute is redundant" }

/-- `RelevantArg` represents an optional argument that should be checked to determine
whether or not to translate the given constant. -/
inductive RelevantArg where
  /-- No argument needs to be checked. This is specified with `(relevant_arg := _)`. -/
  | noArg
  /-- Argument `n` needs to be checked. This is specified with `(relevant_arg := n)`. -/
  | arg (n : Nat)
  deriving BEq, Inhabited

/-- Combine two known `RelevantArg`s by taking the smallest value of the two.
Recall that if there are multiple relevant arguments, `relevant_arg` is set to the smallest one. -/
private def RelevantArg.min : RelevantArg → RelevantArg → RelevantArg
  | .arg x, .arg y => .arg (x.min y)
  | x, .noArg => x
  | .noArg, y => y

instance : ToMessageData RelevantArg where
  toMessageData
    | .arg n => m!"{n + 1}"
    | .noArg => "_"

/-- `TranslationInfo` stores the information of how to translate a constant. -/
structure TranslationInfo where
  /-- The name that we are translating to. -/
  translation : Name
  /-- The arguments that should be reordered when translating, using disjoint cycle notation. -/
  reorder : Reorder := {}
  /-- The argument used to determine whether this constant should be translated. -/
  relevantArg : RelevantArg := .arg 0

/-- `TranslateData` is a structure that holds all data required for a translation attribute. -/
structure TranslateData : Type where
  /-- An attribute that tells that certain arguments of this definition are not
  involved when translating.
  This helps the translation heuristic by also transforming definitions if `ℕ` or another
  fixed type occurs as one of these arguments. -/
  ignoreArgsAttr : NameMapExtension (List Nat)
  /-- The global `do_translate`/`dont_translate` attributes specify whether operations on
  a given type should be translated. `dont_translate` can be used for types that are translated,
  such as `MonoidAlgebra` -> `AddMonoidAlgebra`, or for fixed types, such as `Fin n`/`ZMod n`.
  `do_translate` is for types without arguments, like `Unit` and `Empty`, where the structure on it
  can be translated.

  Note: The name generation is not aware of `dont_translate`, so if some part of a lemma is not
    translated thanks to this, you generally have to specify the translated name manually.
  -/
  doTranslateAttr : NameMapExtension Bool
  /-- The `insert_cast`/`insert_cast_fun` attributes create an abstraction boundary for the tagged
  constant when translating it. For example, `Set.Icc`, `Monotone`, `DecidableLT`, `WCovBy` are all
  morally self-dual, but their definition is not self-dual. So, in order to allow these constants
  to be self-dual, we need to not unfold their definition in the proof term that we translate. -/
  unfoldBoundaries? : Option UnfoldBoundary.UnfoldBoundaryExt := none
  /-- `translations` stores all of the constants that have been tagged with this attribute,
  and maps them to their translation. -/
  translations : NameMapExtension TranslationInfo
  /-- The name of the attribute, for example `to_additive` or `to_dual`. -/
  attrName : Name
  /-- If `changeNumeral := true`, then try to translate the number `1` to `0`. -/
  changeNumeral : Bool
  /-- When `isDual := true`, every translation `A → B` will also give a translation `B → A`. -/
  isDual : Bool
  guessNameData : GuessName.GuessNameData

attribute [inherit_doc GuessName.GuessNameData] TranslateData.guessNameData

/-- Get the translation for the given name. -/
def findTranslation? (env : Environment) (t : TranslateData) : Name → Option TranslationInfo :=
  t.translations.find? env

/-- Get the translation name for the given name. -/
def findTranslationName? (env : Environment) (t : TranslateData) (n : Name) : Option Name :=
  (findTranslation? env t n).map (·.translation)

/-- Check if the given constant exists in the environment, also checking for reserved names.
This function is based on `Lean.realizeGlobalName`. -/
private def realizeGlobalConst (c : Name) : CoreM Bool := do
  let env ← getEnv
  if env.contains c then
    return true
  unless isReservedName env c do
    return false
  try
    executeReservedNameAction c
    return (← getEnv).containsOnBranch c
  catch ex =>
    logError m!"Failed to realize constant {c}:{indentD ex.toMessageData}"
    return false

/-- Get the translation for the given name,
falling back to translating a prefix of the name if the full name can't be translated.
This allows translating automatically generated declarations such as `IsRegular.casesOn`.
We make sure that the new constant is realized. -/
def findPrefixTranslation? (n : Name) (t : TranslateData) : CoreM (Option TranslationInfo) := do
  let env ← getEnv
  if let some info := findTranslation? env t n then
    return info
  let .str n postFix := n | return none
  let some info := go env n [postFix] | return none
  unless ← realizeGlobalConst info.translation do return none
  return info
where
  /-- Loop through the prefixes of `n` to try to find a translation.
  In such a case, we inherit the `relevantArg` option from the translation. -/
  go (env : Environment) (n : Name) (postFixes : List String) : Option TranslationInfo := Id.run do
  if let some info := findTranslation? env t n then
    return some {
      translation := postFixes.foldl .str info.translation
      relevantArg := info.relevantArg }
  if isPrivateName n then
    if let some info := findTranslation? env t (privateToUserName n) then
      return some {
        translation := postFixes.foldl .str (mkPrivateName env info.translation)
        relevantArg := info.relevantArg }
  let .str n postFix := n | return none
  return go env n (postFix :: postFixes)

/-- Add a translation to the translations map. If the translation attribute is dual,
also add the reverse translation. -/
def insertTranslation (t : TranslateData) (src tgt : Name) (reorder : Reorder)
    (relevantArg : RelevantArg) (ref : Syntax) :
    CoreM Unit := do
  insertTranslationAux src t { translation := tgt, reorder, relevantArg }
  if t.isDual && src != tgt then
    /- In practice, `relevantArg` does not overlap with `reorder` for dual translations,
    so we don't bother applying the permutation to `relevantArg`. -/
    insertTranslationAux tgt t {
      translation := src, reorder := reorder.reverse, relevantArg }
where
  /-- Insert only one direction of a translation. -/
  insertTranslationAux (src : Name) (t : TranslateData) (info : TranslationInfo) : CoreM Unit := do
    if let some info' := findTranslation? (← getEnv) t src then
      -- After `insert_to_additive_translation`, we may end up adding same translation again.
      -- So in that case, don't log a warning.
      if info.translation != info'.translation then
        Linter.logLintIf linter.translateOverwrite ref m!"`{src}` was already translated to \
          `{info'.translation}` instead of `{info.translation}`.\n\
          Unless the original translation was wrong, please remove this `{t.attrName}` attribute."
    modifyEnv (t.translations.addEntry · (src, info))
    trace[translate] "Added translation {src} ↦ {tgt}\
      {if info.reorder.isEmpty then "" else s!" (reorder := {info.reorder})}"} \
      (relevant_arg := {info.relevantArg})"

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
  reorder? : Option Reorder := none
  /-- The argument used to determine whether this constant should be translated. -/
  relevantArg? : Option RelevantArg := none
  /-- The attributes which we want to give to the original and translated declaration.
  For `simps` this will also add generated lemmas to the translation dictionary. -/
  attrs : Array Syntax := #[]
  /-- A list of positions of type variables that should not be translated. -/
  dontTranslate : List Nat := []
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
  If `self := true`, we should also have `existing := true`. -/
  self : Bool := false
  /-- An optional flag for not giving the new declaration a user-facing name.
  This is achieved by appending e.g. `_to_dual_1` to the name of the original declaration. -/
  none : Bool := false

/-- Eta expands `e` exactly `n` times. -/
def etaExpandN (n : Nat) (e : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType e) (some n) fun xs _ ↦ do
    if xs.size ≠ n then
      throwError "{e} is not a function of arity at least {n}"
    mkLambdaFVars xs (mkAppN e xs)

/-- Monad used by `applyReplacementFun`.
- The reader stores the free variables on which nothing should be translated.
- The state stores the free variables on which something has been translated.
- The cache caches the results on subexpressions. -/
abbrev ReplacementM :=
  ReaderT (Array FVarId) <| MonadCacheT ExprStructEq Expr StateRefT (Std.HashSet FVarId) MetaM

/-- Run a `ReplacementM` computation, returning the result and the value of `relevant_arg` that
corresponds to this translation. -/
def ReplacementM.run {α} (dontTranslate allFVars : Array FVarId) (x : ReplacementM α) :
    MetaM (α × Option Nat) := do
  let (a, relevantFVars) ← x dontTranslate |>.run |>.run {}
  return (a, allFVars.findIdx? relevantFVars.contains)

/-- Implementation function for `shouldTranslate`.
Returning `none` means that `e` contains no constant that blocks translation.
We cache previous applications of the function, using an expression cache using ptr equality
to avoid visiting the same subexpression many times.

Note that this function is still called many times by `applyReplacementFun`
and we're not remembering the cache between these calls. -/
private unsafe def shouldTranslateUnsafe (env : Environment) (t : TranslateData) (e : Expr) :
    ReplacementM (Option Expr) := do
  let visitedFVars : IO.Ref (Array FVarId) ← IO.mkRef #[]
  let dontTranslate ← read
  let rec visit (e : Expr) : ExceptT Expr (StateT (PtrSet Expr) BaseIO) Unit := do
    if (← get).contains e then
      return
    modify fun s => s.insert e
    match e with
    | .app .. => e.withApp fun f args ↦ do
      match f with
      | .const n _ =>
        -- A constant in an application, e.g. `Prod` in `α × β`, is translated by default.
        let doTranslate := (t.doTranslateAttr.find? env n).getD true
        unless doTranslate do throw e
        let l := (t.ignoreArgsAttr.find? env n).getD []
        args.size.forM fun i _ ↦ do
          if !l.contains i then visit args[i]
      | .fvar .. => visit f -- We don't look in the arguments of free variables.
      | _ => visit f; args.forM visit
    | .const n _ =>
      -- A constant not in an application, e.g. `ℕ`, is not translated by default.
      let doTranslate := (t.doTranslateAttr.find? env n).getD (findTranslation? env t n).isSome
      unless doTranslate do throw e
    | .lam _ _ t _       => visit t
    | .forallE _ _ t _   => visit t
    | .letE _ _ e body _ => visit e; visit body
    | .mdata _ b         => visit b
    | .proj _ _ b        => visit b
    | .fvar fvarId       =>
      if dontTranslate.contains fvarId then
        throw e
      visitedFVars.modify (·.push fvarId)
    /- We do not translate the order on `Prop`.
    TODO: We also don't want to translate the category on `Type u`. Unfortunately, replacing
    `.sort 0` with `.sort _` here breaks some uses of `to_additive` on `MonCat`. -/
    | .sort 0            => throw e
    | _                  => pure ()
  match ← (visit e).run' mkPtrSet with
  | .error e => return some e
  | .ok () =>
    /- In the case that we do translate, we mark the visited free variables as relevant for
    the translation by inserting them into the state. -/
    modify (·.insertMany (← visitedFVars.get))
    return none

/-- `shouldTranslate e` tests whether the expression `e` contains a constant
that is not applied to any arguments and that doesn't have a translation itself.
This is used for deciding which subexpressions to translate: we only translate
constants if `shouldTranslate` applied to their relevant argument returns `true`.
This means we will replace expression applied to e.g. `α` or `α × β`, but not when applied to
e.g. `ℕ` or `ℝ × α`.
We ignore all arguments specified by the `ignore` `NameMap`. -/
@[implemented_by shouldTranslateUnsafe]
opaque shouldTranslate (env : Environment) (t : TranslateData) (e : Expr) :
  ReplacementM (Option Expr)

/--
`applyReplacementFun e` replaces the expression `e` with its translation.
It translates each identifier (inductive type, defined function etc) in an expression, unless
* The identifier occurs in an application with `relevantArg` argument `arg`; and
* `shouldTranslate arg` is false.

It will also reorder arguments of certain functions, using the stored `reorder`.
-/
partial def applyReplacementFun (t : TranslateData) (e : Expr) : ReplacementM Expr :=
  visit e
where
  /-- The implementation of this function is based on `Meta.transform`.
  We can't use `Meta.transform`, because that would cause the types of free variables to be
  translated, which would create type-incorrect terms. Instead, we give the free variables
  their original type and the translated type is only used when constructing the final term. -/
  visit (e : Expr) : ReplacementM Expr :=
    withTraceNode `translate_detail (fun res => return m!"{exceptEmoji res} translating {e}") do
    checkCache { val := e : ExprStructEq } fun _ => do
    let e ← match e with
      | .forallE .. => visitForall e
      | .lam ..     => visitLambda e
      | .letE ..    => visitLet e
      | .mdata _ b  => return e.updateMData! (← visit b)
      | .proj ..    => visitApp e
      | .app ..     => visitApp e
      | .const ..   => visitApp e
      | _           => pure e
    trace[translate_detail] "result: {e}"
    return e
  visitApp (e : Expr) := e.withApp fun f args ↦ do
    let env ← getEnv
    match f with
    | .proj n i b =>
      let some info := getStructureInfo? env n |
        return mkAppN (f.updateProj! (← visit b)) (← args.mapM visit) -- e.g. if `n` is `Exists`
      let some projName := info.getProjFn? i | unreachable!
      -- if `projName` has a translation, replace `f` with the application `projName s`
      -- and then visit `projName s args` again.
      if findTranslation? env t projName |>.isNone then
        return mkAppN (f.updateProj! (← visit b)) (← args.mapM visit)
      visit <| (← whnfD (← inferType b)).withApp fun bf bargs ↦
        mkAppN (.app (mkAppN (.const projName bf.constLevels!) bargs) b) args
    | .const n₀ ls₀ =>
      -- Replace numeral `1` with `0` in applications of `OfNat` and `OfNat.ofNat`.
      if h : t.changeNumeral ∧ (n₀ matches ``OfNat | ``OfNat.ofNat) ∧ 2 ≤ args.size then
        if args[1] == mkRawNatLit 1 then
          if (← shouldTranslate env t args[0]).isNone then
            -- In this case, we still update all arguments of `g` that are not numerals,
            -- since all other arguments can contain subexpressions like
            -- `(fun x ↦ ℕ) (1 : G)`, and we have to update the `(1 : G)` to `(0 : G)`
            trace[translate_detail] "applyReplacementFun: We change the numeral in this \
              expression to 0. However, we will still recurse into all the non-numeral arguments."
            let args := args.set 1 (mkRawNatLit 0)
            return mkAppN f (← args.mapM visit)
      let some { translation := n₁, reorder, relevantArg } ← findPrefixTranslation? n₀ t |
        return mkAppN f (← args.mapM visit)
      -- Use `relevantArg` to test if the head should be translated.
      if let .arg relevantArg := relevantArg then
        if h : relevantArg < args.size then
          if let some fixed ← shouldTranslate (← getEnv) t args[relevantArg] then
            trace[translate_detail]
              "The application of {n₀} contains the fixed type {fixed} so it is not changed."
            return mkAppN f (← args.mapM visit)
      -- If the number of arguments is too small for `reorder`, we need to eta expand first
      if args.size < reorder.range then
        let e' ← etaExpandN (reorder.range - args.size) e
        trace[translate_detail] "eta expanded {e} to {e'}"
        return ← visit e'
      let f' := Expr.const n₁ (reorder.permuteUniv ls₀)
      trace[translate_detail]"changing {f} to {f'}"
      unless reorder.perm.isEmpty do
        trace[translate_detail]
          "reordering the arguments of {f'} using the cyclic permutations {reorder.perm}"
      let mut args := args
      /- It would be possible to, instead of calling `reorderLambda`,
      do the reordering of arguments as part of the main loop. This would be more efficient,
      but since this is a rare case, this will likely not save a significant amount of time. -/
      for (arg, argReorder) in reorder.argReorders do
        args ← args.modifyM arg (reorderLambda argReorder ·)
      args := reorder.permute! args
      return mkAppN f' (← args.mapM visit)
    | _ => return mkAppN (← visit f) (← args.mapM visit)
  /- In `visitLambda`, `visitForall` and `visitLet`,
  we use a fresh `tmpLCtx : LocalContext` to store the translated types of the free variables.
  This is because the local context in the `MetaM` monad stores their original types. -/
  visitLambda (e : Expr) (fvars : Array Expr := #[]) (tmpLCtx : LocalContext := {}) := do
    if let .lam n d b bi := e then
      let d := d.instantiateRev fvars
      let d' ← visit d
      withLocalDecl n bi d fun x => do
        visitLambda b (fvars.push x) (tmpLCtx.addDecl ((← getFVarLocalDecl x).setType d'))
    else
      let e ← visit (e.instantiateRev fvars)
      return tmpLCtx.mkLambda fvars e
  visitForall (e : Expr) (fvars : Array Expr := #[]) (tmpLCtx : LocalContext := {}) := do
    if let .forallE n d b bi := e then
      let d := d.instantiateRev fvars
      let d' ← visit d
      withLocalDecl n bi d fun x => do
        visitForall b (fvars.push x) (tmpLCtx.addDecl ((← getFVarLocalDecl x).setType d'))
    else
      let e ← visit (e.instantiateRev fvars)
      return tmpLCtx.mkForall fvars e
  visitLet (e : Expr) (fvars : Array Expr := #[]) (tmpLCtx : LocalContext := {}) := do
    if let .letE n t v b nondep := e then
      let t := t.instantiateRev fvars; let v := v.instantiateRev fvars
      let t' ← visit t; let v' ← visit v
      withLetDecl n t v (nondep := nondep) fun x => do
        visitLet b (fvars.push x) (tmpLCtx.addDecl
          (((← getFVarLocalDecl x).setType t').setValue v'))
    else
      let e ← visit (e.instantiateRev fvars)
      -- Note that `mkLambda` will make `let` expressions because it will see the `LocalDecl.ldecl`.
      return tmpLCtx.mkLambda (usedLetOnly := false) fvars e

/-- Rename binder names in pi type. -/
def renameBinderNames (t : TranslateData) (src : Expr) : Expr :=
  src.mapForallBinderNames fun
    | .str p s => .str p (GuessName.guessName t.guessNameData s)
    | n => n

/-- Run `applyReplacementFun` on an expression `∀ x₁ .. xₙ, e`,
making sure not to translate type-classes on `xᵢ` if `i` is in `dontTranslate`. -/
def applyReplacementForall (t : TranslateData) (dontTranslate : List Nat) (e : Expr) :
    MetaM (Expr × Option RelevantArg) :=
  withTraceNode `translate_detail (fun res =>
    return m!"{exceptEmoji res} translating the type {e}") do
  forallTelescope e fun xs e => do
    let xs := xs.map (·.fvarId!)
    let dontTranslate := dontTranslate.filterMap (xs[·]?) |>.toArray
    let (e, relevantArg?) ← ReplacementM.run dontTranslate xs do
      let mut e ← applyReplacementFun t e
      for x in xs.reverse do
        let decl ← x.getDecl
        let xType ← applyReplacementFun t decl.type
        e := .forallE decl.userName xType (e.abstract #[.fvar x]) decl.binderInfo
      return e
    -- Heuristic: for instances, the `relevant_arg` option defaults to `.noArg`.
    -- This is useful in `to_additive` for instances on `GrpCat`/`MonCat`.
    let relevantArg? ← match relevantArg? with
      | some relevantArg => pure (some <| .arg relevantArg)
      | none => pure <| if (← isClass? e).isSome then some .noArg else none
    return (e, relevantArg?)

/-- Run `applyReplacementFun` on an expression `fun x₁ .. xₙ ↦ e`,
making sure not to translate type-classes on `xᵢ` if `i` is in `dontTranslate`. -/
def applyReplacementLambda (t : TranslateData) (dontTranslate : List Nat) (e : Expr) :
    MetaM (Expr × Option RelevantArg) :=
  withTraceNode `translate_detail (fun res =>
    return m!"{exceptEmoji res} translating the value {e}") do
  lambdaTelescope e fun xs e => do
    let xs := xs.map (·.fvarId!)
    let dontTranslate := dontTranslate.filterMap (xs[·]?) |>.toArray
    let (e, relevantArg?) ← ReplacementM.run dontTranslate xs do
      let mut e ← applyReplacementFun t e
      for x in xs.reverse do
        let decl ← x.getDecl
        let xType ← applyReplacementFun t decl.type
        e := .lam decl.userName xType (e.abstract #[.fvar x]) decl.binderInfo
      return e
    return (e, relevantArg?.map .arg)

/-- Run `applyReplacementFun` on the given `srcDecl` to make a new declaration with name `tgt`. -/
def updateDecl (t : TranslateData) (tgt : Name) (srcDecl : ConstantInfo)
    (reorder : Reorder) (dont : List Nat)
    (unfoldBoundaries? : Option UnfoldBoundary.UnfoldBoundaries) :
    MetaM (ConstantInfo × Option RelevantArg) := do
  unless srcDecl.all == [srcDecl.name] do
    throwError "`{t.attrName}` does not support mutually recursive declarations."
  let decl := srcDecl.updateName tgt
  let decl := decl.updateAll [tgt]
  let decl := decl.updateLevelParams (reorder.permuteUniv decl.levelParams)
  let mut value := decl.value! (allowOpaque := true)
  if let some b := unfoldBoundaries? then
    value ← b.cast (← b.insertBoundaries value t.attrName) decl.type t.attrName
  trace[translate] "Value before translation:{indentExpr value}"
  let (value', relevantArg₁) ← applyReplacementLambda t dont value
  value ← reorderLambda reorder value'
  if let some b := unfoldBoundaries? then
    value ← b.unfoldInsertions value
  let decl := decl.updateValue value
  let mut type := decl.type
  if let some b := unfoldBoundaries? then
    type ← b.insertBoundaries decl.type t.attrName
  let (type', relevantArg₂) ← applyReplacementForall t dont <| renameBinderNames t type
  type ← reorderForall reorder type'
  if let some b := unfoldBoundaries? then
    type ← b.unfoldInsertions type
  return (decl.updateType type, .merge .min relevantArg₁ relevantArg₂)

/-- Translate the source declaration and then run `addDecl`. If the kernel throws an error,
try to emit a better error message.

For efficiency in `to_dual`, we first run `updateDecl` without any `UnfoldBoundaries`,
and only if that fails do we try to include them.
The reason is that in the most common case, `to_dual` succeeds without needing to insert
unfold boundaries, and figuring out whether to insert them can be quite expensive. -/
def updateAndAddDecl (t : TranslateData) (tgt : Name) (srcDecl : ConstantInfo)
    (reorder : Reorder) (dont : List Nat) : MetaM (ConstantInfo × Option RelevantArg) :=
  -- Set `Elab.async` to `false` so that we can catch kernel errors.
  withOptions (Elab.async.set · false) do
  let decl ←
    if let some unfoldBoundaries := t.unfoldBoundaries? then
      let env ← getEnv
      -- First attempt to generate the translation without unfold boundaries.
      let declAttempt ← updateDecl t tgt srcDecl reorder dont none
      try
        addDecl declAttempt.1.toDeclaration!
        trace[translate] "generating\n{tgt} : {declAttempt.1.type} :=\
          {indentExpr <| declAttempt.1.value! (allowOpaque := true)}"
        return declAttempt -- early return
      catch _ =>
        setEnv env
        updateDecl t tgt srcDecl reorder dont (unfoldBoundaries.getState env)
    else
      updateDecl t tgt srcDecl reorder dont none
  trace[translate] "generating\n{tgt} : {decl.1.type} :=\
    {indentExpr <| decl.1.value! (allowOpaque := true)}"
  try
    addDecl decl.1.toDeclaration!
    return decl
  catch ex =>
    try
      withoutExporting <| check (decl.1.value! (allowOpaque := true))
    catch ex =>
      throwError "@[{t.attrName}] failed to add declaration `{decl.1.name}`.\n  \
        The translated value is not type correct.\n  \
        For help, see the docstring of `to_additive`, section `Troubleshooting`.\n\
        {ex.toMessageData}"
    throwError "@[{t.attrName}] failed. Nested error message:\n{ex.toMessageData}"

/-- Unfold `simp` and `gcongr` auxlemmas in the type and value.
The reason why we can't just translate them is that they are generated by the `@[simp]` attribute,
so it would require a change in the implementation of `@[simp]` to add these translations.
Additionally, these lemmas have very short proofs, so unfolding them is not costly. -/
def declUnfoldSimpAuxLemmas (decl : ConstantInfo) : MetaM ConstantInfo := do
  let unfold (e : Expr) := deltaExpand e fun
    | .str _ s => "_simp_".isPrefixOf s || "_gcongr_".isPrefixOf s
    | _ => false
  let mut decl := decl
  decl := decl.updateType <| ← unfold decl.type
  if let some v := decl.value? (allowOpaque := true) then
    decl := decl.updateValue <| ← unfold v
  return decl

/-- Find the target name of `src`, which is assumed to have been selected by `findAuxDecls`. -/
def findTargetName (env : Environment) (t : TranslateData) (src rootSrc rootTgt : Name) :
    CoreM Name := do
  /- This covers auxiliary declarations like `match_i` and `proof_i`. -/
  if let some post := (privateToUserName rootSrc).isPrefixOf? (privateToUserName src) then
    let tgt := rootTgt ++ post
    return if isPrivateName src then mkPrivateName env tgt else tgt
  if src.hasMacroScopes then
    mkFreshUserName src.eraseMacroScopes
  else
    withDeclNameForAuxNaming src do mkAuxDeclName (Name.mkSimple s!"_{t.attrName.toString}")

/-- Returns a `NameSet` of auxiliary constants in `decl` that might have been generated
when adding `pre` to the environment, and which hence might need to be translated.
Examples include `pre.match_5`, `pre._proof_2`, `someOtherDeclaration._proof_2` and `wrapped✝`.
The reason why we have to include `_proof_i` lemmas from other declarations is that there is a
cache of such proofs, and previous such auxiliary proofs are reused when possible.
These auxiliary declarations may be private or not, independent of whether `pre` is private.
`wrapped✝` is generated by `irreducible_def`, and it has macro scopes.
-/
def findAuxDecls (decl : ConstantInfo) (pre : Name) : CoreM (Array Name) := do
  let env ← withoutExporting getEnv
  return (Expr.app decl.type (decl.value! (allowOpaque := true))).foldConsts #[] fun n l ↦
    if (env.find? n).any (·.hasValue (allowOpaque := true)) &&
      ((match n with | .str _ s => "_proof_".isPrefixOf s | _ => false) ||
      (privateToUserName n).getPrefix == privateToUserName pre || n.hasMacroScopes) then
      l.push n
    else
      l

/-- Return the `relevant_arg` option based on the computed `relevantArg?`
and the given `cfg.relevantArg?`. -/
def getRelevantArg (t : TranslateData) (cfg : Config) (relevantArg? : Option RelevantArg)
    (src : Name) : CoreM RelevantArg := do
  let relevantArg := relevantArg?.getD (.arg 0)
  if let some relevantArg' := cfg.relevantArg? then
    if relevantArg == relevantArg' then
      Linter.logLintIf linter.translateRelevantArg cfg.ref m!"\
        `{t.attrName}` correctly autogenerated `(relevant_arg := {relevantArg'})` for \
        `{.ofConstName src}`.\nYou may remove the option."
    else if relevantArg?.isSome then
      Linter.logLintIf linter.translateRelevantArg cfg.ref m!"\
        `{t.attrName}` determined that `(relevant_arg := {relevantArg})` \
        is the right option for `{.ofConstName src}`, \
        rather than `(relevant_arg := {relevantArg'})`.\nYou may remove the option."
    pure relevantArg'
  else
    return relevantArg

/-- Translate the declaration `src` and recursively all declarations `rootSrc._proof_i`
occurring in `src` using the `translations` dictionary.

- `rootSrc` is the declaration that got the translation attribute and `rootTgt` is its target.
- `src` is assumed to have a value available in the environment.
- `reorder` is used only for the translation of `src`.
-/
partial def transformDeclRec (t : TranslateData) (cfg : Config) (rootSrc rootTgt src : Name)
    (reorder : Reorder := {}) : CoreM Unit := do
  let env ← getEnv
  trace[translate_detail] "visiting {src}"
  -- if we have already translated this declaration, we do nothing.
  if (findTranslation? env t src).isSome && src != rootSrc then
    return
  -- if this declaration is not `rootSrc` and not an internal declaration, we return an error,
  -- since we should have already translated this declaration.
  if src != rootSrc && !src.isInternalDetail then
    throwError "The declaration {rootSrc} depends on the declaration {src} \
    which is in the namespace {rootSrc}, but does not have the `@[{t.attrName}]` attribute. \
    This is not supported.\nWorkaround: move {src} to a different namespace."
  -- we find, or guess, the translated name of `src`
  let tgt ← findTargetName env t src rootSrc rootTgt
  -- we skip if we already transformed this declaration before.
  if env.setExporting false |>.contains tgt then
    if tgt == src then
      -- Note: this can happen for equation lemmas of declarations without a translation.
      trace[translate_detail] "Auxiliary declaration {src} will be translated to itself."
    else
      trace[translate_detail] "Already visited {tgt} as translation of {src}."
    return
  let srcDecl ← withoutExporting do getConstInfo src
  -- we first unfold all auxlemmas, since they are not always able to be translated on their own
  let srcDecl ← withoutExporting do MetaM.run' do declUnfoldSimpAuxLemmas srcDecl
  -- we then transform all auxiliary declarations generated when elaborating `rootSrc`
  for n in ← findAuxDecls srcDecl rootSrc do
    transformDeclRec t cfg rootSrc rootTgt n
  -- expose target body when source body is exposed
  withExporting (isExporting := (← getEnv).setExporting true |>.find? src |>.any (·.hasValue)) do
  -- We still lack a heuristic that automatically infers the `dontTranslate`,
  -- so for now we do a best guess based on argument names.
  let dontTranslate ← if cfg.dontTranslate.isEmpty then pure [] else
    if src == rootSrc then pure cfg.dontTranslate else
      let namesPre := (← getConstInfo rootSrc).type.getForallBinderNames
      let namesSrc := (← getConstInfo src).type.getForallBinderNames
      pure <| cfg.dontTranslate.filterMap (namesPre[·]? >>= namesSrc.idxOf?)
  -- now transform the source declaration
  let (tgtDecl, relevantArg?) ← MetaM.run' <| updateAndAddDecl t tgt srcDecl reorder dontTranslate
  let relevantArg ←
    if src == rootSrc then
      getRelevantArg t cfg relevantArg? src
    else
      pure (relevantArg?.getD .noArg)
  insertTranslation t src tgt reorder relevantArg cfg.ref
  if src == rootSrc && srcDecl.isThm && tgtDecl.type == srcDecl.type then
    Linter.logLintIf linter.translateRedundant cfg.ref m!"`{t.attrName}` did not change the type \
      of theorem `{.ofConstName src}`. Please remove the attribute."
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
  if isNoncomputable (← getEnv) src then
    modifyEnv (addNoncomputable · tgt)
  else
    if isMarkedMeta (← getEnv) src then
      -- We need to mark `tgt` as `meta` before running `compileDecl`
      modifyEnv (markMeta · tgt)
    compileDecl tgtDecl.toDeclaration! (logErrors := (IR.findEnvDecl (← getEnv) src).isSome)
  if let .defnInfo { hints := .abbrev, .. } := tgtDecl then
    if (← getReducibilityStatus src) == .reducible then
      setReducibilityStatus tgt .reducible
    if Compiler.getInlineAttribute? (← getEnv) src == some .inline then
      MetaM.run' <| Meta.setInlineAttribute tgt
  -- now add declaration ranges so jump-to-definition works
  -- note: we currently also do this for auxiliary declarations, while they are not normally
  -- generated for those. We could change that.
  addDeclarationRangesFromSyntax tgt (← getRef) cfg.ref
  if isProtected (← getEnv) src then
    modifyEnv (addProtected · tgt)
  if defeqAttr.hasTag (← getEnv) src then
    /- It can be that `src` holds reflexively but `tgt` doesn't, so we need to use `inferDefEqAttr`.
    For example in `Ici_inter_Iic : Ici a ∩ Iic b = Icc a b := rfl`. -/
    MetaM.run' <| inferDefEqAttr tgt
  if let some matcherInfo ← getMatcherInfo? src then
    Match.addMatcherInfo tgt matcherInfo
  -- necessary so that e.g. match equations can be generated for `tgt`
  enableRealizationsForConst tgt

/-- Copy the instance attribute in a `to_additive`

[todo] it seems not to work when the `to_additive` is added as an attribute later. -/
def copyInstanceAttribute (src tgt : Name) : CoreM Unit := do
  if let some prio ← getInstancePriority? src then
    let attr_kind := (← getInstanceAttrKind? src).getD .global
    -- Copy implicit_reducible status before adding instance attribute
    if (← getReducibilityStatus src) matches .implicitReducible then
      setReducibilityStatus tgt .implicitReducible
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
    (t : TranslateData) (names : Array Name) (reorder : Reorder) (relevantArg : RelevantArg)
    (desc : String) (ref : Syntax) (runAttr : Name → m (Array Name)) : m Unit := do
  let auxLemmas ← names.mapM runAttr
  let nLemmas := auxLemmas[0]!.size
  for (nm, lemmas) in names.zip auxLemmas do
    unless lemmas.size == nLemmas do
      throwError "{names[0]!} and {nm} do not generate the same number of {desc}."
  for (srcLemmas, tgtLemmas) in auxLemmas.zip <| auxLemmas.eraseIdx! 0 do
    for (srcLemma, tgtLemma) in srcLemmas.zip tgtLemmas do
      insertTranslation t srcLemma tgtLemma reorder relevantArg ref

/-- Return the provided target name or autogenerate one if one was not provided. -/
def targetName (t : TranslateData) (cfg : Config) (src : Name) : CoreM Name := do
  if cfg.self then
    if cfg.tgt != .anonymous then
      logWarning m!"`{t.attrName} self` ignores the provided name {cfg.tgt}"
    return src
  if cfg.none then
    if cfg.tgt != .anonymous then
      logWarning m!"`{t.attrName} private` ignores the provided name {cfg.tgt}"
    return ← withDeclNameForAuxNaming src do
      mkAuxDeclName <| .mkSimple ("_" ++ t.attrName.toString)
  -- When re-tagging an existing translation, simply return that existing translation.
  if cfg.existing then
    if cfg.tgt == .anonymous then
      if let some tgt := findTranslationName? (← getEnv) t src then
        return tgt
  let .str pre s := src | throwError "{t.attrName}: can't transport {src}"
  trace[translate_detail] "The name {s} splits as {open GuessName in s.splitCase}"
  let tgt_auto := GuessName.guessName t.guessNameData s
  let depth := cfg.tgt.getNumParts
  let pre := translateNamespace (← getEnv) pre
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
where
  translateNamespace (env : Environment) (n : Name) : Name :=
    let n' := Name.mapPrefix (findTranslationName? env t) n
    if n' == n && isPrivateName n then
      mkPrivateName env <| .mapPrefix (findTranslationName? env t) (privateToUserName n)
    else
      n'

/-- Verify that the type of `srcDecl` translates to that of `tgtDecl`.
Also try to autogenerate the `reorder` option for this translation. -/
partial def checkExistingType (t : TranslateData) (src tgt : Name) (cfg : Config) :
    MetaM (Reorder × RelevantArg) := withoutExporting do
  let srcDecl ← getConstInfo src
  let tgtDecl ← getConstInfo tgt
  unless srcDecl.levelParams.length == tgtDecl.levelParams.length do
    throwError "`{t.attrName}` validation failed:\n  expected {srcDecl.levelParams.length} \
      universe levels, but '{tgt}' has {tgtDecl.levelParams.length} universe levels"
  let mut srcType := srcDecl.type
  let unfoldBoundaries? ← t.unfoldBoundaries?.mapM (return ·.getState (← getEnv))
  if let some b := unfoldBoundaries? then
    srcType ← b.insertBoundaries srcType t.attrName
  let (srcType', relevantArg?) ← applyReplacementForall t cfg.dontTranslate srcType
  srcType := srcType'
  let reorder' ← guessReorder srcType tgtDecl.type
  trace[translate_detail] "The guessed reorder is {reorder'}"
  let reorder ←
    if let some reorder := cfg.reorder? then
      if reorder == reorder' then
        Linter.logLintIf linter.translateReorder cfg.ref m!"\
          `{t.attrName}` correctly autogenerated `(reorder := {reorder'})` for {src}.\n\
          You may remove the `(reorder := {reorder})` argument."
      pure reorder
    else
      pure reorder'
  if cfg.self && reorder.isEmpty then
    Linter.logLintIf linter.translateRedundant cfg.ref m!"\
      `{t.attrName} self` is redundant when none of the arguments are reordered.\n\
      Please remove the attribute, or provide an explicit `(reorder := ...)` argument.\n\
      If you need to give a hint to `{t.attrName}` to translate expressions involving `{src}`,\n\
      use `{t.attrName}_do_translate` instead"
  srcType ← reorderForall reorder srcType
  if let some b := unfoldBoundaries? then
    srcType ← b.unfoldInsertions srcType
  let srcDecl := srcDecl.updateLevelParams (reorder.permuteUniv srcDecl.levelParams)
  -- instantiate both types with the same universes. `instantiateLevelParams` does some
  -- normalization, so we apply it to both types.
  srcType := srcType.instantiateLevelParams
    srcDecl.levelParams (tgtDecl.levelParams.map mkLevelParam)
  let tgtType := tgtDecl.type.instantiateLevelParams
    tgtDecl.levelParams (tgtDecl.levelParams.map mkLevelParam)
  unless ← withReducible <| isDefEq srcType tgtType do
    throwError "`{t.attrName}` validation failed: expected{indentExpr srcType}\nbut '{tgt}' has \
      type{indentExpr tgtType}"
  return (reorder, ← getRelevantArg t cfg relevantArg? src)

/-- if `f src = #[a_1, ..., a_n]` and `f tgt = #[b_1, ... b_n]` then `proceedFieldsAux src tgt f`
will insert translations from `a_i` to `b_i`. -/
def proceedFieldsAux (t : TranslateData) (src tgt : Name) (reorder : Reorder)
    (relevantArg : RelevantArg) (ref : Syntax) (f : Name → Array Name) : CoreM Unit := do
  let srcFields := f src
  let tgtFields := f tgt
  if srcFields.size != tgtFields.size then
    throwError "Failed to map fields of {src}, {tgt} with {srcFields} ↦ {tgtFields}.\n \
      Lengths do not match."
  for srcField in srcFields, tgtField in tgtFields do
    insertTranslation t srcField tgtField reorder relevantArg ref

/-- Add the structure fields of `src` to the translations dictionary
so that they will be translated correctly. -/
def proceedFields (t : TranslateData) (src tgt : Name) (reorder : Reorder)
    (relevantArg : RelevantArg) (ref : Syntax) : CoreM Unit := do
  let env ← getEnv
  let aux := proceedFieldsAux t src tgt reorder relevantArg ref
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
- `stx[2]` is the remaining `attrArgs`

TODO: Currently, we don't deduce any `dont_translate` arguments based on the type of `declName`.
In the future we would like that the presence of `MonoidAlgebra k G` will automatically
flag `k` as a type to not be translated. -/
def elabTranslationAttr (declName : Name) (stx : Syntax) : CoreM Config := do
  match stx[2] with
  | `(attrArgs| $hint $[$opts:bracketedOption]* $[$tgt]? $[$doc]?) =>
    MetaM.run' <| forallTelescope (← getConstInfo declName).type fun xs _ => do
    let argNames ← xs.mapM (·.fvarId!.getUserName)
    let mut attrs := #[]
    let mut reorder? := none
    let mut relevantArg? := none
    let mut dontTranslate := []
    for opt in opts do
      match opt with
      | `(bracketedOption| (attr := $[$stxs],*)) =>
        attrs := attrs ++ stxs
      | `(bracketedOption| (reorder := $reorder)) =>
        if reorder?.isSome then
          throwErrorAt opt "cannot specify `reorder` multiple times"
        reorder? ← elabReorder reorder argNames xs (.ofConstName declName)
      | `(bracketedOption| (relevant_arg := $n)) =>
        if relevantArg?.isSome then
          throwErrorAt opt "cannot specify `relevant_arg` multiple times"
        if let `($_:hole) := n then
          relevantArg? := some .noArg
        else
          relevantArg? := some <| .arg (← elabArgStx ⟨n.raw⟩ argNames xs (.ofConstName declName))
      | `(bracketedOption| (dont_translate := $[$types]*)) =>
        dontTranslate := dontTranslate ++
          (← types.toList.mapM (elabArgStx · argNames xs (.ofConstName declName)))
      | _ => throwUnsupportedSyntax
    let mut existing := false; let mut self := false; let mut none := false
    match hint with
    | `(translationHint| existing) => existing := true
    | `(translationHint| self) => existing := true; self := true
    | `(translationHint| none) => none := true
    | _ => pure ()
    if (self || none) && !attrs.isEmpty then
      throwError "invalid `(attr := ...)` after `self` or `none`, \
        as there is no other declaration for the attributes.\n\
        Instead, you can write the attributes in the usual way."
    trace[translate_detail]
      "attributes: {attrs}; reorder arguments: {reorder?.elim "none" (·.toString)}"
    let doc ← doc.mapM fun
      | `(str|$doc:str) => open Linter in do
        -- Deprecate `str` docstring syntax (since := "2025-08-12")
        if getLinterValue linter.deprecated (← getLinterOptions) then
          let hintSuggestion := {
            diffGranularity := .none
            toTryThisSuggestion := { suggestion := "/-- " ++ doc.getString.trimAscii ++ " -/" }
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
      tgt := match tgt with | some tgt => tgt.getId | _ => Name.anonymous
      doc, attrs, reorder?, relevantArg?, dontTranslate, existing, self, none
      ref := match tgt with | some tgt => tgt.raw | _ => stx[0] }
  | _ => throwUnsupportedSyntax

mutual
/-- Apply attributes to the original and translated declarations. -/
partial def applyAttributes (t : TranslateData) (cfg : Config) (src tgt : Name) (reorder : Reorder)
    (relevantArg : RelevantArg) : TermElabM (Array Name) := do
  -- we only copy the `instance` attribute, since it is nice to directly tag `instance` declarations
  copyInstanceAttribute src tgt
  -- Warn users if the original declaration has an attributee
  if !cfg.self && !cfg.none && linter.existingAttributeWarning.get (← getOptions) then
    let appliedAttrs ← getAllSimpAttrs src
    if appliedAttrs.size > 0 then
      let appliedAttrs := ", ".intercalate (appliedAttrs.toList.map toString)
      -- Note: we're not bothering to print the correct attribute arguments.
      Linter.logLintIf linter.existingAttributeWarning cfg.ref m!"\
        The source declaration {src} was given the simp-attribute(s) {appliedAttrs} before \
        calling @[{t.attrName}].\nThe preferred method is to use something like \
        `@[{t.attrName} (attr := {appliedAttrs})]`\nto apply the attribute to both \
        {src} and the target declaration {tgt}."
    warnAttr cfg.ref Lean.Meta.Ext.extExtension
      (fun b n => (b.tree.values.any fun t => t.declName = n)) t.attrName `ext src tgt
    warnAttr cfg.ref Lean.Meta.Rfl.reflExt (·.values.contains ·) t.attrName `refl src tgt
    warnAttr cfg.ref Lean.Meta.Symm.symmExt (·.values.contains ·) t.attrName `symm src tgt
    warnAttr cfg.ref Batteries.Tactic.transExt (·.values.contains ·) t.attrName `trans src tgt
    warnAttr cfg.ref Lean.Meta.coeExt (·.contains ·) t.attrName `coe src tgt
    warnParametricAttr cfg.ref Lean.Linter.deprecatedAttr t.attrName `deprecated src tgt
    -- the next line also warns for `@[to_additive, simps]`, because of the application times
    warnParametricAttr cfg.ref simpsAttr t.attrName `simps src tgt
    warnAttrCore cfg.ref Term.elabAsElim.hasTag t.attrName `elab_as_elim src tgt
  -- add attributes
  -- the following is similar to `Term.ApplyAttributesCore`, but we hijack the implementation of
  -- `simps` and `to_additive`.
  let attrs ← elabAttrs cfg.attrs
  let (additiveAttrs, attrs) := attrs.partition (·.name == t.attrName)
  let nestedDecls ←
    match h : additiveAttrs.size with
    | 0 => pure #[]
    | 1 =>
      let cfg ← elabTranslationAttr src additiveAttrs[0].stx
      addTranslationAttr t tgt cfg additiveAttrs[0].kind
    | _ => throwError "cannot apply {t.attrName} multiple times."
  let allDecls := #[src, tgt] ++ nestedDecls
  if attrs.size > 0 then
    trace[translate_detail] "Applying attributes {attrs.map (·.stx)} to {allDecls}"
  for attr in attrs do
    if attr.name == `simps then
      withRef attr.stx do withLogging do
        translateLemmas t allDecls reorder relevantArg "simps lemmas" cfg.ref
          (simpsTacFromSyntax · attr.stx)
    else
      for decl in allDecls do
        Term.applyAttributes decl #[attr]
  return nestedDecls

/--
Copies equation lemmas and attributes from `src` to `tgt`
-/
partial def copyMetaData (t : TranslateData) (cfg : Config) (src : Name) : CoreM (Array Name) := do
  let some { reorder, relevantArg, translation := tgt } := findTranslation? (← getEnv) t src |
    throwError "internal `{t.attrName}` error: {src} was not translated."
  -- The equation lemmas can only be related if the value of `tgt` is the translated value of `src`.
  unless cfg.existing do
    if let some eqns := eqnsAttribute.find? (← getEnv) src then
      unless (eqnsAttribute.find? (← getEnv) tgt).isSome do
        for eqn in eqns do
          _ ← addTranslationAttr t eqn cfg
        eqnsAttribute.add tgt (eqns.map (findTranslationName? (← getEnv) t · |>.get!))
    else
      /- We need to generate all equation lemmas for `src` and `tgt`, even for non-recursive
      definitions. If we don't do that, the equation lemma for `src` might be generated later
      when doing a `rw`, but it won't be generated for `tgt`. -/
      translateLemmas t #[src, tgt] reorder relevantArg "equation lemmas" cfg.ref fun nm ↦
        (·.getD #[]) <$> MetaM.run' (getEqnsFor? nm)
  applyAttributes t cfg src tgt reorder relevantArg |>.run'.run'

/-- `addTranslationAttr src cfg` adds a translation attribute to `src` with configuration `cfg`.
See the attribute implementation for more details.
It returns an array with names of translated declarations (usually 1, but more if there are nested
`to_additive` calls). -/
partial def addTranslationAttr (t : TranslateData) (src : Name) (cfg : Config)
    (kind := AttributeKind.global) : AttrM (Array Name) := do
  if (kind != AttributeKind.global) then
    throwError "`{t.attrName}` can only be used as a global attribute"
  withOptions (fun o => if cfg.trace then o.set `trace.translate true else o) do
  let tgt ← targetName t cfg src
  let alreadyExists ← realizeGlobalConst tgt
  if cfg.existing != alreadyExists && !(← isInductive src) && !cfg.self then
    Linter.logLintIf linter.translateExisting cfg.ref <|
      if alreadyExists then
        m!"The translated declaration already exists. Please specify this explicitly using \
           `@[{t.attrName} existing]`."
      else
        "The translated declaration doesn't exist. Please remove the option `existing`."
  if alreadyExists then
    let (reorder, relevantArg) ← MetaM.run' <| checkExistingType t src tgt cfg
    insertTranslation t src tgt reorder relevantArg cfg.ref
    -- since `tgt` already exists, we just need to
    -- add translations `src.x ↦ tgt.x'` for any subfields.
    trace[translate_detail] "declaration {tgt} already exists."
    proceedFields t src tgt reorder relevantArg cfg.ref
  else
    unless (← withoutExporting do getConstInfo src).hasValue (allowOpaque := true) do
      throwError "`{t.attrName}` cannot translate `{.ofConstName src}` because it has no value."
    let reorder := cfg.reorder?.getD {}
    -- tgt doesn't exist, so let's make it
    transformDeclRec t cfg src tgt src reorder
  let nestedNames ← copyMetaData t cfg src
  -- add pop-up information when mousing over the given translated name
  -- (the information will be over the attribute if no translated name is given)
  Term.addTermInfo' cfg.ref (← mkConstWithLevelParams tgt) (isBinder := !alreadyExists)
    |>.run' |>.run'
  if let some doc := cfg.doc then
    addDocStringCore tgt doc
  return nestedNames.push tgt

end

end Mathlib.Tactic.Translate
