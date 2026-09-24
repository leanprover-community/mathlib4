/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn, Jon Eugster, Bryan Gin-ge Chen,
Jovan Gerbscheid
-/
module

public meta import Batteries.Lean.NameMapAttribute

public import Mathlib.Tactic.Translate.Reorder
public import Mathlib.Tactic.Translate.UnfoldBoundary
public import Mathlib.Tactic.Translate.GuessName

/-!
# Expression translation for the translation attribute.

This file implements the translation of expressions, and all of the infrastructure that is
needed for it.

- `TranslateData` contains the information specific to the translation attribute
  (`to_additive` or `to_dual`)
- `shouldTranslate` implements the heuristic for whether or not to translate an expression.
- `applyReplacementForall`/`applyReplacementLambda` implement the expression translation.
-/

meta section

open Lean Meta

namespace Mathlib.Tactic.Translate

/-- `RelevantArg` represents an optional argument that should be checked to determine
whether or not to translate the given constant. -/
public inductive RelevantArg where
  /-- No argument needs to be checked. This is specified with `(relevant_arg := _)`. -/
  | noArg
  /-- Argument `n` needs to be checked. This is specified with `(relevant_arg := n)`. -/
  | arg (n : Nat)
  deriving BEq, Inhabited

/-- Combine two known `RelevantArg`s by taking the smallest value of the two.
Recall that if there are multiple relevant arguments, `relevant_arg` is set to the smallest one. -/
public def RelevantArg.min : RelevantArg → RelevantArg → RelevantArg
  | .arg x, .arg y => .arg (x.min y)
  | x, .noArg => x
  | .noArg, y => y

public instance : ToMessageData RelevantArg where
  toMessageData
    | .arg n => m!"{n + 1}"
    | .noArg => "_"

/-- `TranslationInfo` stores the information of how to translate a constant. -/
public structure TranslationInfo where
  /-- The name that we are translating to. -/
  translation : Name
  /-- The arguments that should be reordered when translating, using disjoint cycle notation. -/
  reorder : Reorder := {}
  /-- The argument used to determine whether this constant should be translated. -/
  relevantArg : RelevantArg := .arg 0

/-- `TranslateData` is a structure that holds all data required for a translation attribute. -/
public structure TranslateData where
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
  /-- When `isDual := true`, every translation `A ↦ B` will also give a translation `B ↦ A`. -/
  isDual : Bool
  guessNameExt : GuessName.GuessNameExt

attribute [inherit_doc GuessName.GuessNameExt] TranslateData.guessNameExt

/-- Get the translation for the given name. -/
public def findTranslation? (env : Environment) (t : TranslateData) :
    Name → Option TranslationInfo :=
  t.translations.find? env

/-- Get the translation name for the given name. -/
public def findTranslationName? (env : Environment) (t : TranslateData) (n : Name) : Option Name :=
  (findTranslation? env t n).map (·.translation)

/-- Check if the given constant exists in the environment, also checking for reserved names.
This function is based on `Lean.realizeGlobalName`. -/
public def realizeGlobalConst (c : Name) : CoreM Bool := do
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
public abbrev ReplacementM :=
  ReaderT (Array FVarId) <| MonadCacheT ExprStructEq Expr StateRefT (Std.HashSet FVarId) MetaM

/-- Run a `ReplacementM` computation, returning the result and the value of `relevant_arg` that
corresponds to this translation. -/
public def ReplacementM.run {α} (dontTranslate allFVars : Array FVarId) (x : ReplacementM α) :
    MetaM (α × RelevantArg) := do
  let (a, relevantFVars) ← x dontTranslate |>.run |>.run {}
  return (a, (allFVars.findIdx? relevantFVars.contains).elim .noArg .arg)

/-- Implementation function for `shouldTranslate`.
Returning `none` means that `e` contains no constant that blocks translation.
We cache previous applications of the function, using an expression cache using ptr equality
to avoid visiting the same subexpression many times.

Note that this function is still called many times by `applyReplacementFun`
and we're not remembering the cache between these calls. -/
unsafe def shouldTranslateUnsafe (env : Environment) (t : TranslateData) (e : Expr) :
    ReplacementM (Option Expr) := do
  let visitedFVars : IO.Ref (Array FVarId) ← IO.mkRef #[]
  let dontTranslate ← read
  let lctx ← getLCtx
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
      if let some value := (lctx.get! fvarId).value? (allowNondep := true) then
        visit value
      else
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
    withTraceNode `translate_detail (fun _ => return m!"translating {e}") do
    checkCache { val := e : ExprStructEq } fun _ => do
    let e ← match e with
      | .forallE .. => visitForall e
      | .lam ..     => visitLambda e []
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
      let { univReorder, reorder } := reorder
      -- If the number of arguments is too small for `reorder`, we need to eta expand first
      if args.size < reorder.range then
        let e' ← etaExpandN (reorder.range - args.size) e
        trace[translate_detail] "eta expanded {e} to {e'}"
        return ← visit e'
      let f' := Expr.const n₁ (univReorder.permuteList! ls₀)
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
    | .lam .. => return mkAppN (← visitLambda f args.toList) (← args.mapM visit)
    | _ => return mkAppN (← visit f) (← args.mapM visit)
  /- In `visitLambda`, `visitForall` and `visitLet`,
  we use a fresh `tmpLCtx : LocalContext` to store the translated types of the free variables.
  This is because the local context in the `MetaM` monad stores their original types.

  In `visitLambda`, we keep track of the value of  variables, which helps in `shouldTranslate`. -/
  visitLambda (e : Expr) (values : List Expr) (fvars : Array Expr := #[])
      (tmpLCtx : LocalContext := {}) := do
    if let .lam n d b bi := e then
      let d := d.instantiateRev fvars
      let d' ← visit d
      if let value :: values := values then
        withLetDecl n d value fun x =>
          visitLambda b values (fvars.push x) (tmpLCtx.mkLocalDecl x.fvarId! n d' bi)
      else
        withLocalDecl n bi d fun x =>
          visitLambda b values (fvars.push x) (tmpLCtx.mkLocalDecl x.fvarId! n d' bi)
    else
      let e ← visit (e.instantiateRev fvars)
      return tmpLCtx.mkLambda fvars e
  visitForall (e : Expr) (fvars : Array Expr := #[]) (tmpLCtx : LocalContext := {}) := do
    if let .forallE n d b bi := e then
      let d := d.instantiateRev fvars
      let d' ← visit d
      withLocalDecl n bi d fun x =>
        visitForall b (fvars.push x) (tmpLCtx.mkLocalDecl x.fvarId! n d' bi)
    else
      let e ← visit (e.instantiateRev fvars)
      return tmpLCtx.mkForall fvars e
  visitLet (e : Expr) (fvars : Array Expr := #[]) (tmpLCtx : LocalContext := {}) := do
    if let .letE n t v b nondep := e then
      let t := t.instantiateRev fvars; let v := v.instantiateRev fvars
      let t' ← visit t; let v' ← visit v
      withLetDecl n t v (nondep := nondep) fun x =>
        visitLet b (fvars.push x) (tmpLCtx.mkLetDecl x.fvarId! n t' v' nondep)
    else
      let e ← visit (e.instantiateRev fvars)
      -- Note that `mkLambda` will make `let` expressions because it will see the `LocalDecl.ldecl`.
      return tmpLCtx.mkLambda (usedLetOnly := false) fvars e

/-- Run `applyReplacementFun` on an expression `∀ x₁ .. xₙ, e`,
making sure not to translate type-classes on `xᵢ` if `i` is in `dontTranslate`. -/
public def applyReplacementForall (t : TranslateData) (dontTranslate : List Nat) (e : Expr) :
    MetaM (Expr × RelevantArg) :=
  withTraceNode `translate_detail (fun _ =>
    return m!"translating the type {e}") do
  forallTelescope e fun xs e => do
    let xs := xs.map (·.fvarId!)
    let dontTranslate := dontTranslate.filterMap (xs[·]?) |>.toArray
    ReplacementM.run dontTranslate xs do
      let mut e ← applyReplacementFun t e
      for x in xs.reverse do
        let decl ← x.getDecl
        let xType ← applyReplacementFun t decl.type
        e := .forallE decl.userName xType (e.abstract #[.fvar x]) decl.binderInfo
      return e

/-- Run `applyReplacementFun` on an expression `fun x₁ .. xₙ ↦ e`,
making sure not to translate type-classes on `xᵢ` if `i` is in `dontTranslate`. -/
public def applyReplacementLambda (t : TranslateData) (dontTranslate : List Nat) (e : Expr) :
    MetaM (Expr × RelevantArg) :=
  withTraceNode `translate_detail (fun _ =>
    return m!"translating the value {e}") do
  lambdaTelescope e fun xs e => do
    let xs := xs.map (·.fvarId!)
    let dontTranslate := dontTranslate.filterMap (xs[·]?) |>.toArray
    ReplacementM.run dontTranslate xs do
      let mut e ← applyReplacementFun t e
      for x in xs.reverse do
        let decl ← x.getDecl
        let xType ← applyReplacementFun t decl.type
        e := .lam decl.userName xType (e.abstract #[.fvar x]) decl.binderInfo
      return e

end Mathlib.Tactic.Translate
