/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn, Bryan Gin-ge Chen, Jovan Gerbscheid
-/
module

public meta import Batteries.Lean.NameMapAttribute
public import Mathlib.Tactic.Translate.GuessName
public import Mathlib.Tactic.Translate.Reorder
public import Mathlib.Tactic.Translate.UnfoldBoundary

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
  /-- Whether `translation` should be unfolded. This is used by `to_dual_for`. -/
  unfold : Bool := false

/-- `TranslateData` is a structure that holds all data required for a translation attribute. -/
public structure TranslateData where
  /-- The global `do_translate`/`dont_translate` attributes specify whether operations on
  a given type should be translated. `dont_translate` can be used for types that are translated,
  such as `MonoidAlgebra` -> `AddMonoidAlgebra`, or for fixed types, such as `Fin n`/`ZMod n`.
  `do_translate` is for types without arguments, like `Unit` and `Empty`, where the structure on it
  can be translated.

  Note: The name generation is not aware of `dont_translate`, so if some part of a lemma is not
    translated thanks to this, you generally have to specify the translated name manually.
  -/
  dontTranslateAttr : NameMapExtension Unit
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

/-- Monad used for expression translation.
- The reader stores the free variables on which nothing should be translated.
- The state stores the free variables on which something has been translated.
- The cache caches the results on subexpressions. -/
abbrev ReplacementM :=
  ReaderT (Array FVarId) <| MonadCacheT ExprStructEq Expr StateRefT (Std.HashSet FVarId) MetaM

/-- Run a `ReplacementM` computation, returning the result and the value of `relevant_arg` that
corresponds to this translation. -/
def ReplacementM.run {α} (dontTranslate allFVars : Array FVarId) (x : ReplacementM α) :
    MetaM (α × RelevantArg) := do
  let (a, relevantFVars) ← x dontTranslate |>.run |>.run {}
  return (a, (allFVars.findIdx? relevantFVars.contains).elim .noArg .arg)

/-- `shouldTranslate e` tests whether the expression `e` contains a constant
that is not applied to any arguments and that doesn't have a translation itself.
This is used for deciding which subexpressions to translate: we only translate
constants if `shouldTranslate` applied to their relevant argument returns `true`.
This means we will replace expression applied to e.g. `α` or `α × β`, but not when applied to
e.g. `ℕ` or `ℝ × α`.
-/
partial def shouldTranslate (t : TranslateData) (e : Expr) :
    ReplacementM Bool := do
  trace[translate_detail] "checking whether to translate terms of type `{e}`"
  (← whnfCore e).withApp fun f args ↦ do
  match f with
  | .const n _ =>
    let env ← getEnv
    if args.isEmpty then
      -- A constant not in an application, e.g. `ℕ`, is not translated by default.
      let result := (findTranslation? env t n).isSome && (t.dontTranslateAttr.find? env n).isNone
      trace[translate_detail] "`{f}` is {if result then "not " else ""}a fixed constant."
      return result
    -- A constant in an application, e.g. `Prod` in `α × β`, is translated by default.
    if (t.dontTranslateAttr.find? env n).isSome then
      trace[translate_detail] "`{f}` is a fixed constant."
      return false
    let arg? := match findTranslation? env t n with
      | some { relevantArg := .noArg, .. } => none
      | some { relevantArg := .arg n, .. } => args[n]?
      | none => args[0]?
    if let some arg := arg? then
      shouldTranslate t arg
    else
      trace[translate_detail] "`{f}` is not a fixed constant."
      return true
  | .fvar fvarId =>
    if (← read).contains fvarId then
      trace[translate_detail] "`{f}` is a fixed free variable."
      return false
    trace[translate_detail] "`{f}` is not a fixed free variable."
    modify (·.insert fvarId)
    return true
  | .forallE .. => forallTelescope f fun _ ↦ shouldTranslate t
  | .lam .. => lambdaTelescope f fun _ ↦ shouldTranslate t
  | .sort _ =>
    trace[translate_detail] "`{f}` is a sort, so it is fixed."
    return false
  | _ => return true -- We don't really expect this case to come up in practice.

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
    match f with
    | .proj n i b =>
      let env ← getEnv
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
          if ← shouldTranslate t args[0] then
            -- In this case, we still update all arguments of `g` that are not numerals,
            -- since all other arguments can contain subexpressions like
            -- `(fun x ↦ ℕ) (1 : G)`, and we have to update the `(1 : G)` to `(0 : G)`
            trace[translate_detail] "changing the numeral in this expression to 0."
            let args := args.set 1 (mkRawNatLit 0)
            return mkAppN f (← args.mapM visit)
      let some { translation := n₁, reorder, relevantArg, unfold } ← findPrefixTranslation? n₀ t |
        return mkAppN f (← args.mapM visit)
      -- Use `relevantArg` to test if the head should be translated.
      if let .arg relevantArg := relevantArg then
        if h : relevantArg < args.size then
          unless ← shouldTranslate t args[relevantArg] do
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
      let result := mkAppN f' (← args.mapM visit)
      if unfold then
        unfoldDefinition result
      else
        return result
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
