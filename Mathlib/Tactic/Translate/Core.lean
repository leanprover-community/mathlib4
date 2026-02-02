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
public meta import Mathlib.Data.Array.Defs
public meta import Mathlib.Lean.Meta.Simp
public meta import Mathlib.Tactic.Simps.Basic
public meta import Lean.Meta.CoeAttr
public import Batteries.Lean.NameMapAttribute
public import Batteries.Tactic.Trans
public import Mathlib.Tactic.Eqns
public import Mathlib.Tactic.Simps.Basic
public import Mathlib.Tactic.Translate.GuessName
public meta import Mathlib.Util.MemoFix

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
/--
`(reorder := ...)` reorders the arguments/hypotheses in the generated declaration.
It uses cycle notation. For example `(reorder := α β, 5 6)` swaps the arguments `α` and `β`
with each other and the fifth and the sixth argument, and `(reorder := 3 4 5)` will move
the fifth argument before the third argument. This is used in `to_dual` to swap the arguments in
`≤`, `<` and `⟶`. It is also used in `to_additive` to translate from `a ^ n` to `n • a`.

If the translated declaration already exists (i.e. when using `existing` or `self`), this is
inferred automatically using the function `guessReorder`.
-/
syntax reorderOption := &"reorder" " := " ((ident <|> num)+),*
/--
the `(relevant_arg := ...)` option tells which argument to look at to determine whether to
translate this constant. This is inferred automatically using the function `findRelevantArg`,
but it can also be overwritten using this syntax.

If there are multiple possible arguments, we typically tag the first one.
If this argument contains a fixed type, this declaration will not be translated.
See the Heuristics section of the `to_additive` doc-string for more details.

If a declaration is not tagged, it is presumed that the first argument is relevant.

Use `(relevant_arg := _)` to indicate that there is no relevant argument.

Implementation note: we only allow exactly 1 relevant argument, even though some declarations
(like `Prod.instGroup`) have multiple relevant argument.
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

/-- Linter used by translate attributes that checks if the attribute was already applied -/
register_option linter.translateOverwrite : Bool := {
  defValue := true
  descr := "Linter used by translate attributes that checks if the attribute was already applied" }

/-- Linter used by translate attributes that checks if the attribute is redundant -/
register_option linter.translateRedundant : Bool := {
  defValue := true
  descr := "Linter used by translate attributes that checks if the attribute is redundant" }

/-- `ArgInfo` stores information about how a constant should be translated. -/
structure ArgInfo where
  /-- The arguments that should be reordered when translating, using cycle notation. -/
  reorder : List (List Nat) := []
  /-- The argument used to determine whether this constant should be translated. -/
  relevantArg : Nat := 0
  deriving BEq

/-- `TranslateData` is a structure that holds all data required for a translation attribute. -/
structure TranslateData : Type where
  /-- An attribute that tells that certain arguments of this definition are not
  involved when translating.
  This helps the translation heuristic by also transforming definitions if `ℕ` or another
  fixed type occurs as one of these arguments. -/
  ignoreArgsAttr : NameMapExtension (List Nat)
  /-- `argInfoAttr` stores the declarations that need some extra information to be translated. -/
  argInfoAttr : NameMapExtension ArgInfo
  /-- The global `do_translate`/`dont_translate` attributes specify whether operations on
  a given type should be translated. `dont_translate` can be used for types that are translated,
  such as `MonoidAlgebra` -> `AddMonoidAlgebra`, or for fixed types, such as `Fin n`/`ZMod n`.
  `do_translate` is for types without arguments, like `Unit` and `Empty`, where the structure on it
  can be translated.

  Note: The name generation is not aware of `dont_translate`, so if some part of a lemma is not
    translated thanks to this, you generally have to specify the translated name manually.
  -/
  doTranslateAttr : NameMapExtension Bool
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

attribute [inherit_doc GuessName.GuessNameData] TranslateData.guessNameData

/-- Get the translation for the given name. -/
def findTranslation? (env : Environment) (t : TranslateData) : Name → Option Name :=
  (t.translations.getState env).find?

/-- Get the translation for the given name,
falling back to translating a prefix of the name if the full name can't be translated.
This allows translating automatically generated declarations such as `IsRegular.casesOn`. -/
def findPrefixTranslation (env : Environment) (nm : Name) (t : TranslateData) : Name :=
  nm.mapPrefix fun n ↦ do
    if let some n' := findTranslation? env t n then
      return n'
    if isPrivateName n then
      let n' ← findTranslation? env t (privateToUserName n)
      return mkPrivateName env n'
    none

/-- Compute the `ArgInfo` for the reverse translation. The `reorder` permutation is inverted.
In practice, `relevantArg` does not overlap with `reorder` for dual translations,
so we don't bother applying the permutation to `relevantArg`. -/
def ArgInfo.reverse (i : ArgInfo) : ArgInfo where
  reorder := i.reorder.map (·.reverse)
  relevantArg := i.relevantArg

/-- Add a name translation to the translations map and add the `argInfo` information to `src`.
If the translation attribute is dual, also add the reverse translation. -/
def insertTranslation (t : TranslateData) (src tgt : Name) (argInfo : ArgInfo) (ref : Syntax) :
    CoreM Unit := do
  insertTranslationAux t src tgt argInfo
  if t.isDual && src != tgt then
    insertTranslationAux t tgt src argInfo.reverse
where
  /-- Insert only one direction of a translation. -/
  insertTranslationAux (t : TranslateData) (src tgt : Name)
      (argInfo : ArgInfo) : CoreM Unit := do
    if let some tgt' := findTranslation? (← getEnv) t src then
      -- After `insert_to_additive_translation`, we may end up adding same translation again.
      -- So in that case, don't log a warning.
      if tgt != tgt' then
        Linter.logLintIf linter.translateOverwrite ref
          m!"`{src}` was already translated to `{tgt'}` instead of `{tgt}`.\n\
          Unless the original translation was wrong, please remove this `{t.attrName}` attribute."
    modifyEnv (t.translations.addEntry · (src, tgt))
    trace[translate] "Added translation {src} ↦ {tgt}"
    if argInfo != ((t.argInfoAttr.getState (← getEnv)).find? src).getD {} then
      trace[translate] "@[{t.attrName}] will reorder the arguments of {src} by {argInfo.reorder}."
      trace[translate_detail] "Setting relevant_arg for {src} to be {argInfo.relevantArg}."
      modifyEnv (t.argInfoAttr.addEntry · (src, argInfo))

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
  reorder? : Option (List (List Nat)) := none
  /-- The argument used to determine whether this constant should be translated. -/
  relevantArg? : Option Nat := none
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
  deriving Repr

-- See https://github.com/leanprover/lean4/issues/10295
attribute [nolint unusedArguments] instReprConfig.repr

/-- Eta expands `e` exactly `n` times. -/
def etaExpandN (n : Nat) (e : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType e) (some n) fun xs _ ↦ do
    if xs.size ≠ n then
      throwError "{e} is not a function of arity at least {n}"
    mkLambdaFVars xs (mkAppN e xs)

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
    (dontTranslate : Array FVarId) : Option Expr :=
  let rec visit (e : Expr) (inApp := false) : OptionT (StateM (PtrSet Expr)) Expr := do
    if e.isConst then
      let doTranslate :=
        (t.doTranslateAttr.find? env e.constName!).getD <|
          inApp || (findTranslation? env t e.constName).isSome
      if doTranslate then failure else return e
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
    | .fvar fvarId       => if dontTranslate.contains fvarId then return e else failure
    /- We do not translate the order on `Prop`.
    TODO: We also don't want to translate the category on `Type u`. Unfortunately, replacing
    `.sort 0` with `.sort _` here breaks some uses of `to_additive` on `MonCat`. -/
    | .sort 0            => return e
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
    (dontTranslate : Array FVarId := #[]) : Option Expr :=
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
`applyReplacementFun e` replaces the expression `e` with its translation.
It translates each identifier (inductive type, defined function etc) in an expression, unless
* The identifier occurs in an application with first argument `arg`; and
* `test arg` is false.
However, if `f` is in the dictionary `relevant`, then the argument `relevant.find f`
is tested, instead of the first argument.

It will also reorder arguments of certain functions, using `reorderFn`:
e.g. `g x₁ x₂ x₃ ... xₙ` becomes `g x₂ x₁ x₃ ... xₙ` if `reorderFn g = some [1]`.
-/
partial def applyReplacementFun (t : TranslateData) (e : Expr)
    (dontTranslate : Array FVarId := #[]) : MetaM Expr := do
  let e' ← visit e |>.run {}
  -- Make sure any new reserved names in the expr are realized
  e'.getUsedConstants.forM fun n => do
    if !(← hasConst (skipRealize := false) n) && isReservedName (← getEnv) n then
      executeReservedNameAction n
  return e'
where
  /-- The implementation of this function is based on `Meta.transform`.
  We can't use `Meta.transform`, because that would cause the types of free variables to be
  translated, which would create type-incorrect terms. Instead, we give the free variables
  their original type and the translated type is only used when constructing the final term. -/
  visit (e : Expr) : MonadCacheT ExprStructEq Expr MetaM Expr :=
    checkCache { val := e : ExprStructEq } fun _ => do
    match e with
    | .forallE .. => visitForall e
    | .lam ..     => visitLambda e
    | .letE ..    => visitLet e
    | .mdata _ b  => return e.updateMData! (← visit b)
    | .proj ..    => visitApp e
    | .app ..     => visitApp e
    | .const ..   => visitApp e
    | _           => return e
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
      withTraceNode `translate_detail (fun res => return m!"{exceptEmoji res} replacing at {e}") do
      -- Replace numeral `1` with `0` in applications of `OfNat` and `OfNat.ofNat`.
      if t.changeNumeral && n₀ matches ``OfNat | ``OfNat.ofNat then
        if let some firstArg := args[0]? then
          if shouldTranslate env t firstArg dontTranslate |>.isNone then
            -- In this case, we still update all arguments of `g` that are not numerals,
            -- since all other arguments can contain subexpressions like
            -- `(fun x ↦ ℕ) (1 : G)`, and we have to update the `(1 : G)` to `(0 : G)`
            trace[translate_detail] "applyReplacementFun: We change the numerals in this \
                expression. However, we will still recurse into all the non-numeral arguments."
            let args := args.modify 1 changeNumeral
            return mkAppN f (← args.mapM visit)
      let some n₁ := findTranslation? env t n₀ <|> do
        let n₁ := findPrefixTranslation env n₀ t
        guard (n₀ != n₁ && (isReservedName env n₁ || env.contains n₁)); some n₁
        | return mkAppN f (← args.mapM visit)
      let { reorder, relevantArg } := t.argInfoAttr.find? env n₀ |>.getD {}
      -- Use `relevantArg` to test if the head should be translated.
      if h : relevantArg < args.size then
        if let some fixed := shouldTranslate env t args[relevantArg] dontTranslate then
          trace[translate_detail]
            "The application of {n₀} contains the fixed type {fixed} so it is not changed."
          return mkAppN f (← args.mapM visit)
      -- If the number of arguments is too small for `reorder`, we need to eta expand first
      unless reorder.isEmpty do
        let reorderNumArgs := reorder.flatten.foldl Nat.max 0 + 1
        if reorderNumArgs > args.size then
          let e' ← etaExpandN (reorderNumArgs - args.size) e
          trace[translate_detail] "eta expanded {e} to {e'}"
          return ← visit e'
      let swapUniv := reorder.any (·.contains 0)
      let ls₁ := if swapUniv then ls₀.swapFirstTwo else ls₀
      let args := args.permute! reorder
      trace[translate_detail]"changing {n₀} to {n₁}"
      if swapUniv then
        trace[translate_detail] "reordering the universe variables from {ls₀} to {ls₁}"
      unless reorder.isEmpty do
        trace[translate_detail]
          "reordering the arguments of {n₀} using the cyclic permutations {reorder}"
      return mkAppN (.const n₁ ls₁) (← args.mapM visit)
    | _ => return mkAppN (← visit f) (← args.mapM visit)
  /- In `visitLambda`, `visitForall` and `visitLet`,
  we use a fresh `tmpLCtx : LocalContext` to store the translated types of the free variables.
  This is because the local context in the `MetaM` monad stores their original types. -/
  visitLambda (e : Expr) (fvars : Array Expr := #[]) (tmpLCtx : LocalContext := {}) := do
    if let .lam n d b c := e then
      withLocalDecl n c (d.instantiateRev fvars) fun x => do
        let decl ← getFVarLocalDecl x
        let decl := decl.setType (← visit decl.type)
        visitLambda b (fvars.push x) (tmpLCtx.addDecl decl)
    else
      let e ← visit (e.instantiateRev fvars)
      return tmpLCtx.mkLambda fvars e
  visitForall (e : Expr) (fvars : Array Expr := #[]) (tmpLCtx : LocalContext := {}) := do
    if let .forallE n d b c := e then
      withLocalDecl n c (d.instantiateRev fvars) fun x => do
        let decl ← getFVarLocalDecl x
        let decl := decl.setType (← visit decl.type)
        visitForall b (fvars.push x) (tmpLCtx.addDecl decl)
    else
      let e ← visit (e.instantiateRev fvars)
      return tmpLCtx.mkForall fvars e
  visitLet (e : Expr) (fvars : Array Expr := #[]) (tmpLCtx : LocalContext := {}) := do
    if let .letE n t v b nondep := e then
      withLetDecl n (t.instantiateRev fvars) (v.instantiateRev fvars) (nondep := nondep)
        fun x => do
        let decl ← getFVarLocalDecl x
        let decl := decl.setType (← visit decl.type) |>.setValue (← visit (decl.value true))
        visitLet b (fvars.push x) (tmpLCtx.addDecl decl)
    else
      let e ← visit (e.instantiateRev fvars)
      -- Note that `mkLambda` will make `let` expressions because it will see the `LocalDecl.ldecl`.
      return tmpLCtx.mkLambda (usedLetOnly := false) fvars e

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

/-- Run `applyReplacementFun` on the given `srcDecl` to make a new declaration with name `tgt`. -/
def updateDecl (t : TranslateData) (tgt : Name) (srcDecl : ConstantInfo)
    (reorder : List (List Nat)) (dont : List Nat) : MetaM ConstantInfo := do
  let mut decl := srcDecl.updateName tgt
  if reorder.any (·.contains 0) then
    decl := decl.updateLevelParams decl.levelParams.swapFirstTwo
  decl := decl.updateType <| ← reorderForall reorder <| ← applyReplacementForall t dont <|
    renameBinderNames t decl.type
  if let some v := decl.value? (allowOpaque := true) then
    decl := decl.updateValue <| ← reorderLambda reorder <| ← applyReplacementLambda t dont v
  return decl

/--
Find the argument of `nm` that appears in the first translatable (type-class) argument.
Returns 1 if there are no types with a translatable class as arguments.
E.g. `Prod.instGroup` returns 1, and `Pi.instOne` returns 2.
Note: we only consider the relevant argument (`(relevant_arg := ...)`) of each type-class.
E.g. `[Pow A N]` is a translatable type-class on `A`, not on `N`.
-/
def findRelevantArg (t : TranslateData) (nm : Name) : CoreM Nat := MetaM.run' do
  forallTelescopeReducing (← getConstInfo nm).type fun xs ty ↦ do
    let env ← getEnv
    -- check if `tgt` has a translatable type argument, and if so,
    -- find the index of a type from `xs` appearing in there
    let relevantArg? (tgt : Expr) : Option Nat := do
      let c ← tgt.getAppFn.constName?
      guard (findTranslation? env t c).isSome
      let relevantArg := (t.argInfoAttr.find? env c).elim 0 (·.relevantArg)
      let arg ← tgt.getArg? relevantArg
      xs.findIdx? (arg.containsFVar ·.fvarId!)
    -- run the above check on all hypotheses and on the conclusion
    let arg ← OptionT.run <| xs.firstM fun x ↦ OptionT.mk do
        forallTelescope (← inferType x) fun _ys tgt ↦ return relevantArg? tgt
    let arg := arg <|> relevantArg? ty
    trace[translate_detail] "findRelevantArg: {arg}"
    return arg.getD 0

/-- Unfold `simp` auxlemmas in the type and value.
The reason why we can't just translate them is that they are generated by the `@[simp]` attribute,
so it would require a change in the implementation of `@[simp]` to add these translateions.
Additionally, these lemmas have very short proofs, so unfolding them is not costly. -/
def declUnfoldSimpAuxLemmas (decl : ConstantInfo) : MetaM ConstantInfo := do
  let unfold (e : Expr) := deltaExpand e fun
    | .str _ s => "_simp_".isPrefixOf s
    | _ => false
  let mut decl := decl
  decl := decl.updateType <| ← unfold decl.type
  if let some v := decl.value? (allowOpaque := true) then
    trace[translate] "value before unfold:{indentExpr v}"
    decl := decl.updateValue <| ← unfold v
    trace[translate] "value after unfold:{indentExpr decl.value!}"
  return decl

/-- Find the target name of `src`, which is assumed to have been selected by `findAuxDecls`. -/
def findTargetName (env : Environment) (t : TranslateData) (src pre tgt_pre : Name) :
    CoreM Name := do
  /- This covers auxiliary declarations like `match_i` and `proof_i`. -/
  if let some post := (privateToUserName pre).isPrefixOf? (privateToUserName src) then
    let tgt := tgt_pre ++ post
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

/-- Translate the declaration `src` and recursively all declarations `pre._proof_i`
occurring in `src` using the `translations` dictionary.

`replace_all`, `trace`, `ignore` and `reorder` are configuration options.

`pre` is the declaration that got the translation attribute and `tgt_pre` is the target of this
declaration. -/
partial def transformDeclRec (t : TranslateData) (ref : Syntax) (pre tgt_pre src : Name)
    (dontTranslate : List Nat) (reorder : List (List Nat) := []) : CoreM Unit := do
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
  -- we then transform all auxiliary declarations generated when elaborating `pre`
  for n in ← findAuxDecls srcDecl pre do
    transformDeclRec t ref pre tgt_pre n dontTranslate
  -- expose target body when source body is exposed
  withExporting (isExporting := (← getEnv).setExporting true |>.find? src |>.any (·.hasValue)) do
  -- if the auxiliary declaration doesn't have prefix `pre`, then we have to add this declaration
  -- to the translation dictionary, since otherwise we cannot translate the name.
  let relevantArg ← findRelevantArg t src
  if !pre.isPrefixOf src || src != pre && relevantArg != 0 then
    insertTranslation t src tgt { relevantArg } ref
  -- We still lack a heuristic that automatically infers the `dontTranslate`,
  -- so for now we do a best guess based on argument names.
  let dontTranslate ← if dontTranslate.isEmpty then pure [] else
    if src == pre then pure dontTranslate else
      let namesPre := (← getConstInfo pre).type.getForallBinderNames
      let namesSrc := (← getConstInfo src).type.getForallBinderNames
      pure <| dontTranslate.filterMap (namesPre[·]? >>= namesSrc.idxOf?)
  -- now transform the source declaration
  let trgDecl ← MetaM.run' <| updateDecl t tgt srcDecl reorder dontTranslate
  if src == pre && srcDecl.isThm && trgDecl.type == srcDecl.type then
    Linter.logLintIf linter.translateRedundant ref m!"`{t.attrName}` did not change the type \
      of theorem `{.ofConstName src}`. Please remove the attribute."
  let value := trgDecl.value! (allowOpaque := true)
  trace[translate] "generating\n{tgt} : {trgDecl.type} :=\n  {value}"
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
  try
    -- set `Elab.async` to `false` in order to be able to catch kernel errors
    withOptions (Elab.async.set · false) do
    if isNoncomputable env src then
      addDecl trgDecl.toDeclaration!
      setEnv <| addNoncomputable (← getEnv) tgt
    else
      addAndCompile trgDecl.toDeclaration! (logCompileErrors := (IR.findEnvDecl env src).isSome)
  catch ex =>
    -- Try to emit a better error message if the kernel throws an error.
    try
      withoutExporting <| MetaM.run' <| check value
      throwError "@[{t.attrName}] failed.\n{ex.toMessageData}"
    catch ex =>
      throwError "@[{t.attrName}] failed. \
        The translated value is not type correct. For help, see the docstring \
        of `to_additive`, section `Troubleshooting`. \
        Failed to add declaration\n{tgt}:\n{ex.toMessageData}"
  if let .defnInfo { hints := .abbrev, .. } := trgDecl then
    if (← getReducibilityStatus src) == .reducible then
      setReducibilityStatus tgt .reducible
    if Compiler.getInlineAttribute? (← getEnv) src == some .inline then
      MetaM.run' <| Meta.setInlineAttribute tgt
  -- now add declaration ranges so jump-to-definition works
  -- note: we currently also do this for auxiliary declarations, while they are not normally
  -- generated for those. We could change that.
  addDeclarationRangesFromSyntax tgt (← getRef) ref
  if isProtected (← getEnv) src then
    setEnv <| addProtected (← getEnv) tgt
  if defeqAttr.hasTag (← getEnv) src then
    defeqAttr.setTag tgt
  if let some matcherInfo ← getMatcherInfo? src then
    Match.addMatcherInfo tgt matcherInfo
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
    (t : TranslateData) (names : Array Name) (argInfo : ArgInfo) (desc : String) (ref : Syntax)
    (runAttr : Name → m (Array Name)) : m Unit := do
  let auxLemmas ← names.mapM runAttr
  let nLemmas := auxLemmas[0]!.size
  for (nm, lemmas) in names.zip auxLemmas do
    unless lemmas.size == nLemmas do
      throwError "{names[0]!} and {nm} do not generate the same number of {desc}."
  for (srcLemmas, tgtLemmas) in auxLemmas.zip <| auxLemmas.eraseIdx! 0 do
    for (srcLemma, tgtLemma) in srcLemmas.zip tgtLemmas do
      insertTranslation t srcLemma tgtLemma argInfo ref

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
      if let some tgt := findTranslation? (← getEnv) t src then
        return tgt
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

/-- Try to determine the value of the `(reorder := ...)` option that would be needed to translate
type `e₁` to type `e₂`. If there is no good guess, default to `[]`.
The heuristic that we use is to compare the conclusions of `e₁` and `e₂`,
and to observe which variables are swapped. -/
def guessReorder (src tgt : Expr) : List (List Nat) := Id.run do
  let mut n := 0; let mut src := src; let mut tgt := tgt
  while isDepForall src && isDepForall tgt do
    src := src.bindingBody!
    tgt := tgt.bindingBody!
    n := n + 1
  -- We substitute the loose bound variables with (numbered) free variables,
  -- so that we can keep track of them more easily.
  let vars := Array.ofFn (n := n) (.fvar ⟨.num .anonymous ·⟩)
  src := src.instantiateRev vars
  tgt := tgt.instantiateRev vars
  let mut some map := go src tgt (.replicate n none) | return []
  -- Compute the list of cycles representing the permutation `map`.
  let mut perm := []
  for h : i in 0...n do
    let mut some j := map[i] | continue
    if i = j then continue
    let mut cycle := [i, j]
    repeat do
      let some j' := map[j] | return [] -- If the permutation is malformed, return `[]`.
       -- To avoid computing the same cycle multiple times, and to avoid infinite loops,
       -- we erase visited elements from `map`.
      map := map.set! j none
      if j' = i then break
      j := j'
      cycle := cycle ++ [↑j]
    perm := cycle :: perm
  return perm
where
  /-- Determine whether the given expression is a forall with a dependency.
  If it has no dependency, then we can treat it as the conclusion. -/
  isDepForall : Expr → Bool
    | .forallE _ _ b _ => b.hasLooseBVar 0 || isDepForall b
    | _ => false
  /-- Determine for each `i : Fin n` to what `j : Fin n` it should get translated. -/
  go (src tgt : Expr) {n : Nat} (map : Vector (Option (Fin n)) n) :
      Option (Vector (Option (Fin n)) n) := do
    match src, tgt with
    | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => go d₁ d₂ map >>= go b₁ b₂
    | .lam _ d₁ b₁ _    , .lam _ d₂ b₂ _     => go d₁ d₂ map >>= go b₁ b₂
    | .mdata _ e₁       , .mdata _ e₂        => go e₁ e₂ map
    | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => go t₁ t₂ map >>= go v₁ v₂ >>= go b₁ b₂
    | .app f₁ a₁        , .app f₂ a₂         => go f₁ f₂ map >>= go a₁ a₂
    | .proj _ _ e₁      , .proj _ _ e₂       => go e₁ e₂ map
    | .fvar ⟨.num _ i₁⟩  , .fvar ⟨.num _ i₂⟩  =>
      if h : i₂ < n then
        if let some i₂' := map[i₁]! then
          guard (i₂ == i₂') -- If `i₂ ≠ i₂'`, it's not clear what `i₁` should be translated to.
          some map
        else
          some <| map.set! i₁ (some ⟨i₂, h⟩)
      else
        panic! "index {i₂} is out of bounds ({n})"
    /- To avoid false positives, we do a sanity check to make sure that the two expressions are
    indeed of the same shape. Note that we cannot check for `e₁ == e₁`, because the universes
    in `e₁` and `e₂` might be different (because we decide only later whether to swap them). -/
    | .lit _, .lit _ | .bvar _, .bvar _ | .sort _, .sort _ | .const .., .const .. => some map
    | _, _ => none

/-- Verify that the type of `srcDecl` translates to that of `tgtDecl`.
Also try to autogenerate the `reorder` option for this translation. -/
partial def checkExistingType (t : TranslateData) (src tgt : Name) (cfg : Config) :
    MetaM (List (List Nat)) := withoutExporting do
  let mut srcDecl ← getConstInfo src
  let tgtDecl ← getConstInfo tgt
  unless srcDecl.levelParams.length == tgtDecl.levelParams.length do
    throwError "`{t.attrName}` validation failed:\n  expected {srcDecl.levelParams.length} \
      universe levels, but '{tgt}' has {tgtDecl.levelParams.length} universe levels"
  let srcType ← applyReplacementForall t cfg.dontTranslate srcDecl.type
  let reorder' := guessReorder srcType tgtDecl.type
  trace[translate_detail] "The guessed reorder is {reorder'}"
  let reorder ←
    if let some reorder := cfg.reorder? then
      -- check whether the permutations are equal by running both on `(0...=max).toArray`
      if let some max := reorder.flatten.max? then
        if reorder'.flatten.max? == max then
          let range : Array Nat := (0...=max).toArray
          if range.permute! reorder == range.permute! reorder' then
            Linter.logLintIf linter.translateReorder cfg.ref m!"\
              `{t.attrName}` correctly autogenerated the `(reorder := ...)` argument for {src}.\n\
              You may remove the `(reorder := ...)` argument."
      pure reorder
    else
      pure reorder'
  if cfg.self && reorder.isEmpty then
    Linter.logLintIf linter.translateRedundant cfg.ref m!"\
      `{t.attrName} self` is redundant when none of the arguments are reordered.\n\
      Please remove the attribute, or provide an explicit `(reorder := ...)` argument.\n\
      If you need to give a hint to `{t.attrName}` to translate expressions involving `{src}`,\n\
      use `{t.attrName}_do_translate` instead"
  let srcType ← reorderForall reorder srcType
  if reorder.any (·.contains 0) then
    srcDecl := srcDecl.updateLevelParams srcDecl.levelParams.swapFirstTwo
  -- instantiate both types with the same universes. `instantiateLevelParams` does some
  -- normalization, so we apply it to both types.
  let srcType := srcType.instantiateLevelParams
    srcDecl.levelParams (tgtDecl.levelParams.map mkLevelParam)
  let tgtType := tgtDecl.type.instantiateLevelParams
    tgtDecl.levelParams (tgtDecl.levelParams.map mkLevelParam)
  unless ← withReducible <| isDefEq srcType tgtType do
    throwError "`{t.attrName}` validation failed: expected{indentExpr srcType}\nbut '{tgt}' has \
      type{indentExpr tgtType}"
  return reorder

/-- if `f src = #[a_1, ..., a_n]` and `f tgt = #[b_1, ... b_n]` then `proceedFieldsAux src tgt f`
will insert translations from `a_i` to `b_i`. -/
def proceedFieldsAux (t : TranslateData) (src tgt : Name) (argInfo : ArgInfo) (ref : Syntax)
    (f : Name → Array Name) : CoreM Unit := do
  let srcFields := f src
  let tgtFields := f tgt
  if srcFields.size != tgtFields.size then
    throwError "Failed to map fields of {src}, {tgt} with {srcFields} ↦ {tgtFields}.\n \
      Lengths do not match."
  for srcField in srcFields, tgtField in tgtFields do
    insertTranslation t srcField tgtField argInfo ref

/-- Add the structure fields of `src` to the translations dictionary
so that they will be translated correctly. -/
def proceedFields (t : TranslateData) (src tgt : Name) (argInfo : ArgInfo) (ref : Syntax) :
    CoreM Unit := do
  let env ← getEnv
  let aux := proceedFieldsAux t src tgt argInfo ref
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

/-- Elaborate syntax that refers to an argument of the declaration.
This is either a 1-indexed number, or a name from `argNames`.
`args` is only used to add hover information to `stx`,
and `declName` is only used for the error message. -/
def elabArgStx (declName : Name) (argNames : Array Name) (args : Array Expr)
    (stx : TSyntax [`ident, `num]) : MetaM Nat := do
  let n ← match stx with
    | `($name:ident) => match argNames.idxOf? name.getId with
      | some n => pure n
      | none => throwErrorAt stx
        "invalid argument '{stx}', it is not an argument of '{.ofConstName declName}'."
    | `($n:num) =>
      if n.getNat = 0 then
        throwErrorAt stx "invalid index `{stx}`, arguments are counted starting from 1."
      if n.getNat > args.size then
        throwErrorAt stx "index `{stx}` is out of bounds, there are only `{args.size}` arguments"
      pure (n.getNat - 1)
    | _ => throwUnsupportedSyntax
  Elab.Term.addTermInfo' stx args[n]! |>.run'
  return n

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
      | `(bracketedOption| (reorder := $[$[$reorders]*],*)) =>
        if reorder?.isSome then
          throwErrorAt opt "cannot specify `reorder` multiple times"
        reorder? ← reorders.toList.mapM fun cycle => do
          if h : cycle.size = 1 then
            throwErrorAt cycle[0].raw "\
              invalid cycle `{cycle[0]}`, a cycle must have at least 2 elements.\n\
              `(reorder := ...)` uses cycle notation to specify a permutation.\n\
              For example `(reorder := 1 2, 5 6)` swaps the first two arguments with each other \
              and the fifth and the sixth argument and `(reorder := 3 4 5)` will move \
              the fifth argument before the third argument."
          cycle.toList.mapM (elabArgStx declName argNames xs)
      | `(bracketedOption| (relevant_arg := $n)) =>
        if relevantArg?.isSome then
          throwErrorAt opt "cannot specify `relevant_arg` multiple times"
        else
          if let `($_:hole) := n then
            relevantArg? := some 1000000 -- set `relevantArg?` to be out of bounds
          else
            relevantArg? ← elabArgStx declName argNames xs ⟨n.raw⟩
      | `(bracketedOption| (dont_translate := $[$types]*)) =>
        dontTranslate := dontTranslate ++ (← types.toList.mapM (elabArgStx declName argNames xs))
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
    trace[translate_detail] "attributes: {attrs}; reorder arguments: {reorder?}"
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
partial def applyAttributes (t : TranslateData) (cfg : Config) (src tgt : Name)
    (argInfo : ArgInfo) : TermElabM (Array Name) := withoutExporting do
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
    withRef attr.stx do withLogging do
    if attr.name == `simps then
      translateLemmas t allDecls argInfo "simps lemmas" cfg.ref (simpsTacFromSyntax · attr.stx)
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
  -- The equation lemmas can only be related if the value of `tgt` is the translated value of `src`.
  unless cfg.existing do
    if let some eqns := eqnsAttribute.find? (← getEnv) src then
      unless (eqnsAttribute.find? (← getEnv) tgt).isSome do
        for eqn in eqns do
          _ ← addTranslationAttr t eqn cfg
        eqnsAttribute.add tgt (eqns.map (findTranslation? (← getEnv) t · |>.get!))
    else
      /- We need to generate all equation lemmas for `src` and `tgt`, even for non-recursive
      definitions. If we don't do that, the equation lemma for `src` might be generated later
      when doing a `rw`, but it won't be generated for `tgt`. -/
      translateLemmas t #[src, tgt] argInfo "equation lemmas" cfg.ref fun nm ↦
        (·.getD #[]) <$> MetaM.run' (getEqnsFor? nm)
  applyAttributes t cfg src tgt argInfo |>.run'.run'

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
  let alreadyExists := (← getEnv).contains tgt
  if cfg.existing != alreadyExists && !(← isInductive src) && !cfg.self then
    Linter.logLintIf linter.translateExisting cfg.ref <|
      if alreadyExists then
        m!"The translated declaration already exists. Please specify this explicitly using \
           `@[{t.attrName} existing]`."
      else
        "The translated declaration doesn't exist. Please remove the option `existing`."
  let reorder ←
    if alreadyExists then
      MetaM.run' <| checkExistingType t src tgt cfg
    else
      pure (cfg.reorder?.getD [])
  let relevantArg ← cfg.relevantArg?.getDM <| findRelevantArg t src
  let argInfo := { reorder, relevantArg }
  insertTranslation t src tgt argInfo cfg.ref
  if alreadyExists then
    -- since `tgt` already exists, we just need to
    -- add translations `src.x ↦ tgt.x'` for any subfields.
    trace[translate_detail] "declaration {tgt} already exists."
    proceedFields t src tgt argInfo cfg.ref
  else
    -- tgt doesn't exist, so let's make it
    transformDeclRec t cfg.ref src tgt src cfg.dontTranslate argInfo.reorder
  let nestedNames ← copyMetaData t cfg src tgt argInfo
  -- add pop-up information when mousing over the given translated name
  -- (the information will be over the attribute if no translated name is given)
  Term.addTermInfo' cfg.ref (← mkConstWithLevelParams tgt) (isBinder := !alreadyExists)
    |>.run' |>.run'
  if let some doc := cfg.doc then
    addDocStringCore tgt doc
  return nestedNames.push tgt

end

end Mathlib.Tactic.Translate
