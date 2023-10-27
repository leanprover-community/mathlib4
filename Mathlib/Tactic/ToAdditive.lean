/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn, Jon Eugster
-/
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Data.String.Defs
import Mathlib.Data.Array.Defs
import Mathlib.Data.KVMap
import Mathlib.Lean.Expr.ReplaceRec
import Mathlib.Lean.EnvExtension
import Mathlib.Lean.Meta.Simp
import Std.Lean.NameMapAttribute
import Std.Data.Option.Basic
import Std.Tactic.CoeExt -- just to copy the attribute
import Std.Tactic.Ext.Attr -- just to copy the attribute
import Std.Tactic.Lint -- useful to lint this file and for for DiscrTree.elements
import Std.Tactic.Relation.Rfl -- just to copy the attribute
import Std.Tactic.Relation.Symm -- just to copy the attribute
import Mathlib.Tactic.Relation.Trans -- just to copy the attribute
import Mathlib.Tactic.Eqns -- just to copy the attribute
import Mathlib.Tactic.Simps.Basic

/-!
# The `@[to_additive]` attribute.

The attribute `to_additive` can be used to automatically transport theorems
and definitions (but not inductive types and structures) from a multiplicative
theory to an additive theory.
-/

set_option autoImplicit true

open Lean Meta Elab Command Std

/-- The `to_additive_ignore_args` attribute. -/
syntax (name := to_additive_ignore_args) "to_additive_ignore_args" (ppSpace num)* : attr
/-- The `to_additive_relevant_arg` attribute. -/
syntax (name := to_additive_relevant_arg) "to_additive_relevant_arg " num : attr
/-- The `to_additive_reorder` attribute. -/
syntax (name := to_additive_reorder) "to_additive_reorder " (num+),+ : attr
/-- The `to_additive_change_numeral` attribute. -/
syntax (name := to_additive_change_numeral) "to_additive_change_numeral" (ppSpace num)* : attr
/-- An `attr := ...` option for `to_additive`. -/
syntax toAdditiveAttrOption := &"attr" " := " Parser.Term.attrInstance,*
/-- A `reorder := ...` option for `to_additive`. -/
syntax toAdditiveReorderOption := &"reorder" " := " (num+),+
/-- Options to `to_additive`. -/
syntax toAdditiveParenthesizedOption := "(" toAdditiveAttrOption <|> toAdditiveReorderOption ")"
/-- Options to `to_additive`. -/
syntax toAdditiveOption := toAdditiveParenthesizedOption <|> &"existing"
/-- Remaining arguments of `to_additive`. -/
syntax toAdditiveRest := (ppSpace toAdditiveOption)* (ppSpace ident)? (ppSpace str)?
/-- The `to_additive` attribute. -/
syntax (name := to_additive) "to_additive" "?"? toAdditiveRest : attr

/-- The `to_additive` attribute. -/
macro "to_additive?" rest:toAdditiveRest : attr => `(attr| to_additive ? $rest)

/-- A set of strings of names that end in a capital letter.
* If the string contains a lowercase letter, the string should be split between the first occurrence
  of a lower-case letter followed by an upper-case letter.
* If multiple strings have the same prefix, they should be grouped by prefix
* In this case, the second list should be prefix-free
  (no element can be a prefix of a later element)

Todo: automate the translation from `String` to an element in this `RBMap`
  (but this would require having something similar to the `rb_lmap` from Lean 3). -/
def endCapitalNames : Lean.RBMap String (List String) compare :=
  -- todo: we want something like
  -- endCapitalNamesOfList ["LE", "LT", "WF", "CoeTC", "CoeT", "CoeHTCT"]
  .ofList [("LE", [""]), ("LT", [""]), ("WF", [""]), ("Coe", ["TC", "T", "HTCT"])]

/--
This function takes a String and splits it into separate parts based on the following
(naming conventions)[https://github.com/leanprover-community/mathlib4/wiki#naming-convention].

E.g. `#eval "InvHMulLEConjugate₂SMul_ne_top".splitCase` yields
`["Inv", "HMul", "LE", "Conjugate₂", "SMul", "_", "ne", "_", "top"]`.
-/
partial def String.splitCase (s : String) (i₀ : Pos := 0) (r : List String := []) : List String :=
Id.run do
  -- We test if we need to split between `i₀` and `i₁`.
  let i₁ := s.next i₀
  if s.atEnd i₁ then
    -- If `i₀` is the last position, return the list.
    let r := s::r
    return r.reverse
  /- We split the string in three cases
  * We split on both sides of `_` to keep them there when rejoining the string;
  * We split after a name in `endCapitalNames`;
  * We split after a lower-case letter that is followed by an upper-case letter
    (unless it is part of a name in `endCapitalNames`). -/
  if s.get i₀ == '_' || s.get i₁ == '_' then
    return splitCase (s.extract i₁ s.endPos) 0 <| (s.extract 0 i₁)::r
  if (s.get i₁).isUpper then
    if let some strs := endCapitalNames.find? (s.extract 0 i₁) then
      if let some (pref, newS) := strs.findSome?
        fun x : String ↦ (s.extract i₁ s.endPos).dropPrefix? x |>.map (x, ·.toString) then
        return splitCase newS 0 <| (s.extract 0 i₁ ++ pref)::r
    if !(s.get i₀).isUpper then
      return splitCase (s.extract i₁ s.endPos) 0 <| (s.extract 0 i₁)::r
  return splitCase s i₁ r

namespace ToAdditive

initialize registerTraceClass `to_additive
initialize registerTraceClass `to_additive_detail

/-- Linter to check that the `reorder` attribute is not given manually -/
register_option linter.toAdditiveReorder : Bool := {
  defValue := true
  descr := "Linter to check that the reorder attribute is not given manually." }

/-- Linter, mostly used by `@[to_additive]`, that checks that the source declaration doesn't have
certain attributes -/
register_option linter.existingAttributeWarning : Bool := {
  defValue := true
  descr := "Linter, mostly used by `@[to_additive]`, that checks that the source declaration " ++
    "doesn't have certain attributes" }

/-- Linter to check that the `to_additive` attribute is not given manually -/
register_option linter.toAdditiveGenerateName : Bool := {
  defValue := true
  descr := "Linter used by `@[to_additive]` that checks if `@[to_additive]` automatically " ++
    "generates the user-given name" }

/-- Linter to check whether the user correctly specified that the additive declaration already
exists -/
register_option linter.toAdditiveExisting : Bool := {
  defValue := true
  descr := "Linter used by `@[to_additive]` that checks whether the user correctly specified that
    the additive declaration already exists" }


/--
An attribute that tells `@[to_additive]` that certain arguments of this definition are not
involved when using `@[to_additive]`.
This helps the heuristic of `@[to_additive]` by also transforming definitions if `ℕ` or another
fixed type occurs as one of these arguments.
-/
initialize ignoreArgsAttr : NameMapExtension (List Nat) ←
  registerNameMapAttribute {
    name  := `to_additive_ignore_args
    descr :=
      "Auxiliary attribute for `to_additive` stating that certain arguments are not additivized."
    add   := fun _ stx ↦ do
        let ids ← match stx with
          | `(attr| to_additive_ignore_args $[$ids:num]*) => pure <| ids.map (·.1.isNatLit?.get!)
          | _ => throwUnsupportedSyntax
        return ids.toList }

/--
An attribute that stores all the declarations that needs their arguments reordered when
applying `@[to_additive]`. It is applied automatically by the `(reorder := ...)` syntax of
`to_additive`, and should not usually be added manually.
-/
initialize reorderAttr : NameMapExtension (List $ List Nat) ←
  registerNameMapAttribute {
    name := `to_additive_reorder
    descr :=
      "Auxiliary attribute for `to_additive` that stores arguments that need to be reordered.
        This should not appear in any file.
        We keep it as an attribute for now so that mathport can still use it, and it can generate a
        warning."
    add := fun
    | _, stx@`(attr| to_additive_reorder $[$[$reorders:num]*],*) => do
      Linter.logLintIf linter.toAdditiveReorder stx
        m!"Using this attribute is deprecated. Use `@[to_additive (reorder := <num>)]` {""
        }instead.\nThat will also generate the additive version with the arguments swapped, {""
        }so you are probably able to remove the manually written additive declaration."
      pure <| reorders.toList.map (·.toList.map (·.raw.isNatLit?.get! - 1))
    | _, _ => throwUnsupportedSyntax }

/--
An attribute that is automatically added to declarations tagged with `@[to_additive]`, if needed.

This attribute tells which argument is the type where this declaration uses the multiplicative
structure. If there are multiple argument, we typically tag the first one.
If this argument contains a fixed type, this declaration will note be additivized.
See the Heuristics section of `to_additive.attr` for more details.

If a declaration is not tagged, it is presumed that the first argument is relevant.
`@[to_additive]` uses the function `to_additive.first_multiplicative_arg` to automatically tag
declarations. It is ok to update it manually if the automatic tagging made an error.

Implementation note: we only allow exactly 1 relevant argument, even though some declarations
(like `prod.group`) have multiple arguments with a multiplicative structure on it.
The reason is that whether we additivize a declaration is an all-or-nothing decision, and if
we will not be able to additivize declarations that (e.g.) talk about multiplication on `ℕ × α`
anyway.

Warning: interactions between this and the `(reorder := ...)` argument are not well-tested.
-/
initialize relevantArgAttr : NameMapExtension Nat ←
  registerNameMapAttribute {
    name := `to_additive_relevant_arg
    descr := "Auxiliary attribute for `to_additive` stating" ++
      " which arguments are the types with a multiplicative structure."
    add := fun
    | _, `(attr| to_additive_relevant_arg $id) => pure <| id.1.isNatLit?.get!.pred
    | _, _ => throwUnsupportedSyntax }

/--
An attribute that stores all the declarations that deal with numeric literals on variable types.

Numeral literals occur in expressions without type information, so in order to decide whether `1`
needs to be changed to `0`, the context around the numeral is relevant.
Most numerals will be in an `OfNat.ofNat` application, though tactics can add numeral literals
inside arbitrary functions. By default we assume that we do not change numerals, unless it is
in a function application with the `to_additive_change_numeral` attribute.

`@[to_additive_change_numeral n₁ ...]` should be added to all functions that take one or more
numerals as argument that should be changed if `additiveTest` succeeds on the first argument,
i.e. when the numeral is only translated if the first argument is a variable
(or consists of variables).
The arguments `n₁ ...` are the positions of the numeral arguments (starting counting from 1).
-/
initialize changeNumeralAttr : NameMapExtension (List Nat) ←
  registerNameMapAttribute {
    name := `to_additive_change_numeral
    descr :=
      "Auxiliary attribute for `to_additive` that stores functions that have numerals as argument."
    add := fun
    | _, `(attr| to_additive_change_numeral $[$arg]*) =>
      pure <| arg.map (·.1.isNatLit?.get!.pred) |>.toList
    | _, _ => throwUnsupportedSyntax }

/-- Maps multiplicative names to their additive counterparts. -/
initialize translations : NameMapExtension Name ← registerNameMapExtension _

/-- Get the multiplicative → additive translation for the given name. -/
def findTranslation? (env : Environment) : Name → Option Name :=
  (ToAdditive.translations.getState env).find?

/-- Add a (multiplicative → additive) name translation to the translations map. -/
def insertTranslation (src tgt : Name) (failIfExists := true) : CoreM Unit := do
  if let some tgt' := findTranslation? (← getEnv) src then
    if failIfExists then
      throwError "The translation {src} ↦ {tgt'} already exists"
    else
      trace[to_additive] "The translation {src} ↦ {tgt'} already exists"
      return
  modifyEnv (ToAdditive.translations.addEntry · (src, tgt))
  trace[to_additive] "Added translation {src} ↦ {tgt}"

/-- `Config` is the type of the arguments that can be provided to `to_additive`. -/
structure Config : Type where
  /-- View the trace of the to_additive procedure.
  Equivalent to `set_option trace.to_additive true`. -/
  trace : Bool := false
  /-- The name of the target (the additive declaration).-/
  tgt : Name := Name.anonymous
  /-- An optional doc string.-/
  doc : Option String := none
  /-- If `allowAutoName` is `false` (default) then
  `@[to_additive]` will check whether the given name can be auto-generated. -/
  allowAutoName : Bool := false
  /-- The arguments that should be reordered by `to_additive`, using cycle notation. -/
  reorder : List (List Nat) := []
  /-- The attributes which we want to give to both the multiplicative and additive versions.
  For certain attributes (such as `simp` and `simps`) this will also add generated lemmas to the
  translation dictionary. -/
  attrs : Array Syntax := #[]
  /-- The `Syntax` element corresponding to the original multiplicative declaration
  (or the `to_additive` attribute if it is added later),
  which we need for adding definition ranges. -/
  ref : Syntax
  /-- An optional flag stating whether the additive declaration already exists.
    If this flag is set but wrong about whether the additive declaration exists, `to_additive` will
    raise a linter error.
    Note: the linter will never raise an error for inductive types and structures. -/
  existing : Option Bool := none
  deriving Repr

variable [Monad M] [MonadOptions M] [MonadEnv M]

open Lean.Expr.FindImpl in
/-- Implementation function for `additiveTest`.
  We cache previous applications of the function, using the same method that `Expr.find?` uses,
  to avoid visiting the same subexpression many times. Note that we only need to cache the
  expressions without taking the value of `inApp` into account, since `inApp` only matters when
  the expression is a constant. However, for this reason we have to make sure that we never
  cache constant expressions, so that's why the `if`s in the implementation are in this order.

  Note that this function is still called many times by `applyReplacementFun`
  and we're not remembering the cache between these calls. -/
unsafe def additiveTestUnsafe (findTranslation? : Name → Option Name)
  (ignore : Name → Option (List ℕ)) (e : Expr) : Option Name :=
  let rec visit (e : Expr) (inApp := false) : OptionT FindM Name := do
    if e.isConst then
      if inApp || (findTranslation? e.constName).isSome then
        failure
      else
        return e.constName
    checkVisited e
    match e with
    | x@(.app e a)       =>
        visit e true <|> do
          -- make sure that we don't treat `(fun x => α) (n + 1)` as a type that depends on `Nat`
          guard !x.isConstantApplication
          if let some n := e.getAppFn.constName? then
            if let some l := ignore n then
              if e.getAppNumArgs + 1 ∈ l then
                failure
          visit a
    | .lam _ _ t _       => visit t
    | .forallE _ _ t _   => visit t
    | .letE _ _ e body _ => visit e <|> visit body
    | .mdata _ b         => visit b
    | .proj _ _ b        => visit b
    | _                  => failure
  Id.run <| (visit e).run' mkPtrSet

/--
`additiveTest e` tests whether the expression `e` contains a constant
`nm` that is not applied to any arguments, and such that `translations.find?[nm] = none`.
This is used in `@[to_additive]` for deciding which subexpressions to transform: we only transform
constants if `additiveTest` applied to their first argument returns `true`.
This means we will replace expression applied to e.g. `α` or `α × β`, but not when applied to
e.g. `ℕ` or `ℝ × α`.
We ignore all arguments specified by the `ignore` `NameMap`.
-/
def additiveTest (findTranslation? : Name → Option Name)
    (ignore : Name → Option (List ℕ)) (e : Expr) : Option Name :=
  unsafe additiveTestUnsafe findTranslation? ignore e

/-- Swap the first two elements of a list -/
def _root_.List.swapFirstTwo {α : Type _} : List α → List α
  | []      => []
  | [x]     => [x]
  | x::y::l => y::x::l

/-- Change the numeral `nat_lit 1` to the numeral `nat_lit 0`.
Leave all other expressions unchanged. -/
def changeNumeral : Expr → Expr
  | .lit (.natVal 1) => mkRawNatLit 0
  | e                => e

/--
`applyReplacementFun e` replaces the expression `e` with its additive counterpart.
It translates each identifier (inductive type, defined function etc) in an expression, unless
* The identifier occurs in an application with first argument `arg`; and
* `test arg` is false.
However, if `f` is in the dictionary `relevant`, then the argument `relevant.find f`
is tested, instead of the first argument.

It will also reorder arguments of certain functions, using `reorderFn`:
e.g. `g x₁ x₂ x₃ ... xₙ` becomes `g x₂ x₁ x₃ ... xₙ` if `reorderFn g = some [1]`.
-/
def applyReplacementFun (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let reorderFn : Name → List (List ℕ) := fun nm ↦ (reorderAttr.find? env nm |>.getD [])
  let relevantArg : Name → ℕ := fun nm ↦ (relevantArgAttr.find? env nm).getD 0
  return aux
      (findTranslation? <| ← getEnv) reorderFn (ignoreArgsAttr.find? env)
      (changeNumeralAttr.find? env) relevantArg (← getBoolOption `trace.to_additive_detail) e
where /-- Implementation of `applyReplacementFun`. -/
  aux (findTranslation? : Name → Option Name)
    (reorderFn : Name → List (List ℕ)) (ignore : Name → Option (List ℕ))
    (changeNumeral? : Name → Option (List Nat)) (relevantArg : Name → ℕ) (trace : Bool) :
    Expr → Expr :=
  Lean.Expr.replaceRec fun r e ↦ Id.run do
    if trace then
      dbg_trace s!"replacing at {e}"
    match e with
    | .const n₀ ls₀ => do
      let n₁ := n₀.mapPrefix findTranslation?
      let ls₁ : List Level := if 0 ∈ (reorderFn n₀).join then ls₀.swapFirstTwo else ls₀
      if trace then
        if n₀ != n₁ then
          dbg_trace s!"changing {n₀} to {n₁}"
        if 0 ∈ (reorderFn n₀).join then
          dbg_trace s!"reordering the universe variables from {ls₀} to {ls₁}"
      return some <| Lean.mkConst n₁ ls₁
    | .app g x => do
      let gf := g.getAppFn
      if gf.isBVar && x.isLit then
        if trace then
          dbg_trace s!"applyReplacementFun: Variables applied to numerals are not changed {g.app x}"
        return some <| g.app x
      let gArgs := g.getAppArgs
      let mut gAllArgs := gArgs.push x
      let (gfAdditive, gAllArgsAdditive) ←
        if let some nm := gf.constName? then
          -- e = `(nm y₁ .. yₙ x)
          /- Test if the head should not be replaced. -/
          let relevantArgId := relevantArg nm
          let gfAdditive :=
            if relevantArgId < gAllArgs.size && gf.isConst then
              if let some fxd := additiveTest findTranslation? ignore gAllArgs[relevantArgId]! then
                Id.run <| do
                  if trace then
                    dbg_trace s!"The application of {nm} contains the fixed type {fxd
                      }, so it is not changed"
                  gf
              else
                r gf
            else
              r gf
          /- Test if arguments should be reordered. -/
          let reorder := reorderFn nm
          if !reorder.isEmpty && relevantArgId < gAllArgs.size &&
            (additiveTest findTranslation? ignore gAllArgs[relevantArgId]!).isNone then
            gAllArgs := gAllArgs.permute! reorder
            if trace then
              dbg_trace s!"reordering the arguments of {nm} using the cyclic permutations {reorder}"
          /- Do not replace numerals in specific types. -/
          let firstArg := gAllArgs[0]!
          if let some changedArgNrs := changeNumeral? nm then
            if additiveTest findTranslation? ignore firstArg |>.isNone then
              if trace then
                dbg_trace s!"applyReplacementFun: We change the numerals in this expression. {
                  ""}However, we will still recurse into all the non-numeral arguments."
              -- In this case, we still update all arguments of `g` that are not numerals,
              -- since all other arguments can contain subexpressions like
              -- `(fun x ↦ ℕ) (1 : G)`, and we have to update the `(1 : G)` to `(0 : G)`
              gAllArgs := gAllArgs.mapIdx fun argNr arg ↦
                if changedArgNrs.contains argNr then
                  changeNumeral arg
                else
                  arg
          pure <| (gfAdditive, ← gAllArgs.mapM r)
        else
          pure (← r gf, ← gAllArgs.mapM r)
      return some <| mkAppN gfAdditive gAllArgsAdditive
    | .proj n₀ idx e => do
      let n₁ := n₀.mapPrefix findTranslation?
      if trace then
        dbg_trace s!"applyReplacementFun: in projection {e}.{idx} of type {n₀}, {""
          }replace type with {n₁}"
      return some <| .proj n₁ idx <| ← r e
    | _ => return none

/-- Eta expands `e` at most `n` times.-/
def etaExpandN (n : Nat) (e : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType e) (some n) fun xs _ ↦ mkLambdaFVars xs (mkAppN e xs)

/-- `e.expand` eta-expands all expressions that have as head a constant `n` in
`reorder`. They are expanded until they are applied to one more argument than the maximum in
`reorder.find n`. -/
def expand (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let reorderFn : Name → List (List ℕ) := fun nm ↦ (reorderAttr.find? env nm |>.getD [])
  let e₂ ← Lean.Meta.transform (input := e) (post := fun e => return .done e) <| fun e ↦ do
    let e0 := e.getAppFn
    let es := e.getAppArgs
    let some e0n := e0.constName? | return .continue
    let reorder := reorderFn e0n
    if reorder.isEmpty then
      -- no need to expand if nothing needs reordering
      return .continue
    let needed_n := reorder.join.foldr Nat.max 0 + 1
    -- the second disjunct is a temporary fix to avoid infinite loops.
    -- We may need to use `replaceRec` or something similar to not change the head of an application
    if needed_n ≤ es.size || es.size == 0 then
      return .continue
    else
      -- in this case, we need to reorder arguments that are not yet
      -- applied, so first η-expand the function.
      let e' ← etaExpandN (needed_n - es.size) e
      trace[to_additive_detail] "expanded {e} to {e'}"
      return .continue e'
  if e != e₂ then
    trace[to_additive_detail] "expand:\nBefore: {e}\nAfter:  {e₂}"
  return e₂

/-- Reorder pi-binders. See doc of `reorderAttr` for the interpretation of the argument -/
def reorderForall (src : Expr) (reorder : List (List Nat) := []) : MetaM Expr := do
  if reorder == [] then
    return src
  forallTelescope src fun xs e => do
    mkForallFVars (xs.permute! reorder) e

/-- Reorder lambda-binders. See doc of `reorderAttr` for the interpretation of the argument -/
def reorderLambda (src : Expr) (reorder : List (List Nat) := []) : MetaM Expr := do
  if reorder == [] then
    return src
  lambdaTelescope src fun xs e => do
    mkLambdaFVars (xs.permute! reorder) e

/-- Run applyReplacementFun on the given `srcDecl` to make a new declaration with name `tgt` -/
def updateDecl (tgt : Name) (srcDecl : ConstantInfo) (reorder : List (List Nat) := []) :
    MetaM ConstantInfo := do
  let mut decl := srcDecl.updateName tgt
  if 0 ∈ reorder.join then
    decl := decl.updateLevelParams decl.levelParams.swapFirstTwo
  decl := decl.updateType <| ← applyReplacementFun <| ← reorderForall (← expand decl.type) reorder
  if let some v := decl.value? then
    decl := decl.updateValue <| ← applyReplacementFun <| ← reorderLambda (← expand v) reorder
  else if let .opaqueInfo info := decl then -- not covered by `value?`
    decl := .opaqueInfo { info with
      value := ← applyReplacementFun <| ← reorderLambda (← expand info.value) reorder }
  return decl

/-- Find the target name of `pre` and all created auxiliary declarations. -/
def findTargetName (env : Environment) (src pre tgt_pre : Name) : CoreM Name :=
  /- This covers auxiliary declarations like `match_i` and `proof_i`. -/
  if let some post := pre.isPrefixOf? src then
    return tgt_pre ++ post
  /- This covers equation lemmas (for other declarations). -/
  else if let some post := privateToUserName? src then
    match findTranslation? env post.getPrefix with
    -- this is an equation lemma for a declaration without `to_additive`. We will skip this.
    | none => return src
    -- this is an equation lemma for a declaration with `to_additive`. We will additivize this.
    -- Note: if this errors we could do this instead by calling `getEqnsFor?`
    | some addName => return src.updatePrefix <| mkPrivateName env addName
  -- Note: this additivizes lemmas generated by `simp`.
  -- Todo: we do not currently check whether such lemmas actually should be additivized.
  else if let some post := env.mainModule ++ `_auxLemma |>.isPrefixOf? src then
    return env.mainModule ++ `_auxAddLemma ++ post
  else if src.hasMacroScopes then
    mkFreshUserName src.eraseMacroScopes
  else
    throwError "internal @[to_additive] error."

/-- Returns a `NameSet` of all auxiliary constants in `e` that might have been generated
when adding `pre` to the environment.
Examples include `pre.match_5`, `Mathlib.MyFile._auxLemma.3` and
`_private.Mathlib.MyFile.someOtherNamespace.someOtherDeclaration._eq_2`.
The last two examples may or may not have been generated by this declaration.
The last example may or may not be the equation lemma of a declaration with the `@[to_additive]`
attribute. We will only translate it has the `@[to_additive]` attribute.
-/
def findAuxDecls (e : Expr) (pre mainModule : Name) : NameSet :=
  let auxLemma := mainModule ++ `_auxLemma
  e.foldConsts ∅ fun n l ↦
    if n.getPrefix == pre || n.getPrefix == auxLemma || isPrivateName n || n.hasMacroScopes then
      l.insert n
    else
      l

/-- transform the declaration `src` and all declarations `pre._proof_i` occurring in `src`
using the transforms dictionary.
`replace_all`, `trace`, `ignore` and `reorder` are configuration options.
`pre` is the declaration that got the `@[to_additive]` attribute and `tgt_pre` is the target of this
declaration. -/
partial def transformDeclAux
    (cfg : Config) (pre tgt_pre : Name) : Name → CoreM Unit := fun src ↦ do
  let env ← getEnv
  trace[to_additive_detail] "visiting {src}"
  -- if we have already translated this declaration, we do nothing.
  if (findTranslation? env src).isSome && src != pre then
      return
  -- if this declaration is not `pre` and not an internal declaration, we return an error,
  -- since we should have already translated this declaration.
  if src != pre && !src.isInternal' then
    throwError "The declaration {pre} depends on the declaration {src} which is in the namespace {
      pre}, but does not have the `@[to_additive]` attribute. This is not supported.\n{""
      }Workaround: move {src} to a different namespace."
  -- we find the additive name of `src`
  let tgt ← findTargetName env src pre tgt_pre
  -- we skip if we already transformed this declaration before.
  if env.contains tgt then
    if tgt == src then
      -- Note: this can happen for equation lemmas of declarations without `@[to_additive]`.
      trace[to_additive_detail] "Auxiliary declaration {src} will be translated to itself."
    else
      trace[to_additive_detail] "Already visited {tgt} as translation of {src}."
    return
  let srcDecl ← getConstInfo src
  -- we first transform all auxiliary declarations generated when elaborating `pre`
  for n in findAuxDecls srcDecl.type pre env.mainModule do
    transformDeclAux cfg pre tgt_pre n
  if let some value := srcDecl.value? then
    for n in findAuxDecls value pre env.mainModule do
      transformDeclAux cfg pre tgt_pre n
  if let .opaqueInfo {value, ..} := srcDecl then
    for n in findAuxDecls value pre env.mainModule do
      transformDeclAux cfg pre tgt_pre n
  -- if the auxiliary declaration doesn't have prefix `pre`, then we have to add this declaration
  -- to the translation dictionary, since otherwise we cannot find the additive name.
  if !pre.isPrefixOf src then
    insertTranslation src tgt
  -- now transform the source declaration
  let trgDecl : ConstantInfo ←
    MetaM.run' <| updateDecl tgt srcDecl <| if src == pre then cfg.reorder else []
  let value ← match trgDecl with
    | .thmInfo { value, .. } | .defnInfo { value, .. } | .opaqueInfo { value, .. } => pure value
    | _ => throwError "Expected {tgt} to have a value."
  trace[to_additive] "generating\n{tgt} : {trgDecl.type} :=\n  {value}"
  try
    -- make sure that the type is correct,
    -- and emit a more helpful error message if it fails
    discard <| MetaM.run' <| inferType value
  catch
    | Exception.error _ msg => throwError "@[to_additive] failed.
      Type mismatch in additive declaration. For help, see the docstring
      of `to_additive.attr`, section `Troubleshooting`.
      Failed to add declaration\n{tgt}:\n{msg}"
    | _ => panic! "unreachable"
  if isNoncomputable env src then
    addDecl trgDecl.toDeclaration!
    setEnv $ addNoncomputable (← getEnv) tgt
  else
    addAndCompile trgDecl.toDeclaration!
  -- now add declaration ranges so jump-to-definition works
  -- note: we currently also do this for auxiliary declarations, while they are not normally
  -- generated for those. We could change that.
  addDeclarationRanges tgt {
    range := ← getDeclarationRange (← getRef)
    selectionRange := ← getDeclarationRange cfg.ref }
  if isProtected (← getEnv) src then
    setEnv $ addProtected (← getEnv) tgt

/-- Copy the instance attribute in a `to_additive`

[todo] it seems not to work when the `to_additive` is added as an attribute later. -/
def copyInstanceAttribute (src tgt : Name) : CoreM Unit := do
  if (← isInstance src) then
    let prio := (← getInstancePriority? src).getD 100
    let attr_kind := (← getInstanceAttrKind? src).getD .global
    trace[to_additive_detail] "Making {tgt} an instance with priority {prio}."
    addInstance tgt attr_kind prio |>.run'

/-- Warn the user when the multiplicative declaration has an attribute. -/
def warnExt [Inhabited σ] (stx : Syntax) (ext : PersistentEnvExtension α β σ) (f : σ → Name → Bool)
    (thisAttr attrName src tgt : Name) : CoreM Unit := do
  if f (ext.getState (← getEnv)) src then
    Linter.logLintIf linter.existingAttributeWarning stx <|
      m!"The source declaration {src} was given attribute {attrName} before calling @[{thisAttr}]. {
      ""}The preferred method is to use `@[{thisAttr} (attr := {attrName})]` to apply the {
      ""}attribute to both {src} and the target declaration {tgt}." ++
      if thisAttr == `to_additive then
      m!"\nSpecial case: If this declaration was generated by @[to_additive] {
      ""}itself, you can use @[to_additive (attr := to_additive, {attrName})] on the original {
      ""}declaration." else ""

/-- Warn the user when the multiplicative declaration has a simple scoped attribute. -/
def warnAttr [Inhabited β] (stx : Syntax) (attr : SimpleScopedEnvExtension α β)
    (f : β → Name → Bool) (thisAttr attrName src tgt : Name) : CoreM Unit :=
warnExt stx attr.ext (f ·.stateStack.head!.state ·) thisAttr attrName src tgt

/-- Warn the user when the multiplicative declaration has a parametric attribute. -/
def warnParametricAttr (stx : Syntax) (attr : ParametricAttribute β)
    (thisAttr attrName src tgt : Name) : CoreM Unit :=
warnExt stx attr.ext (·.contains ·) thisAttr attrName src tgt

/-- `runAndAdditivize names desc t` runs `t` on all elements of `names`
and adds translations between the generated lemmas (the output of `t`).
`names` must be non-empty. -/
def additivizeLemmas [Monad m] [MonadError m] [MonadLiftT CoreM m]
    (names : Array Name) (desc : String) (t : Name → m (Array Name)) : m Unit := do
  let auxLemmas ← names.mapM t
  let nLemmas := auxLemmas[0]!.size
  for (nm, lemmas) in names.zip auxLemmas do
    unless lemmas.size == nLemmas do
      throwError "{names[0]!} and {nm} do not generate the same number of {desc}."
  for (srcLemmas, tgtLemmas) in auxLemmas.zip <| auxLemmas.eraseIdx 0 do
    for (srcLemma, tgtLemma) in srcLemmas.zip tgtLemmas do
      insertTranslation srcLemma tgtLemma

/--
Find the first argument of `nm` that has a multiplicative type-class on it.
Returns 1 if there are no types with a multiplicative class as arguments.
E.g. `Prod.Group` returns 1, and `Pi.One` returns 2.
Note: we only consider the first argument of each type-class.
E.g. `[Pow A N]` is a multiplicative type-class on `A`, not on `N`.
-/
def firstMultiplicativeArg (nm : Name) : MetaM Nat := do
  forallTelescopeReducing (← getConstInfo nm).type fun xs _ ↦ do
    -- xs are the arguments to the constant
    let xs := xs.toList
    let l ← xs.filterMapM fun x ↦ do
      -- x is an argument and i is the index
      -- write `x : (y₀ : α₀) → ... → (yₙ : αₙ) → tgt_fn tgt_args₀ ... tgt_argsₘ`
      forallTelescopeReducing (← inferType x) fun _ys tgt ↦ do
        let (_tgt_fn, tgt_args) := tgt.getAppFnArgs
        if let some c := tgt.getAppFn.constName? then
          if findTranslation? (← getEnv) c |>.isNone then
            return none
        return tgt_args[0]?.bind fun tgtArg ↦
          xs.findIdx? fun x ↦ Expr.containsFVar tgtArg x.fvarId!
    trace[to_additive_detail] "firstMultiplicativeArg: {l}"
    match l with
    | [] => return 0
    | (head :: tail) => return tail.foldr Nat.min head

/-- Helper for `capitalizeLike`. -/
partial def capitalizeLikeAux (s : String) (i : String.Pos := 0) (p : String) : String :=
  if p.atEnd i || s.atEnd i then
    p
  else
    let j := p.next i
    if (s.get i).isLower then
      capitalizeLikeAux s j <| p.set i (p.get i |>.toLower)
    else if (s.get i).isUpper then
      capitalizeLikeAux s j <| p.set i (p.get i |>.toUpper)
    else
      capitalizeLikeAux s j p

/-- Capitalizes `s` char-by-char like `r`. If `s` is longer, it leaves the tail untouched. -/
def capitalizeLike (r : String) (s : String) :=
  capitalizeLikeAux r 0 s

/-- Capitalize First element of a list like `s`.
Note that we need to capitalize multiple characters in some cases,
in examples like `HMul` or `hAdd`. -/
def capitalizeFirstLike (s : String) : List String → List String
  | x :: r => capitalizeLike s x :: r
  | [] => []

/--
Dictionary used by `guessName` to autogenerate names.

Note: `guessName` capitalizes first element of the output according to
capitalization of the input. Input and first element should therefore be lower-case,
2nd element should be capitalized properly.
-/
def nameDict : String → List String
  | "one"         => ["zero"]
  | "mul"         => ["add"]
  | "smul"        => ["vadd"]
  | "inv"         => ["neg"]
  | "div"         => ["sub"]
  | "prod"        => ["sum"]
  | "hmul"        => ["hadd"]
  | "hsmul"       => ["hvadd"]
  | "hdiv"        => ["hsub"]
  | "hpow"        => ["hsmul"]
  | "finprod"     => ["finsum"]
  | "pow"         => ["nsmul"]
  | "npow"        => ["nsmul"]
  | "zpow"        => ["zsmul"]
  | "monoid"      => ["add", "Monoid"]
  | "submonoid"   => ["add", "Submonoid"]
  | "group"       => ["add", "Group"]
  | "subgroup"    => ["add", "Subgroup"]
  | "semigroup"   => ["add", "Semigroup"]
  | "magma"       => ["add", "Magma"]
  | "haar"        => ["add", "Haar"]
  | "prehaar"     => ["add", "Prehaar"]
  | "unit"        => ["add", "Unit"]
  | "units"       => ["add", "Units"]
  | "rootable"    => ["divisible"]
  | x             => [x]

/--
Turn each element to lower-case, apply the `nameDict` and
capitalize the output like the input.
-/
def applyNameDict : List String → List String
  | x :: s => (capitalizeFirstLike x (nameDict x.toLower)) ++ applyNameDict s
  | [] => []

/--
There are a few abbreviations we use. For example "Nonneg" instead of "ZeroLE"
or "addComm" instead of "commAdd".
Note: The input to this function is case sensitive!
Todo: A lot of abbreviations here are manual fixes and there might be room to
      improve the naming logic to reduce the size of `fixAbbreviation`.
-/
def fixAbbreviation : List String → List String
  | "cancel" :: "Add" :: s            => "addCancel" :: fixAbbreviation s
  | "Cancel" :: "Add" :: s            => "AddCancel" :: fixAbbreviation s
  | "left" :: "Cancel" :: "Add" :: s  => "addLeftCancel" :: fixAbbreviation s
  | "Left" :: "Cancel" :: "Add" :: s  => "AddLeftCancel" :: fixAbbreviation s
  | "right" :: "Cancel" :: "Add" :: s => "addRightCancel" :: fixAbbreviation s
  | "Right" :: "Cancel" :: "Add" :: s => "AddRightCancel" :: fixAbbreviation s
  | "cancel" :: "Comm" :: "Add" :: s  => "addCancelComm" :: fixAbbreviation s
  | "Cancel" :: "Comm" :: "Add" :: s  => "AddCancelComm" :: fixAbbreviation s
  | "comm" :: "Add" :: s              => "addComm" :: fixAbbreviation s
  | "Comm" :: "Add" :: s              => "AddComm" :: fixAbbreviation s
  | "Zero" :: "LE" :: s               => "Nonneg" :: fixAbbreviation s
  | "zero" :: "_" :: "le" :: s        => "nonneg" :: fixAbbreviation s
  | "Zero" :: "LT" :: s               => "Pos" :: fixAbbreviation s
  | "zero" :: "_" :: "lt" :: s        => "pos" :: fixAbbreviation s
  | "LE" :: "Zero" :: s               => "Nonpos" :: fixAbbreviation s
  | "le" :: "_" :: "zero" :: s        => "nonpos" :: fixAbbreviation s
  | "LT" :: "Zero" :: s               => "Neg" :: fixAbbreviation s
  | "lt" :: "_" :: "zero" :: s        => "neg" :: fixAbbreviation s
  | "Add" :: "Single" :: s            => "Single" :: fixAbbreviation s
  | "add" :: "Single" :: s            => "single" :: fixAbbreviation s
  | "add" :: "_" :: "single" :: s     => "single" :: fixAbbreviation s
  | "Add" :: "Support" :: s           => "Support" :: fixAbbreviation s
  | "add" :: "Support" :: s           => "support" :: fixAbbreviation s
  | "add" :: "_" :: "support" :: s    => "support" :: fixAbbreviation s
  | "Add" :: "TSupport" :: s          => "TSupport" :: fixAbbreviation s
  | "add" :: "TSupport" :: s          => "tsupport" :: fixAbbreviation s
  | "add" :: "_" :: "tsupport" :: s   => "tsupport" :: fixAbbreviation s
  | "Add" :: "Indicator" :: s         => "Indicator" :: fixAbbreviation s
  | "add" :: "Indicator" :: s         => "indicator" :: fixAbbreviation s
  | "add" :: "_" :: "indicator" :: s  => "indicator" :: fixAbbreviation s
  | "is" :: "Square" :: s             => "even" :: fixAbbreviation s
  | "Is" :: "Square" :: s             => "Even" :: fixAbbreviation s
  -- "Regular" is well-used in mathlib3 with various meanings (e.g. in
  -- measure theory) and a direct translation
  -- "regular" --> ["add", "Regular"] in `nameDict` above seems error-prone.
  | "is" :: "Regular" :: s            => "isAddRegular" :: fixAbbreviation s
  | "Is" :: "Regular" :: s            => "IsAddRegular" :: fixAbbreviation s
  | "is" :: "Left" :: "Regular" :: s  => "isAddLeftRegular" :: fixAbbreviation s
  | "Is" :: "Left" :: "Regular" :: s  => "IsAddLeftRegular" :: fixAbbreviation s
  | "is" :: "Right" :: "Regular" :: s => "isAddRightRegular" :: fixAbbreviation s
  | "Is" :: "Right" :: "Regular" :: s => "IsAddRightRegular" :: fixAbbreviation s
  -- the capitalization heuristic of `applyNameDict` doesn't work in the following cases
  | "HSmul" :: s                      => "HSMul" :: fixAbbreviation s -- from `HPow`
  | "NSmul" :: s                      => "NSMul" :: fixAbbreviation s -- from `NPow`
  | "Nsmul" :: s                      => "NSMul" :: fixAbbreviation s -- from `Pow`
  | "ZSmul" :: s                      => "ZSMul" :: fixAbbreviation s -- from `ZPow`
  | "neg" :: "Fun" :: s               => "invFun" :: fixAbbreviation s
  | "Neg" :: "Fun" :: s               => "InvFun" :: fixAbbreviation s
  | "unique" :: "Prods" :: s          => "uniqueSums" :: fixAbbreviation s
  | "Unique" :: "Prods" :: s          => "UniqueSums" :: fixAbbreviation s
  | "order" :: "Of" :: s              => "addOrderOf" :: fixAbbreviation s
  | "Order" :: "Of" :: s              => "AddOrderOf" :: fixAbbreviation s
  | "is"::"Of"::"Fin"::"Order"::s     => "isOfFinAddOrder" :: fixAbbreviation s
  | "Is"::"Of"::"Fin"::"Order"::s     => "IsOfFinAddOrder" :: fixAbbreviation s
  | "is" :: "Central" :: "Scalar" :: s  => "isCentralVAdd" :: fixAbbreviation s
  | "Is" :: "Central" :: "Scalar" :: s  => "IsCentralVAdd" :: fixAbbreviation s
  | x :: s                            => x :: fixAbbreviation s
  | []                                => []

/--
Autogenerate additive name.
This runs in several steps:
1) Split according to capitalisation rule and at `_`.
2) Apply word-by-word translation rules.
3) Fix up abbreviations that are not word-by-word translations, like "addComm" or "Nonneg".
-/
def guessName : String → String :=
  String.mapTokens '\'' <|
  fun s =>
    String.join <|
    fixAbbreviation <|
    applyNameDict <|
    s.splitCase

/-- Return the provided target name or autogenerate one if one was not provided. -/
def targetName (cfg : Config) (src : Name) : CoreM Name := do
  let .str pre s := src | throwError "to_additive: can't transport {src}"
  trace[to_additive_detail] "The name {s} splits as {s.splitCase}"
  let tgt_auto := guessName s
  let depth := cfg.tgt.getNumParts
  let pre := pre.mapPrefix <| findTranslation? (← getEnv)
  let (pre1, pre2) := pre.splitAt (depth - 1)
  if cfg.tgt == pre2.str tgt_auto && !cfg.allowAutoName && cfg.tgt != src then
    Linter.logLintIf linter.toAdditiveGenerateName cfg.ref
      m!"to_additive correctly autogenerated target name for {src}. {"\n"
      }You may remove the explicit argument {cfg.tgt}."
  let res := if cfg.tgt == .anonymous then pre.str tgt_auto else pre1 ++ cfg.tgt
  -- we allow translating to itself if `tgt == src`, which is occasionally useful for `additiveTest`
  if res == src && cfg.tgt != src then
    throwError "to_additive: can't transport {src} to itself."
  if cfg.tgt != .anonymous then
    trace[to_additive_detail] "The automatically generated name would be {pre.str tgt_auto}"
  return res

/-- if `f src = #[a_1, ..., a_n]` and `f tgt = #[b_1, ... b_n]` then `proceedFieldsAux src tgt f`
  will insert translations from `src.a_i` to `tgt.b_i`. -/
def proceedFieldsAux (src tgt : Name) (f : Name → CoreM (Array Name)) : CoreM Unit := do
  let srcFields ← f src
  let tgtFields ← f tgt
  if srcFields.size != tgtFields.size then
    throwError "Failed to map fields of {src}, {tgt} with {srcFields} ↦ {tgtFields}"
  for (srcField, tgtField) in srcFields.zip tgtFields do
    if srcField != tgtField then
      insertTranslation (src ++ srcField) (tgt ++ tgtField)
    else
      trace[to_additive] "Translation {src ++ srcField} ↦ {tgt ++ tgtField} is automatic."

/-- Add the structure fields of `src` to the translations dictionary
so that future uses of `to_additive` will map them to the corresponding `tgt` fields. -/
def proceedFields (src tgt : Name) : CoreM Unit := do
  let aux := proceedFieldsAux src tgt
  aux fun declName ↦ do
    if isStructure (← getEnv) declName then
      return getStructureFields (← getEnv) declName
    else
      return #[]
  aux fun declName ↦ do match (← getEnv).find? declName with
    | some (ConstantInfo.inductInfo {ctors := ctors, ..}) => return ctors.toArray.map (·.getString)
    | _ => pure #[]

/-- Elaboration of the configuration options for `to_additive`. -/
def elabToAdditive : Syntax → CoreM Config
  | `(attr| to_additive%$tk $[?%$trace]? $[$opts:toAdditiveOption]* $[$tgt]? $[$doc]?) => do
    let mut attrs := #[]
    let mut reorder := []
    let mut existing := some false
    for stx in opts do
      match stx with
      | `(toAdditiveOption| (attr := $[$stxs],*)) =>
        attrs := attrs ++ stxs
      | `(toAdditiveOption| (reorder := $[$[$reorders:num]*],*)) =>
        reorder := reorder ++ reorders.toList.map (·.toList.map (·.raw.isNatLit?.get! - 1))
      | `(toAdditiveOption| existing) =>
        existing := some true
      | _ => throwUnsupportedSyntax
    reorder := reorder.reverse
    trace[to_additive_detail] "attributes: {attrs}; reorder arguments: {reorder}"
    return { trace := trace.isSome
             tgt := match tgt with | some tgt => tgt.getId | none => Name.anonymous
             doc := doc.bind (·.raw.isStrLit?)
             allowAutoName := false
             attrs
             reorder
             existing
             ref := (tgt.map (·.raw)).getD tk }
  | _ => throwUnsupportedSyntax

mutual
/-- Apply attributes to the multiplicative and additive declarations. -/
partial def applyAttributes (stx : Syntax) (rawAttrs : Array Syntax) (thisAttr src tgt : Name) :
  TermElabM (Array Name) := do
  -- we only copy the `instance` attribute, since `@[to_additive] instance` is nice to allow
  copyInstanceAttribute src tgt
  -- Warn users if the multiplicative version has an attribute
  if linter.existingAttributeWarning.get (← getOptions) then
    let appliedAttrs ← getAllSimpAttrs src
    if appliedAttrs.size > 0 then
      Linter.logLintIf linter.existingAttributeWarning stx <|
        m!"The source declaration {src} was given the simp-attribute(s) {appliedAttrs} before {
        ""}calling @[{thisAttr}]. The preferred method is to use {
        ""}`@[{thisAttr} (attr := {appliedAttrs})]` to apply the attribute to both {
        src} and the target declaration {tgt}."
    warnAttr stx Std.Tactic.Ext.extExtension
      (fun b n => (b.tree.values.any fun t => t.declName = n)) thisAttr `ext src tgt
    warnAttr stx Std.Tactic.reflExt (·.values.contains ·) thisAttr `refl src tgt
    warnAttr stx Std.Tactic.symmExt (·.values.contains ·) thisAttr `symm src tgt
    warnAttr stx Mathlib.Tactic.transExt (·.values.contains ·) thisAttr `trans src tgt
    warnAttr stx Std.Tactic.Coe.coeExt (·.contains ·) thisAttr `coe src tgt
    warnParametricAttr stx Lean.Linter.deprecatedAttr thisAttr `deprecated src tgt
    -- the next line also warns for `@[to_additive, simps]`, because of the application times
    warnParametricAttr stx simpsAttr thisAttr `simps src tgt
    warnExt stx Term.elabAsElim.ext (·.contains ·) thisAttr `elab_as_elim src tgt
  -- add attributes
  -- the following is similar to `Term.ApplyAttributesCore`, but we hijack the implementation of
  -- `simp`, `simps` and `to_additive`.
  let attrs ← elabAttrs rawAttrs
  let (additiveAttrs, attrs) := attrs.partition (·.name == `to_additive)
  let nestedDecls ←
    match additiveAttrs.size with
      | 0 => pure #[]
      | 1 => addToAdditiveAttr tgt (← elabToAdditive additiveAttrs[0]!.stx) additiveAttrs[0]!.kind
      | _ => throwError "cannot apply {thisAttr} multiple times."
  let allDecls := #[src, tgt] ++ nestedDecls
  if attrs.size > 0 then
    trace[to_additive_detail] "Applying attributes {attrs.map (·.stx)} to {allDecls}"
  for attr in attrs do
    withRef attr.stx do withLogging do
    -- todo: also support other simp-attributes,
    -- and attributes that generate simp-attributes, like `norm_cast`
    if attr.name == `simp then
      additivizeLemmas allDecls "simp lemmas"
        (Meta.Simp.addSimpAttrFromSyntax · simpExtension attr.kind attr.stx)
      return
    if attr.name == `simps then
      additivizeLemmas allDecls "simps lemmas" (simpsTacFromSyntax · attr.stx)
      return
    let env ← getEnv
    match getAttributeImpl env attr.name with
    | Except.error errMsg => throwError errMsg
    | Except.ok attrImpl  =>
      let runAttr := do
        attrImpl.add src attr.stx attr.kind
        attrImpl.add tgt attr.stx attr.kind
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
partial def copyMetaData (cfg : Config) (src tgt : Name) : CoreM (Array Name) := do
  if let some eqns := eqnsAttribute.find? (← getEnv) src then
    unless (eqnsAttribute.find? (← getEnv) tgt).isSome do
      for eqn in eqns do _ ← addToAdditiveAttr eqn cfg
      eqnsAttribute.add tgt (eqns.map (findTranslation? (← getEnv) · |>.get!))
  else
    /- We need to generate all equation lemmas for `src` and `tgt`, even for non-recursive
    definitions. If we don't do that, the equation lemma for `src` might be generated later
    when doing a `rw`, but it won't be generated for `tgt`. -/
    additivizeLemmas #[src, tgt] "equation lemmas" fun nm ↦
      (·.getD #[]) <$> MetaM.run' (getEqnsFor? nm true)
  MetaM.run' <| Elab.Term.TermElabM.run' <|
    applyAttributes cfg.ref cfg.attrs `to_additive src tgt

/--
Make a new copy of a declaration, replacing fragments of the names of identifiers in the type and
the body using the `translations` dictionary.
This is used to implement `@[to_additive]`.
-/
partial def transformDecl (cfg : Config) (src tgt : Name) : CoreM (Array Name) := do
  transformDeclAux cfg src tgt src
  copyMetaData cfg src tgt

/-- `addToAdditiveAttr src cfg` adds a `@[to_additive]` attribute to `src` with configuration `cfg`.
See the attribute implementation for more details.
It returns an array with names of additive declarations (usually 1, but more if there are nested
`to_additive` calls. -/
partial def addToAdditiveAttr (src : Name) (cfg : Config) (kind := AttributeKind.global) :
  AttrM (Array Name) := do
  if (kind != AttributeKind.global) then
    throwError "`to_additive` can only be used as a global attribute"
  withOptions (· |>.updateBool `trace.to_additive (cfg.trace || ·)) <| do
  let tgt ← targetName cfg src
  let alreadyExists := (← getEnv).contains tgt
  if cfg.existing == some !alreadyExists && !(← isInductive src) then
    Linter.logLintIf linter.toAdditiveExisting cfg.ref <|
      if alreadyExists then
        m!"The additive declaration already exists. Please specify this explicitly using {
          ""}`@[to_additive existing]`."
      else
        "The additive declaration doesn't exist. Please remove the option `existing`."
  if cfg.reorder != [] then
    trace[to_additive] "@[to_additive] will reorder the arguments of {tgt}."
    reorderAttr.add src cfg.reorder
    -- we allow using this attribute if it's only to add the reorder configuration
    if findTranslation? (← getEnv) src |>.isSome then
      return #[tgt]
  let firstMultArg ← MetaM.run' <| firstMultiplicativeArg src
  if firstMultArg != 0 then
    trace[to_additive_detail] "Setting relevant_arg for {src} to be {firstMultArg}."
    relevantArgAttr.add src firstMultArg
  insertTranslation src tgt alreadyExists
  let nestedNames ←
    if alreadyExists then
      -- since `tgt` already exists, we just need to copy metadata and
      -- add translations `src.x ↦ tgt.x'` for any subfields.
      trace[to_additive_detail] "declaration {tgt} already exists."
      proceedFields src tgt
      copyMetaData cfg src tgt
    else
      -- tgt doesn't exist, so let's make it
      transformDecl cfg src tgt
  -- add pop-up information when mousing over `additive_name` of `@[to_additive additive_name]`
  -- (the information will be over the attribute of no additive name is given)
  pushInfoLeaf <| .ofTermInfo {
    elaborator := .anonymous, lctx := {}, expectedType? := none, isBinder := !alreadyExists,
    stx := cfg.ref, expr := ← mkConstWithLevelParams tgt }
  if let some doc := cfg.doc then
    addDocString tgt doc
  return nestedNames.push tgt

end

/--
The attribute `to_additive` can be used to automatically transport theorems
and definitions (but not inductive types and structures) from a multiplicative
theory to an additive theory.

To use this attribute, just write:

```
@[to_additive]
theorem mul_comm' {α} [CommSemigroup α] (x y : α) : x * y = y * x := mul_comm x y
```

This code will generate a theorem named `add_comm'`. It is also
possible to manually specify the name of the new declaration:

```
@[to_additive add_foo]
theorem foo := sorry
```

An existing documentation string will _not_ be automatically used, so if the theorem or definition
has a doc string, a doc string for the additive version should be passed explicitly to
`to_additive`.

```
/-- Multiplication is commutative -/
@[to_additive "Addition is commutative"]
theorem mul_comm' {α} [comm_semigroup α] (x y : α) : x * y = y * x := comm_semigroup.mul_comm
```

The transport tries to do the right thing in most cases using several
heuristics described below.  However, in some cases it fails, and
requires manual intervention.

Use the `(reorder := ...)` syntax to reorder the arguments in the generated additive declaration.
This is specified using cycle notation. For example `(reorder := 1 2, 5 6)` swaps the first two
arguments with each other and the fifth and the sixth argument and `(reorder := 3 4 5)` will move
the fifth argument before the third argument. This is mostly useful to translate declarations using
`Pow` to those using `SMul`.

Use the `(attr := ...)` syntax to apply attributes to both the multiplicative and the additive
version:

```
@[to_additive (attr := simp)] lemma mul_one' {G : Type*} [group G] (x : G) : x * 1 = x := mul_one x
```

For `simp` and `simps` this also ensures that some generated lemmas are added to the additive
dictionary.
`@[to_additive (attr := to_additive)]` is a special case, where the `to_additive`
attribute is added to the generated lemma only, to additivize it again.
This is useful for lemmas about `Pow` to generate both lemmas about `SMul` and `VAdd`. Example:
```
@[to_additive (attr := to_additive VAdd_lemma, simp) SMul_lemma]
lemma Pow_lemma ... :=
```
In the above example, the `simp` is added to all 3 lemmas. All other options to `to_additive`
(like the generated name or `(reorder := ...)`) are not passed down,
and can be given manually to each individual `to_additive` call.

## Implementation notes

The transport process generally works by taking all the names of
identifiers appearing in the name, type, and body of a declaration and
creating a new declaration by mapping those names to additive versions
using a simple string-based dictionary and also using all declarations
that have previously been labeled with `to_additive`.

In the `mul_comm'` example above, `to_additive` maps:
* `mul_comm'` to `add_comm'`,
* `comm_semigroup` to `add_comm_semigroup`,
* `x * y` to `x + y` and `y * x` to `y + x`, and
* `comm_semigroup.mul_comm'` to `add_comm_semigroup.add_comm'`.

### Heuristics

`to_additive` uses heuristics to determine whether a particular identifier has to be
mapped to its additive version. The basic heuristic is

* Only map an identifier to its additive version if its first argument doesn't
  contain any unapplied identifiers.

Examples:
* `@Mul.mul Nat n m` (i.e. `(n * m : Nat)`) will not change to `+`, since its
  first argument is `Nat`, an identifier not applied to any arguments.
* `@Mul.mul (α × β) x y` will change to `+`. It's first argument contains only the identifier
  `prod`, but this is applied to arguments, `α` and `β`.
* `@Mul.mul (α × Int) x y` will not change to `+`, since its first argument contains `Int`.

The reasoning behind the heuristic is that the first argument is the type which is "additivized",
and this usually doesn't make sense if this is on a fixed type.

There are some exceptions to this heuristic:

* Identifiers that have the `@[to_additive]` attribute are ignored.
  For example, multiplication in `↥Semigroup` is replaced by addition in `↥AddSemigroup`.
* If an identifier `d` has attribute `@[to_additive_relevant_arg n]` then the argument
  in position `n` is checked for a fixed type, instead of checking the first argument.
  `@[to_additive]` will automatically add the attribute `@[to_additive_relevant_arg n]` to a
  declaration when the first argument has no multiplicative type-class, but argument `n` does.
* If an identifier has attribute `@[to_additive_ignore_args n1 n2 ...]` then all the arguments in
  positions `n1`, `n2`, ... will not be checked for unapplied identifiers (start counting from 1).
  For example, `ContMDiffMap` has attribute `@[to_additive_ignore_args 21]`, which means
  that its 21st argument `(n : WithTop ℕ)` can contain `ℕ`
  (usually in the form `Top.top ℕ ...`) and still be additivized.
  So `@Mul.mul (C^∞⟮I, N; I', G⟯) _ f g` will be additivized.

### Troubleshooting

If `@[to_additive]` fails because the additive declaration raises a type mismatch, there are
various things you can try.
The first thing to do is to figure out what `@[to_additive]` did wrong by looking at the type
mismatch error.

* Option 1: The most common case is that it didn't additivize a declaration that should be
  additivized. This happened because the heuristic applied, and the first argument contains a
  fixed type, like `ℕ` or `ℝ`. However, the heuristic misfires on some other declarations.
  Solutions:
  * First figure out what the fixed type is in the first argument of the declaration that didn't
    get additivized. Note that this fixed type can occur in implicit arguments. If manually finding
    it is hard, you can run `set_option trace.to_additive_detail true` and search the output for the
    fragment "contains the fixed type" to find what the fixed type is.
  * If the fixed type has an additive counterpart (like `↥Semigroup`), give it the `@[to_additive]`
    attribute.
  * If the fixed type has nothing to do with algebraic operations (like `TopCat`), add the attribute
    `@[to_additive existing Foo]` to the fixed type `Foo`.
  * If the fixed type occurs inside the `k`-th argument of a declaration `d`, and the
    `k`-th argument is not connected to the multiplicative structure on `d`, consider adding
    attribute `[to_additive_ignore_args k]` to `d`.
    Example: `ContMDiffMap` ignores the argument `(n : WithTop ℕ)`
* Option 2: It additivized a declaration `d` that should remain multiplicative. Solution:
  * Make sure the first argument of `d` is a type with a multiplicative structure. If not, can you
    reorder the (implicit) arguments of `d` so that the first argument becomes a type with a
    multiplicative structure (and not some indexing type)?
    The reason is that `@[to_additive]` doesn't additivize declarations if their first argument
    contains fixed types like `ℕ` or `ℝ`. See section Heuristics.
    If the first argument is not the argument with a multiplicative type-class, `@[to_additive]`
    should have automatically added the attribute `@[to_additive_relevant_arg]` to the declaration.
    You can test this by running the following (where `d` is the full name of the declaration):
    ```
      open Lean in run_cmd logInfo m!"{ToAdditive.relevantArgAttr.find? (← getEnv) `d}"
    ```
    The expected output is `n` where the `n`-th (0-indexed) argument of `d` is a type (family)
    with a multiplicative structure on it. `none` means `0`.
    If you get a different output (or a failure), you could add the attribute
    `@[to_additive_relevant_arg n]` manually, where `n` is an (1-indexed) argument with a
    multiplicative structure.
* Option 3: Arguments / universe levels are incorrectly ordered in the additive version.
  This likely only happens when the multiplicative declaration involves `pow`/`^`. Solutions:
  * Ensure that the order of arguments of all relevant declarations are the same for the
    multiplicative and additive version. This might mean that arguments have an "unnatural" order
    (e.g. `Monoid.npow n x` corresponds to `x ^ n`, but it is convenient that `Monoid.npow` has this
    argument order, since it matches `AddMonoid.nsmul n x`.
  * If this is not possible, add `(reorder := ...)` argument to `to_additive`.

If neither of these solutions work, and `to_additive` is unable to automatically generate the
additive version of a declaration, manually write and prove the additive version.
Often the proof of a lemma/theorem can just be the multiplicative version of the lemma applied to
`multiplicative G`.
Afterwards, apply the attribute manually:

```
attribute [to_additive foo_add_bar] foo_bar
```

This will allow future uses of `to_additive` to recognize that
`foo_bar` should be replaced with `foo_add_bar`.

### Handling of hidden definitions

Before transporting the “main” declaration `src`, `to_additive` first
scans its type and value for names starting with `src`, and transports
them. This includes auxiliary definitions like `src._match_1`,
`src._proof_1`.

In addition to transporting the “main” declaration, `to_additive` transports
its equational lemmas and tags them as equational lemmas for the new declaration.

### Structure fields and constructors

If `src` is a structure, then the additive version has to be already written manually.
In this case `to_additive` adds all structure fields to its mapping.

### Name generation

* If `@[to_additive]` is called without a `name` argument, then the
  new name is autogenerated.  First, it takes the longest prefix of
  the source name that is already known to `to_additive`, and replaces
  this prefix with its additive counterpart. Second, it takes the last
  part of the name (i.e., after the last dot), and replaces common
  name parts (“mul”, “one”, “inv”, “prod”) with their additive versions.

* [todo] Namespaces can be transformed using `map_namespace`. For example:
  ```
  run_cmd to_additive.map_namespace `quotient_group `quotient_add_group
  ```

  Later uses of `to_additive` on declarations in the `quotient_group`
  namespace will be created in the `quotient_add_group` namespaces.

* If `@[to_additive]` is called with a `name` argument `new_name`
  /without a dot/, then `to_additive` updates the prefix as described
  above, then replaces the last part of the name with `new_name`.

* If `@[to_additive]` is called with a `name` argument
  `new_namespace.new_name` /with a dot/, then `to_additive` uses this
  new name as is.

As a safety check, in the first case `to_additive` double checks
that the new name differs from the original one.

-/
initialize registerBuiltinAttribute {
    name := `to_additive
    descr := "Transport multiplicative to additive"
    add := fun src stx kind ↦ do _ ← addToAdditiveAttr src (← elabToAdditive stx) kind
    -- we (presumably) need to run after compilation to properly add the `simp` attribute
    applicationTime := .afterCompilation
  }

end ToAdditive
