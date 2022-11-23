/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn, Jon Eugster
Ported by: E.W.Ayers
-/
import Mathlib.Data.String.Defs
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.Expr.ReplaceRec
import Mathlib.Lean.Expr
import Lean
import Lean.Data
import Lean.Elab.Term
import Std.Lean.NameMapAttribute

/-!
# The `@[to_additive]` attribute.

The attribute `to_additive` can be used to automatically transport theorems
and definitions (but not inductive types and structures) from a multiplicative
theory to an additive theory.
-/

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Command
open Std

/-- The  `to_additive_ignore_args` attribute. -/
syntax (name := to_additive_ignore_args) "to_additive_ignore_args" num* : attr
/-- The  `to_additive_relevant_arg` attribute. -/
syntax (name := to_additive_relevant_arg) "to_additive_relevant_arg" num : attr
/-- The  `to_additive_reorder` attribute. -/
syntax (name := to_additive_reorder) "to_additive_reorder" num* : attr
/-- The  `to_additive_fixed_numeral` attribute. -/
syntax (name := to_additive_fixed_numeral) "to_additive_fixed_numeral" "?"? : attr
/-- Remaining arguments of `to_additive`. -/
syntax to_additiveRest := (ppSpace ident)? (ppSpace str)?
/-- The `to_additive` attribute. -/
syntax (name := to_additive) "to_additive" "!"? "?"? to_additiveRest : attr

/-- The `to_additive` attribute. -/
macro "to_additive!"  rest:to_additiveRest : attr => `(attr| to_additive !   $rest)
/-- The `to_additive` attribute. -/
macro "to_additive?"  rest:to_additiveRest : attr => `(attr| to_additive   ? $rest)
/-- The `to_additive` attribute. -/
macro "to_additive!?" rest:to_additiveRest : attr => `(attr| to_additive ! ? $rest)
/-- The `to_additive` attribute. -/
macro "to_additive?!" rest:to_additiveRest : attr => `(attr| to_additive ! ? $rest)

/--
This function takes a String and splits it into separate parts based on the following
(naming conventions)[https://github.com/leanprover-community/mathlib4/wiki#naming-convention].

E.g. `#eval  "InvHMulLEConjugate₂Smul_ne_top".splitCase` yields
`["Inv", "HMul", "LE", "Conjugate₂", "Smul", "_", "ne", "_", "top"]`.
-/
partial def String.splitCase (s : String) (i₀ : Pos := 0) (r : List String := []) : List String :=
  -- We test if we need to split between `i₀` and `i₁`.
  let i₁ := s.next i₀
  let i₂ := s.next i₁
  if s.atEnd i₁ then
    -- If `i₀` is the last position, return the list.
    let r := s::r
    r.reverse
  -- First, we split on both sides of `_` to keep them there when rejoining the string.
  else if (s.get i₀ = '_') || (s.get i₁ = '_') then
    let r := (s.extract 0 i₁)::r
    splitCase (s.extract i₁ s.endPos) 0 r
  -- Otherwise, we only ever split when there is an upper case at `i₁`.
  else if (s.get i₁).isUpper then
    -- There are two cases we need to split:
    if (s.get i₀).isUpper then
      -- 1) If `i₀` and `i₁` are upper, `i₂` is not upper, and `i₀ > 0`.
      -- This prevents single capital letters being split.
      -- Example: Splits `LEOne`to `LE`, `One` but leaves `HMul` together.
      if (i₀ ≠ 0) && ¬((s.get i₂).isUpper) then
        let r := (s.extract 0 i₁)::r
        splitCase (s.extract i₁ s.endPos) 0 r
      else
        splitCase s i₁ r
    -- 2) Upper `i₁` is preceeded by non-upper `i₀`.
    else
      let r := (s.extract 0 i₁)::r
      splitCase (s.extract i₁ s.endPos) 0 r
  else
    splitCase s i₁ r

namespace ToAdditive

initialize registerTraceClass `to_additive
initialize registerTraceClass `to_additive_detail

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
        return ids.toList
  }

/-- Gets the set of arguments that should be ignored for the given name
(according to `@[to_additive_ignore_args ...]`).
This value is used in `additiveTestAux`. -/
def ignore [Functor M] [MonadEnv M]: Name → M (Option (List Nat))
  | n => (ignoreArgsAttr.find? · n) <$> getEnv

/--
An attribute that stores all the declarations that needs their arguments reordered when
applying `@[to_additive]`. Currently, we only support swapping consecutive arguments.
The list of the natural numbers contains the positions of the first of the two arguments
to be swapped.
If the first two arguments are swapped, the first two universe variables are also swapped.
Example: `@[to_additive_reorder 1 4]` swaps the first two arguments and the arguments in
positions 4 and 5.
-/
initialize reorderAttr : NameMapExtension (List Nat) ←
  registerNameMapAttribute {
    name := `to_additive_reorder
    descr :=
      "Auxiliary attribute for `to_additive` that stores arguments that need to be reordered."
    add := fun
    | _, `(attr| to_additive_reorder $[$ids:num]*) =>
      pure <| Array.toList <| ids.map (·.1.isNatLit?.get!)
    | _, _ => throwUnsupportedSyntax }

/-- Get the reorder list (defined using `@[to_additive_reorder ...]`) for the given declaration. -/
def getReorder [Functor M] [MonadEnv M]: Name →  M (List Nat)
  | n => (reorderAttr.find? · n |>.getD []) <$> getEnv

/-- Given a declaration name and an argument index, determines whether this index
should be swapped with the next one. -/
def shouldReorder [Functor M] [MonadEnv M]: Name → Nat → M Bool
  | n, i => (i ∈ ·) <$> (getReorder n)

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

Warning: adding `@[to_additive_reorder]` with an equal or smaller number than the number in this
attribute is currently not supported.
-/
initialize relevantArgAttr : NameMapExtension Nat ←
  registerNameMapAttribute {
    name := `to_additive_relevant_arg
    descr := "Auxiliary attribute for `to_additive` stating" ++
      " which arguments are the types with a multiplicative structure."
    add := fun
    | _, `(attr| to_additive_relevant_arg $id) => pure <| id.1.isNatLit?.get!.pred
    | _, _ => throwUnsupportedSyntax }

/-- Given a declaration name and an argument index, determines whether it
is relevant. This is used in `applyReplacementFun` where more detail on what it
does can be found. -/
def isRelevant [Monad M] [MonadEnv M] (n : Name) (i : Nat) : M Bool := do
  match relevantArgAttr.find? (← getEnv) n with
  | some j => return i == j
  | none => return i == 0

/--
An attribute that stores all the declarations that deal with numeric literals on fixed types.
*  `@[to_additive_fixed_numeral]` should be added to all functions that take a numeral as argument
  that should never be changed by `@[to_additive]` (because it represents a numeral in a fixed
  type).
* `@[to_additive_fixed_numeral?]` should be added to all functions that take a numeral as argument
  that should only be changed if `additiveTest` succeeds on the first argument, i.e. when the
  numeral is only translated if the first argument is a variable (or consists of variables).
-/
initialize fixedNumeralAttr : NameMapExtension Bool ←
  registerNameMapAttribute {
    name := `to_additive_fixed_numeral
    descr :=
      "Auxiliary attribute for `to_additive` that stores functions that have numerals as argument."
    add := fun
    | _, `(attr| to_additive_fixed_numeral $[?%$conditional]?) =>
      pure <| conditional.isSome
    | _, _ => throwUnsupportedSyntax }

/-- Maps multiplicative names to their additive counterparts. -/
initialize translations : NameMapExtension Name ← registerNameMapExtension _

/-- Get the multiplicative → additive translation for the given name. -/
def findTranslation? (env : Environment) : Name → Option Name :=
  (ToAdditive.translations.getState env).find?

/-- Add a (multiplicative → additive) name translation to the translations map. -/
def insertTranslation (src tgt : Name) : CoreM Unit := do
  if let some tgt' := findTranslation? (←getEnv) src then
    throwError "Already exists translation {src} ↦ {tgt'}"
  modifyEnv (ToAdditive.translations.addEntry · (src, tgt))
  trace[to_additive] "Added translation {src} ↦ {tgt}."

/-- Get whether or not the replace-all flag is set. If this is true, then the
additiveTest heuristic is not used and all instances of multiplication are replaced.
You can enable this with `@[to_additive!]`-/
def replaceAll [Functor M] [MonadOptions M] : M Bool :=
  (·.getBool `to_additive.replaceAll) <$> getOptions

variable [Monad M] [MonadOptions M] [MonadEnv M]

/-- Auxilliary function for `additiveTest`. The bool argument *only* matters when applied
to exactly a constant. -/
private def additiveTestAux : Bool → Expr → M Bool
  | b, .const n _ => return b || (findTranslation? (← getEnv) n).isSome
  | _, .app e a => do
      if ← additiveTestAux true e then
        return true
      if let some n := e.getAppFn.constName? then
        if let some l ← ignore n then
          if e.getAppNumArgs + 1 ∈ l then
            return true
      additiveTestAux false a
  | _, .lam _ _ t _ => additiveTestAux false t
  | _, .forallE _ _ t _ => additiveTestAux false t
  | _, .letE _ _ e body _ =>
    additiveTestAux false e <&&> additiveTestAux false body
  | _, _                => return true

/--
`additiveTest e` tests whether the expression `e` contains no constant
`nm` that is not applied to any arguments, and such that `translations.find?[nm] = none`.
This is used in `@[to_additive]` for deciding which subexpressions to transform: we only transform
constants if `additiveTest` applied to their first argument returns `true`.
This means we will replace expression applied to e.g. `α` or `α × β`, but not when applied to
e.g. `Nat` or `ℝ × α`.
We ignore all arguments specified by the `ignore` `NameMap`.
If `replaceAll` is `true` the test always returns `true`.
-/
def additiveTest (e : Expr) : M Bool := do
  if (←replaceAll) then
    return true
  else
    additiveTestAux false e

/-- Checks whether a numeral should be translated. -/
def shouldTranslateNumeral [Monad M] [MonadEnv M] (n : Name) (firstArg : Expr) : M Bool := do
  match fixedNumeralAttr.find? (← getEnv) n with
  | some true => additiveTest firstArg
  | some false => return false
  | none => return true

/--
`applyReplacementFun e` replaces the expression `e` with its additive counterpart.
It translates each identifier (inductive type, defined function etc) in an expression, unless
* The identifier occurs in an application with first argument `arg`; and
* `test arg` is false.
However, if `f` is in the dictionary `relevant`, then the argument `relevant.find f`
is tested, instead of the first argument.

It will also reorder arguments of certain functions, using `shouldReorder`:
e.g. `g x₁ x₂ x₃ ... xₙ` becomes `g x₂ x₁ x₃ ... xₙ` if `reorderAttr.find? env g = some [1]`.
-/
def applyReplacementFun : Expr → MetaM Expr :=
  Lean.Expr.replaceRecMeta fun r e ↦ do
    trace[to_additive_detail] "applyReplacementFun: replace at {e}"
    match e with
    | .lit (.natVal 1) => pure <| mkRawNatLit 0
    | .const n₀ ls => do
      let n₁ := Name.mapPrefix (findTranslation? <|← getEnv) n₀
      if n₀ != n₁ then
        trace[to_additive_detail] "applyReplacementFun: {n₀} → {n₁}"
      let ls : List Level ← (do -- [todo] just get Lean to figure out the levels?
        if ← shouldReorder n₀ 1 then
            return ls.get! 1::ls.head!::ls.drop 2
        return ls)
      return some $ Lean.mkConst n₁ ls
    | .app g x => do
      let gf := g.getAppFn
      if let some nm := gf.constName? then
        let gArgs := g.getAppArgs
        -- e = `(nm y₁ .. yₙ x)
        trace[to_additive_detail] "applyReplacementFun: app {nm} {gArgs} {x}"
        /- Test if arguments should be reordered. -/
        if h : gArgs.size > 0 then
          let c1 ← shouldReorder nm gArgs.size
          let c2 ← additiveTest gArgs[0]
          if c1 && c2 then
            -- interchange `x` and the last argument of `g`
            let x ← r x
            let gf ← r g.appFn!
            let ga ← r g.appArg!
            let e₂ :=  mkApp2 gf x ga
            trace[to_additive_detail]
              "applyReplacementFun: reordering {nm}: {x} ↔ {ga}\nBefore: {e}\nAfter:  {e₂}"
            return some e₂
        /- Test if the head should not be replaced. -/
        let c1 ← isRelevant nm gArgs.size
        let c2 := gf.isConst
        let c3 ← additiveTest x
        if c1 && c2 && c3 then
          trace[to_additive_detail]
            "applyReplacementFun: {x} doesn't contain a fixed type, so we will change {nm}"
        if c1 && c2 && not c3 then
          -- the test failed, so don't update the function body.
          trace[to_additive_detail]
            "applyReplacementFun: {x} contains a fixed type, so {nm} is not changed"
          let x ← r x
          let args ← gArgs.mapM r
          return some $ mkApp (mkAppN gf args) x
        /- Do not replace numerals in specific types. -/
        let firstArg := if h : gArgs.size > 0 then gArgs[0] else x
        if not (← shouldTranslateNumeral nm firstArg) then
          trace[to_additive_detail] "applyReplacementFun: Do not change numeral {g.app x}"
          return some <| g.app x
      return e.updateApp! (← r g) (← r x)
    | _ => return none

/-- Eta expands `e` at most `n` times.-/
def etaExpandN (n : Nat) (e : Expr): MetaM Expr := do
  forallBoundedTelescope (← inferType e) (some n) fun xs _ ↦ mkLambdaFVars xs (mkAppN e xs)

/-- `e.expand` eta-expands all expressions that have as head a constant `n` in
`reorder`. They are expanded until they are applied to one more argument than the maximum in
`reorder.find n`. -/
def expand (e : Expr) : MetaM Expr := do
  let e₂ ←e.replaceRecMeta $ fun r e ↦ do
    let e0 := e.getAppFn
    let es := e.getAppArgs
    let some e0n := e0.constName? | return none
    let reorder ← getReorder e0n
    if reorder.isEmpty then
      -- no need to expand if nothing needs reordering
      return none
    let e' := mkAppN e0 $ ← es.mapM r
    let needed_n := reorder.foldr Nat.max 0 + 1
    if needed_n ≤ es.size then
      return some e'
    else
      -- in this case, we need to reorder arguments that are not yet
      -- applied, so first η-expand the function.
      let e' ← etaExpandN (needed_n - es.size) e'
      return some $ e'
  trace[to_additive_detail] "expand:\nBefore: {e}\nAfter:  {e₂}"
  return e₂

/-- Run applyReplacementFun on the given `srcDecl` to make a new declaration with name `tgt` -/
def updateDecl
  (tgt : Name) (srcDecl : ConstantInfo)
  : MetaM ConstantInfo := do
  let mut decl := srcDecl.updateName tgt
  decl := decl.updateType $ (← applyReplacementFun (← expand decl.type))
  if let some v := decl.value? then
    decl := decl.updateValue (← applyReplacementFun (← expand v))
  return decl

/-- Lean 4 makes declarations which are not internal
(that is, head string starts with `_`) but which should be transformed.
e.g. `proof_1` in `Lean.Meta.mkAuxDefinitionFor` this might be better fixed in core.
This method is polyfill for that.
Note: this declaration also occurs as `shouldIgnore` in the Lean 4 file `test/lean/run/printDecls`.
-/
def isInternal' (declName : Name) : Bool :=
  declName.isInternal ||
  match declName with
  | .str _ s => "match_".isPrefixOf s || "proof_".isPrefixOf s || "eq_".isPrefixOf s
  | _        => true

/-- transform the declaration `src` and all declarations `pre._proof_i` occurring in `src`
using the transforms dictionary.
`replace_all`, `trace`, `ignore` and `reorder` are configuration options.
`pre` is the declaration that got the `@[to_additive]` attribute and `tgt_pre` is the target of this
declaration. -/
partial def transformDeclAux
  (ref : Option Syntax) (pre tgt_pre : Name) : Name → CoreM Unit := fun src ↦ do
  -- if this declaration is not `pre` or an internal declaration, we do nothing.
  if not (src == pre || isInternal' src) then
    if (findTranslation? (← getEnv) src).isSome then
      return
    throwError "The declaration {pre} depends on the declaration {src} which is in the namespace {
      pre}, but does not have the `@[to_additive]` attribute. This is not supported.\n{""
      }Workaround: move {src} to a different namespace."
  let env ← getEnv
  -- we find the additive name of `src`
  let tgt := src.mapPrefix (fun n ↦ if n == pre then some tgt_pre else none)
  -- we skip if we already transformed this declaration before
  if env.contains tgt then
    return
  let srcDecl ← getConstInfo src
  -- we first transform all auxilliary declarations generated when elaborating `pre`
  for n in srcDecl.type.listNamesWithPrefix pre do
    transformDeclAux none pre tgt_pre n
  if let some value := srcDecl.value? then
    for n in value.listNamesWithPrefix pre do
      transformDeclAux none pre tgt_pre n
  -- now transform the source declaration
  let trgDecl : ConstantInfo ← MetaM.run' $ updateDecl tgt srcDecl
  if ¬ trgDecl.hasValue then
    throwError "Expected {trgDecl.name} to have a value."
  trace[to_additive] "generating\n{trgDecl.name} :=\n  {trgDecl.value!}"
  try
    -- make sure that the type is correct,
    -- and emit a more helpful error message if it fails
    discard <| MetaM.run' <| inferType trgDecl.value!
  catch
    | Exception.error _ msg => throwError "@[to_additive] failed.
      Type mismatch in additive declaration. For help, see the docstring
      of `to_additive.attr`, section `Troubleshooting`.
      Failed to add declaration\n{trgDecl.name}:\n{msg}"
    | _ => panic! "unreachable"
  if isNoncomputable env src then
    addDecl trgDecl.toDeclaration!
    setEnv $ addNoncomputable (← getEnv) trgDecl.name
  else
    addAndCompile trgDecl.toDeclaration!
  -- now add declaration ranges so jump-to-definition works
  addDeclarationRanges tgt {
    range := ← getDeclarationRange (← getRef)
    selectionRange := ← getDeclarationRange (ref.getD (← getRef))
  }
  if let some ref := ref then
    -- TODO: make a function for this
    pushInfoLeaf <| .ofTermInfo {
      elaborator := .anonymous, lctx := {}, expectedType? := none
      stx := ref, isBinder := true
      expr := ← mkConstWithLevelParams trgDecl.name
    }
  if isProtected (← getEnv) src then
    setEnv $ addProtected (← getEnv) tgt

/-- This should copy all of the attributes on src to tgt.
At the moment it only copies `simp` attributes because attributes
are not stored by the environment.

[todo] add more attributes. A change is coming to core that should
allow us to iterate the attributes applied to a given decalaration.
-/
-- TODO once we can copy `instance`, tidy up `Algebra/CovariantAndContravariant.lean` and
-- `Algebra/Group/OrderSynonym.lean`.
def copyAttributes (src tgt : Name) : CoreM Unit := do
  -- [todo] other simp theorems
  let some ext ← getSimpExtension? `simp | return
  let thms ← ext.getTheorems
  if (¬ thms.isLemma (.decl src)) || thms.isLemma (.decl tgt) then
    return
  -- [todo] how to get prio data from SimpTheorems?
  Lean.Meta.addSimpTheorem ext tgt
    (post := true)
    (inv := false)
    (attrKind := AttributeKind.global)
    (prio := 1000) |>.run'

/--
Make a new copy of a declaration, replacing fragments of the names of identifiers in the type and
the body using the `translations` dictionary.
This is used to implement `@[to_additive]`.
-/
def transformDecl (ref : Option Syntax) (src tgt : Name) : CoreM Unit := do
  transformDeclAux ref src tgt src
  let eqns? ← MetaM.run' (getEqnsFor? src true)
  -- now transform all of the equational lemmas
  if let some eqns := eqns? then
    for src_eqn in eqns do
      transformDeclAux none src tgt src_eqn
      -- [todo] copy attributes for equations
      -- [todo] add equation lemmas to tgt_eqn
  copyAttributes src tgt

/--
Find the first argument of `nm` that has a multiplicative type-class on it.
Returns 1 if there are no types with a multiplicative class as arguments.
E.g. `prod.group` returns 1, and `pi.has_one` returns 2.
-/
def firstMultiplicativeArg (nm : Name) : MetaM Nat := do
  forallTelescopeReducing (← getConstInfo nm).type fun xs _ ↦ do
    -- xs are the arguments to the constant
    let xs := xs.toList
    let l ← xs.mapM fun x ↦ do
      -- x is an argument and i is the index
      -- write `x : (y₀ : α₀) → ... → (yₙ : αₙ) → tgt_fn tgt_args₀ ... tgt_argsₘ`
      forallTelescopeReducing (← inferType x) fun _ys tgt ↦ do
        let (_tgt_fn, tgt_args) := tgt.getAppFnArgs
        if let some c := tgt.getAppFn.constName? then
          if findTranslation? (← getEnv) c |>.isNone then
            return []
        return tgt_args.toList.filterMap fun tgt_arg ↦
          xs.findIdx? fun x ↦ Expr.containsFVar tgt_arg x.fvarId!
    trace[to_additive_detail] "firstMultiplicativeArg: {l}"
    match l.join with
    | [] => return 0
    | (head :: tail) => return tail.foldr Nat.min head

/-- `ValueType` is the type of the arguments that can be provided to `to_additive`. -/
structure ValueType : Type where
  /-- Replace all multiplicative declarations, do not use the heuristic. -/
  replaceAll : Bool := false
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
  /-- The `Syntax` element corresponding to the original multiplicative declaration
  (or the `to_additive` attribute if it is added later),
  which we need for adding definition ranges. -/
  ref : Syntax
  deriving Repr

/-- Helper for `capitalizeLike`. -/
partial def capitalizeLikeAux (s : String) (i : String.Pos := 0) : String →  String :=
  fun p =>
  if p.atEnd i || s.atEnd i then
    p
  else
    let j := p.next i
    if (s.get i).isLower then
      capitalizeLikeAux s j (p.set i (p.get i |>.toLower))
    else if (s.get i).isUpper then
      capitalizeLikeAux s j (p.set i (p.get i |>.toUpper))
    else
      capitalizeLikeAux s j p

/-- Capitalizes `s` char-by-char like `r`. If `s` is longer, it leaves the tail untouched. -/
def capitalizeLike (r : String) (s : String) :=
  capitalizeLikeAux r 0 s

/-- Capitalize First element of a list like `s`. -/
def capitalizeFirstLike (s : String) : List String → List String
  | x :: r => capitalizeLike s x :: r
  | [] => []

/--
Dictionary used by `guessName` to autogenerate names.

Note: `guessName` capitalizes first element of the output according to
capitalization of the input. Input and first element should therefore be lower-case,
2nd element should be capitalized properly.
-/
private def nameDict : String → List String
| "one"         => ["zero"]
| "mul"         => ["add"]
| "smul"        => ["vadd"]
| "inv"         => ["neg"]
| "div"         => ["sub"]
| "prod"        => ["sum"]
| "hmul"        => ["hadd"]
| "hdiv"        => ["hsub"]
| "hpow"        => ["hmul"]
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
 -- TODO: Is it `TSupport` or `Tsupport`?
| "Add" :: "TSupport" :: s          => "TSupport" :: fixAbbreviation s
| "add" :: "TSupport" :: s          => "tsupport" :: fixAbbreviation s
| "add" :: "_" :: "tsupport" :: s   => "tsupport" :: fixAbbreviation s
| "Add" :: "Indicator" :: s         => "Indicator" :: fixAbbreviation s
| "add" :: "Indicator" :: s         => "indicator" :: fixAbbreviation s
| "add" :: "_" :: "indicator" :: s  => "indicator" :: fixAbbreviation s
-- TODO: Bug in `splitCase` splits like ["LEH", "Pow"] instead of ["LE", "HPow"].
-- Currently we just fix these cases manually.
| "HNsmul" :: s                     => "HMul" :: fixAbbreviation s
| "hnsmul" :: s                     => "hmul" :: fixAbbreviation s
| "Zero" :: "LEH" :: s              => "NonnegH" :: fixAbbreviation s
| "Zero" :: "LTH" :: s              => "PosH" :: fixAbbreviation s
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
  String.mapTokens ''' <|
  fun s =>
    String.join <|
    fixAbbreviation <|
    applyNameDict <|
    s.splitCase

/-- Return the provided target name or autogenerate one if one was not provided. -/
def targetName (src tgt : Name) (allowAutoName : Bool) : CoreM Name := do
  let res ← do
    if tgt.getPrefix != Name.anonymous || allowAutoName then
      return tgt
    let .str pre s := src | throwError "to_additive: can't transport {src}"
    let tgt_auto := guessName s
    if tgt.toString == tgt_auto then
      dbg_trace "{src}: correctly autogenerated target name {tgt_auto
        }, you may remove the explicit {tgt} argument."
    let pre := pre.mapPrefix <| findTranslation? (← getEnv)
    if tgt == Name.anonymous then
      return Name.mkStr pre tgt_auto
    else
      return  Name.mkStr pre tgt.toString
  if res == src && tgt != src then
    throwError "to_additive: can't transport {src} to itself."
  return res

private def proceedFieldsAux (src tgt : Name) (f : Name → CoreM (Array Name)) : CoreM Unit := do
  let srcFields ← f src
  let tgtFields ← f tgt
  if srcFields.size != tgtFields.size then
    throwError "Failed to map fields of {src}, {tgt} with {srcFields} ↦ {tgtFields}"
  for (srcField, tgtField) in srcFields.zip tgtFields do
    if srcField != tgtField then
      insertTranslation (src ++ srcField) (tgt ++ tgtField)

/-- Add the structure fields of `src` to the translations dictionary
so that future uses of `to_additive` will map them to the corresponding `tgt` fields. -/
def proceedFields (src tgt : Name) : CoreM Unit := do
  let env : Environment ← getEnv
  let aux := proceedFieldsAux src tgt
  aux fun n ↦ pure <| if isStructure env n then getStructureFields env n else #[]
  -- We don't have to run toAdditive on the constructor of a structure, since the use of
  -- `Name.mapPrefix` will do that automatically.

private def elabToAdditiveAux (ref : Syntax) (replaceAll trace : Bool) (tgt : Option Syntax)
    (doc : Option Syntax) : ValueType :=
  { replaceAll := replaceAll
    trace := trace
    tgt := match tgt with | some tgt => tgt.getId | none => Name.anonymous
    doc := doc.bind (·.isStrLit?)
    allowAutoName := false
    ref }

private def elabToAdditive : Syntax → CoreM ValueType
  | `(attr| to_additive%$tk $[!%$replaceAll]? $[?%$trace]? $[$tgt]? $[$doc]?) =>
    return elabToAdditiveAux ((tgt.map (·.raw)).getD tk) replaceAll.isSome trace.isSome tgt doc
  | _ => throwUnsupportedSyntax

/-- `addToAdditiveAttr src val` adds a `@[to_additive]` attribute to `src` with configuration `val`.
See the attribute implementation for more details. -/
def addToAdditiveAttr (src : Name) (val : ValueType) : AttrM Unit := do
  let tgt ← targetName src val.tgt val.allowAutoName
  if let some tgt' := findTranslation? (← getEnv) src then
    throwError "{src} already has a to_additive translation {tgt'}."
  insertTranslation src tgt
  let firstMultArg ← MetaM.run' <| firstMultiplicativeArg src
  if firstMultArg != 0 then
    trace[to_additive_detail] "Setting relevant_arg for {src} to be {firstMultArg}."
    relevantArgAttr.add src firstMultArg
  if (← getEnv).contains tgt then
    -- since tgt already exists, we just need to add a translation src ↦ tgt
    -- and also src.𝑥 ↦ tgt.𝑥' for any subfields.
    proceedFields src tgt
  else
    -- tgt doesn't exist, so let's make it
    let shouldTrace := val.trace || ((← getOptions) |>.getBool `trace.to_additive)
    withOptions
      (fun o ↦ o |>.setBool `to_additive.replaceAll val.replaceAll
                  |>.setBool `trace.to_additive shouldTrace)
      (transformDecl val.ref src tgt)
  if let some doc := val.doc then
    addDocString tgt doc
  return ()

/--
The attribute `to_additive` can be used to automatically transport theorems
and definitions (but not inductive types and structures) from a multiplicative
theory to an additive theory.

To use this attribute, just write:

```
@[to_additive]
theorem mul_comm' {α} [comm_semigroup α] (x y : α) : x * y = y * x := comm_semigroup.mul_comm
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

If the declaration to be transported has attributes which need to be
copied to the additive version, then `to_additive` should come last:

```
@[simp, to_additive] lemma mul_one' {G : Type*} [group G] (x : G) : x * 1 = x := mul_one x
```

Currently only the `simp` attribute is supported.

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
  For example, `cont_mdiff_map` has attribute `@[to_additive_ignore_args 21]`, which means
  that its 21st argument `(n : WithTop Nat)` can contain `Nat`
  (usually in the form `has_top.top Nat ...`) and still be additivized.
  So `@Mul.mul (C^∞⟮I, N; I', G⟯) _ f g` will be additivized.

### Troubleshooting

If `@[to_additive]` fails because the additive declaration raises a type mismatch, there are
various things you can try.
The first thing to do is to figure out what `@[to_additive]` did wrong by looking at the type
mismatch error.

* Option 1: It additivized a declaration `d` that should remain multiplicative. Solution:
  * Make sure the first argument of `d` is a type with a multiplicative structure. If not, can you
    reorder the (implicit) arguments of `d` so that the first argument becomes a type with a
    multiplicative structure (and not some indexing type)?
    The reason is that `@[to_additive]` doesn't additivize declarations if their first argument
    contains fixed types like `Nat` or `ℝ`. See section Heuristics.
    If the first argument is not the argument with a multiplicative type-class, `@[to_additive]`
    should have automatically added the attribute `@[to_additive_relevant_arg]` to the declaration.
    You can test this by running the following (where `d` is the full name of the declaration):
    ```
      #eval (do isRelevant `d >>= trace)
    ```
    The expected output is `n` where the `n`-th argument of `d` is a type (family) with a
    multiplicative structure on it. If you get a different output (or a failure), you could add
    the attribute `@[to_additive_relevant_arg n]` manually, where `n` is an argument with a
    multiplicative structure.
* Option 2: It didn't additivize a declaration that should be additivized.
  This happened because the heuristic applied, and the first argument contains a fixed type,
  like `Nat` or `ℝ`. Solutions:
  * If the fixed type has an additive counterpart (like `↥Semigroup`), give it the `@[to_additive]`
    attribute.
  * If the fixed type occurs inside the `k`-th argument of a declaration `d`, and the
    `k`-th argument is not connected to the multiplicative structure on `d`, consider adding
    attribute `[to_additive_ignore_args k]` to `d`.
  * If you want to disable the heuristic and replace all multiplicative
    identifiers with their additive counterpart, use `@[to_additive!]`.
* Option 3: Arguments / universe levels are incorrectly ordered in the additive version.
  This likely only happens when the multiplicative declaration involves `pow`/`^`. Solutions:
  * Ensure that the order of arguments of all relevant declarations are the same for the
    multiplicative and additive version. This might mean that arguments have an "unnatural" order
    (e.g. `Monoid.npow n x` corresponds to `x ^ n`, but it is convenient that `Monoid.npow` has this
    argument order, since it matches `AddMonoid.nsmul n x`.
  * If this is not possible, add the `[to_additive_reorder k]` to the multiplicative declaration
    to indicate that the `k`-th and `(k+1)`-st arguments are reordered in the additive version.

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
its equational lemmas and tags them as equational lemmas for the new declaration,
attributes present on the original equational lemmas are also transferred first (notably
`_refl_lemma`).

### Structure fields and constructors

If `src` is a structure, then `to_additive` automatically adds
structure fields to its mapping, and similarly for constructors of
inductive types.

For new structures this means that `to_additive` automatically handles
coercions, and for old structures it does the same, if ancestry
information is present in `@[ancestor]` attributes. The `ancestor`
attribute must come before the `to_additive` attribute, and it is
essential that the order of the base structures passed to `ancestor` matches
between the multiplicative and additive versions of the structure.

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
    add := fun src stx kind ↦ do
      if (kind != AttributeKind.global) then
        throwError "`to_additive` can't be used as a local attribute"
      let val ← elabToAdditive stx
      addToAdditiveAttr src val
    -- Because `@[simp]` runs after compilation,
    -- we have to as well to be able to copy attributes correctly.
    applicationTime := .afterCompilation
  }

end ToAdditive
