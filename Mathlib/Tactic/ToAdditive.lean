/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn
Ported by: E.W.Ayers
-/
import Mathlib.Data.String.Defs
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.Expr.ReplaceRec
import Mathlib.Lean.Expr
import Mathlib.Lean.NameMapAttribute
import Lean
import Lean.Data

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Command

syntax (name := to_additive_ignore_args) "to_additive_ignore_args" num* : attr
syntax (name := to_additive_relevant_arg) "to_additive_relevant_arg" num : attr
syntax (name := to_additive_reorder) "to_additive_reorder" num* : attr
syntax (name := to_additive) "to_additive" "!"? "?"? (ppSpace ident)? (ppSpace str)? : attr

namespace ToAdditive

initialize registerTraceClass `to_additive
initialize registerTraceClass `to_additive_detail

initialize ignoreArgsAttr : NameMapAttribute (List Nat) ←
  registerNameMapAttribute {
    name  := `to_additive_ignore_args
    descr := "Auxiliary attribute for `to_additive` stating that certain arguments are not additivized."
    add   := fun _ stx => do
        let ids ← match stx with
          | `(attr|to_additive_ignore_args $[$ids:num]*) => pure <| ids.map (·.1.isNatLit?.get!)
          | _ => throwError "unexpected to_additive_ignore_args syntax {stx}"
        return ids.toList
  }

/-- Gets the set of arguments that should be ignored for the given name
(according to `@[to_additive_ignore_args ...]`).
This value is used in `additiveTestAux`. -/
def ignore [Functor M] [MonadEnv M]: Name → M (Option (List Nat))
  | n => (ignoreArgsAttr.find? · n) <$> getEnv

initialize reorderAttr : NameMapAttribute (List Nat) ←
  registerNameMapAttribute {
    name := `to_additive_reorder
    descr := "Auxiliary attribute for `to_additive` that stores arguments that need to be reordered."
    add := fun
    | _, `(attr|to_additive_reorder $[$ids:num]*) => pure <| Array.toList <| ids.map (·.1.isNatLit?.get!)
    | _, stx => throwError "unexpected to_additive_reorder syntax {stx}"
  }

/-- Get the reorder list (defined using `@[to_additive_reorder ...]`) for the given declaration. -/
def getReorder [Functor M] [MonadEnv M]: Name →  M (List Nat)
  | n => (reorderAttr.find? · n |>.getD []) <$> getEnv

/-- Given a declaration name and an argument index, determines whether this index
should be swapped with the next one. -/
def shouldReorder [Functor M] [MonadEnv M]: Name → Nat → M Bool
  | n, i => (i ∈ ·) <$> (getReorder n)

initialize relevantArgAttr : NameMapAttribute (Nat) ←
  registerNameMapAttribute {
    name := `to_additive_relevant_arg
    descr := "Auxiliary attribute for `to_additive` stating which arguments are the types with a multiplicative structure."
    add := fun
    | _, `(attr|to_additive_relevant_arg $id) => pure <| id.1.isNatLit?.get!
    | _, stx => throwError "unexpected to_additive_relevant_arg syntax {stx}"
  }

/-- Given a declaration name and an argument index, determines whether it
is relevant. This is used in `applyReplacementFun` where more detail on what it
does can be found. -/
def isRelevant [Monad M] [MonadEnv M] (n : Name) (i : Nat) : M Bool := do
  match relevantArgAttr.find? (← getEnv) n with
  | some j => return i == j
  | none => return i == 0

/- Maps multiplicative names to their additive counterparts. -/
initialize translations : NameMapExtension Name ←
  mkNameMapExtension Name `translations

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

/--
`e.applyReplacementFun f test` applies `f` to each identifier
(inductive type, defined function etc) in an expression, unless
* The identifier occurs in an application with first argument `arg`; and
* `test arg` is false.
However, if `f` is in the dictionary `relevant`, then the argument `relevant.find f`
is tested, instead of the first argument.

Reorder contains the information about what arguments to reorder:
e.g. `g x₁ x₂ x₃ ... xₙ` becomes `g x₂ x₁ x₃ ... xₙ` if `reorder.find g = some [1]`.
We assume that all functions where we want to reorder arguments are fully applied.
This can be done by applying `etaExpand` first.
-/
def applyReplacementFun : Expr → MetaM Expr :=
  Lean.Expr.replaceRecMeta fun r e => do
    trace[to_additive_detail] "applyReplacementFun: replace at {e}"
    match e with
    | .lit (.natVal 1) => pure <| mkNatLit 0
    | .const n₀ ls => do
      let n₁ := Name.mapPrefix (findTranslation? <|← getEnv) n₀
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
        if h : gArgs.size > 0 then
          let c1 ← shouldReorder nm gArgs.size
          let c2 ← additiveTest gArgs[0]
          if c1 && c2 then
            -- interchange `x` and the last argument of `g`
            let x ← r x
            let gf ← r g.appFn!
            let ga ← r g.appArg!
            let e₂ :=  mkApp2 gf x ga
            trace[to_additive_detail] "applyReplacementFun: reordering {nm}: {x} ↔ {ga}\nBefore: {e}\nAfter:  {e₂}"
            return some e₂
        let c1 ← isRelevant nm gArgs.size
        let c2 := gf.isConst
        let c3 ← additiveTest x
        if c1 && c2 && not c3 then
          -- the test failed, so don't update the function body.
          trace[to_additive_detail] "applyReplacementFun: isRelevant and test failed: {nm} {gArgs} {x}"
          let x ← r x
          let args ← gArgs.mapM r
          return some $ mkApp (mkAppN gf args) x
      return e.updateApp! (← r g) (← r x)
    | _ => return none

/-- Eta expands `e` at most `n` times.-/
def etaExpandN (n : Nat) (e : Expr): MetaM Expr := do
  forallBoundedTelescope (← inferType e) (some n) fun xs _ => mkLambdaFVars xs (mkAppN e xs)

/-- `e.expand` eta-expands all expressions that have as head a constant `n` in
`reorder`. They are expanded until they are applied to one more argument than the maximum in
`reorder.find n`. -/
def expand (e : Expr) : MetaM Expr := do
  let e₂ ←e.replaceRecMeta $ fun r e => do
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
eg `proof_1` in `Lean.Meta.mkAuxDefinitionFor` this might be better fixed in core.
This method is polyfill for that. -/
def isInternal' : Name → Bool
  | n@(.str _ s) => s.startsWith "proof_" || n.isInternal
  | n => Name.isInternal n

/-- transform the declaration `src` and all declarations `pre._proof_i` occurring in `src`
using the transforms dictionary.
`replace_all`, `trace`, `ignore` and `reorder` are configuration options.
`pre` is the declaration that got the `@[to_additive]` attribute and `tgt_pre` is the target of this
declaration. -/
partial def transformDeclAux
  (pre tgt_pre : Name) : Name → CoreM Unit := fun src => do
  -- if this declaration is not `pre` or an internal declaration, we do nothing.
  if not (src == pre || isInternal' src) then
    if (findTranslation? (← getEnv) src).isSome then
      return ()
    else
      throwError "The declaration {pre} depends on the declaration {src} which is in the namespace {pre}, but does not have the `@[to_additive]` attribute. This is not supported. Workaround: move {src} to a different namespace."
  let env ← getEnv
  -- we find the additive name of `src`
  let tgt := src.mapPrefix (fun n => if n == pre then some tgt_pre else none)
  -- we skip if we already transformed this declaration before
  if env.contains tgt then
    return
  let srcDecl ← getConstInfo src
  -- we first transform all the declarations of the form `pre._proof_i`
  for n in srcDecl.type.listNamesWithPrefix pre do
    transformDeclAux pre tgt_pre n
  if let some value := srcDecl.value? then
    for n in value.listNamesWithPrefix pre do
      transformDeclAux pre tgt_pre n
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
  addAndCompile trgDecl.toDeclaration!
  if isProtected (← getEnv) src then
    setEnv $ addProtected (← getEnv) tgt

/-- This should copy all of the attributes on src to tgt.
At the moment it only copies `simp` attributes because attributes
are not stored by the environment.

[todo] add more attributes. A change is coming to core that should
allow us to iterate the attributes applied to a given decalaration.
-/
def copyAttributes (src tgt : Name) : CoreM Unit := do
  -- [todo] other simp theorems
  let some ext ← getSimpExtension? `simp | return ()
  let thms ← ext.getTheorems
  if (¬ thms.isLemma src) || thms.isLemma tgt then
    return ()
  -- [todo] how to get prio data from SimpTheorems?
  MetaM.run' $ Lean.Meta.addSimpTheorem ext tgt
    (post := true)
    (inv := false)
    (attrKind := AttributeKind.global)
    (prio := 1000)
  return ()

/--
Make a new copy of a declaration, replacing fragments of the names of identifiers in the type and
the body using the `translations` dictionary.
This is used to implement `@[to_additive]`.
-/
def transformDecl (src tgt : Name) : CoreM Unit := do
  transformDeclAux src tgt src
  let eqns? ← MetaM.run' (getEqnsFor? src true)
  -- now transform all of the equational lemmas
  if let some eqns := eqns? then
    for src_eqn in eqns do
      transformDeclAux src tgt src_eqn
      -- [todo] copy attributes for equations
      -- [todo] add equation lemmas to tgt_eqn
  copyAttributes src tgt
  return ()
/--
Find the first argument of `nm` that has a multiplicative type-class on it.
Returns 1 if there are no types with a multiplicative class as arguments.
E.g. `prod.group` returns 1, and `pi.has_one` returns 2.
-/
def firstMultiplicativeArg (nm : Name) : MetaM (Option Nat) := do
  forallTelescopeReducing (← getConstInfo nm).type fun xs _ => do
    -- xs are the arguments to the constant
    let xs := xs.toList
    let l ← xs.mapM fun x => do
      -- x is an argument and i is the index
      -- write `x : (y₀ : α₀) → ... → (yₙ : αₙ) → tgt_fn tgt_args₀ ... tgt_argsₘ`
      forallTelescopeReducing (← inferType x) fun _ys tgt => do
        let (_tgt_fn, tgt_args) := tgt.getAppFnArgs
        if let some c := tgt.getAppFn.constName? then
          if findTranslation? (← getEnv) c |>.isNone then
            return []
        return tgt_args.toList.filterMap fun tgt_arg =>
          xs.findIdx? fun x => Expr.containsFVar tgt_arg x.fvarId!
    trace[to_additive_detail] "firstMultiplicativeArg: {l}"
    match l.join with
    | [] => return none
    | (head :: tail) => return some <| tail.foldr Nat.min head


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
  /-- If `allow_auto_name` is `false` (default) then
  `@[to_additive]` will check whether the given name can be auto-generated. -/
  allowAutoName : Bool := false
  deriving Repr

/-- `add_comm_prefix x s` returns `"comm_" ++ s` if `x = tt` and `s` otherwise. -/
def addCommPrefix : Bool → String → String
| true, s => "comm" ++ s.capitalize
| false, s => s

/-- Dictionary used by `to_additive.guess_name` to autogenerate names.
[todo] update to Lean 4 naming -/
private def guessNameDict (is_comm : Bool) : List String → List String
| "one" :: "le" :: s        => addCommPrefix is_comm "nonneg"    :: guessNameDict false s
| "one" :: "lt" :: s        => addCommPrefix is_comm "pos"       :: guessNameDict false s
| "le" :: "one" :: s        => addCommPrefix is_comm "nonpos"    :: guessNameDict false s
| "lt" :: "one" :: s        => addCommPrefix is_comm "neg"       :: guessNameDict false s
| "mul" :: "single" :: s    => addCommPrefix is_comm "single"    :: guessNameDict false s
| "mul" :: "support" :: s   => addCommPrefix is_comm "support"   :: guessNameDict false s
| "mul" :: "tsupport" :: s  => addCommPrefix is_comm "tsupport"  :: guessNameDict false s
| "mul" :: "indicator" :: s => addCommPrefix is_comm "indicator" :: guessNameDict false s
| "mul" :: s                => addCommPrefix is_comm "add"       :: guessNameDict false s
| "smul" :: s               => addCommPrefix is_comm "vadd"      :: guessNameDict false s
| "inv" :: s                => addCommPrefix is_comm "neg"       :: guessNameDict false s
| "div" :: s                => addCommPrefix is_comm "sub"       :: guessNameDict false s
| "one" :: s                => addCommPrefix is_comm "zero"      :: guessNameDict false s
| "prod" :: s               => addCommPrefix is_comm "sum"       :: guessNameDict false s
| "finprod" :: s            => addCommPrefix is_comm "finsum"    :: guessNameDict false s
| "pow" :: s                => addCommPrefix is_comm "nsmul"     :: guessNameDict false s
| "npow" :: s               => addCommPrefix is_comm "nsmul"     :: guessNameDict false s
| "zpow" :: s               => addCommPrefix is_comm "zsmul"     :: guessNameDict false s
| "monoid" :: s      => ("add_" ++ addCommPrefix is_comm "monoid")    :: guessNameDict false s
| "submonoid" :: s   => ("add_" ++ addCommPrefix is_comm "submonoid") :: guessNameDict false s
| "group" :: s       => ("add_" ++ addCommPrefix is_comm "group")     :: guessNameDict false s
| "subgroup" :: s    => ("add_" ++ addCommPrefix is_comm "subgroup")  :: guessNameDict false s
| "semigroup" :: s   => ("add_" ++ addCommPrefix is_comm "semigroup") :: guessNameDict false s
| "magma" :: s       => ("add_" ++ addCommPrefix is_comm "magma")     :: guessNameDict false s
| "haar" :: s        => ("add_" ++ addCommPrefix is_comm "haar")      :: guessNameDict false s
| "prehaar" :: s     => ("add_" ++ addCommPrefix is_comm "prehaar")   :: guessNameDict false s
| "unit" :: s        => ("add_" ++ addCommPrefix is_comm "unit")      :: guessNameDict false s
| "units" :: s       => ("add_" ++ addCommPrefix is_comm "units")     :: guessNameDict false s
| "comm" :: s        => guessNameDict true s
| x :: s             => (addCommPrefix is_comm x :: guessNameDict false s)
| []                 => bif is_comm then ["comm"] else []

/-- Autogenerate target name for `to_additive`. -/
def guessName : String → String :=
  -- [todo] replace with camelcase logic?
  String.mapTokens ''' $
  fun s => String.intercalate (String.singleton '_') $
  guessNameDict false (s.splitOn "_")

/-- Return the provided target name or autogenerate one if one was not provided. -/
def targetName (src tgt : Name) (allowAutoName : Bool) : CoreM Name := do
  let res ← do
    if tgt.getPrefix != Name.anonymous || allowAutoName then
      return tgt
    let .str pre s := src | throwError "to_additive: can't transport {src}"
    let tgt_auto := guessName s
    if tgt.toString == tgt_auto then
      dbg_trace "{src}: correctly autogenerated target name {tgt_auto}, you may remove the explicit {tgt} argument."
    let pre := pre.mapPrefix <| findTranslation? (← getEnv)
    if tgt == Name.anonymous then
      return Name.mkStr pre tgt_auto
    else
      return  Name.mkStr pre tgt.toString
  if res == src && tgt != src then
    throwError "to_additive: can't transport {src} to itself."
  return res

private def proceedFieldsAux (src tgt : Name) (f : Name → CoreM (List String)) : CoreM Unit := do
  let srcFields ← f src
  let tgtFields ← f tgt
  if srcFields.length != tgtFields.length then
    throwError "Failed to map fields of {src}, {tgt} with {srcFields} ↦ {tgtFields}"
  for (srcField, tgtField) in List.zip srcFields tgtFields do
    if srcField != tgtField then
      insertTranslation (src ++ srcField) (tgt ++ tgtField)

/-- Add the structure fields of `src` to the translations dictionary
so that future uses of `to_additive` will map them to the corresponding `tgt` fields. -/
def proceedFields (src tgt : Name) : CoreM Unit := do
  let env : Environment ← getEnv
  let aux := proceedFieldsAux src tgt
  aux (fun n => do
    let fields := if isStructure env n then getStructureFieldsFlattened env n else #[]
    return fields |> .map Name.toString |> Array.toList
  )
  -- [todo] run to_additive on the constructors of n:
  -- aux (fun n => (env.constructorsOf n).mmap $ ...

private def elabToAdditiveAux
  (replaceAll trace : Bool) (tgt : Option Syntax) (doc : Option Syntax) : ValueType :=
  { replaceAll := replaceAll
    trace := trace
    tgt := match tgt with | some tgt => tgt.getId | none => Name.anonymous
    doc := doc.bind (·.isStrLit?)
    allowAutoName := false
  }

private def elabToAdditive : Syntax → CoreM ValueType
  | `(attr| to_additive $[!%$replaceAll]? $[?%$trace]? $[$tgt]? $[$doc]?) =>
    return elabToAdditiveAux replaceAll.isSome trace.isSome tgt doc
  | _ => throwUnsupportedSyntax

/-!
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
    descr :="Transport multiplicative to additive"
    add := fun src stx kind => do
      if (kind != AttributeKind.global) then
        throwError "`to_additive` can't be used as a local attribute"
      let val ← elabToAdditive stx
      let tgt ← targetName src val.tgt val.allowAutoName
      if let some tgt' := findTranslation? (← getEnv) src then
        throwError "{src} already has a to_additive translation {tgt'}."
      insertTranslation src tgt
      if let some firstMultArg ← (MetaM.run' <| firstMultiplicativeArg src) then
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
          (fun o => o |>.setBool `to_additive.replaceAll val.replaceAll
                      |>.setBool `trace.to_additive shouldTrace)
          (transformDecl src tgt)
      if let some doc := val.doc then
        addDocString tgt doc
      return ()
  }


end ToAdditive
