/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn
Ported by: E.W.Ayers
-/
import Mathlib.Data.String.Defs
import Mathlib.Lean.Expr
import Mathlib.Lean.Expr.ReplaceRec
import Lean
import Lean.Data

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Command

syntax (name := toAdditiveIgnoreArgs) "to_additive_ignore_args" num* : attr
syntax (name := toAdditiveRelevantArg) "to_additive_relevant_arg" num : attr
syntax (name := toAdditiveReorder) "to_additive_reorder" num* : attr
syntax (name := toAdditive) "to_additive" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive!) "to_additive!" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive?) "to_additive?" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive!?) "to_additive!?" (ppSpace ident)? (ppSpace str)? : attr

namespace ToAdditive

/-- Context for toAdditive expression traverser. -/
structure Context where
  (nameFn : Name → Option Name)
  (replaceAll : Bool)
  (trace : Bool)
  (relevant : NameMap Nat)
  (ignore : NameMap (List Nat))
  (reorder : NameMap (List Nat))

variable {M} [Functor M] [MonadReader Context M]

def getNameFn : M (Name → Option Name) := Context.nameFn <$> read

def runNameFn : Name → M (Option Name)
| n => (Context.nameFn . n) <$> read

def shouldTrace : M Bool := Context.trace <$> read

def ignore : Name → M (Option (List Nat))
| n => read |> Functor.map fun ctx => ctx.ignore.find? n

def getReorder : Name →  M (List Nat)
| n => read |> Functor.map fun ctx =>
  match ctx.reorder.find? n with
  | some ns => ns
  | none => []

def shouldReorder : Name → Nat → M Bool
| n, i => (i ∈ .) <$> (getReorder n)

def isRelevant : Name → Nat → M Bool
| n, i => read |> Functor.map fun ctx =>
  match ctx.relevant.find? n with
  | some j => i == j
  | none => i == 0

def replaceAll : M Bool := Context.replaceAll <$> read

variable [Monad M]

/-- Auxilliary function for `additive_test`. The bool argument *only* matters when applied
to exactly a constant. -/
private def additiveTestAux: Bool → Expr → M Bool
  | b, Expr.const n _ _           => return b || (← runNameFn n).isSome
  | b, (Expr.app e a _) => do
      if (← additiveTestAux true e) then
        return true
      if let (some n) := e.getAppFn.constName? then
        if let (some l) ← ignore n then
          if e.getAppNumArgs + 1 ∈ l then
            return true
      additiveTestAux false a
  | b, (Expr.lam n e t _) => additiveTestAux false t
  | b, (Expr.forallE n e t _) => additiveTestAux false t
  | b, (Expr.letE n g e body _) =>
    return (←additiveTestAux false e) && (← additiveTestAux false body)
  | b, _                => return true

/--
`additive_test f replace_all ignore e` tests whether the expression `e` contains no constant
`nm` that is not applied to any arguments, and such that `f nm = none`.
This is used in `@[to_additive]` for deciding which subexpressions to transform: we only transform
constants if `additive_test` applied to their first argument returns `tt`.
This means we will replace expression applied to e.g. `α` or `α × β`, but not when applied to
e.g. `ℕ` or `ℝ × α`.
`f` is the dictionary of declarations that are in the `to_additive` dictionary.
We ignore all arguments specified in the `name_map` `ignore`.
If `replace_all` is `tt` the test always return `tt`.
-/
def additiveTest (e : Expr) : M Bool := do
  if (←replaceAll) then
    return true
  else
    additiveTestAux false e

/--
`e.apply_replacement_fun f test` applies `f` to each identifier
(inductive type, defined function etc) in an expression, unless
* The identifier occurs in an application with first argument `arg`; and
* `test arg` is false.
However, if `f` is in the dictionary `relevant`, then the argument `relevant.find f`
is tested, instead of the first argument.

Reorder contains the information about what arguments to reorder:
e.g. `g x₁ x₂ x₃ ... xₙ` becomes `g x₂ x₁ x₃ ... xₙ` if `reorder.find g = some [1]`.
We assume that all functions where we want to reorder arguments are fully applied.
This can be done by applying `expr.eta_expand` first.
-/
def applyReplacementFun : Expr → ReaderT Context MetaM Expr :=
  Lean.Expr.replaceRecM fun r e =>
    match e with
    | Expr.const n ls _ => do
      let nameFun ← getNameFn
      let n := Name.mapPrefix nameFun n
      let ls : List Level ← (do
        if ← shouldReorder n 1 then
            return ls.get! 1::ls.head!::ls.drop 2
        return ls)
      return some $ Lean.mkConst n ls
    | Expr.app g x _ => do
      let gf := g.getAppFn
      let nm := gf.constName!
      let nArgs := g.getAppNumArgs
      -- e = `($gf y₁ .. yₙ $x)
      if ← shouldReorder nm nArgs then
          if ← additiveTest g.getAppArgs[0] then
            -- interchange `x` and the last argument of `g`
            let x ← r x
            let gf ← r (g.appFn!)
            let ga ← r (g.appArg!)
            return some $ mkApp2 gf x ga
      if ← isRelevant nm nArgs then
        if gf.isConst && not (← additiveTest x) then
          let x ← r x
          let args ← g.getAppArgs.mapM r
          return some $ mkApp (mkAppN gf args) x
      return none
    | _ => return none

/-- Eta expands `e` at most `n` times.-/
def etaExpandN (n : Nat) (e : Expr): MetaM Expr := do
  let t ← inferType e
  forallBoundedTelescope t (some n) fun xs _ =>
    mkLambdaFVars xs (mkAppN e xs)

/-- `e.expand` eta-expands all expressions that have as head a constant `n` in
`reorder`. They are expanded until they are applied to one more argument than the maximum in
`reorder.find n`. -/
private def expand : Expr → ReaderT Context MetaM Expr
| e => e.replaceRecM $ fun r e => do
  let e0 := e.getAppFn
  let es := e.getAppArgs
  let reorder ← getReorder e0.constName!
  if reorder.isEmpty then
    return none
  let e' := mkAppN e0 $ ← es.mapM r
  let needed_n := reorder.foldr Nat.max 0 + 1
  if needed_n ≤ es.size then
    return some e'
  else
    let e' ← etaExpandN (needed_n - es.size) e'
    return some $ e'

def updateWithFun
  (tgt : Name) (decl : ConstantInfo)
  : ReaderT Context MetaM ConstantInfo := do
  let mut decl := decl.updateName tgt
  decl := decl.updateType $ (← applyReplacementFun (← expand decl.type))
  if let some v := decl.value? then
    decl := decl.updateValue (← applyReplacementFun (← expand v))
  return decl

private def liftToMeta (declName? : Option Name := none) : ReaderT Context MetaM α → ReaderT Context CommandElabM α
| r, ctx => liftTermElabM (declName? := declName?) (r ctx)

private def liftToMeta2 (declName? : Option Name := none) : MetaM α → ReaderT Context CommandElabM α
| r, _ => liftTermElabM (declName? := declName?) r


/-- transform the declaration `src` and all declarations `pre._proof_i` occurring in `src`
using the dictionary `f`.
`replace_all`, `trace`, `ignore` and `reorder` are configuration options.
`pre` is the declaration that got the `@[to_additive]` attribute and `tgt_pre` is the target of this
declaration. -/
partial def transformDeclWithPrefixFunAux
  (pre tgt_pre : Name) : Name → ReaderT Context CommandElabM Unit := fun src => do
  -- if this declaration is not `pre` or an internal declaration, we do nothing.
  if not (src == pre || src.isInternal) then
    if (← runNameFn src).isSome then
      return ()
    else
      throwError "The declaration {pre} depends on the declaration {src} which is in the namespace {pre}, but does not have the `@[to_additive]` attribute. This is not supported. Workaround: move {src} to a different namespace."
  let env ← getEnv
  -- we find the additive name of `src`
  let tgt := src.mapPrefix (fun n => if n == pre then some tgt_pre else none)
  -- we skip if we already transformed this declaration before
  if env.contains tgt then
    return
  let decl ← getConstInfo src
  -- we first transform all the declarations of the form `pre._proof_i`
  for n in decl.type.listNamesWithPrefix pre do
    transformDeclWithPrefixFunAux pre tgt_pre n
  if let some value := decl.value? then
    for n in value.listNamesWithPrefix pre do
      transformDeclWithPrefixFunAux pre tgt_pre n
  -- we transform `decl` using `f` and the configuration options.
  -- let mx : (α:Type) → _ → ReaderT _ _ _ := monadMap x
  let decl : ConstantInfo ← liftToMeta (declName? := some tgt) $ updateWithFun tgt decl
    -- decl.update_with_fun env (name.map_prefix f) (additive_test f replace_all ignore)
    --   relevant reorder tgt
  -- o ← get_options, set_options $ o.set_bool `pp.all tt, -- print with pp.all (for debugging)
  if ← shouldTrace then
    dbg_trace "[to_additive] > generating\n{decl.name}"

  -- decorate_error (format!"@[to_additive] failed. Type mismatch in additive declaration. For help, see the docstring of `to_additive.attr`, section `Troubleshooting`. Failed to add declaration\n{pp_decl}
  let decl : Declaration := decl.toDeclaration!
  addAndCompile decl
  if isProtected (← getEnv) src then
    setEnv $ addProtected (← getEnv) tgt

def transformDeclWithPrefixFun (src tgt : Name) (attrs : List Name) : ReaderT Context CommandElabM Unit := do
  transformDeclWithPrefixFunAux src tgt src
  let eqns? ← liftToMeta2 none (getEqnsFor? src true)
  -- now transform all of the equational lemmas
  if let some eqns := eqns? then
    for src_eqn in eqns do
      transformDeclWithPrefixFunAux src tgt src_eqn
      -- -- copy attributes for the equational lemmas so that they know if they are refl lemmas
      -- let tgt_eqn := Name.mapPrefix (fun n => if n == src then some tgt else none) src_eqn
      -- for attr in attrs do
      --   copyAttribute attr src_eqn tgt_eqn
      -- -- set the transformed equation lemmas as equation lemmas for the new declaration
      -- addEqnLemma tgt_eqn
  -- for attr in attrs do
  --   copyAttributes attr src tgt
  return ()

def hasAttribute' (name : Name) : MetaM Bool :=
  pure false -- [todo] implement

/--
Find the first argument of `nm` that has a multiplicative type-class on it.
Returns 1 if there are no types with a multiplicative class as arguments.
E.g. `prod.group` returns 1, and `pi.has_one` returns 2.
-/
def firstMultiplicativeArg (nm : Name) : MetaM Nat := do
  let d ← getConstInfo nm
  forallTelescopeReducing (← getConstInfo nm).type fun xs _ => do
    let l ← xs.mapIdxM fun i x => do
      forallTelescopeReducing (← inferType x) fun ys tgt => do
        let (tgt_fn, tgt_args) := tgt.getAppFnArgs
        let n_bi := ys.size
        if let some c :=  tgt.getAppFn.constName? then
          if ← hasAttribute' `to_additive then
            return none
        if tgt_args.size > 0 then
          return tgt_args[0].getAppFn.bvarIdx?.map (i + n_bi - .)
        return none
    let l := l.filterMap id
    if l.size == 0 then
      return 1
    else
      return l.foldr min l[0]

/-- `value_type` is the type of the arguments that can be provided to `to_additive`.
`to_additive.parser` parses the provided arguments:
* `replace_all`: replace all multiplicative declarations, do not use the heuristic.
* `trace`: output the generated additive declaration.
* `tgt : name`: the name of the target (the additive declaration).
* `doc`: an optional doc string.
* if `allow_auto_name` is `ff` (default) then `@[to_additive]` will check whether the given name
  can be auto-generated.
-/
structure ValueType : Type where
  replaceAll : Bool
  trace : Bool
  tgt : Name
  doc : Option String
  allowAutoName : Bool

/-- `add_comm_prefix x s` returns `"comm_" ++ s` if `x = tt` and `s` otherwise. -/
def addCommPrefix : Bool → String → String
| true, s => "comm" ++ s -- [todo] should toupper
| false, s => s

/-- Dictionary used by `to_additive.guess_name` to autogenerate names. -/
def tr : Bool → List String → List String
| is_comm, ("one" :: "le" :: s)        => addCommPrefix is_comm "nonneg"    :: tr false s
| is_comm, ("one" :: "lt" :: s)        => addCommPrefix is_comm "pos"       :: tr false s
| is_comm, ("le" :: "one" :: s)        => addCommPrefix is_comm "nonpos"    :: tr false s
| is_comm, ("lt" :: "one" :: s)        => addCommPrefix is_comm "neg"       :: tr false s
| is_comm, ("mul" :: "single" :: s)    => addCommPrefix is_comm "single"    :: tr false s
| is_comm, ("mul" :: "support" :: s)   => addCommPrefix is_comm "support"   :: tr false s
| is_comm, ("mul" :: "tsupport" :: s)  => addCommPrefix is_comm "tsupport"  :: tr false s
| is_comm, ("mul" :: "indicator" :: s) => addCommPrefix is_comm "indicator" :: tr false s
| is_comm, ("mul" :: s)                => addCommPrefix is_comm "add"       :: tr false s
| is_comm, ("smul" :: s)               => addCommPrefix is_comm "vadd"      :: tr false s
| is_comm, ("inv" :: s)                => addCommPrefix is_comm "neg"       :: tr false s
| is_comm, ("div" :: s)                => addCommPrefix is_comm "sub"       :: tr false s
| is_comm, ("one" :: s)                => addCommPrefix is_comm "zero"      :: tr false s
| is_comm, ("prod" :: s)               => addCommPrefix is_comm "sum"       :: tr false s
| is_comm, ("finprod" :: s)            => addCommPrefix is_comm "finsum"    :: tr false s
| is_comm, ("pow" :: s)                => addCommPrefix is_comm "nsmul"     :: tr false s
| is_comm, ("npow" :: s)               => addCommPrefix is_comm "nsmul"     :: tr false s
| is_comm, ("zpow" :: s)               => addCommPrefix is_comm "zsmul"     :: tr false s
| is_comm, ("monoid" :: s)      => ("add_" ++ addCommPrefix is_comm "monoid")    :: tr false s
| is_comm, ("submonoid" :: s)   => ("add_" ++ addCommPrefix is_comm "submonoid") :: tr false s
| is_comm, ("group" :: s)       => ("add_" ++ addCommPrefix is_comm "group")     :: tr false s
| is_comm, ("subgroup" :: s)    => ("add_" ++ addCommPrefix is_comm "subgroup")  :: tr false s
| is_comm, ("semigroup" :: s)   => ("add_" ++ addCommPrefix is_comm "semigroup") :: tr false s
| is_comm, ("magma" :: s)       => ("add_" ++ addCommPrefix is_comm "magma")     :: tr false s
| is_comm, ("haar" :: s)        => ("add_" ++ addCommPrefix is_comm "haar")      :: tr false s
| is_comm, ("prehaar" :: s)     => ("add_" ++ addCommPrefix is_comm "prehaar")   :: tr false s
| is_comm, ("unit" :: s)        => ("add_" ++ addCommPrefix is_comm "unit")      :: tr false s
| is_comm, ("units" :: s)       => ("add_" ++ addCommPrefix is_comm "units")     :: tr false s
| is_comm, ("comm" :: s)        => tr true s
| is_comm, (x :: s)             => (addCommPrefix is_comm x :: tr false s)
| true, []                        => ["comm"]
| false, []                        => []

/-- Autogenerate target name for `to_additive`. -/
def guessName : String → String :=
  String.mapTokens ''' $
  λ s => String.intercalate (String.singleton '_') $
  tr false (s.splitOn "_") -- [todo] replace with camelcase logic

/-- Return the provided target name or autogenerate one if one was not provided. -/
def targetName (src tgt : Name) (dict : NameMap Name) (allowAutoName : Bool) : MetaM Name := do
  let res ← do
    if tgt.getPrefix != Name.anonymous || allowAutoName then
      return tgt
    let (Name.str pre s _) := src | throwError "to_additive: can't transport {src}"
    let tgt_auto := guessName s
    if tgt.toString == tgt_auto || tgt != src then
      dbg_trace "{src}: correctly autogenerated target name, you may remove the explicit {tgt_auto} argument."
    let pre := pre.mapPrefix dict.find?
    if tgt == Name.anonymous then
      return Name.mkStr pre tgt_auto
    else
      return  Name.mkStr pre tgt.toString
  if res == src && tgt != src then
    throwError "to_additve: can't transport {src} to itself."
  return res


section Commands

/-! An attribute that tells `@[toAdditive]` that certain arguments of this definition are not
involved when using `@[toAdditive]`.
This helps the heuristic of `@[toAdditive]` by also transforming definitions if `ℕ` or another
fixed type occurs as one of these arguments. -/

-- initialize toAdditiveIgnoreArgsAttr : ParametricAttribute (Array Nat) ←
--   registerParametricAttribute {
--     name := `toAdditiveIgnoreArgs
--     descr :=
--       "Auxiliary attribute for `toAdditive` stating that certain arguments are not additivized."
--     getParam := λ decl stx =>
--       match stx with
--         | `(attr|toAdditiveIgnoreArgs $[$ns]*) => ns.map (·.toNat)
--         | _ => throwError "unexpected toAdditiveIgnoreArgs syntax {stx}"
--   }

-- ignoreArgsAttr
-- relevantArgAttr
-- reorderAttr

end Commands

/-! An attribute that is automatically added to declarations tagged with `@[toAdditive]`, if needed.

This attribute tells which argument is the type where this declaration uses the multiplicative
structure. If there are multiple argument, we typically tag the first one.
If this argument contains a fixed type, this declaration will note be additivized.
See the Heuristics section of `toAdditive.attr` for more details.

If a declaration is not tagged, it is presumed that the first argument is relevant.
`@[toAdditive]` uses the function `toAdditive.firstMultiplicativeArg` to automatically tag
declarations. It is ok to update it manually if the automatic tagging made an error.

def getConfig : Syntax → AttrM Config
| `(attr|to_additive)   => pure {}
| `(attr|to_additive?)  => pure {trace := true}
| `(attr|to_additive!)  => pure {replace_all := true}
| `(attr|to_additive!?) => pure {replace_all := true, trace := true}
| _ => throwUnsupportedSyntax
-/

end ToAdditive

/- # examples -/

-- @[to_additive]
-- theorem mul_one' [group G] (x : G) : x * 1 = x := mul_one x
