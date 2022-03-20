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
  (f : Name → Option Name)
  (replaceAll : Bool)
  (trace : Bool)
  (relevant : NameMap Nat)
  (ignore : NameMap (List Nat))
  (reorder : NameMap (List Nat))

variable {M} [Monad M] [MonadReader Context M]

def f [MonadReader Context M]: Name → M (Option Name)
| n => return Context.f (← read) n

def ignore : Name → M (Option (List Nat))
| n => return NameMap.find? (Context.ignore (← read)) n

def getReorder : Name →  M (List Nat)
| n => do
  let r := NameMap.find? (Context.reorder (← read)) n
  match r with
  | some ns => return ns
  | none => return []

def reorder? : Name → Nat → M Bool
| n, i => return i ∈ (← getReorder n)

def relevant? : Name → Nat → M Bool
| n, i => do
  match NameMap.find? (Context.relevant (← read)) n with
  | some j => return i == j
  | none => return i == 0

def replaceAll : M Bool := return (←read).replaceAll

/-- Auxilliary function for `additive_test`. The bool argument *only* matters when applied
to exactly a constant. -/
private def additiveTestAux : Bool → Expr → M Bool
  | b, Expr.const n _ _           => return b || (← f n).isSome
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
def applyReplacementFun (f : Name → Name) (test : Expr → Bool) : Expr → M Expr :=
  Lean.Expr.replaceRecM fun r e =>
    match e with
    | Expr.const n ls _ => do
      let ls : List Level ← (do
        if ← reorder? n 1 then
            return ls.get! 1::ls.head!::ls.drop 2
        return ls)
      return some $ e.updateConst! ls
    | Expr.app g x _ => do
      let gf := g.getAppFn
      let nm := gf.constName!
      let nArgs := g.getAppNumArgs
      -- e = `($gf y₁ .. yₙ $x)
      if ← reorder? nm nArgs then
          if test g.getAppArgs[0] then
            -- interchange `x` and the last argument of `g`
            let x ← r x
            let gf ← r (g.appFn!)
            let ga ← r (g.appArg!)
            return some $ mkApp2 gf x ga
      if ← relevant? nm nArgs then
        if gf.isConst && not (test x) then
          let x ← r x
          let args ← g.getAppArgs.mapM r
          return some $ mkApp (mkAppN gf args) x
      return none
    | _ => return none

/-- Infer the type of an application of the form `f x1 x2 ... xn`, where `f` is an identifier.
This also works if `x1, ... xn` contain free variables. -/
protected def simpleInferType [MonadEnv E] [MonadError E] (e : Expr) : E Expr := do
  let Expr.const n ls _ := e.getAppFn | throwError "expression is not a constant applied to arguments"
  let es := e.getAppArgs
  let decl ← getConstInfo n
  return $ (d.type.instantiate_pis es).instantiate_univ_params $ d.univ_params.zip ls

/-- Auxilliary function for `head_eta_expand`. -/
def head_eta_expand_aux : ℕ → expr → expr → expr
| (n+1) e (pi x bi d b) :=
  lam x bi d $ head_eta_expand_aux n e b
| _ e _ := e

/-- `head_eta_expand n e t` eta-expands `e` `n` times, with the binders info and domains obtained
  by its type `t`. -/
def head_eta_expand (n : ℕ) (e t : expr) : expr :=
((e.liftVars 0 n).mk_app $ (list.range n).reverse.map var).head_eta_expand_aux n t


/-- `e.eta_expand` eta-expands all expressions that have as head a constant `n` in
`reorder`. They are expanded until they are applied to one more argument than the maximum in
`reorder.find n`. -/
protected def etaExpand [MonadEnv M] : Expr → MetaM Expr
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
    let e'_type ← Meta.inferType e'
    return some $ head_eta_expand (needed_n - es.length) e' e'_type


def updateWithFun [MonadEnv E] [Monad E] (f : Name → Name) (test : Expr → Name) (tgt : Name) (decl : ConstantInfo) : E ConstantInfo := do
  let decl := decl.updateName tgt
  let e := decl.type.etaExpand
  let decl := decl.updateType
  return decl


/-- transform the declaration `src` and all declarations `pre._proof_i` occurring in `src`
using the dictionary `f`.
`replace_all`, `trace`, `ignore` and `reorder` are configuration options.
`pre` is the declaration that got the `@[to_additive]` attribute and `tgt_pre` is the target of this
declaration. -/
def transformDeclWithPrefixFunAux
  (pre tgt_pre : Name) : Name → ReaderT Context CommandElabM Unit :=
fun src => do
  -- if this declaration is not `pre` or an internal declaration, we do nothing.
  if not (src == pre || src.isInternal) then
    if (← f src).isSome then
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
  let decl :=
    decl.update_with_fun env (name.map_prefix f) (additive_test f replace_all ignore)
      relevant reorder tgt
  -- o ← get_options, set_options $ o.set_bool `pp.all tt, -- print with pp.all (for debugging)
  let pp_decl ← pp decl
  if trace then
    dbg_trace[to_additive] "[to_additive] > generating\n{pp_decl}"

  -- decorate_error (format!"@[to_additive] failed. Type mismatch in additive declaration. For help, see the docstring of `to_additive.attr`, section `Troubleshooting`. Failed to add declaration\n{pp_decl}

/--
`applyReplacementFun f test relevant reorder e` applies `f` to each identifier in `e`, unless
* The identifier occurs in an application with first argument `arg`; and
* `test arg` is false.
If `f` is in the dictionary `relevant`, then the argument `relevant.find f` is tested,
instead of the first argument.

Furthermore, we reorder some arguments according to the dictionary `reorder`.
E.g. `g x₁ x₂ x₃ ... xₙ` becomes `g x₂ x₁ x₃ ... xₙ` if `reorder.find g = some [1]`.
We assume that all functions where we want to reorder arguments are fully applied.
This can be done by applying `Expr.etaExpand` first.
-/
partial def applyReplacementFun
  : Expr → AddM Expr :=
  Expr.replaceRecM fun r e =>
    match e with
      | Expr.const n ls _ =>
        -- if the first two arguments are reordered, we also reorder the first two universe parameters
        (if 1 ∈ (reorder.find? n).getD [] then (ls.get! 1)::ls.head!::ls.drop 2 else ls)
        |> mkConst (f n)
        |> some
      | e@(Expr.app g x _) =>
        let f := g.getAppFn
        let nm? := f.constName?
        match nm? with
        | none => none
        | some nm =>
          let nArgs := g.getAppNumArgs
          -- Do we want to reorder the last two arguments of `g`?

          if ((reorder.find? nm).getD []).contains nArgs && ((g.getAppArgs.get? 0).map test).getD true then
            -- interchange `x` and the last argument of `g`
            some $ mkApp (r g.appFn!)
            some (#[g.appFn!, x, g.appArg!], λ es => mkApp es[1] es[2])
          else if nArgs == (relevant.find? nm).getD 0 && f.isConst && !test x then
            some (g.getAppArgs.append #[x], λ es => mkAppN f es)
          else
            none
      | _ => none

/-! An attribute that tells `@[toAdditive]` that certain arguments of this definition are not
involved when using `@[toAdditive]`.
This helps the heuristic of `@[toAdditive]` by also transforming definitions if `ℕ` or another
fixed type occurs as one of these arguments. -/
initialize toAdditiveIgnoreArgsAttr : ParametricAttribute (Array Nat) ←
  registerParametricAttribute {
    name := `toAdditiveIgnoreArgs
    descr :=
      "Auxiliary attribute for `toAdditive` stating that certain arguments are not additivized."
    getParam := λ decl stx =>
      match stx with
        | `(attr|toAdditiveIgnoreArgs $[$ns]*) => ns.map (·.toNat)
        | _ => throwError "unexpected toAdditiveIgnoreArgs syntax {stx}"
  }

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


/-- `add_comm_prefix x s` returns `"comm_" ++ s` if `x = tt` and `s` otherwise. -/
def add_comm_prefix : Bool → String → String
| true, s => "comm_" ++ s
| false, s => s

/-- Dictionary used by `to_additive.guess_name` to autogenerate names. -/
def tr : Bool → List String → List String
| is_comm, ("one" :: "le" :: s)        => add_comm_prefix is_comm "nonneg"    :: tr false s
| is_comm, ("one" :: "lt" :: s)        => add_comm_prefix is_comm "pos"       :: tr false s
| is_comm, ("le" :: "one" :: s)        => add_comm_prefix is_comm "nonpos"    :: tr false s
| is_comm, ("lt" :: "one" :: s)        => add_comm_prefix is_comm "neg"       :: tr false s
| is_comm, ("mul" :: "single" :: s)    => add_comm_prefix is_comm "single"    :: tr false s
| is_comm, ("mul" :: "support" :: s)   => add_comm_prefix is_comm "support"   :: tr false s
| is_comm, ("mul" :: "tsupport" :: s)  => add_comm_prefix is_comm "tsupport"  :: tr false s
| is_comm, ("mul" :: "indicator" :: s) => add_comm_prefix is_comm "indicator" :: tr false s
| is_comm, ("mul" :: s)                => add_comm_prefix is_comm "add"       :: tr false s
| is_comm, ("smul" :: s)               => add_comm_prefix is_comm "vadd"      :: tr false s
| is_comm, ("inv" :: s)                => add_comm_prefix is_comm "neg"       :: tr false s
| is_comm, ("div" :: s)                => add_comm_prefix is_comm "sub"       :: tr false s
| is_comm, ("one" :: s)                => add_comm_prefix is_comm "zero"      :: tr false s
| is_comm, ("prod" :: s)               => add_comm_prefix is_comm "sum"       :: tr false s
| is_comm, ("finprod" :: s)            => add_comm_prefix is_comm "finsum"    :: tr false s
| is_comm, ("pow" :: s)                => add_comm_prefix is_comm "nsmul"     :: tr false s
| is_comm, ("npow" :: s)               => add_comm_prefix is_comm "nsmul"     :: tr false s
| is_comm, ("zpow" :: s)               => add_comm_prefix is_comm "zsmul"     :: tr false s
| is_comm, ("monoid" :: s)             => ("add_" ++ add_comm_prefix is_comm "monoid")    :: tr false s
| is_comm, ("submonoid" :: s)          => ("add_" ++ add_comm_prefix is_comm "submonoid") :: tr false s
| is_comm, ("group" :: s)              => ("add_" ++ add_comm_prefix is_comm "group")     :: tr false s
| is_comm, ("subgroup" :: s)           => ("add_" ++ add_comm_prefix is_comm "subgroup")  :: tr false s
| is_comm, ("semigroup" :: s)          => ("add_" ++ add_comm_prefix is_comm "semigroup") :: tr false s
| is_comm, ("magma" :: s)              => ("add_" ++ add_comm_prefix is_comm "magma")     :: tr false s
| is_comm, ("haar" :: s)               => ("add_" ++ add_comm_prefix is_comm "haar")      :: tr false s
| is_comm, ("prehaar" :: s)            => ("add_" ++ add_comm_prefix is_comm "prehaar")   :: tr false s
| is_comm, ("unit" :: s)               => ("add_" ++ add_comm_prefix is_comm "unit")      :: tr false s
| is_comm, ("units" :: s)              => ("add_" ++ add_comm_prefix is_comm "units")     :: tr false s
| is_comm, ("comm" :: s)               => tr true s
| is_comm, (x :: s)                    => (add_comm_prefix is_comm x :: tr false s)
| true, []                             => ["comm"]
| false, []                            => []

/-- Autogenerate target name for `to_additive`. -/
def guess_name : String → String :=
String.mapTokens ''' $ fun s => String.intercalate (String.singleton '_') $ tr false $ s.splitOn "_"

/-- Return the provided target name or autogenerate one if one was not provided. -/
def target_name (src tgt : Name) (dict : NameMap Name) (allow_auto_name : Bool)
  : TermElabM Name := do
  let res ←
    if (tgt.getPrefix ≠ Name.anonymous) ∨ allow_auto_name then
      -- `tgt` is a full name
      pure tgt
    else
      match src with
      | (Name.str s pre _) =>
          let tgt_auto := guess_name s
          if ((toString tgt) = tgt_auto ∧ tgt ≠ src) then
            trace[ToAdditive.target_name] "`to_additive {src}`: correctly autogenerated target name, you may remove the explicit {tgt_auto} argument."
          pure $ Name.mkStr
                (if tgt = Name.anonymous then tgt_auto else toString tgt)
                (pre.mapPrefix dict.find)
      | _ => throwError "to_additive: can't transport {src}"
  if res = src ∧ tgt ≠ src then
    throwError "to_additive: can't transport {src} to itself. Give the desired additive name explicitly using `@[to_additive additive_name]`. "
  else
    pure res

end ToAdditive

/- # examples -/

@[to_additive]
theorem mul_one' [group G] (x : G) : x * 1 = x := mul_one x
