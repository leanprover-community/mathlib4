/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

-- import Mathlib.Lean.Expr
import Lean
import Mathlib.Init.Data.List.Basic
import Mathlib.Init.Data.Nat.Basic

/-!
# Stub for implementation of the `@[simps]` attribute.

This file is currently just a stub that creates a no-operation `@[simps]` attribute.
Without this, all declarations in the mathport output for mathlib3 that use `@[simps]` fail.
With the no-operation attribute, the declarations can succeed,
but of course all later proofs that rely on the existence of the automatically generated lemmas
will fail.

Later we will need to port the implementation from mathlib3.

OLD DOC:

# simps attribute

This file defines the `@[simps]` attribute, to automatically generate `simp` lemmas
reducing a definition when projections are applied to it.

## Implementation Notes

There are three attributes being defined here
* `@[simps]` is the attribute for objects of a structure or instances of a class. It will
  automatically generate simplification lemmas for each projection of the object/instance that
  contains data. See the doc strings for `simpsAttr` and `simps_cfg` for more details and
  configuration options.
* `@[_simps_str]` is automatically added to structures that have been used in `@[simps]` at least
  once. This attribute contains the data of the projections used for this structure by all following
  invocations of `@[simps]`.
* `@[notationClass]` should be added to all classes that define notation, like `has_mul` and
  `has_zero`. This specifies that the projections that `@[simps]` used are the projections from
  these notation classes instead of the projections of the superclasses.
  Example: if `has_mul` is tagged with `@[notationClass]` then the projection used for `semigroup`
  will be `λ α hα, @has_mul.mul α (@semigroup.to_has_mul α hα)` instead of `@semigroup.mul`.

## Tags

structures, projections, simp, simplifier, generates declarations
-/

-- move
namespace String

/-- `getRest s pre` returns `some post` if `s = pre ++ post`.
  If `pre` is not a prefix of `s`, it returns `none`. -/
def getRest (s pre : String) : Option String :=
if startsWith s pre then some <| s.drop pre.length else none

end String

open Lean Meta

namespace Lean.Parser
namespace Attr

syntax (name := simps) "simps" (" (" &"config" " := " term ")")? (ppSpace ident)* : attr
syntax (name := simps?) "simps?" (" (" &"config" " := " term ")")? (ppSpace ident)* : attr

end Attr

namespace Command

syntax simpsRule.rename := ident " → " ident
syntax simpsRule.erase := "-" ident
syntax simpsRule := (simpsRule.rename <|> simpsRule.erase) &" as_prefix"?
syntax simpsProj := ident (" (" simpsRule,+ ")")?
syntax (name := initializeSimpsProjections) "initializeSimpsProjections"
  (ppSpace simpsProj)* : command
syntax (name := initializeSimpsProjections?) "initializeSimpsProjections?"
  (ppSpace simpsProj)* : command

end Command
end Lean.Parser
def foo := 1
builtin_initialize registerTraceClass `Simps.verbose
builtin_initialize registerTraceClass `Simps.debug

/--
Projection data for a single projection of a structure, consisting of the following fields:
- the name used in the generated `simp` lemmas
- an expression used by simps for the projection. It must be definitionally equal to an original
  projection (or a composition of multiple projections).
  These expressions can contain the universe parameters specified in the first argument of
  `simps_str_attr`.
- a list of natural numbers, which is the projection number(s) that have to be applied to the
  expression. For example the list `[0, 1]` corresponds to applying the first projection of the
  structure, and then the second projection of the resulting structure (this assumes that the
  target of the first projection is a structure with at least two projections).
  The composition of these projections is required to be definitionally equal to the provided
  expression.
- A boolean specifying whether `simp` lemmas are generated for this projection by default.
- A boolean specifying whether this projection is written as prefix.
-/
structure ProjectionData where
  Name : Name
  Expr : Expr
  proj_nrs : List ℕ
  is_default : Bool
  IsPrefix : Bool
  deriving Inhabited

/-- Temporary projection data parsed from `initializeSimpsProjections` before the expression
  matching this projection has been found. Only used internally in `simpsGetRawProjections`. -/
unsafe structure ParsedProjectionData where
  orig_name : Name
  -- name for this projection used in the structure definition
  new_name : Name
  -- name for this projection used in the generated `simp` lemmas
  is_default : Bool
  IsPrefix : Bool

/-- The type of rules that specify how metadata for projections in changes.
  See `initializeSimpsProjections`. -/
abbrev ProjectionRule :=
  Name × Name ⊕ Name × Bool

/-- Returns the projection information of a structure. -/
def projectionsInfo (l : List ProjectionData) (pref : String) (str : Name) : Format :=
  let ⟨defaults, nondefaults⟩ := l.partition (·.is_default)
  let toPrint : List Format :=
    defaults.map fun s =>
      let prefixStr := if s.IsPrefix then "(prefix) " else ""
      f!"Projection {prefixStr}{s.Name}: {s.Expr}"
  let print2 := String.join <| (nondefaults.map fun nm : ProjectionData => toString nm.1).intersperse ", "
  let toPrint :=
    toPrint.map toString ++
      if nondefaults.isEmpty then [] else ["No lemmas are generated for the projections: " ++ print2 ++ "."]
  let toPrint := String.join <| toPrint.intersperse "\n        > "
  f! "[simps] > {pref } {str }:\n        > {toPrint}"

/-- Auxiliary function of `getCompositeOfProjections`. -/
partial def getCompositeOfProjectionsAux : ∀ (str : Name) (proj : String) (x : Expr)
  (pos : List ℕ) (args : Array Expr), MetaM (Expr × List ℕ)
  | str, proj, x, Pos, args => do
    let env ← getEnv
    let projs := (getStructureInfo? env str).get!
    let projInfo := projs.fieldNames.toList.mapIdx
      fun n p => (fun x => (x, n, p)) <$> proj.getRest ("_" ++ p.getString!)
    if (projInfo.filterMap id).isEmpty then
      throwError "Failed to find constructor {proj.drop 1} in structure {str}."
    let (projRest, index, projName) := (projInfo.filterMap id).last!
    let strDecl := (env.find? str).get!
    let projExpr : Expr := mkConst (str ++ projName) <| strDecl.levelParams.map mkLevelParam
    let projDecl := (env.find? (str ++ projName)).get!
    let type ← inferType x
    let params := type.getAppArgs
    let newX := mkAppN (projExpr.instantiateLevelParams
      projDecl.levelParams sorry /-type.getAppFn.levelParams-/) <| params ++ [x]
    let newPos := Pos ++ [index]
    if projRest.isEmpty then return (← mkLambdaFVars args newX, newPos)
      else do
        let type ← inferType newX
        forallTelescopeReducing type fun typeArgs tgt =>
          getCompositeOfProjectionsAux tgt.getAppFn.constName! projRest (mkAppN newX typeArgs)
            newPos (args ++ typeArgs)

/-- Given a structure `str` and a projection `proj`, that could be multiple nested projections
  (separated by `_`), returns an expression that is the composition of these projections and a
  list of natural numbers, that are the projection numbers of the applied projections. -/
def getCompositeOfProjections (str : Name) (proj : String) : MetaM (Expr × List ℕ) := do
  let env ← getEnv
  let strDecl := (env.find? str).get!
  let strExpr : Expr := mkConst str <| strDecl.levelParams.map mkLevelParam
  let type ← inferType strExpr
  forallTelescopeReducing type fun typeArgs tgt => do
    let str_ap := mkAppN strExpr typeArgs
    let x := mkFVar sorry -- mk_local' `x BinderInfo.default str_ap
    getCompositeOfProjectionsAux str ("_" ++ proj) x [] <| typeArgs ++ [x]


/-- Get the projections used by `simps` associated to a given structure `str`.

  The returned information is also stored in a parameter of the attribute `@[_simps_str]`, which
  is given to `str`. If `str` already has this attribute, the information is read from this
  attribute instead. See the documentation for this attribute for the data this tactic returns.

  The returned universe levels are the universe levels of the structure. For the projections there
  are three cases
  * If the declaration `{structure_name}.simps.{projection_name}` has been declared, then the value
    of this declaration is used (after checking that it is definitionally equal to the actual
    projection. If you rename the projection name, the declaration should have the *new* projection
    name.
  * You can also declare a custom projection that is a composite of multiple projections.
  * Otherwise, for every class with the `notationClass` attribute, and the structure has an
    instance of that notation class, then the projection of that notation class is used for the
    projection that is definitionally equal to it (if there is such a projection).
    This means in practice that coercions to function types and sorts will be used instead of
    a projection, if this coercion is definitionally equal to a projection. Furthermore, for
    notation classes like `has_mul` and `has_zero` those projections are used instead of the
    corresponding projection.
    Projections for coercions and notation classes are not automatically generated if they are
    composites of multiple projections (for example when you use `extend` without the
    `olstrDeclucture_cmd`).
  * Otherwise, the projection of the structure is chosen.
    For example: ``simpsGetRawProjections env `prod`` gives the default projections
```
  ([u, v], [prod.fst.{u v}, prod.snd.{u v}])
```
    while ``simpsGetRawProjections env `equiv`` gives
```
  ([u_1, u_2], [λ α β, coe_fn, λ {α β} (e : α ≃ β), ⇑(e.symm), left_inv, right_inv])
```
    after declaring the coercion from `equiv` to function and adding the declaration
```
  def equiv.simps.invFun {α β} (e : α ≃ β) : β → α := e.symm
```

  Optionally, this command accepts three optional arguments:
  * If `trace_if_exists` the command will always generate a trace message when the structure already
    has the attribute `@[_simps_str]`.
  * The `rules` argument accepts a list of pairs `sum.inl (old_name, new_name)`. This is used to
    change the projection name `old_name` to the custom projection name `new_name`. Example:
    for the structure `equiv` the projection `toFun` could be renamed `apply`. This name will be
    used for parsing and generating projection names. This argument is ignored if the structure
    already has an existing attribute. If an element of `rules` is of the form `sum.inr name`, this
    means that the projection `name` will not be applied by default.
  * if `trc` is true, this tactic will trace information.
-/
-- if performance becomes a problem, possible heuristic: use the names of the projections to
-- skip all classes that don't have the corresponding field.
def simpsGetRawProjections (e : environment) (str : Name) (trace_if_exists : Bool := false)
    (rules : List ProjectionRule := []) (trc := false) : CoreM (List Name × List ProjectionData) := do
  let trc := trc || isTraceEnabledFor `simps.verbose
  let hasAttr ← hasAttribute `_simps_str str
  if hasAttr then do
      let data ← simps_str_attr str
      -- We always print the projections when they already exists and are called by
            -- `initializeSimpsProjections`.
            when
            (trace_if_exists || isTraceEnabledFor `simps.verbose) <|
          projectionsInfo data.2 "Already found projection information for structure" str >>= trace
      return data
    else do
      if trc then dbg_trace "[simps] > generating projection information for structure {← str}."
      whenTracing `simps.debug
          (← do
            dbg_trace "[simps] > Applying the rules {← rules}.")
      let strDecl ← (env.find? str).get!
      let rawUnivs := strDecl
      let rawLevels := rawUnivs.map (·.paramName!)
      let projs
        ← /- Figure out projections, including renamings. The information for a projection is (before we
                figure out the `expr` of the projection:
                `(original name, given name, is default, is prefix)`.
                The first projections are always the actual projections of the structure, but `rules` could
                specify custom projections that are compositions of multiple projections. -/
            e
            str
      let projs : List ParsedProjectionData := projs fun nm => ⟨nm, nm, tt, ff⟩
      let projs : List ParsedProjectionData :=
        rules
          (fun projs rule =>
            match rule with
            | (inl (old_nm, new_nm), is_prefix) =>
              if old_nm ∈ projs fun x => x then
                projs fun proj => if proj = old_nm then { proj with new_name := new_nm, IsPrefix } else proj
              else projs ++ [⟨old_nm, new_nm, tt, is_prefix⟩]
            | (inr nm, is_prefix) =>
              if nm ∈ projs fun x => x then
                projs fun proj => if proj = nm then { proj with is_default := ff, IsPrefix } else proj
              else projs ++ [⟨nm, nm, ff, is_prefix⟩])
          projs
      whenTracing `simps.debug
          (← do
            dbg_trace "[simps] > Projection info after applying the rules: {← projs}.")
      when ¬(projs fun x => x : List Name).Nodup <|
          fail <|
            "Invalid projection names. Two projections have the same name.\nThis is likely because a custom composition of projections was given the same name as an " ++
                "existing projection. Solution: rename the existing projection (before renaming the custom " ++
              "projection)."
      let raw_exprs_and_nrs
        ←/- Define the raw expressions for the projections, by default as the projections
                (as an expression), but this can be overriden by the user. -/
            projs
            fun ⟨orig_nm, new_nm, _, _⟩ => do
            let (raw_expr, nrs) ← getCompositeOfProjections str orig_nm
            let custom_proj ←
              (do
                    let decl ← e (str ++ `simps ++ new_nm)
                    let custom_proj := decl <| decl rawLevels
                    when trc
                        (← do
                          dbg_trace "[simps] > found custom projection for {(← new_nm)}:
                                    > {← custom_proj}")
                    return custom_proj) <|>
                  return raw_expr
            is_def_eq custom_proj
                  raw_expr <|>-- if the type of the expression is different, we show a different error message, because
              -- that is more likely going to be helpful.
              do
                let custom_proj_type ← infer_type custom_proj
                let raw_expr_type ← infer_type raw_expr
                let b ← succeeds (is_def_eq custom_proj_type raw_expr_type)
                if b then
                    throwError "Invalid custom projection:
                        {(← custom_proj)}
                      Expression is not definitionally equal to
                        {← raw_expr}"
                  else
                    throwError "Invalid custom projection:
                        {(← custom_proj)}
                      Expression has different type than {(← str ++ orig_nm)}. Given type:
                        {(← custom_proj_type)}
                      Expected type:
                        {← raw_expr_type}"
            return (custom_proj, nrs)
      let raw_exprs := raw_exprs_and_nrs Prod.fst
      let-- Check for other coercions and type-class arguments to use as projections instead.
        (args, _)
        ← open_pis strDecl
      let e_str := (expr.const str rawLevels).mk_app args
      let automatic_projs ← attribute.get_instances `notationClass
      let raw_exprs ←
        automatic_projs
            (fun class_nm =>
              (/- For this class, find the projection. `raw_expr` is the projection found applied to `args`,
                        and `lambda_raw_expr` has the arguments `args` abstracted. -/
                -- Note: `expr.bind_lambda` doesn't give the correct type
                /- Use this as projection, if the function reduces to a projection, and this projection has
                        not been overrriden by the user. -/
                do
                  let (is_class, projName) ← notationClass_attr class_nm
                  let projName ← projName <|> (e class_nm).map List.headₓ
                  let (raw_expr, lambda_raw_expr) ←
                    if is_class then do
                        guardₓ <| args = 1
                        let e_inst_type := (const class_nm rawLevels).mk_app args
                        let (hyp, e_inst) ← try_for 1000 (mk_conditional_instance e_str e_inst_type)
                        let raw_expr ← mk_mapp projName [args, e_inst]
                        clear hyp
                        let raw_expr_lambda ← lambdas [hyp] raw_expr
                        return (raw_expr, raw_expr_lambda args)
                      else do
                        let e_inst_type ← to_expr (((const class_nm []).app (pexpr.of_expr e_str)).app (pquote.1 _))
                        let e_inst ← try_for 1000 (mk_instance e_inst_type)
                        let raw_expr ← mk_mapp projName [e_str, none, e_inst]
                        return (raw_expr, raw_expr args)
                  let raw_expr_whnf ← whnf raw_expr
                  let relevant_proj := raw_expr_whnf
                  guardₓ <| projs fun x => x.1 = relevant_proj ∧ ¬e (str ++ `simps ++ x)
                  let pos := projs fun x => x.1 = relevant_proj
                  when trc
                      (← do
                        dbg_trace "        > using {(← projName)} instead of the default projection {← relevant_proj}.")
                  whenTracing `simps.debug
                      (← do
                        dbg_trace "[simps] > The raw projection is:
                            {← lambda_raw_expr}")
                  return <| raw_exprs Pos lambda_raw_expr) <|>
                return raw_exprs)
            raw_exprs
      let positions := raw_exprs_and_nrs Prod.snd
      let proj_names := projs fun x => x
      let defaults := projs fun x => x
      let prefixes := projs fun x => x
      let projs := proj_names ProjectionData.mk raw_exprs positions defaults prefixes
      let projs
        ←-- make all proof non-default.
            projs
            fun proj => is_proof proj >>= fun b => return <| if b then { proj with is_default := ff } else proj
      when trc <| projectionsInfo projs "generated projections for" str >>= trace
      simps_str_attr str (rawUnivs, projs) tt
      whenTracing `simps.debug
          (← do
            dbg_trace "[simps] > Generated raw projection data:
              {← (rawUnivs, projs)}")
      return (rawUnivs, projs)




/-!
-- FROM MATHLIBPORT

/-- The `@[_simps_str]` attribute specifies the preferred projections of the given structure,
used by the `@[simps]` attribute.
- This will usually be tagged by the `@[simps]` tactic.
- You can also generate this with the command `initializeSimpsProjections`.
- To change the default value, see Note [custom simps projection].
- You are strongly discouraged to add this attribute manually.
- The first argument is the list of names of the universe variables used in the structure
- The second argument is a list that consists of the projection data for each projection.
-/
@[user_attribute]
def simps_str_attr : user_attribute Unit (List Name × List ProjectionData) where
  Name := `_simps_str
  descr := "An attribute specifying the projection of the given structure."
  parser := failed

/-- The `@[notationClass]` attribute specifies that this is a notation class,
  and this notation should be used instead of projections by @[simps].
  * The first argument `tt` for notation classes and `ff` for classes applied to the structure,
    like `has_coe_to_sort` and `has_coe_toFun`
  * The second argument is the name of the projection (by default it is the first projection
    of the structure)
-/
@[user_attribute]
def notationClass_attr : user_attribute Unit (Bool × Option Name) where
  Name := `notationClass
  descr := "An attribute specifying that this is a notation class. Used by @[simps]."
  parser := Prod.mk <$> Option.isNone <$> (tk "*")? <*> ident?

attribute [notationClass]
  Zero One Add Mul Inv Neg Sub Div Dvd Mod LE LT Append HasAndthen HasUnion HasInter HasSdiff
  HasEquivₓ HasSubset HasSsubset HasEmptyc HasInsert HasSingleton HasSep HasMem Pow

attribute [notationClass* coeSort] CoeSort

attribute [notationClass* coeFn] CoeFun

/-- Parse a rule for `initializeSimpsProjections`. It is either `<name>→<name>` or `-<name>`,
  possibly following by `as_prefix`.-/
def simpsParseRule : parser ProjectionRule :=
  Prod.mk <$> ((fun x y => inl (x, y)) <$> ident <*> (tk "->" >> ident) <|> inr <$> (tk "-" >> ident)) <*>
    isSome <$> (tk "as_prefix")?

library_note "custom simps projection"/-- You can specify custom projections for the `@[simps]` attribute.
To do this for the projection `my_structure.original_projection` by adding a declaration
`my_structure.simps.my_projection` that is definitionally equal to
`my_structure.original_projection` but has the projection in the desired (simp-normal) form.
Then you can call
```
initializeSimpsProjections (original_projection → my_projection, ...)
```
to register this projection. See `initializeSimpsProjectionsCmd` for more information.

You can also specify custom projections that are definitionally equal to a composite of multiple
projections. This is often desirable when extending structures (without `olstrDeclucture_cmd`).

`has_coe_toFun` and notation class (like `has_mul`) instances will be automatically used, if they
are definitionally equal to a projection of the structure (but not when they are equal to the
composite of multiple projections).
-/


/-- This command specifies custom names and custom projections for the simp attribute `simpsAttr`.
* You can specify custom names by writing e.g.
  `initializeSimpsProjections equiv (toFun → apply, invFun → symm_apply)`.
* See Note [custom simps projection] and the examples below for information how to declare custom
  projections.
* If no custom projection is specified, the projection will be `coe_fn`/`⇑` if a `has_coe_toFun`
  instance has been declared, or the notation of a notation class (like `has_mul`) if such an
  instance is available. If none of these cases apply, the projection itself will be used.
* You can disable a projection by default by running
  `initializeSimpsProjections equiv (-invFun)`
  This will ensure that no simp lemmas are generated for this projection,
  unless this projection is explicitly specified by the user.
* If you want the projection name added as a prefix in the generated lemma name, you can add the
  `as_prefix` modifier:
  `initializeSimpsProjections equiv (toFun → coe as_prefix)`
  Note that this does not influence the parsing of projection names: if you have a declaration
  `foo` and you want to apply the projections `snd`, `coe` (which is a prefix) and `fst`, in that
  order you can run `@[simps snd_coe_fst] def foo ...` and this will generate a lemma with the
  name `coe_foo_snd_fst`.
  * Run `initializeSimpsProjections?` (or `set_option trace.simps.verbose true`)
  to see the generated projections.
* You can declare a new name for a projection that is the composite of multiple projections, e.g.
  ```
    structure A := (proj : ℕ)
    structure B extends A
    initializeSimpsProjections? B (to_A_proj → proj, -to_A)
  ```
  You can also make your custom projection that is definitionally equal to a composite of
  projections. In this case, coercions and notation classes are not automatically recognized, and
  should be manually given by giving a custom projection.
  This is especially useful when extending a structure (without `olstrDeclucture_cmd`).
  In the above example, it is desirable to add `-to_A`, so that `@[simps]` doesn't automatically
  apply the `B.to_A` projection and then recursively the `A.proj` projection in the lemmas it
  generates. If you want to get both the `foo_proj` and `foo_to_A` simp lemmas, you can use
  `@[simps, simps to_A]`.
* Running `initializeSimpsProjections my_struc` without arguments is not necessary, it has the
  same effect if you just add `@[simps]` to a declaration.
* If you do anything to change the default projections, make sure to call either `@[simps]` or
  `initializeSimpsProjections` in the same file as the structure declaration. Otherwise, you might
  have a file that imports the structure, but not your custom projections.

Some common uses:
* If you define a new homomorphism-like structure (like `mul_hom`) you can just run
  `initializeSimpsProjections` after defining the `has_coe_toFun` instance
  ```
    instance {mM : has_mul M} {mN : has_mul N} : has_coe_toFun (mul_hom M N) := ...
    initializeSimpsProjections mul_hom (toFun → apply)
  ```
  This will generate `foo_apply` lemmas for each declaration `foo`.
* If you prefer `coe_foo` lemmas that state equalities between functions, use
  `initializeSimpsProjections mul_hom (toFun → coe as_prefix)`
  In this case you have to use `@[simps {fully_applied := ff}]` or equivalently `@[simps as_fn]`
  whenever you call `@[simps]`.
* You can also initialize to use both, in which case you have to choose which one to use by default,
  by using either of the following
  ```
    initializeSimpsProjections mul_hom (toFun → apply, toFun → coe, -coe as_prefix)
    initializeSimpsProjections mul_hom (toFun → apply, toFun → coe as_prefix, -apply)
  ```
  In the first case, you can get both lemmas using `@[simps, simps coe as_fn]` and in the second
  case you can get both lemmas using `@[simps as_fn, simps apply]`.
* If your new homomorphism-like structure extends another structure (without `olstrDeclucture_cmd`)
  (like `relEmbedding`), then you have to specify explicitly that you want to use a coercion
  as a custom projection. For example
  ```
    def relEmbedding.simps.apply (h : r ↪r s) : α → β := h
    initializeSimpsProjections relEmbedding (to_embedding_toFun → apply, -to_embedding)
  ```
* If you have an isomorphism-like structure (like `equiv`) you often want to define a custom
  projection for the inverse:
  ```
    def equiv.simps.symm_apply (e : α ≃ β) : β → α := e.symm
    initializeSimpsProjections equiv (toFun → apply, invFun → symm_apply)
  ```
-/
@[user_command]
def initializeSimpsProjectionsCmd (_ : parse <| tk "initializeSimpsProjections") : parser Unit := do
  let env ← getEnv
  let trc ← isSome <$> (tk "?")?
  let ns ← (Prod.mk <$> ident <*> (tk "(" >> sep_by (tk ",") simpsParseRule <* tk ")")?)*
  ns fun data => do
      let nm ← resolve_constant data.1
      simpsGetRawProjections env nm tt (data.2.getOrElse []) trc

add_tactic_doc
  { Name := "initializeSimpsProjections", category := DocCategory.cmd,
    declNames := [`initializeSimpsProjectionsCmd], tags := ["simplification"] }

/-- Configuration options for the `@[simps]` attribute.
  * `attrs` specifies the list of attributes given to the generated lemmas. Default: ``[`simp]``.
    The attributes can be either basic attributes, or user attributes without parameters.
    There are two attributes which `simps` might add itself:
    * If ``[`simp]`` is in the list, then ``[`_refl_lemma]`` is added automatically if appropriate.
    * If the definition is marked with `@[to_additive ...]` then all generated lemmas are marked
      with `@[to_additive]`. This is governed by the `add_additive` configuration option.
  * if `simp_rhs` is `tt` then the right-hand-side of the generated lemmas will be put in
    simp-normal form. More precisely: `dsimp, simp` will be called on all these expressions.
    See note [dsimp, simp].
  * `type_md` specifies how aggressively definitions are unfolded in the type of expressions
    for the purposes of finding out whether the type is a function type.
    Default: `instances`. This will unfold coercion instances (so that a coercion to a function type
    is recognized as a function type), but not declarations like `set`.
  * `rhs_md` specifies how aggressively definition in the declaration are unfolded for the purposes
    of finding out whether it is a constructor.
    Default: `none`
    Exception: `@[simps]` will automatically add the options
    `{rhs_md := semireducible, simp_rhs := tt}` if the given definition is not a constructor with
    the given reducibility setting for `rhs_md`.
  * If `fully_applied` is `ff` then the generated `simp` lemmas will be between non-fully applied
    terms, i.e. equalities between functions. This does not restrict the recursive behavior of
    `@[simps]`, so only the "final" projection will be non-fully applied.
    However, it can be used in combination with explicit field names, to get a partially applied
    intermediate projection.
  * The option `not_recursive` contains the list of names of types for which `@[simps]` doesn't
    recursively apply projections. For example, given an equivalence `α × β ≃ β × α` one usually
    wants to only apply the projections for `equiv`, and not also those for `×`. This option is
    only relevant if no explicit projection names are given as argument to `@[simps]`.
  * The option `trace` is set to `tt` when you write `@[simps?]`. In this case, the attribute will
    print all generated lemmas. It is almost the same as setting the option `trace.simps.verbose`,
    except that it doesn't print information about the found projections.
  * if `add_additive` is `some nm` then `@[to_additive]` is added to the generated lemma. This
    option is automatically set to `tt` when the original declaration was tagged with
    `@[to_additive, simps]` (in that order), where `nm` is the additive name of the original
    declaration.
-/
structure SimpsCfg where
  attrs := [`simp]
  simpRhs := false
  typeMd := Transparency.instances
  rhsMd := Transparency.none
  fullyApplied := true
  notRecursive := [`prod, `pprod]
  trace := false
  addAdditive := @none Name
  deriving has_reflect, Inhabited

/-- A common configuration for `@[simps]`: generate equalities between functions instead equalities
  between fully applied expressions. -/
def asFn : SimpsCfg where
  fullyApplied := false

/-- A common configuration for `@[simps]`: don't tag the generated lemmas with `@[simp]`. -/
def lemmasOnly : SimpsCfg where
  attrs := []

/-- Get the projections of a structure used by `@[simps]` applied to the appropriate arguments.
  Returns a list of tuples
  ```
  (corresponding right-hand-side, given projection name, projection expression, projection numbers,
    used by default, is prefix)
  ```
  (where all fields except the first are packed in a `ProjectionData` structure)
  one for each projection. The given projection name is the name for the projection used by the user
  used to generate (and parse) projection names. For example, in the structure

  Example 1: ``simpsGetProjectionExprs env `(α × β) `(⟨x, y⟩)`` will give the output
  ```
    [(`(x), `fst, `(@prod.fst.{u v} α β), [0], tt, ff),
     (`(y), `snd, `(@prod.snd.{u v} α β), [1], tt, ff)]
  ```

  Example 2: ``simpsGetProjectionExprs env `(α ≃ α) `(⟨id, id, λ _, rfl, λ _, rfl⟩)``
  will give the output
  ```
    [(`(id), `apply, `(coe), [0], tt, ff),
     (`(id), `symm_apply, `(λ f, ⇑f.symm), [1], tt, ff),
     ...,
     ...]
  ```
-/
def simpsGetProjectionExprs (e : environment) (tgt : Expr) (rhs : Expr) (cfg : SimpsCfg) :
    tactic <| List <| expr × ProjectionData := do
  let params := get_app_args tgt
  ((-- the parameters of the structure
            params <|
            (get_app_args rhs).take params).mmap'
        fun ⟨a, b⟩ => is_def_eq a b) <|>
      fail "unreachable code (1)"
  let str := tgt.getAppFn.const_name
  let rhs_args := (get_app_args rhs).drop params.length
  let-- the fields of the object
    (rawUnivs, projDeclata)
    ← simpsGetRawProjections e str false [] cfg.trace
  let univs := rawUnivs.zip tgt.getAppFn.levelParams
  let new_projDeclata : List <| expr × ProjectionData :=
    projDeclata.map fun proj =>
      (rhs_args.inth proj.proj_nrs.head,
        { proj with expr := (proj.expr.instantiate_univ_params univs).instantiate_lambdas_or_apps params,
          proj_nrs := proj.proj_nrs.tail })
  return new_projDeclata

/-- Add a lemma with `nm` stating that `lhs = rhs`. `type` is the type of both `lhs` and `rhs`,
  `args` is the list of local constants occurring, and `univs` is the list of universe variables. -/
def simpsAddProjection (nm : Name) (type lhs rhs : Expr) (args : List expr) (univs : List Name)
    (cfg : SimpsCfg) : tactic Unit := do
  whenTracing `simps.debug
      (← do
        dbg_trace "[simps] > Planning to add the equality
                  > {(← lhs)} = ({(← rhs)} : {← type})")
  let lvl ← get_univ_level type
  let-- simplify `rhs` if `cfg.simp_rhs` is true
    (rhs, prf)
    ←
    (do
          guardₓ cfg
          let rhs' ← rhs.dsimp { failIfUnchanged := false }
          whenTracing `simps.debug <|
              when (rhs ≠ rhs')
                (← do
                  dbg_trace "[simps] > `dsimp` simplified rhs to
                            > {← rhs'}")
          let (rhsprf1, rhsprf2, ns) ← rhs'.simp { failIfUnchanged := false }
          whenTracing `simps.debug <|
              when (rhs' ≠ rhsprf1)
                (← do
                  dbg_trace "[simps] > `simp` simplified rhs to
                            > {← rhsprf1}")
          return (Prod.mk rhsprf1 rhsprf2)) <|>
        return (rhs, const `eq.refl [lvl] type lhs)
  let eq_ap := const `eq [lvl] type lhs rhs
  let decl_name ← get_unused_decl_name nm
  let decl_type := eq_ap.pis args
  let decl_value := prf.lambdas args
  let decl := declaration.thm decl_name univs decl_type (pure decl_value)
  when cfg
      (← do
        dbg_trace "[simps] > adding projection {(← decl_name)}:
                  > {← decl_type}")
  decorate_error ("Failed to add projection lemma " ++ decl_name ++ ". Nested error:") <| add_decl decl
  let b ← succeeds <| is_def_eq lhs rhs
  when (b ∧ `simp ∈ cfg) (set_basic_attribute `_refl_lemma decl_name tt)
  cfg fun nm => set_attribute nm decl_name tt
  when cfg <| to_additive.attr decl_name ⟨ff, cfg, cfg, none, tt⟩ tt

/-- Derive lemmas specifying the projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  `to_apply` is non-empty after a custom projection that is a composition of multiple projections
  was just used. In that case we need to apply these projections before we continue changing lhs. -/
def simpsAddProjections :
    ∀ e : environment nm : Name type lhs rhs : Expr args : List expr univs : List Name must_be_str : Bool cfg : SimpsCfg
      todo : List Stringₓ to_apply : List ℕ, tactic Unit
  | e, nm, type, lhs, rhs, args, univs, must_be_str, cfg, todo, to_apply => do
    -- we don't want to unfold non-reducible definitions (like `set`) to apply more arguments
        whenTracing
        `simps.debug
        (← do
          dbg_trace "[simps] > Type of the expression before normalizing: {← type}")
    let (typeArgs, tgt) ← open_pis_whnf type cfg.typeMd
    whenTracing `simps.debug
        (← do
          dbg_trace "[simps] > Type after removing pi's: {← tgt}")
    let tgt ← whnf tgt
    whenTracing `simps.debug
        (← do
          dbg_trace "[simps] > Type after reduction: {← tgt}")
    let new_args := args ++ typeArgs
    let lhs_ap := lhs.instantiate_lambdas_or_apps typeArgs
    let rhs_ap := rhs.instantiate_lambdas_or_apps typeArgs
    let str := tgt.getAppFn.const_name
    let-- We want to generate the current projection if it is in `todo`
    todo_next := todo.filter (· ≠ "")
    /- Don't recursively continue if `str` is not a structure or if the structure is in
            `not_recursive`. -/
        if e str ∧ ¬(todo = [] ∧ str ∈ cfg ∧ ¬must_be_str) then do
        let [intro] ← return <| e str | fail "unreachable code (3)"
        let rhs_whnf ← whnf rhs_ap cfg
        let (rhs_ap, todo_now)
          ←-- `todo_now` means that we still have to generate the current simp lemma
              if ¬is_constant_of rhs_ap intro ∧ is_constant_of rhs_whnf intro then
              /- If this was a desired projection, we want to apply it before taking the whnf.
                          However, if the current field is an eta-expansion (see below), we first want
                          to eta-reduce it and only then construct the projection.
                          This makes the flow of this function messy. -/
                  when
                  ("" ∈ todo ∧ to_apply = [])
                  (if cfg then simpsAddProjection nm tgt lhs_ap rhs_ap new_args univs cfg
                  else simpsAddProjection nm type lhs rhs args univs cfg) >>
                return (rhs_whnf, ff)
            else return (rhs_ap, "" ∈ todo ∧ to_apply = [])
        if is_constant_of (getAppFn rhs_ap) intro then do
            let projInfo
              ←-- if the value is a constructor application
                  simpsGetProjectionExprs
                  e tgt rhs_ap cfg
            whenTracing `simps.debug
                (← do
                  dbg_trace "[simps] > Raw projection information:
                      {← projInfo}")
            let eta ← rhs_ap
            let-- check whether `rhs_ap` is an eta-expansion
            rhs_ap := eta rhs_ap
            -- eta-reduce `rhs_ap`
                  /- As a special case, we want to automatically generate the current projection if `rhs_ap`
                          was an eta-expansion. Also, when this was a desired projection, we need to generate the
                          current projection if we haven't done it above. -/
                  when
                  (todo_now ∨ todo = [] ∧ eta ∧ to_apply = []) <|
                if cfg then simpsAddProjection nm tgt lhs_ap rhs_ap new_args univs cfg
                else simpsAddProjection nm type lhs rhs args univs cfg
            -- If we are in the middle of a composite projection.
                  when
                  (to_apply ≠ []) <|
                do
                let ⟨new_rhs, proj, projExprxpr, proj_nrs, is_default, is_prefix⟩ ← return <| projInfo to_apply
                let new_type ← infer_type new_rhs
                whenTracing `simps.debug
                    (← do
                      dbg_trace "[simps] > Applying a custom composite projection. Current lhs:
                                >  {← lhs_ap}")
                simpsAddProjections e nm new_type lhs_ap new_rhs new_args univs ff cfg todo to_apply
            /- We stop if no further projection is specified or if we just reduced an eta-expansion and we
                        automatically choose projections -/
                  when
                  ¬(to_apply ≠ [] ∨ todo = [""] ∨ eta ∧ todo = []) <|
                do
                let projs : List Name := projInfo fun x => x
                let todo := if to_apply = [] then todo_next else todo
                -- check whether all elements in `todo` have a projection as prefix
                      guardₓ
                      (todo fun x => projs fun proj => ("_" ++ proj).isPrefixOf x) <|>
                    let x := (todo fun x => projs fun proj => ¬("_" ++ proj).isPrefixOf x).iget
                    let simp_lemma := nm x
                    let needed_proj := (x '_').tail.head
                    throwError
                      "Invalid simp lemma {(←
                        simp_lemma)}. Structure {(← str)} does not have projection {(← needed_proj)}.
                      The known projections are:
                        {(← projs)}
                      You can also see this information by running
                        `initializeSimpsProjections? {← str}`.
                      Note: these projection names might not correspond to the projection names of the structure."
                projInfo fun proj_nr ⟨new_rhs, proj, projExprxpr, proj_nrs, is_default, is_prefix⟩ => do
                    let new_type ← infer_type new_rhs
                    let new_todo := todo.filter_map fun x => x ("_" ++ proj)
                    -- we only continue with this field if it is non-propositional or mentioned in todo
                          when
                          (is_default ∧ todo = [] ∨ new_todo ≠ []) <|
                        do
                        let new_lhs := projExprxpr [lhs_ap]
                        let new_nm := nm proj is_prefix
                        let new_cfg :=
                          { cfg with addAdditive := cfg fun nm => nm (to_additive.guess_name proj) is_prefix }
                        whenTracing `simps.debug
                            (← do
                              dbg_trace "[simps] > Recursively add projections for:
                                        >  {← new_lhs}")
                        simpsAddProjections e new_nm new_type new_lhs new_rhs new_args univs ff new_cfg new_todo
                            proj_nrs
          else-- if I'm about to run into an error, try to set the transparency for `rhs_md` higher.
              if cfg = transparency.none ∧ (must_be_str ∨ todo_next ≠ [] ∨ to_apply ≠ []) then do
              when cfg
                  (← do
                    dbg_trace "[simps] > The given definition is not a constructor application:
                              >   {← rhs_ap}
                              > Retrying with the options \{ rhs_md := semireducible, simp_rhs := tt}.")
              simpsAddProjections e nm type lhs rhs args univs must_be_str
                  { cfg with rhsMd := semireducible, simpRhs := tt } todo to_apply
            else do
              when (to_apply ≠ []) <|
                  throwError "Invalid simp lemma {(← nm)}.
                    The given definition is not a constructor application:
                      {← rhs_ap}"
              when must_be_str <|
                  throwError "Invalid `simps` attribute. The body is not a constructor application:
                      {← rhs_ap}"
              when (todo_next ≠ []) <|
                  throwError "Invalid simp lemma {(← nm todo_next)}.
                    The given definition is not a constructor application:
                      {← rhs_ap}"
              if cfg then simpsAddProjection nm tgt lhs_ap rhs_ap new_args univs cfg
                else simpsAddProjection nm type lhs rhs args univs cfg
      else do
        when must_be_str <| throwError "Invalid `simps` attribute. Target {← str} is not a structure"
        when (todo_next ≠ [] ∧ str ∉ cfg) <|
            let first_todo := todo_next
            throwError "Invalid simp lemma {(← nm first_todo)}.
              Projection {← (first_todo '_').tail.head} doesn't exist, because target is not a structure."
        if cfg then simpsAddProjection nm tgt lhs_ap rhs_ap new_args univs cfg
          else simpsAddProjection nm type lhs rhs args univs cfg

/-- `simpsTac` derives `simp` lemmas for all (nested) non-Prop projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  If `short_nm` is true, the generated names will only use the last projection name.
  If `trc` is true, trace as if `trace.simps.verbose` is true. -/
def simpsTac (nm : Name) (cfg : SimpsCfg := {  }) (todo : List Stringₓ := []) (trc := false) : tactic Unit := do
  let env ← getEnv
  let d ← e.get nm
  let lhs : Expr := const d.to_name d.levelParams
  let todo := todo.dedup.map fun proj => "_" ++ proj
  let cfg := { cfg with trace := cfg.trace || isTraceEnabledFor `simps.verbose || trc }
  let b ← hasAttribute' `to_additive nm
  let cfg ←
    if b then do
        let dict ← to_additive.aux_attr.get_cache
        when cfg
            (← do
              dbg_trace "[simps] > @[to_additive] will be added to all generated lemmas.")
        return { cfg with addAdditive := dict nm }
      else return cfg
  simpsAddProjections e nm d lhs d [] d tt cfg todo []

/-- The parser for the `@[simps]` attribute. -/
def simpsParser : parser (Bool × List Stringₓ × SimpsCfg) := do
  -- note: we don't check whether the user has written a nonsense namespace in an argument.
        Prod.mk <$>
        isSome <$> (tk "?")? <*>
      (Prod.mk <$> many (name.last <$> ident) <*> do
        let some e ← parser.pexpr? | return {  }
        eval_pexpr SimpsCfg e)

/-- The `@[simps]` attribute automatically derives lemmas specifying the projections of this
declaration.

Example:
```lean
@[simps] def foo : ℕ × ℤ := (1, 2)
```
derives two `simp` lemmas:
```lean
@[simp] lemma foo_fst : foo.fst = 1
@[simp] lemma foo_snd : foo.snd = 2
```

* It does not derive `simp` lemmas for the prop-valued projections.
* It will automatically reduce newly created beta-redexes, but will not unfold any definitions.
* If the structure has a coercion to either sorts or functions, and this is defined to be one
  of the projections, then this coercion will be used instead of the projection.
* If the structure is a class that has an instance to a notation class, like `has_mul`, then this
  notation is used instead of the corresponding projection.
* You can specify custom projections, by giving a declaration with name
  `{structure_name}.simps.{projection_name}`. See Note [custom simps projection].

  Example:
  ```lean
  def equiv.simps.invFun (e : α ≃ β) : β → α := e.symm
  @[simps] def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩
  ```
  generates
  ```
  @[simp] lemma equiv.trans_toFun : ∀ {α β γ} (e₁ e₂) (a : α), ⇑(e₁.trans e₂) a = (⇑e₂ ∘ ⇑e₁) a
  @[simp] lemma equiv.trans_invFun : ∀ {α β γ} (e₁ e₂) (a : γ),
    ⇑((e₁.trans e₂).symm) a = (⇑(e₁.symm) ∘ ⇑(e₂.symm)) a
  ```

* You can specify custom projection names, by specifying the new projection names using
  `initializeSimpsProjections`.
  Example: `initializeSimpsProjections equiv (toFun → apply, invFun → symm_apply)`.
  See `initializeSimpsProjectionsCmd` for more information.

* If one of the fields itself is a structure, this command will recursively create
  `simp` lemmas for all fields in that structure.
  * Exception: by default it will not recursively create `simp` lemmas for fields in the structures
    `prod` and `pprod`. You can give explicit projection names or change the value of
    `simps_cfg.not_recursive` to override this behavior.

  Example:
  ```lean
  structure my_prod (α β : Type*) := (fst : α) (snd : β)
  @[simps] def foo : prod ℕ ℕ × my_prod ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_snd_fst : foo.snd.fst = 3
  @[simp] lemma foo_snd_snd : foo.snd.snd = 4
  ```

* You can use `@[simps proj1 proj2 ...]` to only generate the projection lemmas for the specified
  projections.
* Recursive projection names can be specified using `proj1_proj2_proj3`.
  This will create a lemma of the form `foo.proj1.proj2.proj3 = ...`.

  Example:
  ```lean
  structure my_prod (α β : Type*) := (fst : α) (snd : β)
  @[simps fst fst_fst snd] def foo : prod ℕ ℕ × my_prod ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_fst_fst : foo.fst.fst = 1
  @[simp] lemma foo_snd : foo.snd = {fst := 3, snd := 4}
  ```
* If one of the values is an eta-expanded structure, we will eta-reduce this structure.

  Example:
  ```lean
  structure equiv_plus_data (α β) extends α ≃ β := (data : bool)
  @[simps] def bar {α} : equiv_plus_data α α := { data := tt, ..equiv.refl α }
  ```
  generates the following:
  ```lean
  @[simp] lemma bar_to_equiv : ∀ {α : Sort*}, bar.to_equiv = equiv.refl α
  @[simp] lemma bar_data : ∀ {α : Sort*}, bar.data = tt
  ```
  This is true, even though Lean inserts an eta-expanded version of `equiv.refl α` in the
  definition of `bar`.
* For configuration options, see the doc string of `simps_cfg`.
* The precise syntax is `('simps' ident* e)`, where `e` is an expression of type `simps_cfg`.
* `@[simps]` reduces let-expressions where necessary.
* When option `trace.simps.verbose` is true, `simps` will print the projections it finds and the
  lemmas it generates. The same can be achieved by using `@[simps?]`, except that in this case it
  will not print projection information.
* Use `@[to_additive, simps]` to apply both `to_additive` and `simps` to a definition, making sure
  that `simps` comes after `to_additive`. This will also generate the additive versions of all
  `simp` lemmas.
-/
/- If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens, so is not included in the official doc). -/
@[user_attribute]
def simpsAttr : user_attribute Unit (Bool × List Stringₓ × SimpsCfg) where
  Name := `simps
  descr := "Automatically derive lemmas specifying the projections of this declaration."
  parser := simpsParser
  after_set :=
    some fun n _ persistent => do
      guardₓ persistent <|> fail "`simps` currently cannot be used as a local attribute"
      let (trc, todo, cfg) ← simpsAttr.get_param n
      simpsTac n cfg todo trc

add_tactic_doc { Name := "simps", category := DocCategory.attr, declNames := [`simpsAttr], tags := ["simplification"] }



-/


/--
  Defines the user attribute `simps` for automatic generation of `@[simp]` lemmas for projections.
-/
initialize simpsAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `simps
    descr := "Automatically derive lemmas specifying the projections of this declaration.",
    getParam := fun
    -- TODO implement support for `config := ...`
    | _, `(attr|simps $[$ids]*) => pure $ ids.map (·.getId.eraseMacroScopes)
    | _, stx => throwError "unexpected simps syntax {stx}"
  }

/-!
-- FROM LEAN 3

import tactic.protected
import algebra.group.to_additive

section
open format
meta instance : has_to_tactic_format ProjectionData :=
⟨λ ⟨a, b, c, d, e⟩, (λ x, group $ nest 1 $ to_fmt "⟨"  ++ to_fmt a ++ to_fmt "," ++ line ++ x ++
  to_fmt "," ++ line ++ to_fmt c ++ to_fmt "," ++ line ++ to_fmt d ++ to_fmt "," ++ line ++
  to_fmt e ++ to_fmt "⟩") <$> pp b⟩

meta instance : has_to_format ParsedProjectionData :=
⟨λ ⟨a, b, c, d⟩, group $ nest 1 $ to_fmt "⟨"  ++ to_fmt a ++ to_fmt "," ++ line ++ to_fmt b ++
  to_fmt "," ++ line ++ to_fmt c ++ to_fmt "," ++ line ++ to_fmt d ++ to_fmt "⟩"⟩
end

/--
The `@[_simps_str]` attribute specifies the preferred projections of the given structure,
used by the `@[simps]` attribute.
- This will usually be tagged by the `@[simps]` tactic.
- You can also generate this with the command `initializeSimpsProjections`.
- To change the default value, see Note [custom simps projection].
- You are strongly discouraged to add this attribute manually.
- The first argument is the list of names of the universe variables used in the structure
- The second argument is a list that consists of the projection data for each projection.
-/
@[user_attribute] meta def simps_str_attr :
  user_attribute unit (list name × list ProjectionData) :=
{ name := `_simps_str,
  descr := "An attribute specifying the projection of the given structure.",
  parser := failed }

/--
  The `@[notationClass]` attribute specifies that this is a notation class,
  and this notation should be used instead of projections by @[simps].
  * The first argument `tt` for notation classes and `ff` for classes applied to the structure,
    like `has_coe_to_sort` and `has_coe_toFun`
  * The second argument is the name of the projection (by default it is the first projection
    of the structure)
-/
@[user_attribute] meta def notationClass_attr : user_attribute unit (bool × option name) :=
{ name := `notationClass,
  descr := "An attribute specifying that this is a notation class. Used by @[simps].",
  parser := prod.mk <$> (option.is_none <$> (tk "*")?) <*> ident? }

attribute [notationClass] has_zero has_one has_add has_mul has_inv has_neg has_sub has_div has_dvd
  has_mod has_le has_lt has_append has_andthen has_union has_inter has_sdiff has_equiv has_subset
  has_ssubset has_emptyc has_insert has_singleton has_sep has_mem has_pow

attribute [notationClass* coe_sort] has_coe_to_sort
attribute [notationClass* coe_fn] has_coe_toFun

/-- Returns the projection information of a structure. -/
meta def projectionsInfo (l : list ProjectionData) (pref : string) (str : name) : TacticM Format :=
do
  ⟨defaults, nondefaults⟩ ← return $ l.partition_map $
    λ s, if s.is_default then inl s else inr s,
  toPrint ← defaults.mmap $ λ s, to_string <$>
    let prefix_str := if s.is_prefix then "(prefix) " else "" in
    pformat!"Projection {prefix_str}{s.name}: {s.expr}",
  let print2 :=
    string.join $ (nondefaults.map (λ nm : ProjectionData, to_string nm.1)).intersperse ", ",
  let toPrint := toPrint ++ if nondefaults.length = 0 then [] else
    ["No lemmas are generated for the projections: " ++ print2 ++ "."],
  let toPrint := string.join $ toPrint.intersperse "\n        > ",
  return format!"[simps] > {pref} {str}:\n        > {toPrint}"

/-- Auxiliary function of `getCompositeOfProjections`. -/
meta def getCompositeOfProjectionsAux : Π (str : name) (proj : string) (x : Expr)
  (pos : list ℕ) (args : list expr), tactic (expr × list ℕ) | str proj x pos args := do
  e ← getEnv,
  projs ← e.structure_fields str,
  let projInfo := projs.map_with_index $ λ n p, (λ x, (x, n, p)) <$> proj.get_rest ("_" ++ p.last),
  when (projInfo.filter_map id = []) $
    fail!"Failed to find constructor {proj.popn 1} in structure {str}.",
  (projRest, index, projName) ← return (projInfo.filter_map id).ilast,
  strDecl ← e.get str,
  let projExpr : Expr := const (str ++ projName) strDecl.levelParams,
  projDecl ← e.get (str ++ projName),
  type ← infer_type x,
  let params := get_app_args type,
  let univs := projDecl.univ_params.zip type.getAppFn.levelParams,
  let newX := (projExpr.instantiate_univ_params univs).mk_app $ params ++ [x],
  let newPos := pos ++ [index],
  if projRest.is_empty then return (newX.lambdas args, newPos) else do
    type ← infer_type newX,
    (typeArgs, tgt) ← open_pis_whnf type,
    let newStr := tgt.getAppFn.const_name,
    getCompositeOfProjectionsAux newStr projRest (newX.mk_app typeArgs) newPos
      (args ++ typeArgs)

/-- Given a structure `str` and a projection `proj`, that could be multiple nested projections
  (separated by `_`), returns an expression that is the composition of these projections and a
  list of natural numbers, that are the projection numbers of the applied projections. -/
meta def getCompositeOfProjections (str : name) (proj : string) : tactic (expr × list ℕ) := do
  e ← getEnv,
  strDecl ← e.get str,
  let strExpr : Expr := const str strDecl.levelParams,
  type ← infer_type strExpr,
  (typeArgs, tgt) ← open_pis_whnf type,
  let str_ap := strExpr.mk_app typeArgs,
  x ← mk_local' `x binder_info.default str_ap,
  getCompositeOfProjectionsAux str ("_" ++ proj) x [] $ typeArgs ++ [x]

/--
  Get the projections used by `simps` associated to a given structure `str`.

  The returned information is also stored in a parameter of the attribute `@[_simps_str]`, which
  is given to `str`. If `str` already has this attribute, the information is read from this
  attribute instead. See the documentation for this attribute for the data this tactic returns.

  The returned universe levels are the universe levels of the structure. For the projections there
  are three cases
  * If the declaration `{structure_name}.simps.{projection_name}` has been declared, then the value
    of this declaration is used (after checking that it is definitionally equal to the actual
    projection. If you rename the projection name, the declaration should have the *new* projection
    name.
  * You can also declare a custom projection that is a composite of multiple projections.
  * Otherwise, for every class with the `notationClass` attribute, and the structure has an
    instance of that notation class, then the projection of that notation class is used for the
    projection that is definitionally equal to it (if there is such a projection).
    This means in practice that coercions to function types and sorts will be used instead of
    a projection, if this coercion is definitionally equal to a projection. Furthermore, for
    notation classes like `has_mul` and `has_zero` those projections are used instead of the
    corresponding projection.
    Projections for coercions and notation classes are not automatically generated if they are
    composites of multiple projections (for example when you use `extend` without the
    `olstrDeclucture_cmd`).
  * Otherwise, the projection of the structure is chosen.
    For example: ``simpsGetRawProjections env `prod`` gives the default projections
```
  ([u, v], [prod.fst.{u v}, prod.snd.{u v}])
```
    while ``simpsGetRawProjections env `equiv`` gives
```
  ([u_1, u_2], [λ α β, coe_fn, λ {α β} (e : α ≃ β), ⇑(e.symm), left_inv, right_inv])
```
    after declaring the coercion from `equiv` to function and adding the declaration
```
  def equiv.simps.invFun {α β} (e : α ≃ β) : β → α := e.symm
```

  Optionally, this command accepts three optional arguments:
  * If `trace_if_exists` the command will always generate a trace message when the structure already
    has the attribute `@[_simps_str]`.
  * The `rules` argument accepts a list of pairs `sum.inl (old_name, new_name)`. This is used to
    change the projection name `old_name` to the custom projection name `new_name`. Example:
    for the structure `equiv` the projection `toFun` could be renamed `apply`. This name will be
    used for parsing and generating projection names. This argument is ignored if the structure
    already has an existing attribute. If an element of `rules` is of the form `sum.inr name`, this
    means that the projection `name` will not be applied by default.
  * if `trc` is true, this tactic will trace information.
-/
-- if performance becomes a problem, possible heuristic: use the names of the projections to
-- skip all classes that don't have the corresponding field.
meta def simpsGetRawProjections (e : environment) (str : name) (trace_if_exists : bool := ff)
  (rules : list projection_rule := []) (trc := ff) :
  tactic (list name × list ProjectionData) := do
  let trc := trc || isTraceEnabledFor `simps.verbose,
  hasAttr ← hasAttribute' `_simps_str str,
  if hasAttr then do
    data ← simps_str_attr.get_param str,
    -- We always print the projections when they already exists and are called by
    -- `initializeSimpsProjections`.
    when (trace_if_exists || isTraceEnabledFor `simps.verbose) $ projectionsInfo data.2
      "Already found projection information for structure" str >>= trace,
    return data
  else do
    when trc trace!"[simps] > generating projection information for structure {str}.",
    whenTracing `simps.debug trace!"[simps] > Applying the rules {rules}.",
    strDecl ← e.get str,
    let rawUnivs := strDecl.univ_params,
    let rawLevels := level.param <$> rawUnivs,
    /- Figure out projections, including renamings. The information for a projection is (before we
    figure out the `expr` of the projection:
    `(original name, given name, is default, is prefix)`.
    The first projections are always the actual projections of the structure, but `rules` could
    specify custom projections that are compositions of multiple projections. -/
    projs ← e.structure_fields str,
    let projs : list ParsedProjectionData := projs.map $ λ nm, ⟨nm, nm, tt, ff⟩,
    let projs : list ParsedProjectionData := rules.foldl (λ projs rule,
      match rule with
      | (inl (old_nm, new_nm), is_prefix) := if old_nm ∈ projs.map (λ x, x.new_name) then
        projs.map $ λ proj,
          if proj.new_name = old_nm then
            { new_name := new_nm, is_prefix := is_prefix, ..proj } else
            proj else
        projs ++ [⟨old_nm, new_nm, tt, is_prefix⟩]
      | (inr nm, is_prefix) := if nm ∈ projs.map (λ x, x.new_name) then
        projs.map $ λ proj, if proj.new_name = nm then
          { is_default := ff, is_prefix := is_prefix, ..proj } else
          proj else
        projs ++ [⟨nm, nm, ff, is_prefix⟩]
      end) projs,
    whenTracing `simps.debug trace!"[simps] > Projection info after applying the rules: {projs}.",
    when ¬ (projs.map $ λ x, x.new_name : list name).nodup $
      fail $ "Invalid projection names. Two projections have the same name.
This is likely because a custom composition of projections was given the same name as an " ++
"existing projection. Solution: rename the existing projection (before renaming the custom " ++
"projection).",
    /- Define the raw expressions for the projections, by default as the projections
    (as an expression), but this can be overriden by the user. -/
    raw_exprs_and_nrs ← projs.mmap $ λ ⟨orig_nm, new_nm, _, _⟩, do
    { (raw_expr, nrs) ← getCompositeOfProjections str orig_nm.last,
      custom_proj ← do
      { decl ← e.get (str ++ `simps ++ new_nm.last),
        let custom_proj := decl.value.instantiate_univ_params $ decl.univ_params.zip rawLevels,
        when trc trace!
          "[simps] > found custom projection for {new_nm}:\n        > {custom_proj}",
        return custom_proj } <|> return raw_expr,
      is_def_eq custom_proj raw_expr <|>
        -- if the type of the expression is different, we show a different error message, because
        -- that is more likely going to be helpful.
        do
        { custom_proj_type ← infer_type custom_proj,
          raw_expr_type ← infer_type raw_expr,
          b ← succeeds (is_def_eq custom_proj_type raw_expr_type),
          if b then fail!"Invalid custom projection:\n  {custom_proj}
Expression is not definitionally equal to\n  {raw_expr}"
          else fail!"Invalid custom projection:\n  {custom_proj}
Expression has different type than {str ++ orig_nm}. Given type:\n  {custom_proj_type}
Expected type:\n  {raw_expr_type}" },
      return (custom_proj, nrs) },
    let raw_exprs := raw_exprs_and_nrs.map prod.fst,
    /- Check for other coercions and type-class arguments to use as projections instead. -/
    (args, _) ← open_pis strDecl.type,
    let e_str := (expr.const str rawLevels).mk_app args,
    automatic_projs ← attribute.get_instances `notationClass,
    raw_exprs ← automatic_projs.mfoldl (λ (raw_exprs : list expr) class_nm, do
    { (is_class, projName) ← notationClass_attr.get_param class_nm,
      projName ← projName <|> (e.structure_fields_full class_nm).map list.head,
      /- For this class, find the projection. `raw_expr` is the projection found applied to `args`,
        and `lambda_raw_expr` has the arguments `args` abstracted. -/
      (raw_expr, lambda_raw_expr) ← if is_class then (do
        guard $ args.length = 1,
        let e_inst_type := (const class_nm rawLevels).mk_app args,
        (hyp, e_inst) ← try_for 1000 (mk_conditional_instance e_str e_inst_type),
        raw_expr ← mk_mapp projName [args.head, e_inst],
        clear hyp,
        -- Note: `expr.bind_lambda` doesn't give the correct type
        raw_expr_lambda ← lambdas [hyp] raw_expr,
        return (raw_expr, raw_expr_lambda.lambdas args))
      else (do
        e_inst_type ← to_expr (((const class_nm []).app (pexpr.of_expr e_str)).app ``(_)),
        e_inst ← try_for 1000 (mk_instance e_inst_type),
        raw_expr ← mk_mapp projName [e_str, none, e_inst],
        return (raw_expr, raw_expr.lambdas args)),
      raw_expr_whnf ← whnf raw_expr,
      let relevant_proj := raw_expr_whnf.binding_body.getAppFn.const_name,
      /- Use this as projection, if the function reduces to a projection, and this projection has
        not been overrriden by the user. -/
      guard $ projs.any $
        λ x, x.1 = relevant_proj.last ∧ ¬ e.contains (str ++ `simps ++ x.new_name.last),
      let pos := projs.find_index (λ x, x.1 = relevant_proj.last),
      when trc trace!
        "        > using {projName} instead of the default projection {relevant_proj.last}.",
      whenTracing `simps.debug trace!"[simps] > The raw projection is:\n  {lambda_raw_expr}",
      return $ raw_exprs.update_nth pos lambda_raw_expr } <|> return raw_exprs) raw_exprs,
    let positions := raw_exprs_and_nrs.map prod.snd,
    let proj_names := projs.map (λ x, x.new_name),
    let defaults := projs.map (λ x, x.is_default),
    let prefixes := projs.map (λ x, x.is_prefix),
    let projs := proj_names.zip_with5 ProjectionData.mk raw_exprs positions defaults prefixes,
    /- make all proof non-default. -/
    projs ← projs.mmap $ λ proj,
      is_proof proj.expr >>= λ b, return $ if b then { is_default := ff, .. proj } else proj,
    when trc $ projectionsInfo projs "generated projections for" str >>= trace,
    simps_str_attr.set str (rawUnivs, projs) tt,
    whenTracing `simps.debug trace!
       "[simps] > Generated raw projection data: \n{(rawUnivs, projs)}",
    return (rawUnivs, projs)

/-- Parse a rule for `initializeSimpsProjections`. It is either `<name>→<name>` or `-<name>`,
  possibly following by `as_prefix`.-/
meta def simpsParseRule : parser projection_rule :=
prod.mk <$>
  ((λ x y, inl (x, y)) <$> ident <*> (tk "->" >> ident) <|> inr <$> (tk "-" >> ident)) <*>
  isSome <$> (tk "as_prefix")?

/--
You can specify custom projections for the `@[simps]` attribute.
To do this for the projection `my_structure.original_projection` by adding a declaration
`my_structure.simps.my_projection` that is definitionally equal to
`my_structure.original_projection` but has the projection in the desired (simp-normal) form.
Then you can call
```
initializeSimpsProjections (original_projection → my_projection, ...)
```
to register this projection. See `initializeSimpsProjectionsCmd` for more information.

You can also specify custom projections that are definitionally equal to a composite of multiple
projections. This is often desirable when extending structures (without `olstrDeclucture_cmd`).

`has_coe_toFun` and notation class (like `has_mul`) instances will be automatically used, if they
are definitionally equal to a projection of the structure (but not when they are equal to the
composite of multiple projections).
-/
library_note "custom simps projection"

/--
This command specifies custom names and custom projections for the simp attribute `simpsAttr`.
* You can specify custom names by writing e.g.
  `initializeSimpsProjections equiv (toFun → apply, invFun → symm_apply)`.
* See Note [custom simps projection] and the examples below for information how to declare custom
  projections.
* If no custom projection is specified, the projection will be `coe_fn`/`⇑` if a `has_coe_toFun`
  instance has been declared, or the notation of a notation class (like `has_mul`) if such an
  instance is available. If none of these cases apply, the projection itself will be used.
* You can disable a projection by default by running
  `initializeSimpsProjections equiv (-invFun)`
  This will ensure that no simp lemmas are generated for this projection,
  unless this projection is explicitly specified by the user.
* If you want the projection name added as a prefix in the generated lemma name, you can add the
  `as_prefix` modifier:
  `initializeSimpsProjections equiv (toFun → coe as_prefix)`
  Note that this does not influence the parsing of projection names: if you have a declaration
  `foo` and you want to apply the projections `snd`, `coe` (which is a prefix) and `fst`, in that
  order you can run `@[simps snd_coe_fst] def foo ...` and this will generate a lemma with the
  name `coe_foo_snd_fst`.
  * Run `initializeSimpsProjections?` (or `set_option trace.simps.verbose true`)
  to see the generated projections.
* You can declare a new name for a projection that is the composite of multiple projections, e.g.
  ```
    structure A := (proj : ℕ)
    structure B extends A
    initializeSimpsProjections? B (to_A_proj → proj, -to_A)
  ```
  You can also make your custom projection that is definitionally equal to a composite of
  projections. In this case, coercions and notation classes are not automatically recognized, and
  should be manually given by giving a custom projection.
  This is especially useful when extending a structure (without `olstrDeclucture_cmd`).
  In the above example, it is desirable to add `-to_A`, so that `@[simps]` doesn't automatically
  apply the `B.to_A` projection and then recursively the `A.proj` projection in the lemmas it
  generates. If you want to get both the `foo_proj` and `foo_to_A` simp lemmas, you can use
  `@[simps, simps to_A]`.
* Running `initializeSimpsProjections my_struc` without arguments is not necessary, it has the
  same effect if you just add `@[simps]` to a declaration.
* If you do anything to change the default projections, make sure to call either `@[simps]` or
  `initializeSimpsProjections` in the same file as the structure declaration. Otherwise, you might
  have a file that imports the structure, but not your custom projections.

Some common uses:
* If you define a new homomorphism-like structure (like `mul_hom`) you can just run
  `initializeSimpsProjections` after defining the `has_coe_toFun` instance
  ```
    instance {mM : has_mul M} {mN : has_mul N} : has_coe_toFun (mul_hom M N) := ...
    initializeSimpsProjections mul_hom (toFun → apply)
  ```
  This will generate `foo_apply` lemmas for each declaration `foo`.
* If you prefer `coe_foo` lemmas that state equalities between functions, use
  `initializeSimpsProjections mul_hom (toFun → coe as_prefix)`
  In this case you have to use `@[simps {fully_applied := ff}]` or equivalently `@[simps as_fn]`
  whenever you call `@[simps]`.
* You can also initialize to use both, in which case you have to choose which one to use by default,
  by using either of the following
  ```
    initializeSimpsProjections mul_hom (toFun → apply, toFun → coe, -coe as_prefix)
    initializeSimpsProjections mul_hom (toFun → apply, toFun → coe as_prefix, -apply)
  ```
  In the first case, you can get both lemmas using `@[simps, simps coe as_fn]` and in the second
  case you can get both lemmas using `@[simps as_fn, simps apply]`.
* If your new homomorphism-like structure extends another structure (without `olstrDeclucture_cmd`)
  (like `relEmbedding`), then you have to specify explicitly that you want to use a coercion
  as a custom projection. For example
  ```
    def relEmbedding.simps.apply (h : r ↪r s) : α → β := h
    initializeSimpsProjections relEmbedding (to_embedding_toFun → apply, -to_embedding)
  ```
* If you have an isomorphism-like structure (like `equiv`) you often want to define a custom
  projection for the inverse:
  ```
    def equiv.simps.symm_apply (e : α ≃ β) : β → α := e.symm
    initializeSimpsProjections equiv (toFun → apply, invFun → symm_apply)
  ```
-/
@[user_command] meta def initializeSimpsProjectionsCmd
  (_ : parse $ tk "initializeSimpsProjections") : parser unit := do
  env ← getEnv,
  trc ← isSome <$> (tk "?")?,
  ns ← (prod.mk <$> ident <*> (tk "(" >> sep_by (tk ",") simpsParseRule <* tk ")")?)*,
  ns.mmap' $ λ data, do
    nm ← resolve_constant data.1,
    simpsGetRawProjections env nm tt (data.2.get_or_else []) trc

add_tactic_doc
{ name                     := "initializeSimpsProjections",
  category                 := doc_category.cmd,
  decl_names               := [`initializeSimpsProjectionsCmd],
  tags                     := ["simplification"] }

/--
  Configuration options for the `@[simps]` attribute.
  * `attrs` specifies the list of attributes given to the generated lemmas. Default: ``[`simp]``.
    The attributes can be either basic attributes, or user attributes without parameters.
    There are two attributes which `simps` might add itself:
    * If ``[`simp]`` is in the list, then ``[`_refl_lemma]`` is added automatically if appropriate.
    * If the definition is marked with `@[to_additive ...]` then all generated lemmas are marked
      with `@[to_additive]`. This is governed by the `add_additive` configuration option.
  * if `simp_rhs` is `tt` then the right-hand-side of the generated lemmas will be put in
    simp-normal form. More precisely: `dsimp, simp` will be called on all these expressions.
    See note [dsimp, simp].
  * `type_md` specifies how aggressively definitions are unfolded in the type of expressions
    for the purposes of finding out whether the type is a function type.
    Default: `instances`. This will unfold coercion instances (so that a coercion to a function type
    is recognized as a function type), but not declarations like `set`.
  * `rhs_md` specifies how aggressively definition in the declaration are unfolded for the purposes
    of finding out whether it is a constructor.
    Default: `none`
    Exception: `@[simps]` will automatically add the options
    `{rhs_md := semireducible, simp_rhs := tt}` if the given definition is not a constructor with
    the given reducibility setting for `rhs_md`.
  * If `fully_applied` is `ff` then the generated `simp` lemmas will be between non-fully applied
    terms, i.e. equalities between functions. This does not restrict the recursive behavior of
    `@[simps]`, so only the "final" projection will be non-fully applied.
    However, it can be used in combination with explicit field names, to get a partially applied
    intermediate projection.
  * The option `not_recursive` contains the list of names of types for which `@[simps]` doesn't
    recursively apply projections. For example, given an equivalence `α × β ≃ β × α` one usually
    wants to only apply the projections for `equiv`, and not also those for `×`. This option is
    only relevant if no explicit projection names are given as argument to `@[simps]`.
  * The option `trace` is set to `tt` when you write `@[simps?]`. In this case, the attribute will
    print all generated lemmas. It is almost the same as setting the option `trace.simps.verbose`,
    except that it doesn't print information about the found projections.
  * if `add_additive` is `some nm` then `@[to_additive]` is added to the generated lemma. This
    option is automatically set to `tt` when the original declaration was tagged with
    `@[to_additive, simps]` (in that order), where `nm` is the additive name of the original
    declaration.
-/
@[derive [has_reflect, inhabited]] structure simps_cfg :=
(attrs         := [`simp])
(simp_rhs      := ff)
(type_md       := transparency.instances)
(rhs_md        := transparency.none)
(fully_applied := tt)
(not_recursive := [`prod, `pprod])
(trace         := ff)
(add_additive  := @none name)

/-- A common configuration for `@[simps]`: generate equalities between functions instead equalities
  between fully applied expressions. -/
def as_fn : simps_cfg := {fully_applied := ff}
/-- A common configuration for `@[simps]`: don't tag the generated lemmas with `@[simp]`. -/
def lemmas_only : simps_cfg := {attrs := []}

/--
  Get the projections of a structure used by `@[simps]` applied to the appropriate arguments.
  Returns a list of tuples
  ```
  (corresponding right-hand-side, given projection name, projection expression, projection numbers,
    used by default, is prefix)
  ```
  (where all fields except the first are packed in a `ProjectionData` structure)
  one for each projection. The given projection name is the name for the projection used by the user
  used to generate (and parse) projection names. For example, in the structure

  Example 1: ``simpsGetProjectionExprs env `(α × β) `(⟨x, y⟩)`` will give the output
  ```
    [(`(x), `fst, `(@prod.fst.{u v} α β), [0], tt, ff),
     (`(y), `snd, `(@prod.snd.{u v} α β), [1], tt, ff)]
  ```

  Example 2: ``simpsGetProjectionExprs env `(α ≃ α) `(⟨id, id, λ _, rfl, λ _, rfl⟩)``
  will give the output
  ```
    [(`(id), `apply, `(coe), [0], tt, ff),
     (`(id), `symm_apply, `(λ f, ⇑f.symm), [1], tt, ff),
     ...,
     ...]
  ```
-/
meta def simpsGetProjectionExprs (e : environment) (tgt : Expr)
  (rhs : Expr) (cfg : simps_cfg) : tactic $ list $ expr × ProjectionData := do
  let params := get_app_args tgt, -- the parameters of the structure
  (params.zip $ (get_app_args rhs).take params.length).mmap' (λ ⟨a, b⟩, is_def_eq a b)
    <|> fail "unreachable code (1)",
  let str := tgt.getAppFn.const_name,
  let rhs_args := (get_app_args rhs).drop params.length, -- the fields of the object
  (rawUnivs, projDeclata) ← simpsGetRawProjections e str ff [] cfg.trace,
  let univs := rawUnivs.zip tgt.getAppFn.levelParams,
  let new_projDeclata : list $ expr × ProjectionData := projDeclata.map $
    λ proj, (rhs_args.inth proj.proj_nrs.head,
      { expr := (proj.expr.instantiate_univ_params univs).instantiate_lambdas_or_apps params,
        proj_nrs := proj.proj_nrs.tail,
        .. proj }),
  return new_projDeclata

/-- Add a lemma with `nm` stating that `lhs = rhs`. `type` is the type of both `lhs` and `rhs`,
  `args` is the list of local constants occurring, and `univs` is the list of universe variables. -/
meta def simpsAddProjection (nm : name) (type lhs rhs : Expr) (args : list expr)
  (univs : list name) (cfg : simps_cfg) : tactic unit := do
  whenTracing `simps.debug trace!
    "[simps] > Planning to add the equality\n        > {lhs} = ({rhs} : {type})",
  lvl ← get_univ_level type,
  -- simplify `rhs` if `cfg.simp_rhs` is true
  (rhs, prf) ← do { guard cfg.simp_rhs,
    rhs' ← rhs.dsimp {fail_if_unchanged := ff},
    whenTracing `simps.debug $ when (rhs ≠ rhs') trace!
      "[simps] > `dsimp` simplified rhs to\n        > {rhs'}",
    (rhsprf1, rhsprf2, ns) ← rhs'.simp {fail_if_unchanged := ff},
    whenTracing `simps.debug $ when (rhs' ≠ rhsprf1) trace!
      "[simps] > `simp` simplified rhs to\n        > {rhsprf1}",
    return (prod.mk rhsprf1 rhsprf2) }
    <|> return (rhs, const `eq.refl [lvl] type lhs),
  let eq_ap := const `eq [lvl] type lhs rhs,
  decl_name ← get_unused_decl_name nm,
  let decl_type := eq_ap.pis args,
  let decl_value := prf.lambdas args,
  let decl := declaration.thm decl_name univs decl_type (pure decl_value),
  when cfg.trace trace!
    "[simps] > adding projection {decl_name}:\n        > {decl_type}",
  decorate_error ("Failed to add projection lemma " ++ decl_name.to_string ++ ". Nested error:") $
    add_decl decl,
  b ← succeeds $ is_def_eq lhs rhs,
  when (b ∧ `simp ∈ cfg.attrs) (set_basic_attribute `_refl_lemma decl_name tt),
  cfg.attrs.mmap' $ λ nm, set_attribute nm decl_name tt,
  when cfg.add_additive.isSome $
    to_additive.attr.set decl_name ⟨ff, cfg.trace, cfg.add_additive.iget, none, tt⟩ tt

/-- Derive lemmas specifying the projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  `to_apply` is non-empty after a custom projection that is a composition of multiple projections
  was just used. In that case we need to apply these projections before we continue changing lhs. -/
meta def simpsAddProjections : Π (e : environment) (nm : name)
  (type lhs rhs : Expr) (args : list expr) (univs : list name) (must_be_str : bool)
  (cfg : simps_cfg) (todo : list string) (to_apply : list ℕ), tactic unit
| e nm type lhs rhs args univs must_be_str cfg todo to_apply := do
  -- we don't want to unfold non-reducible definitions (like `set`) to apply more arguments
  whenTracing `simps.debug trace!
    "[simps] > Type of the expression before normalizing: {type}",
  (typeArgs, tgt) ← open_pis_whnf type cfg.type_md,
  whenTracing `simps.debug trace!"[simps] > Type after removing pi's: {tgt}",
  tgt ← whnf tgt,
  whenTracing `simps.debug trace!"[simps] > Type after reduction: {tgt}",
  let new_args := args ++ typeArgs,
  let lhs_ap := lhs.instantiate_lambdas_or_apps typeArgs,
  let rhs_ap := rhs.instantiate_lambdas_or_apps typeArgs,
  let str := tgt.getAppFn.const_name,
  /- We want to generate the current projection if it is in `todo` -/
  let todo_next := todo.filter (≠ ""),
  /- Don't recursively continue if `str` is not a structure or if the structure is in
    `not_recursive`. -/
  if e.is_structure str ∧ ¬(todo = [] ∧ str ∈ cfg.not_recursive ∧ ¬must_be_str) then do
    [intro] ← return $ e.constructors_of str | fail "unreachable code (3)",
    rhs_whnf ← whnf rhs_ap cfg.rhs_md,
    (rhs_ap, todo_now) ← -- `todo_now` means that we still have to generate the current simp lemma
      if ¬ is_constant_of rhs_ap.getAppFn intro ∧
        is_constant_of rhs_whnf.getAppFn intro then
      /- If this was a desired projection, we want to apply it before taking the whnf.
        However, if the current field is an eta-expansion (see below), we first want
        to eta-reduce it and only then construct the projection.
        This makes the flow of this function messy. -/
      when ("" ∈ todo ∧ to_apply = []) (if cfg.fully_applied then
        simpsAddProjection nm tgt lhs_ap rhs_ap new_args univs cfg else
        simpsAddProjection nm type lhs rhs args univs cfg) >>
      return (rhs_whnf, ff) else
      return (rhs_ap, "" ∈ todo ∧ to_apply = []),
    if is_constant_of (getAppFn rhs_ap) intro then do -- if the value is a constructor application
      projInfo ← simpsGetProjectionExprs e tgt rhs_ap cfg,
      whenTracing `simps.debug trace!"[simps] > Raw projection information:\n  {projInfo}",
      eta ← rhs_ap.is_eta_expansion, -- check whether `rhs_ap` is an eta-expansion
      let rhs_ap := eta.lhoare rhs_ap, -- eta-reduce `rhs_ap`
      /- As a special case, we want to automatically generate the current projection if `rhs_ap`
        was an eta-expansion. Also, when this was a desired projection, we need to generate the
        current projection if we haven't done it above. -/
      when (todo_now ∨ (todo = [] ∧ eta.isSome ∧ to_apply = [])) $
        if cfg.fully_applied then
          simpsAddProjection nm tgt lhs_ap rhs_ap new_args univs cfg else
          simpsAddProjection nm type lhs rhs args univs cfg,
      /- If we are in the middle of a composite projection. -/
      when (to_apply ≠ []) $ do
      { ⟨new_rhs, proj, projExprxpr, proj_nrs, is_default, is_prefix⟩ ←
          return $ projInfo.inth to_apply.head,
        new_type ← infer_type new_rhs,
        whenTracing `simps.debug
          trace!"[simps] > Applying a custom composite projection. Current lhs:
        >  {lhs_ap}",
        simpsAddProjections e nm new_type lhs_ap new_rhs new_args univs ff cfg todo
          to_apply.tail },
      /- We stop if no further projection is specified or if we just reduced an eta-expansion and we
      automatically choose projections -/
      when ¬(to_apply ≠ [] ∨ todo = [""] ∨ (eta.isSome ∧ todo = [])) $ do
        let projs : list name := projInfo.map $ λ x, x.snd.name,
        let todo := if to_apply = [] then todo_next else todo,
        -- check whether all elements in `todo` have a projection as prefix
        guard (todo.all $ λ x, projs.any $ λ proj, ("_" ++ proj.last).is_prefix_of x) <|>
          let x := (todo.find $ λ x, projs.all $ λ proj, ¬ ("_" ++ proj.last).is_prefix_of x).iget,
            simp_lemma := nm.append_suffix x,
            needed_proj := (x.split_on '_').tail.head in
          fail!
"Invalid simp lemma {simp_lemma}. Structure {str} does not have projection {needed_proj}.
The known projections are:
  {projs}
You can also see this information by running
  `initializeSimpsProjections? {str}`.
Note: these projection names might not correspond to the projection names of the structure.",
        projInfo.mmap_with_index' $
          λ proj_nr ⟨new_rhs, proj, projExprxpr, proj_nrs, is_default, is_prefix⟩, do
          new_type ← infer_type new_rhs,
          let new_todo :=
            todo.filter_map $ λ x, x.get_rest ("_" ++ proj.last),
          -- we only continue with this field if it is non-propositional or mentioned in todo
          when ((is_default ∧ todo = []) ∨ new_todo ≠ []) $ do
            let new_lhs := projExprxpr.instantiate_lambdas_or_apps [lhs_ap],
            let new_nm := nm.append_to_last proj.last is_prefix,
            let new_cfg := { add_additive := cfg.add_additive.map $
              λ nm, nm.append_to_last (to_additive.guess_name proj.last) is_prefix, ..cfg },
            whenTracing `simps.debug trace!"[simps] > Recursively add projections for:
        >  {new_lhs}",
            simpsAddProjections e new_nm new_type new_lhs new_rhs new_args univs
              ff new_cfg new_todo proj_nrs
    -- if I'm about to run into an error, try to set the transparency for `rhs_md` higher.
    else if cfg.rhs_md = transparency.none ∧ (must_be_str ∨ todo_next ≠ [] ∨ to_apply ≠ []) then do
      when cfg.trace trace!
        "[simps] > The given definition is not a constructor application:
        >   {rhs_ap}
        > Retrying with the options {{ rhs_md := semireducible, simp_rhs := tt}.",
      simpsAddProjections e nm type lhs rhs args univs must_be_str
        { rhs_md := semireducible, simp_rhs := tt, ..cfg} todo to_apply
    else do
      when (to_apply ≠ []) $
        fail!"Invalid simp lemma {nm}.
The given definition is not a constructor application:\n  {rhs_ap}",
      when must_be_str $
        fail!"Invalid `simps` attribute. The body is not a constructor application:\n  {rhs_ap}",
      when (todo_next ≠ []) $
        fail!"Invalid simp lemma {nm.append_suffix todo_next.head}.
The given definition is not a constructor application:\n  {rhs_ap}",
      if cfg.fully_applied then
        simpsAddProjection nm tgt lhs_ap rhs_ap new_args univs cfg else
        simpsAddProjection nm type lhs rhs args univs cfg
  else do
    when must_be_str $
      fail!"Invalid `simps` attribute. Target {str} is not a structure",
    when (todo_next ≠ [] ∧ str ∉ cfg.not_recursive) $
        let first_todo := todo_next.head in
        fail!"Invalid simp lemma {nm.append_suffix first_todo}.
Projection {(first_todo.split_on '_').tail.head} doesn't exist, because target is not a structure.",
    if cfg.fully_applied then
      simpsAddProjection nm tgt lhs_ap rhs_ap new_args univs cfg else
      simpsAddProjection nm type lhs rhs args univs cfg

/-- `simpsTac` derives `simp` lemmas for all (nested) non-Prop projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  If `short_nm` is true, the generated names will only use the last projection name.
  If `trc` is true, trace as if `trace.simps.verbose` is true. -/
meta def simpsTac (nm : name) (cfg : simps_cfg := {}) (todo : list string := []) (trc := ff) :
  tactic unit := do
  e ← getEnv,
  d ← e.get nm,
  let lhs : Expr := const d.to_name d.levelParams,
  let todo := todo.dedup.map $ λ proj, "_" ++ proj,
  let cfg := { trace := cfg.trace || isTraceEnabledFor `simps.verbose || trc, ..cfg },
  b ← hasAttribute' `to_additive nm,
  cfg ← if b then do
  { dict ← to_additive.aux_attr.get_cache,
    when cfg.trace
      trace!"[simps] > @[to_additive] will be added to all generated lemmas.",
    return { add_additive := dict.find nm, ..cfg } } else
    return cfg,
  simpsAddProjections e nm d.type lhs d.value [] d.univ_params tt cfg todo []

/-- The parser for the `@[simps]` attribute. -/
meta def simpsParser : parser (bool × list string × simps_cfg) := do
/- note: we don't check whether the user has written a nonsense namespace in an argument. -/
prod.mk <$> isSome <$> (tk "?")? <*>
  (prod.mk <$> many (name.last <$> ident) <*>
  (do some e ← parser.pexpr? | return {}, eval_pexpr simps_cfg e))

/--
The `@[simps]` attribute automatically derives lemmas specifying the projections of this
declaration.

Example:
```lean
@[simps] def foo : ℕ × ℤ := (1, 2)
```
derives two `simp` lemmas:
```lean
@[simp] lemma foo_fst : foo.fst = 1
@[simp] lemma foo_snd : foo.snd = 2
```

* It does not derive `simp` lemmas for the prop-valued projections.
* It will automatically reduce newly created beta-redexes, but will not unfold any definitions.
* If the structure has a coercion to either sorts or functions, and this is defined to be one
  of the projections, then this coercion will be used instead of the projection.
* If the structure is a class that has an instance to a notation class, like `has_mul`, then this
  notation is used instead of the corresponding projection.
* You can specify custom projections, by giving a declaration with name
  `{structure_name}.simps.{projection_name}`. See Note [custom simps projection].

  Example:
  ```lean
  def equiv.simps.invFun (e : α ≃ β) : β → α := e.symm
  @[simps] def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩
  ```
  generates
  ```
  @[simp] lemma equiv.trans_toFun : ∀ {α β γ} (e₁ e₂) (a : α), ⇑(e₁.trans e₂) a = (⇑e₂ ∘ ⇑e₁) a
  @[simp] lemma equiv.trans_invFun : ∀ {α β γ} (e₁ e₂) (a : γ),
    ⇑((e₁.trans e₂).symm) a = (⇑(e₁.symm) ∘ ⇑(e₂.symm)) a
  ```

* You can specify custom projection names, by specifying the new projection names using
  `initializeSimpsProjections`.
  Example: `initializeSimpsProjections equiv (toFun → apply, invFun → symm_apply)`.
  See `initializeSimpsProjectionsCmd` for more information.

* If one of the fields itself is a structure, this command will recursively create
  `simp` lemmas for all fields in that structure.
  * Exception: by default it will not recursively create `simp` lemmas for fields in the structures
    `prod` and `pprod`. You can give explicit projection names or change the value of
    `simps_cfg.not_recursive` to override this behavior.

  Example:
  ```lean
  structure my_prod (α β : Type*) := (fst : α) (snd : β)
  @[simps] def foo : prod ℕ ℕ × my_prod ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_snd_fst : foo.snd.fst = 3
  @[simp] lemma foo_snd_snd : foo.snd.snd = 4
  ```

* You can use `@[simps proj1 proj2 ...]` to only generate the projection lemmas for the specified
  projections.
* Recursive projection names can be specified using `proj1_proj2_proj3`.
  This will create a lemma of the form `foo.proj1.proj2.proj3 = ...`.

  Example:
  ```lean
  structure my_prod (α β : Type*) := (fst : α) (snd : β)
  @[simps fst fst_fst snd] def foo : prod ℕ ℕ × my_prod ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_fst_fst : foo.fst.fst = 1
  @[simp] lemma foo_snd : foo.snd = {fst := 3, snd := 4}
  ```
* If one of the values is an eta-expanded structure, we will eta-reduce this structure.

  Example:
  ```lean
  structure equiv_plus_data (α β) extends α ≃ β := (data : bool)
  @[simps] def bar {α} : equiv_plus_data α α := { data := tt, ..equiv.refl α }
  ```
  generates the following:
  ```lean
  @[simp] lemma bar_to_equiv : ∀ {α : Sort*}, bar.to_equiv = equiv.refl α
  @[simp] lemma bar_data : ∀ {α : Sort*}, bar.data = tt
  ```
  This is true, even though Lean inserts an eta-expanded version of `equiv.refl α` in the
  definition of `bar`.
* For configuration options, see the doc string of `simps_cfg`.
* The precise syntax is `('simps' ident* e)`, where `e` is an expression of type `simps_cfg`.
* `@[simps]` reduces let-expressions where necessary.
* When option `trace.simps.verbose` is true, `simps` will print the projections it finds and the
  lemmas it generates. The same can be achieved by using `@[simps?]`, except that in this case it
  will not print projection information.
* Use `@[to_additive, simps]` to apply both `to_additive` and `simps` to a definition, making sure
  that `simps` comes after `to_additive`. This will also generate the additive versions of all
  `simp` lemmas.
-/
/- If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens, so is not included in the official doc). -/
@[user_attribute] meta def simpsAttr : user_attribute unit (bool × list string × simps_cfg) :=
{ name := `simps,
  descr := "Automatically derive lemmas specifying the projections of this declaration.",
  parser := simpsParser,
  after_set := some $
    λ n _ persistent, do
      guard persistent <|> fail "`simps` currently cannot be used as a local attribute",
      (trc, todo, cfg) ← simpsAttr.get_param n,
      simpsTac n cfg todo trc }

add_tactic_doc
{ name                     := "simps",
  category                 := doc_category.attr,
  decl_names               := [`simpsAttr],
  tags                     := ["simplification"] }

-/


/-!

MAYBE NEEDED


unsafe instance : has_to_tactic_format ProjectionData :=
  ⟨fun ⟨a, b, c, d, e⟩ =>
    (fun x =>
        group <|
          nest 1 <|
            to_fmt "⟨" ++ to_fmt a ++ to_fmt "," ++ line ++ x ++ to_fmt "," ++ line ++ to_fmt c ++ to_fmt "," ++ line ++
                      to_fmt d ++
                    to_fmt "," ++
                  line ++
                to_fmt e ++
              to_fmt "⟩") <$>
      pp b⟩

unsafe instance : has_to_format ParsedProjectionData :=
  ⟨fun ⟨a, b, c, d⟩ =>
    group <|
      nest 1 <|
        to_fmt "⟨" ++ to_fmt a ++ to_fmt "," ++ line ++ to_fmt b ++ to_fmt "," ++ line ++ to_fmt c ++ to_fmt "," ++
              line ++
            to_fmt d ++
          to_fmt "⟩"⟩


-/
