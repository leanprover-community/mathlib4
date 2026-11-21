/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public meta import Mathlib.Tactic.Simps.Basic

/-!
# `simps!!`: `simps` with generalized projections

`@[simps!!]` does everything `@[simps!]` does, and also generates lemmas for *generalized
projections*: arbitrary functions out of the type of the definition, registered with
`@[simps_proj]`. For example, after
```
@[simps_proj (hide := π)] abbrev PullbackCone.Simps.fst (c : PullbackCone f g) := c.fst
@[simps_proj (hide := π)] abbrev PullbackCone.Simps.snd (c : PullbackCone f g) := c.snd
```
a definition `@[simps!!] def c : PullbackCone f g := PullbackCone.mk a b w` gets the lemmas
`c_pt : c.pt = W`, `c_fst : c.fst = a` and `c_snd : c.snd = b`, instead of `c_pt` and `c_π_app`.

A generalized projection need not be a projection at all, nor be keyed on a structure: after
```
@[simps_proj (name := fst) (rules := pullback.lift_fst) (attr := reassoc (attr := simp))]
noncomputable abbrev pullbackFst {W} (h : W ⟶ pullback f g) : W ⟶ X := h ≫ pullback.fst f g
```
every morphism into a pullback gets a lemma for its composite with `pullback.fst`, wherever it
appears: as the definition itself, or as a field of it, like the `hom` of an isomorphism.

## Generalized projections

A generalized projection is a definition `p : ∀ params (x : S) extras, R`. Its *self argument*
`x` is the last argument whose type depends (transitively) on all the arguments before it; the
`params` are found by unifying `S` with the type of the definition (or of the field) at hand, and
the `extras` become arguments of the generated lemma. Generalized projections are looked up by
the type `S`, up to reducible unfolding, so a projection registered for `PullbackCone f g` also
applies to a definition of type `Cone (cospan f g)`.

For a term `t` of type `S` with value `v`, the generated lemma is `p params t extras = rhs`, where
`p` is unfolded (so the statement uses its body), and `rhs` is computed from `p params v extras`:
1. definitions applied to structure instances (`PullbackCone.fst ⟨W, π⟩`, say) are unfolded, as
   are class projections applied to them (`⇑(Equiv.mk f g l r) x`), and then projections of
   structure instances, `match`es on constructors and β-redexes are reduced. This is what makes
   generalized projections that are compositions of genuine projections (with arguments) work.
2. the result is simplified by `simp`, with the lemmas given by `(rules := ...)` (and their
   `_assoc` versions, if they exist) added to the simp set. This is what makes generalized
   projections that are characterized by lemmas, like `pullback.lift_fst`, work.

Before that, `simps!!` tries the same with `v` replaced by the body of the definition *as
written*, not unfolded to a constructor application, so that `simp` can use the lemmas about the
definitions it is made of: for `e := pullbackSymmetry f g`, `e.hom ≫ pullback.fst g f` is computed
from `(pullbackSymmetry f g).hom ≫ pullback.fst g f`, which simplifies to `pullback.snd f g` by a
lemma about `pullbackSymmetry`. This result is used if it no longer contains the head of the body
(`pullbackSymmetry`).

`simps!!` then recurses into the result, as `simps` does with the fields of a structure: both
into the genuine projections of its type, if it is a structure, and into the generalized
projections that apply to it.

Options of `@[simps_proj]`:
* `(name := n)`: the name used for this projection in generated lemma names. The default is the
  last component of the name of the declaration.
* `(self := x)`: the self argument is the argument named `x`. This is needed when an extra
  argument also depends on all the arguments before it, as `i` does in
  `(c : RelCWComplex C D) (n : ℕ) (i : cell C n)`.
* `(hide := p₁, …)`: don't generate lemmas for the genuine projections `pᵢ` of the structure
  when this projection applies (e.g. `π` for a `PullbackCone`, in favor of `fst` and `snd`).
* `(rules := l₁, …)`: lemmas to simplify with when computing right-hand sides.
* `(attr := …)`: attributes to add to the lemmas generated for this projection.
* `as_prefix`: the name of the projection is added at the start of the lemma name.
* `precomp`: the name of the projection is added *before* the last component of the lemma name,
  which reads well for projections that precompose, like `fun h ↦ pullback.lift a b w ≫ h`:
  the lemma for `e.hom` is `e_lift_hom`.
* `noRecurse`: don't recurse into the result. The right-hand side is instead expanded by an
  η-rule of its type, if one is registered (see below). Such projections only apply to the
  declaration and its genuine projections, not to the results of other generalized projections:
  `pullback.lift a b w ≫ (e.hom ≫ pullback.fst _ _)` would follow from the lemma for
  `e.hom ≫ pullback.fst _ _`.
* `nonDefault`: only generate lemmas for this projection if it is asked for explicitly.

## η-rules

An η-rule is a theorem `∀ params (x : T), x = c (p₁ x) … (pₙ x)`, registered with
`@[simps_eta]`, that expresses a term of `T` by its generalized projections. After a `noRecurse`
generalized projection, the lemma is stated as `p t extras = c rhs₁ … rhsₙ` instead, where the
`rhsᵢ` are computed by `simp` from `pᵢ (p t extras)`, using the lemmas generated so far. This is
how `simps!!` states the universal property of a limit `L` in terms of a limit `R`, for an
isomorphism `e : L ≅ R`:
`pullback.lift a b w ≫ e.hom = R.lift (…) (…)`.

## Overlapping registrations

Generalized projections and η-rules are found by matching types up to reducible unfolding, so a
registration for `W ⟶ equalizer f g` also applies to `W ⟶ kernel f`, which unfolds to
`W ⟶ equalizer f 0`. When several generalized projections with the same name apply, only the most
specific ones are used (those whose discrimination tree keys have the fewest `*`s), and so is the
most specific η-rule: once kernels have their own registrations, morphisms into kernels get
lemmas about `kernel.ι` and `kernel.lift` only.

## Limitations

* Only fully applied lemmas are generated (`-fullyApplied` is ignored for generalized
  projections).
* The declarations registered with `@[simps_proj]` and `@[simps_eta]` must have their bodies
  exposed (e.g. be `abbrev`s or `@[expose]`), so that they can be unfolded in other modules.
* A generalized projection may live in the namespace `S.Simps` of a structure `S`: `simps!!`
  doesn't count it as an unused custom projection (`linter.simpsUnusedCustomDeclarations`). But
  `@[simps]` and `initialize_simps_projections` do, if they are the first to initialize the
  projections of `S` in the same file.
-/

public meta section

open Lean Meta Elab Term

namespace Lean.Parser.Attr

/-- `(name := n)` option of `@[simps_proj]`. -/
syntax simpsProjName := atomic(" (" &"name" " := ") ident ")"
/-- `(hide := p₁, …)` option of `@[simps_proj]`. -/
syntax simpsProjHide := atomic(" (" &"hide" " := ") ident,+ ")"
/-- `(rules := l₁, …)` option of `@[simps_proj]`. -/
syntax simpsProjRules := atomic(" (" &"rules" " := ") ident,+ ")"
/-- `(attr := …)` option of `@[simps_proj]`. -/
syntax simpsProjAttrs := atomic(" (" &"attr" " := ") Parser.Term.attrInstance,* ")"
/-- `(self := x)` option of `@[simps_proj]`. -/
syntax simpsProjSelf := atomic(" (" &"self" " := ") ident ")"
/-- Flags of `@[simps_proj]`. -/
syntax simpsProjFlag := &" as_prefix" <|> &" precomp" <|> &" noRecurse" <|> &" nonDefault"
/-- An option of `@[simps_proj]`. See `Mathlib.Tactic.Simps.Generalized` for their meanings. -/
syntax simpsProjOpt :=
  simpsProjName <|> simpsProjSelf <|> simpsProjHide <|> simpsProjRules <|> simpsProjAttrs <|>
  simpsProjFlag

/-- `@[simps_proj]` registers a definition `p : ∀ params (x : S) extras, R` as a generalized
projection for `simps!!`: every definition (or field of a definition) of type `S` tagged
`@[simps!!]` gets a lemma `p params t extras = rhs`. See the module documentation of
`Mathlib.Tactic.Simps.Generalized` for details and options. -/
syntax (name := simpsProj) "simps_proj" (simpsProjOpt)* : attr

/-- `@[simps_eta]` registers a theorem `∀ params (x : T), x = c (p₁ x) … (pₙ x)` as an η-rule for
`simps!!`, which uses it to state the lemmas of `noRecurse` generalized projections whose result
has type `T`. See the module documentation of `Mathlib.Tactic.Simps.Generalized`. -/
syntax (name := simpsEta) "simps_eta" : attr

/-- `@[simps!!]` is `@[simps!]` with generalized projections, registered with `@[simps_proj]`.
See the module documentation of `Mathlib.Tactic.Simps.Generalized`. It takes the same arguments
as `@[simps]`; projection names may also be the names of generalized projections. -/
syntax (name := simpsGen) "simps!!" "?"? simpsArgsRest : attr

@[inherit_doc simpsGen] macro "simps!!?" rest:simpsArgsRest : attr => `(attr| simps!! ? $rest)

end Lean.Parser.Attr

namespace Simps.Gen

/-- Where the name of a generalized projection goes in the name of a generated lemma. -/
inductive NamePos where
  /-- At the end (the default). -/
  | suffix
  /-- At the start. -/
  | «prefix»
  /-- Before the last component. -/
  | precomp
  deriving Inhabited, BEq, Repr

/-- A generalized projection, registered with `@[simps_proj]`. -/
structure GenProj where
  /-- The registered declaration. -/
  declName : Name
  /-- The name of the projection, used in the names of generated lemmas. -/
  name : String
  /-- The index of the self argument of `declName`. -/
  selfIdx : Nat
  /-- The discrimination tree keys of the type of the self argument. -/
  keys : Array DiscrTree.Key
  /-- Where the name goes in generated lemma names. -/
  pos : NamePos := .suffix
  /-- Genuine projections not to generate lemmas for when this projection applies. -/
  hides : Array Name := #[]
  /-- Extra lemmas to simplify with when computing right-hand sides. -/
  rules : Array Name := #[]
  /-- Extra attributes for the generated lemmas (`attrInstance` syntax). -/
  attrs : Array Syntax := #[]
  /-- Whether to recurse into the result. -/
  recurse : Bool := true
  /-- Whether lemmas are generated for this projection by default. -/
  isDefault : Bool := true
  deriving Inhabited

instance : BEq GenProj := ⟨(·.declName == ·.declName)⟩

/-- An η-rule, registered with `@[simps_eta]`. -/
structure EtaRule where
  /-- The registered theorem. -/
  declName : Name
  /-- The index of the self argument (the left-hand side of the equation). -/
  selfIdx : Nat
  /-- The discrimination tree keys of the type of the self argument. -/
  keys : Array DiscrTree.Key
  deriving Inhabited

instance : BEq EtaRule := ⟨(·.declName == ·.declName)⟩

/-- The generalized projections, keyed by the type of their self argument, and the set of their
names. -/
initialize projExt : SimpleScopedEnvExtension GenProj (DiscrTree GenProj × NameSet) ←
  registerSimpleScopedEnvExtension {
    initial := ({}, {})
    addEntry := fun (d, s) e => (d.insertKeyValue e.keys e, s.insert e.declName) }

/-- The η-rules, keyed by the type of their self argument. -/
initialize etaExt : SimpleScopedEnvExtension EtaRule (DiscrTree EtaRule) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun d e => d.insertKeyValue e.keys e }

initialize registerTraceClass `simps.gen

/-! ### Registration -/

/-- The free variables `e` depends on: those occurring in it, and (recursively) in their types. -/
partial def depClosure (e : Expr) : MetaM FVarIdSet := do
  let rec go (todo : List FVarId) (acc : FVarIdSet) : MetaM FVarIdSet := do
    match todo with
    | [] => return acc
    | x :: todo =>
      if acc.contains x then go todo acc else
      let ty ← instantiateMVars (← x.getType)
      go ((collectFVars {} ty).fvarIds.toList ++ todo) (acc.insert x)
  go (collectFVars {} (← instantiateMVars e)).fvarIds.toList {}

/-- The index of the self argument of a generalized projection of type `type`: the last argument
whose type depends on all the arguments before it. -/
def findSelfIdx (type : Expr) : MetaM Nat :=
  forallTelescope type fun xs _ => do
    let mut best := none
    for h : i in [:xs.size] do
      let deps ← depClosure (← inferType xs[i])
      if (xs.extract 0 i).all (deps.contains ·.fvarId!) then best := some i
    let some i := best | throwError "no self argument found in{indentExpr type}"
    return i

/-- The discrimination tree keys for the type of the `selfIdx`-th argument of `type`. -/
def selfKeys (type : Expr) (selfIdx : Nat) : MetaM (Array DiscrTree.Key) := do
  let (xs, _, _) ← forallMetaBoundedTelescope type (selfIdx + 1)
  let some x := xs[selfIdx]? | throwError "not enough arguments in{indentExpr type}"
  withReducible <| DiscrTree.mkPath (← instantiateMVars (← inferType x))

/-- The first atom of `stx`. -/
partial def firstAtom : Syntax → String
  | .atom _ v => v
  | .node _ _ args => (args.map firstAtom).find? (· != "") |>.getD ""
  | _ => ""

open Lean.Parser.Attr in
/-- Elaborates the options of `@[simps_proj]` into `g`. -/
def elabProjOpts (g : GenProj) (opts : Array Syntax) : CoreM GenProj := do
  let mut g := g
  for opt in opts do
    let opt := opt[0]
    match opt with
    | `(simpsProjName| (name := $n:ident)) => g := { g with name := n.getId.toString }
    | `(simpsProjSelf| (self := $_:ident)) => pure ()
    | `(simpsProjHide| (hide := $ns:ident,*)) =>
      g := { g with hides := g.hides ++ ns.getElems.map (·.getId) }
    | `(simpsProjRules| (rules := $ns:ident,*)) =>
      let ns ← ns.getElems.mapM fun n => realizeGlobalConstNoOverloadWithInfo n
      g := { g with rules := g.rules ++ ns }
    | `(simpsProjAttrs| (attr := $as:attrInstance,*)) =>
      g := { g with attrs := g.attrs ++ as.getElems.map (·.raw) }
    | _ =>
      match (firstAtom opt).trimAscii.toString with
      | "as_prefix" => g := { g with pos := .prefix }
      | "precomp" => g := { g with pos := .precomp }
      | "noRecurse" => g := { g with recurse := false }
      | "nonDefault" => g := { g with isDefault := false }
      | _ => throwErrorAt opt "unknown `simps_proj` option"
  return g

initialize registerBuiltinAttribute {
  name := `simpsProj
  descr := "register a generalized projection for `simps!!`"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let info ← getConstInfo decl
    unless info.hasValue (allowOpaque := false) && !info.isTheorem do
      throwError "`simps_proj`: {.ofConstName decl} must be a definition"
    let self? := stx[1].getArgs.findSome? fun opt =>
      if opt[0].getKind == ``Lean.Parser.Attr.simpsProjSelf then
        opt[0].getArgs.find? (·.isIdent) |>.map (·.getId)
      else none
    let (selfIdx, keys) ← MetaM.run' do
      let selfIdx ← match self? with
        | none => findSelfIdx info.type
        | some x => forallTelescope info.type fun xs _ => do
          let some i ← xs.findIdxM? fun x' => return (← x'.fvarId!.getUserName) == x |
            throwError "`simps_proj`: {.ofConstName decl} has no argument {x}"
          return i
      return (selfIdx, ← selfKeys info.type selfIdx)
    let g ← elabProjOpts
      { declName := decl, name := decl.lastComponentAsString, selfIdx, keys } stx[1].getArgs
    projExt.add g kind }

initialize registerBuiltinAttribute {
  name := `simpsEta
  descr := "register an η-rule for `simps!!`"
  add := fun decl _ kind => do
    let info ← getConstInfo decl
    let (selfIdx, keys) ← MetaM.run' <| forallTelescope info.type fun xs concl => do
      let some (_, lhs, _) := concl.eq? |
        throwError "`simps_eta`: {.ofConstName decl} must be an equation `x = …`"
      let some selfIdx := xs.idxOf? lhs |
        throwError "`simps_eta`: the left-hand side of {.ofConstName decl} must be a variable"
      return (selfIdx, ← selfKeys info.type selfIdx)
    etaExt.add { declName := decl, selfIdx, keys } kind }

/-! ### Computing right-hand sides -/

/-- Whether `e` is an application of a structure constructor. -/
def isStructCtorApp (e : Expr) : MetaM Bool := do
  let .const c _ := e.getAppFn | return false
  let env ← getEnv
  let some (.ctorInfo ci) := env.find? c | return false
  return isStructure env ci.induct

/-- Whether `normalize` may unfold applications of `c`. -/
def canUnfold (c : Name) : MetaM Bool := do
  let some (.defnInfo _) := (← getEnv).find? c | return false
  if (← isProjectionFn c) || (← isInstance c) || (← isMatcher c) then return false
  return true

/-- Reduces `t` if it is a projection (or projection function) applied to a structure instance. -/
def reduceProjOfCtor? (t : Expr) : MetaM (Option Expr) := do
  match t with
  | .proj _ i s =>
    unless ← isStructCtorApp s do return none
    let some (.ctorInfo ci) := (← getEnv).find? s.getAppFn.constName! | return none
    return s.getAppArgs[ci.numParams + i]?
  | _ =>
    let .const c _ := t.getAppFn | return none
    let some info ← getProjectionFnInfo? c | return none
    let args := t.getAppArgs
    let some s := args[info.numParams]? | return none
    unless ← isStructCtorApp s do return none
    let some field := s.getAppArgs[info.numParams + info.i]? | return none
    return some <| mkAppN field (args.extract (info.numParams + 1)) |>.headBeta

/-- Unfolds the definitions that are applied to structure instances, and then reduces projections
of structure instances, `match`es on constructors and β-redexes, repeatedly. Projections of
structure instances are also reduced in implicit and instance arguments (including types), which
`dsimp` doesn't visit, so that the result is not stuck on mismatched types. -/
def normalize (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext {} (simpTheorems := #[]) (congrTheorems := ← getSimpCongrTheorems)
  let mut e := e
  for _ in [:16] do
    let e' ← Meta.transform e (pre := fun t => do
      let .const c _ := t.getAppFn | return .continue
      unless ← t.getAppArgs.anyM isStructCtorApp do return .continue
      -- a class projection, like the coercion `⇑(Equiv.mk f g l r) x`: unfold the instance
      if let some t' ← unfoldProjInst? t then
        trace[simps.gen] "unfolding the instance of {c}"
        return .visit t'
      unless ← canUnfold c do return .continue
      let some t' ← unfoldDefinition? t | return .continue
      trace[simps.gen] "unfolding {c}"
      return .visit t'.headBeta)
      (post := fun t => do
        let some t' ← reduceProjOfCtor? t | return .done t
        return .visit t')
    let (e', _) ← Meta.dsimp e' ctx
    if e' == e then return e
    e := e'
  return e

/-- The simp context of `simps!!`: the default simp set, together with `rules` and their `_assoc`
versions (if they exist). -/
def simpCtx (rules : Array Name) : MetaM Simp.Context := do
  let mut thms ← getSimpTheorems
  let env ← getEnv
  for r in rules do
    thms ← thms.addConst r
    let r' := r.appendAfter "_assoc"
    if env.contains r' then thms ← thms.addConst r'
  Simp.mkContext {} (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)

/-- Simplifies `e` with `simpCtx rules`. Returns the result and a proof that `e` equals it, or
`none` if it is definitionally equal to `e`.

Unlike `simps!`, this doesn't call `dsimp` first: `dsimp` rewrites implicit arguments, but not
instance arguments, which can leave terms like `@DFunLike.coe (α ≃ β') (EquivLike.toFunLike …β…)`
on which `simp` lemmas no longer unify. -/
def simpRhs (e : Expr) (rules : Array Name) : MetaM (Expr × Option Expr) := do
  let ctx ← simpCtx rules
  let simprocs := #[← Simp.getSimprocs]
  let (r, _) ← Meta.simp e ctx simprocs
  return (r.expr, r.proof?)

/-- Instantiates the generalized projection `g` for a self argument of type `tgt`: returns the
body of `g.declName` applied to its parameters (a function of the self argument and the extra
arguments), or `none` if `g` doesn't apply. -/
def instGenProj (g : GenProj) (tgt : Expr) : MetaM (Option Expr) := do
  let info ← getConstInfo g.declName
  let lvls ← mkFreshLevelMVarsFor info
  let (xs, bis, _) ← forallMetaBoundedTelescope (info.instantiateTypeLevelParams lvls)
    (g.selfIdx + 1)
  let some x := xs[g.selfIdx]? | return none
  unless ← isDefEq (← inferType x) tgt do return none
  let params := xs.pop
  for p in params, bi in bis do
    if bi.isInstImplicit && !(← p.mvarId!.isAssigned) then
      let .some inst ← trySynthInstance (← inferType p) | return none
      unless ← isDefEq p inst do return none
  let params ← params.mapM instantiateMVars
  if params.any (·.hasMVar) then return none
  let some val := info.value? (allowOpaque := false)
    | throwError "`simps!!`: the body of {.ofConstName g.declName} is not available"
  let lvls ← lvls.mapM instantiateLevelMVars
  return (val.instantiateLevelParams info.levelParams lvls).beta params

/-- How specific the discrimination tree keys `keys` are: the number of keys that aren't `*`. -/
def specificity (keys : Array DiscrTree.Key) : Nat :=
  keys.foldl (fun n k => if k matches .star then n else n + 1) 0

/-- The generalized projections that apply to terms of type `tgt`, each with the result of
`instGenProj`.

Of the generalized projections with the same name, only the most specific ones are used: for
instance, a projection registered for `W ⟶ kernel f` takes precedence over one registered for
`W ⟶ equalizer f g`, which `kernel f` unfolds to. -/
def genProjsFor (tgt : Expr) : MetaM (Array (GenProj × Expr)) := do
  let cands ← withReducible <| (projExt.getState (← getEnv)).1.getMatch tgt
  let gens ← cands.filterMapM fun g => do
    let some f ← instGenProj g tgt | return none
    return some (g, f)
  return gens.filter fun (g, _) =>
    gens.all fun (g', _) => g'.name != g.name || specificity g'.keys ≤ specificity g.keys

/-- Applies an η-rule for the type of `x`, if there is one, the most specific one if there are
several: returns `x'` and a proof of `x = x'`. -/
def applyEta? (x : Expr) : MetaM (Option (Expr × Expr)) := do
  let tgt ← inferType x
  let rules ← withReducible <| (etaExt.getState (← getEnv)).getMatch tgt
  -- the most specific rule first (e.g. the one for `kernel f` rather than `equalizer f g`)
  for rule in rules.qsort (specificity ·.keys > specificity ·.keys) do
    let info ← getConstInfo rule.declName
    let lvls ← mkFreshLevelMVarsFor info
    let (xs, bis, concl) ← forallMetaTelescope (info.instantiateTypeLevelParams lvls)
    let some self := xs[rule.selfIdx]? | continue
    unless ← isDefEq self x do continue
    for p in xs, bi in bis do
      if bi.isInstImplicit && !(← p.mvarId!.isAssigned) then
        if let .some inst ← trySynthInstance (← inferType p) then
          discard <| isDefEq p inst
    let prf ← instantiateMVars (mkAppN (.const rule.declName lvls) xs)
    let concl ← instantiateMVars concl
    if prf.hasMVar then continue
    let some (_, _, rhs) := concl.eq? | continue
    return some (rhs, prf)
  return none

/-! ### The unused custom projections linter -/

/-- Initializes the `simps` projections of the structure `str`, as `Simps.getRawProjections`
does, but without counting generalized projections in the namespace `str.Simps` as unused custom
projections in `linter.simpsUnusedCustomDeclarations`. -/
def initProjections (stx : Syntax) (str : Name) : CoreM Unit := do
  let env ← getEnv
  if (Simps.structureExt.find? env str).isSome then return
  let (_, projs) ← withOptions (Lean.Parser.linter.simpsUnusedCustomDeclarations.set · false) <|
    Simps.getRawProjections stx str
  let genProjs := (projExt.getState env).2
  let used := projs.map (str ++ `Simps ++ ·.name)
  let unused := env.constants.map₂.foldl (init := #[]) fun xs nm _ =>
    if (str ++ `Simps).isPrefixOf nm && !nm.isInternalDetail && !isReservedName env nm &&
      !genProjs.contains nm && !used.contains nm then xs.push nm else xs
  unless unused.isEmpty do
    Linter.logLintIf Lean.Parser.linter.simpsUnusedCustomDeclarations stx m!"\
      Not all of the custom declarations {unused} are used. Double check the spelling, and use \
      `?` to get more information."

/-! ### Generating the lemmas -/

/-- The name of a generated lemma, as a list of components joined by `_`. -/
structure LemmaName where
  /-- The namespace of the lemma. -/
  parent : Name
  /-- The components of the last part of the name. -/
  components : List String

/-- The name of the lemma. -/
def LemmaName.toName (n : LemmaName) : Name :=
  .str n.parent <| match n.components with
    | [] => ""
    | [x] => s!"{x}_def"
    | e => "_".intercalate e

/-- Adds the projection name `s` to `n`, at position `pos`. -/
def LemmaName.update (n : LemmaName) (s : String) (pos : NamePos) : LemmaName :=
  { n with components := match pos, n.components.getLast? with
    | .suffix, _ | .precomp, none => n.components ++ [s]
    | .prefix, _ => s :: n.components
    | .precomp, some l => n.components.dropLast ++ [s, l] }

/-- A variant of `String.dropPrefix?` that doesn't consider `toFoo` to be a prefix of `toFoo_1`. -/
def dropPrefixIfNotNumber? (s pre : String) : Option String := do
  let ret ← s.dropPrefix? pre
  if ret.toString.toList.head?.elim false Char.isDigit then none else some ret.toString

/-- The state shared by the recursive calls of `addLemmas`. -/
structure Ctx where
  /-- The syntax of the attribute. -/
  ref : Syntax
  /-- The universe parameters of the declaration. -/
  univs : List Name
  /-- The configuration. -/
  cfg : Simps.Config
  /-- The head constant of the body of the declaration, if it is a definition (not a
  constructor). -/
  rootHead? : Option Name

/-- Adds the lemma `lhs = rhs` (with proof `prf`, or `rfl` if `none`), universally quantified
over `args`, under the name `nm`. -/
def addLemma (c : Ctx) (ref : Syntax) (nm : Name) (lhs rhs : Expr) (prf? : Option Expr)
    (args : Array Expr) (attrs : Array Syntax) : MetaM Unit :=
  withOptions (fun opts => backward.defeqAttrib.useBackward.set opts true) do
  let type ← inferType lhs
  let lvl ← getLevel type
  let prf := prf?.getD (mkApp2 (.const ``Eq.refl [lvl]) type lhs)
  let declType ← instantiateMVars <| ← mkForallFVars args (mkApp3 (.const ``Eq [lvl]) type lhs rhs)
  let declValue ← instantiateMVars <| ← mkLambdaFVars args prf
  if declType.hasMVar || declValue.hasMVar then
    throwError "`simps!!` failed to generate {nm}: the statement{indentExpr declType}\n\
      contains metavariables"
  if (← getEnv).contains nm then
    throwError "`simps!!` tried to add lemma{indentD m!"{.ofConstName nm} : {declType}"}\n\
      to the environment, but it already exists."
  Mathlib.Tactic.warnIfImplicitIllTyped ref nm declType
  prependError "Failed to add projection lemma {nm}:" do
    addDecl <| .thmDecl { name := nm, levelParams := c.univs, type := declType, value := declValue }
  trace[simps] "Adding `{.ofConstName nm}` :{indentExpr declType}"
  inferDefEqAttr nm
  addDeclarationRangesFromSyntax nm (← getRef) ref
  addTermInfo' ref (← mkConstWithLevelParams nm) (isBinder := true) |>.run'
  if c.cfg.isSimp then
    addSimpTheorem simpExtension nm true false .global <| eval_prio default
  TermElabM.run' do
    Term.applyAttributes nm c.cfg.attrs
    Term.applyAttributes nm (← elabAttrs attrs)

/-- The maximal nesting of generalized projections. -/
def maxDepth : Nat := 8

/-- A node of the tree of projections explored by `addLemmas`: the equation `lhs = rhs`, where
both sides have type `type` and contain the variables `args`. -/
structure Node where
  /-- The name of the lemma for this node. -/
  nm : LemmaName
  /-- The type of both sides. -/
  type : Expr
  /-- The left-hand side: (generalized) projections applied to the declaration. -/
  lhs : Expr
  /-- The right-hand side, computed from the body of the declaration, unfolded to constructor
  applications as needed. -/
  rhs : Expr
  /-- The same (generalized) projections applied to the body of the declaration, without
  unfolding it. Simplifying this often gives better results, by using the lemmas about the
  definitions the body is made of. -/
  folded : Expr
  /-- The variables in `lhs` and `rhs`. -/
  args : Array Expr
  /-- Whether this is the declaration itself, for which (generalized) projections must exist. -/
  mustBeStr : Bool := false
  /-- The projections asked for, as in `Simps.addProjections`. -/
  todo : List (String × Syntax)
  /-- The remaining indices of a custom composite projection. -/
  toApply : List Nat := []
  /-- The extra lemmas to simplify the right-hand side with. -/
  rules : Array Name := #[]
  /-- Whether `rhs` and `folded` are a generalized projection applied to a value, to be
  normalized. -/
  pending : Bool := false
  /-- Whether we got here through a `noRecurse` generalized projection. -/
  eta : Bool := false
  /-- Whether we got here through a generalized projection. -/
  viaGen : Bool := false
  /-- The number of generalized projections applied. -/
  depth : Nat := 0
  /-- The extra attributes for the lemma (those of the last generalized projection). -/
  attrs : Array Syntax := #[]

/-- The right-hand side of a lemma, with its proof (`none` for `rfl`): the simp normal form of
`folded`, if it no longer contains the head of the body of the declaration, and that of `rhs`
otherwise. -/
def finalRhs (c : Ctx) (rules : Array Name) (rhs folded : Expr) : MetaM (Expr × Option Expr) := do
  if !c.cfg.simpRhs then return (rhs, none)
  if let some h := c.rootHead? then
    let (r, prf?) ← simpRhs folded rules
    if !r.containsConst (· == h) then return (r, prf?)
    trace[simps.gen] "the folded right-hand side simplifies to{indentExpr r}\nwhich contains {h}"
  simpRhs rhs rules

/-- Derives the lemmas for the node `n`, by applying projections and generalized projections to
both sides, recursively. This follows `Simps.addProjections`. -/
partial def addLemmas (c : Ctx) (n : Node) : MetaM (Array Name) := do
  let cfg := c.cfg
  withTransparency cfg.typeMd <| forallTelescopeReducing n.type fun typeArgs tgt ↦ withDefault do
  let tgtWhnf ← whnfD tgt
  let nm := n.nm
  let newArgs := n.args ++ typeArgs
  let lhsAp := n.lhs.instantiateLambdasOrApps typeArgs
  let mut rhsAp := n.rhs.instantiateLambdasOrApps typeArgs
  let mut foldedAp := n.folded.instantiateLambdasOrApps typeArgs
  if n.pending then
    rhsAp ← normalize rhsAp
    foldedAp ← normalize foldedAp
  trace[simps.gen] "{nm.toName}, before simplification: {lhsAp} = {rhsAp}"
  let todo := n.todo
  let todoNext := todo.filter (·.1 ≠ "")
  let stx? := todo.find? (·.1 == "") |>.map (·.2)
  let stxProj := stx?.getD c.ref[0]
  let leaf (rhsAp : Expr) : MetaM (Array Name) := do
    let (rhs, prf?) ← do
      if n.eta then
        if let some (e, pe) ← applyEta? lhsAp then
          let (r, pr?) ← simpRhs e n.rules
          pure (r, some <| ← match pr? with
            | some pr => mkEqTrans pe pr
            | none => pure pe)
        else finalRhs c n.rules rhsAp foldedAp
      else finalRhs c n.rules rhsAp foldedAp
    addLemma c stxProj nm.toName lhsAp rhs prf? newArgs n.attrs
    return #[nm.toName]
  -- the generalized projections
  let gens ← if n.toApply.isEmpty && !n.eta && n.depth < maxDepth then genProjsFor tgt
    else pure #[]
  let gens := gens.filter fun (g, _) => !(todo.isEmpty && !g.isDefault) &&
    -- projections that don't recurse state a universal property of the object itself, which
    -- after a generalized projection would be redundant
    (g.recurse || !n.viaGen) &&
    (todo.isEmpty || todoNext.any fun (x, _) => (dropPrefixIfNotNumber? x (g.name ++ "_")).isSome)
  let hides := gens.flatMap (·.1.hides)
  -- the genuine projections
  let str := tgtWhnf.getAppFn.constName?.getD .anonymous
  let env ← getEnv
  let isStr := (getStructureInfo? env str).isSome && !n.eta &&
    !(todo.isEmpty && str ∈ cfg.notRecursive && !n.mustBeStr && n.toApply.isEmpty)
  let rhsEta ← Simps.headStructureEtaReduce rhsAp
  if isStr then initProjections c.ref str
  let rhsWhnf? ← if isStr then do
      let rhsWhnf ← withTransparency cfg.rhsMd <| whnf rhsEta
      if rhsWhnf.getAppFn.isConstOf (getStructureCtor env str).name then pure (some rhsWhnf)
      else pure none
    else pure none
  let projInfo ← match rhsWhnf? with
    | some rhsWhnf => Simps.getProjectionExprs c.ref tgtWhnf rhsWhnf cfg
    | none => pure #[]
  -- in the middle of a custom composite projection
  if let idx :: rest := n.toApply then
    let some ⟨newRhs, _⟩ := projInfo[idx]? |
      throwError "Invalid simp lemma {nm.toName}.\nThe given definition is not a constructor \
        application:{indentExpr rhsAp}"
    return ← addLemmas c { n with
      type := ← inferType newRhs, lhs := lhsAp, rhs := newRhs, folded := foldedAp, args := newArgs,
      mustBeStr := false, toApply := rest, pending := false }
  let projInfo := projInfo.filter fun (_, p) => !hides.contains p.name
  if projInfo.isEmpty && gens.isEmpty then
    if n.mustBeStr then
      throwError "Invalid `simps!!` attribute: neither projections nor generalized projections \
        apply to{indentExpr tgt}"
    if let some (x, _) := todoNext.head? then
      throwError "Invalid simp lemma {nm.toName}_{x.dropEnd 1}.\nNo projection or generalized \
        projection applies to{indentExpr tgt}"
    return ← leaf rhsEta
  let addThis := stx?.isSome
  let mut nms := #[]
  if addThis then nms := nms ++ (← leaf rhsEta)
  if todo.length == 1 && addThis then return nms
  -- check that every element of `todo` starts with a projection
  let names := projInfo.map (·.2.name.lastComponentAsString) ++ gens.map (·.1.name)
  if let some (x, _) := todoNext.find? fun (x, _) => names.all
      fun n => (dropPrefixIfNotNumber? x (n ++ "_")).isNone then
    throwError "Invalid simp lemma {nm.toName}_{x.dropEnd 1}. There is no projection or \
      generalized projection {x.dropEnd 1} for{indentExpr tgt}\nThe known ones are:\
      {indentD <| toMessageData names}"
  let newTodo (n : String) := todoNext.filterMap fun (x, stx) =>
    (dropPrefixIfNotNumber? x (n ++ "_")).map (·, stx)
  for ⟨newRhs, proj, projExpr, projNrs, isDefault, isPrefix⟩ in projInfo do
    let p := proj.lastComponentAsString
    if !(isDefault && todoNext.isEmpty) && (newTodo p).isEmpty then continue
    let newLhs := projExpr.instantiateLambdasOrApps #[lhsAp]
    -- the type of the left-hand side is the one written by the user, which is the one that
    -- generalized projections are keyed on (unlike the type of the value)
    nms := nms ++ (← addLemmas c { n with
      nm := nm.update p (if isPrefix then .prefix else .suffix), type := ← inferType newLhs,
      lhs := newLhs, rhs := newRhs, folded := projExpr.instantiateLambdasOrApps #[foldedAp],
      args := newArgs, mustBeStr := false, todo := newTodo p, toApply := projNrs,
      pending := false, eta := false, attrs := #[] })
  -- recursive generalized projections first, so that the lemmas they generate can be used by
  -- the others
  let gens := gens.filter (·.1.recurse) ++ gens.filter (!·.1.recurse)
  for (g, f) in gens do
    let newLhs := f.beta #[lhsAp]
    let newType ← inferType newLhs
    if ← isProp newType then continue
    nms := nms ++ (← addLemmas c {
      nm := nm.update g.name g.pos, type := newType, lhs := newLhs,
      rhs := f.beta #[rhsWhnf?.getD rhsAp], folded := f.beta #[foldedAp], args := newArgs,
      todo := newTodo g.name, rules := n.rules ++ g.rules, pending := true, eta := !g.recurse,
      viaGen := true, depth := n.depth + 1, attrs := g.attrs })
  return nms

/-- `simps!!` applied to the declaration `declName`. -/
def simpsGenTac (ref : Syntax) (declName : Name) (cfg : Simps.Config)
    (todo : List (String × Syntax)) (trc : Bool) : AttrM (Array Name) :=
  withOptions (fun o => if trc then o.set `trace.simps true else o) do
  let env ← withoutExporting getEnv
  let some d := env.find? declName | throwError "Declaration {declName} doesn't exist."
  let lhs : Expr := .const d.name <| d.levelParams.map .param
  let todo := todo.eraseDups.map fun (proj, stx) => (proj ++ "_", stx)
  let nm : LemmaName :=
    { parent := declName.getPrefix
      components :=
        if let some n := cfg.nameStem then
          if n == "" then [] else [n]
        else
          let s := declName.lastComponentAsString
          if (← isInstance declName) ∧ s.startsWith "inst" then [] else [s] }
  let body := d.value! (allowOpaque := true)
  let rootHead? := match body.getLambdaBody.getAppFn with
    | .const h _ => if (env.find? h matches some (.ctorInfo _)) then none else some h
    | _ => none
  withoutExporting <| MetaM.run' <| addLemmas { ref, univs := d.levelParams, cfg, rootHead? }
    { nm, type := d.type, lhs, rhs := body, folded := body, args := #[], mustBeStr := true, todo }

initialize registerBuiltinAttribute {
  name := `simpsGen
  descr := "`simps!` with generalized projections"
  applicationTime := .afterCompilation
  add := fun decl stx _ => do
    match stx with
    | `(attr| simps!! $[?%$trc]? $c:simpsConfig $[$ids]*) =>
      let cfg ← Simps.elabSimpsConfig c
      let cfg := { cfg with rhsMd := .default, simpRhs := true }
      let ids := ids.map fun x => (x.getId.eraseMacroScopes.lastComponentAsString, x.raw)
      discard <| simpsGenTac stx decl cfg ids.toList trc.isSome
    | _ => throwUnsupportedSyntax }

end Simps.Gen
