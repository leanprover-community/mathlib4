/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Elab.DeclarationRange
public meta import Lean.Elab.Tactic
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Elab.Term
public meta import Mathlib.Tactic.Simps.Basic
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Init
public import Lean.Util.CollectFVars
public import Lean.Util.CollectLevelParams

/-!
# `spec_dsimp`

`spec_dsimp(e, x)` specializes `e` by filling either

* a free variable occurring in `e` (replaced by `x` when the result typechecks), or
* one of the `∀` binders in the type of `e`, unified with `x`,

then runs `dsimp` on the resulting expression. For a **proof**, `dsimp` is also run on the inferred
**proposition** (and the result is attached via `mkExpectedTypeHint`), matching `dsimp%` so lemma
types and `#check` show the reduced formula, not only a reduced proof term.

With **two or more** comma-separated arguments that are all **plain** terms, `spec_dsimp` elaborates
the application `e a₁ a₂ … aₙ` (as `dsimp%` does) and defeq-reduces that proof term.

You can instead write **named** binders, e.g. `spec_dsimp(e, F := t)`, in **any order**; they are
filled on the lemma constant while leaving unspecified `∀` parameters as metavariables (so you can
specialize e.g. `J` while keeping another type parameter schematic). The lemma must be an
**identifier** (a constant), not an arbitrary term. Remaining parameters are inferred or generalized
when declaring a lemma with the command.

The `(`/`,`/`)` form avoids Lean parsing `spec_dsimp e x` as `spec_dsimp e` applied to `x`.
If `e` is an identifier, it is resolved as a constant (so implicit lambdas are not inserted).

## Generating a lemma (command)

At **command** position (top-level in a file), use

`spec_dsimp("LemmaName", lemma, specArgs…)`,

where the **first** argument is a **string literal** (the new declaration name), then the lemma,
then the same `specArgs` as in the term form (`term` or `name := term`). The name must come first
so string literals are not parsed as ordinary `specBindArg` terms.
Example:

`spec_dsimp("created", test, Nat)`

elaborates `spec_dsimp(test, Nat)`, infers its (possibly dependent) proposition type, generalizes
any hypotheses introduced during elaboration (e.g. auto-bound implicits), and registers a theorem
in the environment (via `addDecl`), so universe parameters need not round-trip through syntax.
-/

public meta section

open Lean Elab Meta Term
open Lean.Elab.Command
open Lean.Elab.Tactic
open Lean.Elab.Term (ensureHasType getLevelNames levelMVarToParam mkConst ensureNoUnassignedMVars)

namespace Mathlib.Tactic

declare_syntax_cat specBindArg

syntax (name := specBindNamed) ident ppSpace " := " ppSpace term : specBindArg
syntax (name := specBindPlain) term : specBindArg

/-- Collect distinct `FVarId`s appearing in `e`. -/
private def exprFVars (e : Expr) : MetaM (Array FVarId) := do
  let r ← IO.mkRef (#[] : Array FVarId)
  Meta.forEachExpr e fun sub => do
    if let .fvar id := sub then
      r.modify fun a => if a.contains id then a else a.push id
  r.get

/-- Repeatedly try to synthesize currently unassigned instance metavariables. -/
private def tryAssignInstMVars (instMVars : Array MVarId) : MetaM Unit := do
  for _ in [:instMVars.size + 2] do
    for mid in instMVars do
      unless ← mid.isAssigned do
        let decl ← mid.getDecl
        if let .some val ← trySynthInstance decl.type then
          mid.assign val

/-- Try unifying one `∀` argument of `e`'s type with `x` (fresh mvars per attempt). -/
private def trySpecializeForallBinder (e x : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars (← inferType e)
  let n ← withNewMCtxDepth do return (← forallMetaTelescope ty).1.size
  for i in [:n] do
    if let some app ← observing? do
      let (mvars, bis, _) ← forallMetaTelescope ty
      unless i < mvars.size do throwError "internal"
      unless ← withTransparency .all <| isDefEq mvars[i]! x do throwError "internal"
      -- Instance implicits may become assignable after unifying earlier arguments.
      let instMVars := (mvars.zip bis).foldl (init := #[]) fun acc (m, bi) =>
        if bi.isInstImplicit then
          acc.push m.mvarId!
        else
          acc
      tryAssignInstMVars instMVars
      let app := mkAppN e mvars
      let _ ← inferType app
      instantiateMVars app
    then
      return some app
  return none

/-- Unify telescope slot `i` of `e`'s type with `xStx`. -/
private def specializeForallMetaSlot (e : Expr) (i : Nat) (xStx : Syntax) :
    TermElabM (Option Expr) := do
  let e ← instantiateMVars e
  let ty ← instantiateMVars (← inferType e)
  let s ← saveState
  try
    let (mvars, bis, _) ← forallMetaTelescope ty
    unless i < mvars.size do throwError "internal"
    let xI ← withoutErrToSorry <| elabTerm xStx none
    if xI.isSorryAx then throwError "internal"
    synthesizeSyntheticMVarsNoPostponing
    unless ← withTransparency .all <| isDefEq mvars[i]! xI do throwError "internal"
    let instMVars := (mvars.zip bis).foldl (init := #[]) fun acc (m, bi) =>
      if bi.isInstImplicit then
        acc.push m.mvarId!
      else
        acc
    tryAssignInstMVars instMVars
    let app := mkAppN e mvars
    return some (← instantiateMVars app)
  catch _ =>
    restoreState s
    return none

/--
Try unifying one `∀` binder of `e`'s type with `xStx`, re-elaborating `xStx` against each
binder's expected type (so implicit parameters of `xStx` can be resolved differently per slot).
Uses `saveState`/`restoreState` so failed attempts do not leak metavariables.
-/
private def trySpecializeForallBinderWithSyntax (e : Expr) (xStx : Syntax) :
    TermElabM (Option Expr) := do
  let e ← instantiateMVars e
  let ty ← instantiateMVars (← inferType e)
  let n ← withNewMCtxDepth do return (← forallMetaTelescope ty).1.size
  for i in [:n] do
    if let some app ← specializeForallMetaSlot e i xStx then
      return some app
  return none

/-- `i` such that the `i`-th leading `∀` binder of `ty` has name `target` (macro scopes ignored). -/
private partial def findForallParamIndexByName.go (target : Name) (ty : Expr) (i : Nat) :
    MetaM (Option Nat) := do
  let ty ← instantiateMVars ty
  let ty ← whnf ty
  match ty with
  | .forallE n _ b _ =>
      if n.eraseMacroScopes == target.eraseMacroScopes then
        return some i
      else
        findForallParamIndexByName.go target b (i + 1)
  | _ => return none

private def findForallParamIndexByName (ty : Expr) (target : Name) : MetaM (Option Nat) :=
  findForallParamIndexByName.go target.eraseMacroScopes ty 0

/--
Like `mkAppOptM`, but continues with fresh metavariables for every remaining `∀` until the type
is no longer a `∀` (full application). Skips `mkAppMFinal`, so instance goals like `Category A`
need not be solved while `A` is still unknown. Pair with `Term.mkConst` (not isolated level metas)
so universes unify with elaborated RHSs.
-/
private partial def mkAppOptMOpenAux (f : Expr) (xs : Array (Option Expr)) (k : Nat)
    (args : Array Expr) (j : Nat) (instMVars : Array MVarId) (type : Expr) : MetaM Expr := do
  match type with
  | .forallE n d b bi => do
    let d := d.instantiateRevRange j args.size args
    let xProvided? : Option Expr :=
      if h : k < xs.size then
        match xs[k] with
        | some x => some x
        | none => none
      else
        none
    match xProvided? with
    | some x => do
        let xType ← inferType x
        unless ← isDefEq d xType do
          throwError m!"type mismatch in `spec_dsimp` named argument:{indentExpr x}\n\
            expected{indentExpr d}\nbut got{indentExpr xType}"
        mkAppOptMOpenAux f xs (k + 1) (args.push x) j instMVars b
    | none => do
        match bi with
        | .instImplicit => do
          let mvar ← mkFreshExprMVar d .synthetic n
          mkAppOptMOpenAux f xs (k + 1) (args.push mvar) j (instMVars.push mvar.mvarId!) b
        | _ => do
          let mvar ← mkFreshExprMVar d .natural n
          mkAppOptMOpenAux f xs (k + 1) (args.push mvar) j instMVars b
  | type => do
    let type := type.instantiateRevRange j args.size args
    let type ← whnfD type
    if type.isForall then
      mkAppOptMOpenAux f xs k args args.size instMVars type
    else
      let mut r := mkAppN f args
      r ← instantiateMVars r
      tryAssignInstMVars instMVars
      return (← instantiateMVars r)

private def mkAppOptMOpen (lemNm : Name) (xs : Array (Option Expr)) : TermElabM Expr := do
  let f ← mkConst lemNm
  let fType ← inferType f
  mkAppOptMOpenAux f xs 0 #[] 0 #[] fType

/-- Try replacing each `FVar` of `e` by `x` when the result still typechecks. -/
private def tryReplaceFVar (e x : Expr) : MetaM (Option Expr) := do
  let ids ← exprFVars e
  for id in ids do
    if let some e' ← observing? do
      let e' := e.replaceFVar (.fvar id) x
      let _ ← inferType e'
      return e'
    then
      return some e'
  return none

/-- Simp context for a whole-expression `dsimp` (no extra lemmas). -/
private def dsimpCtx : MetaM (Simp.Context × Simp.SimprocsArray) := do
  let { ctx, simprocs, .. } ← mkSimpContextResult (kind := SimpKind.dsimp)
  return (ctx, simprocs)

/--
`dsimp` on `e`, then for proofs `dsimp` on the inferred type and `mkExpectedTypeHint` when the
type changes (so lemma statements and `#check` show the reduced proposition, like `dsimp%` on a
proof). Without this, only the proof term is reduced and the pretty-printed type can still show
e.g. `Functor.map` instead of `whiskerLeft`.
-/
private def dsimpSpecExpr (e : Expr) : MetaM Expr := do
  let (ctx, simprocs) ← dsimpCtx
  let e ← instantiateMVars e
  let (r, _) ← Meta.dsimp e ctx simprocs
  if ← isProof r then
    let ty ← instantiateMVars (← inferType r)
    let (ty', _) ← Meta.dsimp ty ctx simprocs
    if ty' == ty then
      return r
    else
      mkExpectedTypeHint r ty'
  else
    return r

/--
Specialize `e` using `x` by either replacing a free variable in `e` or filling one leading
dependent/forall binder of `e`'s type, then defeq-reduce with `dsimp`.
-/
def specializeAndDsimp (e x : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let x ← instantiateMVars x
  let specialized? ← tryReplaceFVar e x
  let specialized? ← match specialized? with
    | some s => pure (some s)
    | none => trySpecializeForallBinder e x
  let some specialized := specialized?
    | throwError m!"specializeAndDsimp: could not specialize{indentExpr e}\nusing{indentExpr x}"
  dsimpSpecExpr specialized

/-- Elaborator for `spec_dsimp(e, x)` (exactly two arguments); see `spec_dsimp`. -/
syntax (name := specDsimpCoreStx) "specDsimpCore(" term "," term ")" : term

@[term_elab specDsimpCoreStx]
def elabSpecDsimpCore : TermElab := fun stx expectedType? => do
  let eStx := stx[1]
  let xStx := stx[3]
  let e ←
    if eStx.isIdent then do
      let nm ← realizeGlobalConstNoOverloadWithInfo eStx
      let ci ← getConstInfo nm
      pure (.const nm (ci.levelParams.map mkLevelParam))
    else
      elabTerm eStx none
  -- Do not elaborate `xStx` here when `e` has no fvars: the outer `expectedType` (e.g. the goal
  -- `Prop`) would be used and break terms like functor types.
  let ids ← exprFVars e
  let x? ← if ids.isEmpty then
    pure none
  else
    pure (some (← elabTerm xStx none))
  let specialized? ← match x? with
    | some x => tryReplaceFVar e x
    | none => pure none
  let specialized? ← match specialized? with
    | some s => pure (some s)
    | none => trySpecializeForallBinderWithSyntax e xStx
  let some specialized := specialized?
    | do
      let x ← elabTerm xStx none
      throwError m!"specializeAndDsimp: could not specialize{indentExpr e}\nusing{indentExpr x}"
  let r ← liftMetaM (dsimpSpecExpr specialized)
  if let some expectedType := expectedType? then
    ensureHasType (some expectedType) r
  else
    pure r

/-- Like `dsimp% t` with default config (no extra simp lemmas).
Used for multi-argument `spec_dsimp`. -/
private def elabDsimpPercentStyle (inner : TSyntax `term) (expectedType? : Option Expr) :
    TermElabM Expr := do
  let fresh ← mkFreshExprMVar default
  let go : TacticM Expr := do
    let e ← Term.elabTerm inner.raw expectedType?
    let (ctx, simprocs) ← liftMetaM dsimpCtx
    let doDsimp (e : Expr) : MetaM Expr := do
      let e ← instantiateMVars e
      let (r, _) ← Meta.dsimp e ctx simprocs
      if r == e then
        throwError "`dsimp%` made no progress"
      return r
    if ← liftMetaM (isProof e) then
      let ty' ← liftMetaM do doDsimp (← inferType e)
      mkExpectedTypeHint e ty'
    else
      liftMetaM (doDsimp e)
  go { elaborator := .anonymous } |>.run' { goals := [fresh.mvarId!] }

/-- User syntax: `spec_dsimp(lemma, arg, …)` with each `arg` either a term or `name := term`. -/
syntax (name := specDsimpStx) "spec_dsimp(" term "," sepBy1(specBindArg, ",") ")" : term

private def elabSpecDsimpNamedOnly (lemStx : Syntax) (named : Array (Name × TSyntax `term))
    (expectedType? : Option Expr) : TermElabM Expr := do
  /-
  `elabTerm` on `f (x₁ := v₁) …` runs typeclass search while type arguments can still be
  metavariables (e.g. `Category ?A` is stuck). `mkAppOptMOpenAux` fills the remaining `∀` with
  metas without `mkAppMFinal`. Use `Term.mkConst` for the lemma so its universe metavariables live
  in this elaboration context and unify with RHSs like `CompHaus.{u}`.
  -/
  unless lemStx.isIdent do
    throwError "spec_dsimp: named specialization requires the lemma to be a constant identifier"
  let lemNm ← realizeGlobalConstNoOverloadWithInfo lemStx
  let ci ← getConstInfo lemNm
  let ty ← instantiateMVars ci.type
  let mut pairs : Array (Nat × TSyntax `term) := #[]
  for (nm, rhs) in named do
    let some i ← liftMetaM (findForallParamIndexByName ty nm)
      | throwError m!"spec_dsimp: parameter `{nm}` does not appear in the lemma type{indentExpr ty}"
    pairs := pairs.push (i, rhs)
  let mut maxIdx := 0
  for (i, _) in pairs do
    if i > maxIdx then maxIdx := i
  let sz := maxIdx + 1
  let mut opts : Array (Option Expr) := #[]
  for _ in [:sz] do
    opts := opts.push none
  for (i, rhsStx) in pairs do
    match opts[i]! with
    | some _ => throwError "spec_dsimp: two arguments refer to the same `∀` parameter"
    | none => pure ()
    let rhsE ← elabTerm rhsStx none
    opts := opts.set! i (some rhsE)
  synthesizeSyntheticMVarsNoPostponing
  let e ← mkAppOptMOpen lemNm opts
  synthesizeSyntheticMVarsNoPostponing
  let r ← liftMetaM (dsimpSpecExpr e)
  match expectedType? with
  | some et => ensureHasType (some et) r
  | none => pure r

private def elabSpecDsimpAux (lem : TSyntax `term) (args : Array (TSyntax `specBindArg))
    (expectedType? : Option Expr) : TermElabM Expr := do
  let mut plains : Array (TSyntax `term) := #[]
  let mut named : Array (Name × TSyntax `term) := #[]
  for a in args do
    match a with
    | `(specBindArg| $x:ident := $rhs:term) =>
        named := named.push (x.getId.eraseMacroScopes, rhs)
    | `(specBindArg| $t:term) =>
        plains := plains.push t
    | _ => throwErrorAt a "ill-formed `spec_dsimp` argument"
  if !(named.isEmpty || plains.isEmpty) then
    throwError "spec_dsimp: cannot mix `name := value` with positional arguments"
  if !named.isEmpty then
    elabSpecDsimpNamedOnly lem.raw named expectedType?
  else
    match plains.size with
    | 0 => throwError "expected at least one argument after the lemma"
    | 1 =>
      let x := plains[0]!
      Term.elabTerm (← `(term| specDsimpCore($lem, $x))) expectedType?
    | _ =>
      let mut head := lem
      for i in [:plains.size] do
        head ← `(term| $head $(plains[i]!))
      elabDsimpPercentStyle head expectedType?

@[term_elab specDsimpStx]
def elabSpecDsimp : TermElab := fun stx expectedType? => withRef stx do
  unless stx.isOfKind ``specDsimpStx do throwUnsupportedSyntax
  let a := stx.getArgs
  let lem : TSyntax `term := ⟨a[1]!⟩
  let sepNode := a[3]!
  let args : Array (TSyntax `specBindArg) := sepNode.getSepArgs.map fun s => ⟨s⟩
  elabSpecDsimpAux lem args expectedType?

/-- Command: `spec_dsimp("name", lemma, args…)` declares the lemma (name must be first). -/
syntax (name := specDsimpGen) "spec_dsimp(" str "," term "," sepBy1(specBindArg, ",") ")" : command

@[command_elab specDsimpGen]
def elabSpecDsimpGen : CommandElab := fun stx => do
  unless stx.isOfKind ``specDsimpGen do throwUnsupportedSyntax
  let a := stx.getArgs
  let nameStx := a[1]!
  let lem := a[3]!
  let sepNode := a[5]!
  let some lemmaNameStr := nameStx.isStrLit?
    | throwErrorAt nameStx "expected string literal lemma name"
  let declName := Name.mkSimple lemmaNameStr
  unless declName.isAtomic && !lemmaNameStr.isEmpty do
    throwErrorAt nameStx "invalid lemma name"
  let specArgs := sepNode.getSepArgs
  if specArgs.isEmpty then
    throwError "expected at least one argument after the lemma name"
  let lemTs : TSyntax `term := ⟨lem⟩
  let argsTs : Array (TSyntax `specBindArg) := specArgs.map fun s => ⟨s⟩
  let decl ← runTermElabM fun _ => do
    let scopeLevelNames ← getLevelNames
    let proofE ← elabSpecDsimpAux lemTs argsTs none
    synthesizeSyntheticMVarsNoPostponing
    let proofE₀ ← instantiateMVars proofE
    let proofE₀' ← if proofE₀.hasExprMVar then
      pure (← abstractMVars (levels := false) proofE₀).expr
    else
      pure proofE₀
    let proofE ← instantiateMVars proofE₀'
    if proofE.hasExprMVar then
      throwError m!"`spec_dsimp` proof still has metavariables:{indentExpr proofE}"
    let ty ← instantiateMVars (← inferType proofE)
    unless ← isProp ty do
      throwError "`spec_dsimp` must produce a proof of a proposition, got type{indentExpr ty}"
    let lctx ← getLCtx
    let s₀ := collectFVars (collectFVars {} ty) proofE
    let s ← CollectFVars.State.addDependencies s₀
    let fvarIds :=
      s.fvarIds.filter fun fvarId =>
        match lctx.find? fvarId with
        | none => false
        | some ldecl => !ldecl.isAuxDecl
    let fvarIds := lctx.sortFVarsByContextOrder fvarIds
    let fvarExprs := fvarIds.map mkFVar
    let tyAbstract ← mkForallFVars fvarExprs ty
    unless ← isProp tyAbstract do
      throwError "internal error: generalized type is not a proposition"
    let proofAbstract ← mkLambdaFVars fvarExprs proofE
    unless ← isDefEq (← inferType proofAbstract) tyAbstract do
      throwError "internal error: abstracted proof does not match generalized type"
    let tyAbstract ← instantiateMVars tyAbstract
    let proofAbstract ← instantiateMVars proofAbstract
    let tyAbstract ← levelMVarToParam tyAbstract
    let proofAbstract ← levelMVarToParam proofAbstract
    let usedParams := (collectLevelParams (collectLevelParams {} tyAbstract) proofAbstract).params
    let allUserLevelNames ← getLevelNames
    let levelParams ←
      match Lean.Elab.sortDeclLevelParams scopeLevelNames allUserLevelNames usedParams with
      | Except.error msg => throwError msg
      | Except.ok ls => pure ls
    let tyAbstract ← instantiateMVars tyAbstract
    let proofAbstract ← instantiateMVars proofAbstract
    if tyAbstract.hasMVar || proofAbstract.hasMVar then
      throwError m!"`spec_dsimp` declaration still has metavariables after generalization"
    let decl := Declaration.thmDecl {
      name := declName
      levelParams := levelParams
      type := tyAbstract
      value := proofAbstract }
    ensureNoUnassignedMVars decl
    pure decl
  liftCoreM (addDecl decl)
  addDeclarationRangesFromSyntax declName stx

end Mathlib.Tactic
