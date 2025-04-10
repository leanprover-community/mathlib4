/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Wojciech Nawrocki
-/
import Lean.Elab.Tactic
import Mathlib.Init

/-! ## Dependent rewrite tactic -/

namespace Mathlib.Tactic.DepRewrite
open Lean Meta

theorem dcongrArg.{u, v} {α : Sort u} {a a' : α}
    {β : (a' : α) → @Eq α a a' → Sort v} (h : @Eq α a a')
    (f : (a' : α) → (h : @Eq α a a') → β a' h) :
    f a (@Eq.refl α a) =
    @Eq.rec α a' (fun x h' ↦ β x (@Eq.trans α a a' x h h')) (f a' h) a (@Eq.symm α a a' h) :=
  Eq.rec (Eq.refl (f a (Eq.refl a))) h

theorem nddcongrArg.{u, v} {α : Sort u} {a a' : α}
    {β : Sort v} (h : @Eq α a a') (f : (a' : α) → (h : @Eq α a a') → β) :
    f a (@Eq.refl α a) = f a' h :=
  Eq.rec (Eq.refl (f a (Eq.refl a))) h

theorem heqL.{u} {α β : Sort u} {a : α} {b : β} (h : @HEq α a β b) :
    @Eq α a (@cast β α (@Eq.symm (Sort u) α β (@type_eq_of_heq α β a b h)) b) :=
  HEq.rec (Eq.refl a) h

theorem heqR.{u} {α β : Sort u} {a : α} {b : β} (h : @HEq α a β b) :
    @Eq β (@cast α β (@type_eq_of_heq α β a b h) a) b :=
  HEq.rec (Eq.refl a) h

initialize
  registerTraceClass `depRewrite
  registerTraceClass `depRewrite.visit
  registerTraceClass `depRewrite.cast

/-- Determines which, if any, type-incorrect subterms
should be casted along the equality that `depRewrite` is rewriting by. -/
inductive CastMode where
  /-- Don't insert any casts. -/
  | none
  /-- Only insert casts on proofs.

  In this mode, it is *not* permitted to cast subterms of proofs that are not themselves proofs.
  For example, given `y : Fin n`, `P : Fin n → Prop`, `p : (x : Fin n) → P x` and `eq : n = m`,
  we will not rewrite `p y : P y` to `p (eq ▸ y) : P (eq ▸ y)`. -/
  | proofs
  -- TODO: `proofs` plus "good" user-defined casts such as `Fin.cast`.
  -- | userDef
  /-- Insert as many `Eq.rec`s as necessary. -/
  | all
deriving BEq

instance : ToString CastMode := ⟨fun
  | .none => "none"
  | .proofs => "proofs"
  | .all => "all"⟩

def CastMode.toNat : CastMode → Nat
  | .none => 0
  | .proofs => 1
  | .all => 2

instance : LE CastMode where
  le a b := a.toNat ≤ b.toNat

instance : DecidableLE CastMode :=
  fun a b => inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

structure Config where
  transparency : TransparencyMode := .reducible
  offsetCnstrs : Bool := true
  occs : Occurrences := .all
  castMode : CastMode := .proofs

structure Context where
  cfg : DepRewrite.Config
  /-- The pattern to generalize over. -/
  p : Expr
  /-- The free variable to substitute for `p`. -/
  x : Expr
  /-- A proof of `p = x`. Must be an fvar. -/
  h : Expr
  pHeadIdx : HeadIndex := p.toHeadIndex
  pNumArgs : Nat := p.headNumArgs
  subst : FVarSubst := {}

/-- Monad for computing `dabstract`.
The cache is for `visit` (not `visitAndCast`, which has two arguments),
and the `Nat` tracks which occurrence of the pattern we are currently seeing. -/
abbrev M := ReaderT Context <| MonadCacheT ExprStructEq Expr <| StateRefT Nat MetaM

/-- Check that casting `e : t` is allowed in the current mode.
(We don't need to know what type `e` is cast to:
we only check the sort of `t`, and it cannot change.) -/
def checkCastAllowed (e t : Expr) (castMode : CastMode) : MetaM Unit := do
  let throwMismatch : Unit → MetaM Unit := fun _ => do
    throwError "Will not cast{indentExpr e}\nin cast mode '{castMode}'. \
If inserting more casts is acceptable, use `(castMode := .all)`."
  if castMode == .none then
    throwMismatch ()
  if castMode == .proofs && !(← isProp t) then
    throwMismatch ()

/-- If `e : te` is a term whose type mentions `x` or `h` (the generalization variables),
return `⋯ ▸ e : te[p/x,rfl/h]`.
Otherwise return `none`. -/
def castBack? (e te x h : Expr) : MetaM (Option Expr) := do
  if !te.hasFVar || !te.hasAnyFVar (fun f => f == x.fvarId! || f == h.fvarId!) then
    return none
  let motive ←
    withLocalDeclD `x' (← inferType x) fun x' => do
    withLocalDeclD `h' (← mkEq x x') fun h' => do
      mkLambdaFVars #[x', h'] <| te.replaceFVars #[x, h] #[x', ← mkEqTrans h h']
  some <$> mkEqRec motive e (← mkEqSymm h)

def withSubst? {α : Type} (x tx : Expr) (k : M α) : M α := do
  let ctx ← read
  match ← castBack? x tx ctx.x ctx.h with
  | some e =>
    -- We do NOT check whether this is an allowed cast here
    -- because it might not ever be used
    -- (e.g. if the bound variable is never mentioned).
    withReader (fun ctx => { ctx with subst := ctx.subst.insert x.fvarId! e }) k
  | none => k

mutual

/-- Given `e`, return `e[x/p]` (i.e., `e` with occurrences of `p` replaced by `x`).
If `et?` is not `none`, the output is guaranteed to have type (defeq to) `et?`.

Does _not_ assume that `e` is well-typed,
but assumes that for all subterms `e'` of `e`,
`e'[x/p]` is well-typed.
We use this when processing lambdas:
to traverse `fun (x : α) => b`,
we add `x : α[x/p]` to the local context
and continue traversing `b`.
`x : α[x/p] ⊢ b` may be ill-typed,
but the output `x : α[x/p] ⊢ b[x/p]` is well-typed. -/
partial def visitAndCast (e : Expr) (et? : Option Expr) : M Expr := do
  let e' ← visit e et?
  let some et := et? | return e'
  let te' ← inferType e'
  -- Increase transparency to avoid inserting unnecessary casts
  -- between definientia and definienda (δ reductions).
  if ← withAtLeastTransparency .default <| withNewMCtxDepth <| isDefEq te' et then
    return e'
  trace[depRewrite.cast] "casting{indentExpr e'}\nto expected type{indentExpr et}"
  let ctx ← read
  checkCastAllowed e' te' ctx.cfg.castMode
  -- Try casting from the inferred type,
  -- and if that doesn't work,
  -- casting to the expected type.
  if let some e'' ← castBack? e' te' ctx.x ctx.h then
    let te'' ← inferType e''
    if ← withAtLeastTransparency .default <| withNewMCtxDepth <| isDefEq te'' et then
      trace[depRewrite.cast] "from inferred type (x ↦ p):{indentExpr e'}"
      return e''
  let motive ← mkLambdaFVars #[ctx.x, ctx.h] et
  let e' ← mkEqRec motive e' ctx.h
  trace[depRewrite.cast] "to expected type (p ↦ x):{indentExpr e'}"
  return e'

/-- Like `visitAndCast`, but does not insert casts at the top level.
The expected types of certain subterms are computed from `et?`. -/
-- TODO(WN): further speedup might come from returning whether anything
-- was rewritten inside a `visit`,
-- and then skipping the type correctness check if it wasn't.
partial def visit (e : Expr) (et? : Option Expr) : M Expr :=
  withTraceNode `depRewrite.visit (fun
    | .ok e' => pure m!"{e} => {e'} (et: {et?})"
    | .error _ => pure m!"{e} => 💥️") do
  checkCache { val := e : ExprStructEq } fun _ => Meta.withIncRecDepth do
  let ctx ← read
  if e.hasLooseBVars then
    throwError "internal error: forgot to instantiate"
  if ← isProof e then
    /- Recall that `e` might be type-incorrect.
    We assume it will become type-correct after traversal,
    but by proof irrelevance we can skip traversing proofs,
    instead casting them at the top-level.
    However, in this case we need to fix `e`
    by applying the delayed substitution `subst`
    which replaces bound variables with type-correct terms.
    We do not do this eagerly when introducing binders
    because it can introduce more casts than necessary. -/
    -- QUESTION(WN): in `.proofs` cast mode,
    -- can this observably 'leak' non-proof casts in the type of `ctx.subst.apply e`?
    return ctx.subst.apply e
  if e.toHeadIndex == ctx.pHeadIdx && e.headNumArgs == ctx.pNumArgs then
    -- We save the metavariable context here,
    -- so that it can be rolled back unless `occs.contains i`.
    let mctx ← getMCtx
    if ← isDefEq e ctx.p then
      let i ← modifyGet fun i => (i, i+1)
      if ctx.cfg.occs.contains i then
        return ctx.x
      else
        -- Revert the metavariable context,
        -- so that other matches are still possible.
        setMCtx mctx
  match e with
  | .mdata d b => return .mdata d (← visitAndCast b et?)
  | .app f a =>
    let fup ← visit f none
    let tfup ← inferType fup
    withAtLeastTransparency .default <| forallBoundedTelescope tfup (some 1) fun xs _ => do
      let #[r] := xs | throwFunctionExpected fup
      let tr ← inferType r
      let aup ← visitAndCast a tr
      return .app fup aup
  | .proj n i b =>
    let bup ← visit b none
    let tbup ← inferType bup
    if !tbup.isAppOf n then
      throwError m!"projection type mismatch{indentExpr <| .proj n i bup}"
    return .proj n i bup
  | .letE n t v b bi =>
    let tup ← visit t none
    let vup ← visitAndCast v tup
    withLetDecl n tup vup fun r => withSubst? r tup do
      let bup ← visitAndCast (b.instantiate1 r) et?
      return .letE n tup vup (bup.abstract #[r]) bi
  | .lam n t b bi =>
    let tup ← visit t none
    withLocalDecl n bi tup fun r => withSubst? r tup do
      -- TODO(WN): there should be some way to propagate the expected type here,
      -- but it is not easy to do correctly (see `lam (as argument)` tests).
      let bup ← visit (b.instantiate1 r) none
      return .lam n tup (bup.abstract #[r]) bi
  | .forallE n t b bi =>
    let tup ← visit t none
    withLocalDecl n bi tup fun r => withSubst? r tup do
      let bup ← visit (b.instantiate1 r) none
      return .forallE n tup (bup.abstract #[r]) bi
  | _ => return e

end

def dabstract (e : Expr) (p : Expr) (cfg : DepRewrite.Config) : MetaM Expr := do
  let e ← instantiateMVars e
  let tp ← inferType p
  withTraceNode `depRewrite (fun
    -- Message shows unified pattern (without mvars) b/c it is constructed after the body runs
    | .ok motive => pure m!"{e} =[x/{p}]=> {motive}"
    | .error (err : Lean.Exception) => pure m!"{e} =[x/{p}]=> 💥️{indentD err.toMessageData}") do
  withLocalDeclD `x tp fun x => do
  withLocalDeclD `h (← mkEq p x) fun h => do
    let e' ← visit e none |>.run { cfg, p, x, h } |>.run |>.run' 1
    mkLambdaFVars #[x, h] e'

def _root_.Lean.MVarId.depRewrite (mvarId : MVarId) (e : Expr) (heq : Expr)
    (symm : Bool := false) (config := { : DepRewrite.Config }) : MetaM RewriteResult :=
  mvarId.withContext do
    mvarId.checkNotAssigned `depRewrite
    let heqIn := heq
    let heqType ← instantiateMVars (← inferType heq)
    let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
    let heq := mkAppN heq newMVars
    let cont (heq heqType : Expr) : MetaM RewriteResult := do
      match (← matchEq? heqType) with
      | none => throwTacticEx `depRewrite mvarId
                  m!"equality or iff proof expected{indentExpr heqType}"
      | some (α, lhs, rhs) =>
        let cont (heq lhs rhs : Expr) : MetaM RewriteResult := do
          if lhs.getAppFn.isMVar then
            throwTacticEx `depRewrite mvarId
              m!"pattern is a metavariable{indentExpr lhs}\nfrom equation{indentExpr heqType}"
          let e ← instantiateMVars e
          let eAbst ← withConfig (fun oldConfig => { config, oldConfig with }) <|
            dabstract e lhs config
          let .lam _ _ (.lam _ _ eBody _) _ := eAbst |
            throwTacticEx `depRewrite mvarId
              m!"internal error: output{indentExpr eAbst}\nof dabstract is not a lambda"
          if !eBody.hasLooseBVars then
            throwTacticEx `depRewrite mvarId
              m!"did not find instance of the pattern in the target expression{indentExpr lhs}"
          try
            check eAbst
          catch e : Lean.Exception =>
            throwTacticEx `depRewrite mvarId <|
              m!"motive{indentExpr eAbst}\nis not type correct:{indentD e.toMessageData}\n" ++
              m!"unlike with rw/rewrite, this error should NOT happen in rw!/rewrite!:\n" ++
              m!"please report it on the Lean Zulip"
          -- construct rewrite proof
          let eType ← inferType e
          -- `eNew ≡ eAbst rhs heq`
          let eNew := eBody.instantiateRev #[rhs, heq]
          -- Has the type of the term that we rewrote changed?
          -- (Checking whether the motive depends on `x` is overly conservative:
          -- when rewriting by a definitional equality,
          -- the motive may use `x` while the type remains the same.)
          let isDep ← withNewMCtxDepth <| not <$> (inferType eNew >>= isDefEq eType)
          let u1 ← getLevel α
          let u2 ← getLevel eType
          -- `eqPrf : eAbst lhs rfl = eNew`
          -- `eAbst lhs rfl ≡ e`
          let (eNew, eqPrf) ← do
            if isDep then
              lambdaBoundedTelescope eAbst 2 fun xs eBody => do
                let #[x, h] := xs | throwError
                  "internal error: expected 2 arguments in{indentExpr eAbst}"
                let eBodyTp ← inferType eBody
                checkCastAllowed eBody eBodyTp config.castMode
                let some eBody ← castBack? eBody eBodyTp x h | throwError
                  "internal error: body{indentExpr eBody}\nshould mention '{x}' or '{h}'"
                let motive ← mkLambdaFVars xs eBodyTp
                pure (
                  eBody.replaceFVars #[x, h] #[rhs, heq],
                  mkApp6 (.const ``dcongrArg [u1, u2]) α lhs rhs motive heq eAbst)
            else
              pure (eNew, mkApp6 (.const ``nddcongrArg [u1, u2]) α lhs rhs eType heq eAbst)
          postprocessAppMVars `depRewrite mvarId newMVars binderInfos
            (synthAssignedInstances := !tactic.skipAssignedInstances.get (← getOptions))
          let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM fun mvarId =>
            not <$> mvarId.isAssigned
          let otherMVarIds ← getMVarsNoDelayed heqIn
          let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
          let newMVarIds := newMVarIds ++ otherMVarIds
          pure { eNew := eNew, eqProof := eqPrf, mvarIds := newMVarIds.toList }
        match symm with
        | false => cont heq lhs rhs
        | true  => do
          cont (← mkEqSymm heq) rhs lhs
    match heqType.iff? with
    | some (lhs, rhs) =>
      let heqType ← mkEq lhs rhs
      let heq := mkApp3 (mkConst ``propext) lhs rhs heq
      cont heq heqType
    | none => match heqType.heq? with
      | some (α, lhs, β, rhs) =>
        let heq ← mkAppOptM (if symm then ``heqR else ``heqL) #[α, β, lhs, rhs, heq]
        cont heq (← inferType heq)
      | none =>
        cont heq heqType

/--
The configuration used by `rw!` to call `dsimp`.
This configuration uses only iota reduction (recursor application) to simplify terms.
-/
private def depRwContext : MetaM Simp.Context :=
  Simp.mkContext
    {Lean.Meta.Simp.neutralConfig with
     etaStruct := .none
     iota := true
     failIfUnchanged := false}

open Parser Elab Tactic

/--
`rewrite!` is like `rewrite`,
but can also insert casts to adjust types that depend on the term being rewritten.
It is available as an ordinary tactic and a `conv` tactic.

The sort of casts that are inserted is controlled by the `castMode` configuration option.
By default, only proof terms are casted;
by proof irrelevance, this adds no observable complexity.

With `rewrite! (castMode := .all)`, casts are inserted whenever necessary.
This means that the 'motive is not type correct' error never occurs,
at the expense of creating potentially complicated terms.
-/
syntax (name := depRewriteSeq) "rewrite!" optConfig rwRuleSeq (location)? : tactic

/--
`rw!` is like `rewrite!`, but also calls `dsimp` to simplify the result after every substitution.
It is available as an ordinary tactic and a `conv` tactic.
-/
syntax (name := depRwSeq) "rw!" optConfig rwRuleSeq (location)? : tactic

def depRewriteTarget (stx : Syntax) (symm : Bool) (config : DepRewrite.Config := {}) :
    TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getMainTarget) e symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

def depRewriteLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId)
    (config : DepRewrite.Config := {}) : TacticM Unit := withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues #2711 and #2727.
  let rwResult ← Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let localDecl ← fvarId.getDecl
    (← getMainGoal).depRewrite localDecl.type e symm (config := config)
  let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
  replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

declare_config_elab elabDepRewriteConfig Config

@[tactic depRewriteSeq] def evalDepRewriteSeq : Tactic := fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRewriteLocalDecl term symm · cfg)
      (depRewriteTarget term symm cfg)
      (throwTacticEx `depRewrite · "did not find instance of the pattern in the current goal")

@[tactic depRwSeq] def evalDepRwSeq : Tactic := fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRewriteLocalDecl term symm · cfg)
      (depRewriteTarget term symm cfg)
      (throwTacticEx `depRewrite · "did not find instance of the pattern in the current goal")
    -- copied from Lean.Elab.Tactic.evalDSimp
    dsimpLocation (← depRwContext) #[] loc

namespace Conv
open Conv

@[inherit_doc depRewriteSeq]
syntax (name := depRewrite) "rewrite!" optConfig rwRuleSeq (location)? : conv

@[inherit_doc depRwSeq]
syntax (name := depRw) "rw!" optConfig rwRuleSeq (location)? : conv

def depRewriteTarget (stx : Syntax) (symm : Bool) (config : DepRewrite.Config := {}) :
    TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ←  (← getMainGoal).depRewrite (← getLhs) e symm (config := config)
    updateLhs r.eNew r.eqProof
    replaceMainGoal ((← getMainGoal) :: r.mvarIds)

def depRwTarget (stx : Syntax) (symm : Bool) (config : DepRewrite.Config := {}) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ←  (← getMainGoal).depRewrite (← getLhs) e symm (config := config)
    updateLhs r.eNew r.eqProof
    -- copied from Lean.Elab.Conv.Simp
    changeLhs (← dsimp (← getLhs) (← depRwContext)).1
    replaceMainGoal ((← getMainGoal) :: r.mvarIds)

def depRwLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId)
    (config : DepRewrite.Config := {}) : TacticM Unit := withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues #2711 and #2727.
  let rwResult ← Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let localDecl ← fvarId.getDecl
    (← getMainGoal).depRewrite localDecl.type e symm (config := config)
  let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
  let dsimpResult := (← dsimp rwResult.eNew (← depRwContext)).1
  let replaceResult ← replaceResult.mvarId.changeLocalDecl replaceResult.fvarId dsimpResult
  replaceMainGoal (replaceResult :: rwResult.mvarIds)

@[tactic depRewrite]
def evalDepRewriteSeq : Tactic := fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (DepRewrite.depRewriteLocalDecl term symm · cfg)
      (depRewriteTarget term symm cfg)
      (throwTacticEx `depRewrite · "did not find instance of the pattern in the current goal")

@[tactic depRw]
def evalDepRwSeq : Tactic := fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRwLocalDecl term symm · cfg)
      (depRwTarget term symm cfg)
      (throwTacticEx `depRewrite · "did not find instance of the pattern in the current goal")
    -- Note: in this version of the tactic, `dsimp` is done inside `withLocation`.
    -- This is done so that `dsimp` will not close the goal automatically.

end Conv
end Mathlib.Tactic.DepRewrite
