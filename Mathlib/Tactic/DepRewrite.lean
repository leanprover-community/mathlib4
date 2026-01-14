/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Wojciech Nawrocki
-/
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Conv.Basic
import Lean.Elab.Tactic.Rewrite
import Mathlib.Init

/-! ## Dependent rewrite tactic -/

namespace Mathlib.Tactic.DepRewrite
open Lean Meta

theorem dcongrArg.{u, v} {α : Sort u} {a a' : α} {β : (a' : α) → a = a' → Sort v}
    (h : a = a') (f : (a' : α) → (h : a = a') → β a' h) :
    f a rfl = Eq.rec (motive := fun x h' ↦ β x (h.trans h')) (f a' h) h.symm := by
  cases h; rfl

theorem nddcongrArg.{u, v} {α : Sort u} {a a' : α} {β : Sort v}
    (h : a = a') (f : (a' : α) → (h : a = a') → β) :
    f a rfl = f a' h := by
  cases h; rfl

theorem heqL.{u} {α β : Sort u} {a : α} {b : β} (h : HEq a b) :
    a = cast (type_eq_of_heq h).symm b := by
  cases h; rfl

theorem heqR.{u} {α β : Sort u} {a : α} {b : β} (h : HEq a b) :
    cast (type_eq_of_heq h) a = b := by
  cases h; rfl

private def traceCls : Name := `Tactic.depRewrite
private def traceClsVisit : Name := `Tactic.depRewrite.visit
private def traceClsCast : Name := `Tactic.depRewrite.cast

initialize
  registerTraceClass traceCls
  registerTraceClass traceClsVisit
  registerTraceClass traceClsCast

/-- See `Config.castMode`. -/
inductive CastMode where
  /-- Only insert casts on proofs.

  In this mode, it is *not* permitted to cast subterms of proofs that are not themselves proofs. -/
  -- TODO: should we relax this restriction and switch `castMode` when visiting a proof?
  | proofs
  /- TODO: `proofs` plus "good" user-defined casts such as `Fin.cast`.
  See https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/dependent.20rewrite.20tactic/near/497185687 -/
  -- | userDef
  /-- Insert casts whenever necessary. -/
  | all
deriving BEq

instance : ToString CastMode := ⟨fun
  | .proofs => "proofs"
  | .all => "all"⟩

/-- Embedding of `CastMode` into naturals. -/
def CastMode.toNat : CastMode → Nat
  | .proofs => 0
  | .all => 1

instance : LE CastMode where
  le a b := a.toNat ≤ b.toNat

instance : DecidableLE CastMode :=
  fun a b => inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

/-- Configures the behavior of the `rewrite!` and `rw!` tactics. -/
structure Config where
  /-- Which transparency level to use when unifying the rewrite rule's LHS
  against subterms of the term being rewritten. -/
  transparency : TransparencyMode := .reducible
  /-- Which occurrences to rewrite. -/
  occs : Occurrences := .all
  /-- The cast mode specifies when `rw!` is permitted to insert casts
  in order to correct subterms that become type-incorect
  as a result of rewriting.

  For example, given `P : Nat → Prop`, `f : (n : Nat) → P n → Nat` and `h : P n₀`,
  rewriting `f n₀ h` by `eq : n₀ = n₁` produces `f n₁ h`,
  where `h` does not typecheck at `P n₁`.
  The tactic will cast `h` to `eq ▸ h : P n₁` iff `.proofs ≤ castMode`. -/
  castMode : CastMode := .proofs

/-- `ReaderT` context for `M`. -/
structure Context where
  /-- Configuration. -/
  cfg : DepRewrite.Config
  /-- The pattern to generalize over. -/
  p : Expr
  /-- The free variable to substitute for `p`. -/
  x : Expr
  /-- A proof of `p = x`. Must be an fvar. -/
  h : Expr
  /-- The list of *value-less* binders (`cdecl`s and nondependent `ldecl`s)
  that we have introduced.
  Together with each binder, we store its type abstracted over `x` and `h`,
  and with all occurrences of previous entries in `Δ`
  casted along the abstracting equation.

  E.g., if the local context is `a : T, b : U`,
  we store `(a, Ma)` where `Ma := fun (x' : α) (h' : x = x') => T[x'/x, h'/h]`
  and `(b, fun (x' : α) (h' : x = x') => U[x'/x, h'/h, (Eq.rec (motive := Ma) a h)/a])`
  See the docstring on `visitAndCast`. -/
  Δ : Array (FVarId × Expr)
  /-- The set of all *dependent* `ldecl`s that we have introduced. -/
  δ : Std.HashSet FVarId
  -- TODO: use `@[computed_field]`s below when `structure` supports that
  /-- Cached `p.toHeadIndex`. -/
  pHeadIdx : HeadIndex := p.toHeadIndex
  /-- Cached `p.toNumArgs`. -/
  pNumArgs : Nat := p.headNumArgs

/-- We use a cache entry iff the upcoming traversal would abstract exactly the same occurrences
as the cached traversal. -/
def canUseCache (cacheOcc dCacheOcc currOcc : Nat) : Occurrences → Bool
  | .all => true
  | .pos l | .neg l => Id.run do
    let mut prevOccs := #[]
    let mut currOccs := #[]
    for p in l.toArray.qsort do
      if cacheOcc ≤ p && p < cacheOcc + dCacheOcc then
        prevOccs := prevOccs.push (p - cacheOcc)
      if currOcc ≤ p && p < currOcc + dCacheOcc then
        currOccs := currOccs.push (p - currOcc)
    return prevOccs == currOccs

/-- Monad for computing `dabstract`.

The `Nat` state tracks which occurrence of the pattern we are about to see, 1-indexed
(so the initial value is `1`).

The cache stores results of `visit` together with
- the `Nat` state before the cached call; and
- the difference in the state resulting from the call.
We store these because even if the cache hits,
we must update the state as if the call had been made.
Storing the difference suffices because the state increases monotonically.
See also `canUseCache`. -/
abbrev M := ReaderT Context <| MonadCacheT ExprStructEq (Expr × Nat × Nat) <|
  StateRefT Nat MetaM

/-- Check that casting `e : t` is allowed in the current mode.
(We don't need to know what type `e` is cast to:
we only check the sort of `t`, and it cannot change.) -/
def checkCastAllowed (e t : Expr) (castMode : CastMode) : MetaM Unit := do
  let throwMismatch : Unit → MetaM Unit := fun _ => do
    throwError m!"\
      Will not cast{indentExpr e}\nin cast mode '{castMode}'. \
      If inserting more casts is acceptable, use `rw! (castMode := .all)`."
  if castMode == .proofs then
    if !(← isProp t) then
      throwMismatch ()

/-- In `e`, inline the values of those `ldecl`s that appear in `fvars`. -/
def zetaDelta (e : Expr) (fvars : Std.HashSet FVarId) : MetaM Expr :=
  let unfold? (fvarId : FVarId) : MetaM (Option Expr) := do
    if fvars.contains fvarId then
      fvarId.getValue?
    else
      return none
  let pre (e : Expr) : MetaM TransformStep := do
    let .fvar fvarId := e | return .continue
    let some val ← unfold? fvarId | return .continue
    return .visit val
  transform e (pre := pre)

/-- If `e : te` is a term whose type mentions `x`, `h` (the generalization variables)
or entries in `Δ`/`δ`,
return `h.symm ▸ e : te[p/x, rfl/h, …]`.
Otherwise return `none`. -/
def castBack? (e te x h : Expr) (Δ : Array (FVarId × Expr)) (δ : Std.HashSet FVarId) :
    MetaM (Option Expr) := do
  if !te.hasAnyFVar (fun f => f == x.fvarId! || f == h.fvarId! ||
      Δ.any (·.1 == f) || δ.contains f) then
    return none
  let e' ← mkEqRec (← motive) e (← mkEqSymm h)
  trace[Tactic.depRewrite.cast] "casting (x ↦ p):{indentExpr e'}"
  return some e'
where
  /-- Compute the motive that casts `e` back to `te[p/x, rfl/h, …]`. -/
  motive : MetaM Expr := do
    withLocalDeclD `x' (← inferType x) fun x' => do
    withLocalDeclD `h' (← mkEq x x') fun h' => do
      /- The motive computation below operates syntactically, i.e.,
      it looks for the fvars `x` and `h`.
      This breaks in the presence of `let`-binders:
      if we traverse into `b` in `let a := n; b` with `n` as the pattern,
      we will have `a := x` in the local context.
      If the type-correctness of `b` depends on the defeq `a ≡ n`,
      because `b` does not depend on `x` syntactically,
      a `replaceFVars` substitution will not suffice to fix `b`.
      Thus we unfold the necessary dependent `ldecl`s when computing motives.
      If their values depend on `x`,
      this will be visible in the syntactic form of `te`. -/
      let te ← zetaDelta te δ
      let mut fs := #[x, h]
      let mut es := #[x', ← mkEqTrans h h']
      for (f, M) in Δ do
        fs := fs.push (.fvar f)
        es := es.push (← mkEqRec M (.fvar f) h')
      let te := te.replaceFVars fs es
      mkLambdaFVars #[x', h'] te

/-- Cast `e : te[p/x, rfl/h, ...]` to `h ▸ e : te`. -/
def castFwd (e te p x h : Expr) (Δ : Array (FVarId × Expr)) (δ : Std.HashSet FVarId) :
    MetaM Expr := do
  if !te.hasAnyFVar (fun f => f == x.fvarId! || f == h.fvarId! ||
      Δ.any (·.1 == f) || δ.contains f) then
    return e
  let motive ← do
    withLocalDeclD `x' (← inferType x) fun x' => do
    withLocalDeclD `h' (← mkEq p x') fun h' => do
      let te ← zetaDelta te δ
      let mut fs := #[x, h]
      let mut es := #[x', h']
      for (f, M) in Δ do
        fs := fs.push (.fvar f)
        es := es.push (← mkEqRec M (.fvar f) (← mkEqTrans (← mkEqSymm h) h'))
      let te := te.replaceFVars fs es
      mkLambdaFVars #[x', h'] te
  let e' ← mkEqRec motive e h
  trace[Tactic.depRewrite.cast] "casting (p ↦ x):{indentExpr e'}"
  return e'

mutual

/-- Given `e`, return `e'` where `e'` has had
- the occurrences of `p` in `ctx.cfg.occs` replaced by `x`; and
- subterms cast as appropriate in order to make `e'` type-correct.

If `et?` is not `none`, the output is guaranteed to have type (defeq to) `et?`.

We do _not_ assume that `e` is well-typed.
We use this when processing binders:
to traverse `∀ (x : α), β`,
we obtain `α' ← visit α`,
add `x : α'` to the local context
and continue traversing `β`.
Although `x : α' ⊢ β` may not hold,
the output `β'` should have `x : α' ⊢ β'` (otherwise we have a bug).

To achieve this, we maintain the invariant
that all entries in the local context that we have introduced
can be translated back to their original (pre-`visit`) types
using the motive computed by `castBack?.motive`.
(But we have not attempted to prove this.) -/
partial def visitAndCast (e : Expr) (et? : Option Expr) : M Expr := do
  let e' ← visit e et?
  let some et := et? | return e'
  let te' ← inferType e'
  -- Increase transparency to avoid inserting unnecessary casts
  -- between definientia and definienda (δ reductions).
  if ← withAtLeastTransparency .default <| withNewMCtxDepth <| isDefEq te' et then
    return e'
  trace[Tactic.depRewrite.cast] "casting{indentExpr e'}\nto expected type{indentExpr et}"
  let ctx ← read
  checkCastAllowed e' te' ctx.cfg.castMode

  /- Try casting from the inferred type (x ↦ p),
  and to the expected type (p ↦ x).
  In certain cases we need to cast in both directions (see `bool_dep_test`). -/
  match ← castBack? e' te' ctx.x ctx.h ctx.Δ ctx.δ with
  | some e'' =>
    let te'' ← inferType e''
    if ← withAtLeastTransparency .default <| withNewMCtxDepth <| isDefEq te'' et then
      return e''

    castFwd e'' et ctx.p ctx.x ctx.h ctx.Δ ctx.δ
  | none =>
    castFwd e' et ctx.p ctx.x ctx.h ctx.Δ ctx.δ

/-- Like `visitAndCast`, but does not insert casts at the top level.
The expected types of certain subterms are computed from `et?`. -/
partial def visit (e : Expr) (et? : Option Expr) : M Expr :=
  withTraceNode traceClsVisit (fun
    | .ok e' => pure m!"{e} => {e'} (et: {et?})"
    | .error _ => pure m!"{e} => 💥️") <| Meta.withIncRecDepth do
  let ctx ← read
  if let some (eup, cacheOcc, dCacheOcc) ← MonadCache.findCached? { val := e : ExprStructEq } then
    if canUseCache cacheOcc dCacheOcc (← get) ctx.cfg.occs then
      modify (· + dCacheOcc)
      return eup
  let initOccs ← get
  let eup ← visitInner e et?
  MonadCache.cache { val := e : ExprStructEq } (eup, initOccs, (← get) - initOccs)
  return eup

-- TODO(WN): further speedup might come from returning whether anything
-- was rewritten inside a `visit`,
-- and then skipping the type correctness check if it wasn't.
/-- See `visit`. -/
partial def visitInner (e : Expr) (et? : Option Expr) : M Expr := do
  let ctx ← read
  if e.hasLooseBVars then
    throwError "internal error: forgot to instantiate"
  if e.toHeadIndex == ctx.pHeadIdx && e.headNumArgs == ctx.pNumArgs then
    -- We save the metavariable context here,
    -- so that it can be rolled back unless `occs.contains i`.
    let mctx ← getMCtx
    -- Note that the pattern `ctx.p` is created in the outer lctx,
    -- so bvars from the visited term will not be unified into the pattern.
    if ← withTransparency ctx.cfg.transparency <| isDefEq e ctx.p then
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
    let (fup, tr) ← do
      let fup ← visit f none
      let tfup ← inferType fup
      withAtLeastTransparency .default <| forallBoundedTelescope tfup (some 1) fun xs _ => do
        match xs with
        | #[r] => return (fup, ← inferType r)
        | _ =>
          -- The term in function position was rewritten to a non-function,
          -- so cast it back to one.
          let some fup' ← castBack? fup tfup ctx.x ctx.h ctx.Δ ctx.δ
            | throwError "internal error: unexpected castBack failure on{indentExpr fup}"
          let tfup' ← inferType fup'
          withAtLeastTransparency .default <| forallBoundedTelescope tfup' (some 1) fun xs _ => do
            let #[r] := xs | throwError "internal error: function expected, got{indentExpr fup'}"
            return (fup', ← inferType r)

    let aup ← visitAndCast a tr
    return .app fup aup
  | .proj n i b =>
    let bup ← visit b none
    let tbup ← inferType bup
    if (← withAtLeastTransparency .default <| whnf tbup).isAppOf n then
      return .proj n i bup

    /- Otherwise the term in structure position was rewritten to have a different type,
    so cast it back to the original type.
    (While the other type may itself be a structure type,
    we can't assume that its projections are the same as those of the original.) -/
    let some bup' ← castBack? bup tbup ctx.x ctx.h ctx.Δ ctx.δ
      | throwError "internal error: could not cast back in{indentExpr bup}"
    return .proj n i bup'
  | .letE n t v b nondep =>
    let tup ← visit t none
    let vup ← visitAndCast v tup
    if nondep || !vup.hasAnyFVar (fun f => f == ctx.x.fvarId! || f == ctx.h.fvarId! ||
        ctx.Δ.any (·.1 == f) || ctx.δ.contains f) then
      return ← withLetDecl n tup vup (nondep := nondep) fun r => do
        let motive ← castBack?.motive tup ctx.x ctx.h ctx.Δ ctx.δ
        let bup ← withReader (fun ctx => { ctx with Δ := ctx.Δ.push (r.fvarId!, motive) })
          (visitAndCast (b.instantiate1 r) et?)
        return .letE n tup vup (bup.abstract #[r]) nondep

    withLetDecl n tup vup (nondep := nondep) fun r => do
      let bup ← withReader (fun ctx => { ctx with δ := ctx.δ.insert r.fvarId! })
        (visitAndCast (b.instantiate1 r) et?)
      return .letE n tup vup (bup.abstract #[r]) nondep
  | .lam n t b bi =>
    let tup ← visit t none
    withLocalDecl n bi tup fun r => do
      -- NOTE(WN): there should be some way to propagate the expected type here,
      -- but it is not easy to do correctly (see `lam (as argument)` tests).
      let motive ← castBack?.motive tup ctx.x ctx.h ctx.Δ ctx.δ
      let bup ← withReader (fun ctx => { ctx with Δ := ctx.Δ.push (r.fvarId!, motive) })
        (visit (b.instantiate1 r) none)
      return .lam n tup (bup.abstract #[r]) bi
  | .forallE n t b bi =>
    let tup ← visit t none
    withLocalDecl n bi tup fun r => do
      let motive ← castBack?.motive tup ctx.x ctx.h ctx.Δ ctx.δ
      let bup ← withReader (fun ctx => { ctx with Δ := ctx.Δ.push (r.fvarId!, motive) })
        (visit (b.instantiate1 r) none)
      return .forallE n tup (bup.abstract #[r]) bi
  | _ => return e

end

/-- Analogue of `kabstract` with support for inserting casts. -/
def dabstract (e : Expr) (p : Expr) (cfg : DepRewrite.Config) : MetaM Expr := do
  let e ← instantiateMVars e
  let tp ← inferType p
  withTraceNode traceCls (fun
    -- Message shows unified pattern (without mvars) b/c it is constructed after the body runs
    | .ok motive => pure m!"{e} =[x/{p}]=> {motive}"
    | .error (err : Lean.Exception) => pure m!"{e} =[x/{p}]=> 💥️{indentD err.toMessageData}") do
  withLocalDeclD `x tp fun x => do
  withLocalDeclD `h (← mkEq p x) fun h => do
    let e' ← visit e none |>.run { cfg, p, x, h, Δ := ∅, δ := ∅ } |>.run.run' 1
    mkLambdaFVars #[x, h] e'

/-- Analogue of `Lean.MVarId.rewrite` with support for inserting casts. -/
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
            throwTacticEx `depRewrite mvarId <| m!"\
              motive{indentExpr eAbst}\nis not type correct:{indentD e.toMessageData}\n\
              unlike with rw/rewrite, this error should NOT happen in rw!/rewrite!: \
              please report it on the Lean Zulip"
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
                let some eBody ← castBack? eBody eBodyTp x h ∅ ∅ | throwError
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
but can also insert casts to adjust types that depend on the LHS of a rewrite.
It is available as an ordinary tactic and a `conv` tactic.

The sort of casts that are inserted is controlled by the `castMode` configuration option.
By default, only proof terms are casted;
by proof irrelevance, this adds no observable complexity.

With `rewrite! +letAbs (castMode := .all)`, casts are inserted whenever necessary.
This means that the 'motive is not type correct' error never occurs,
at the expense of creating potentially complicated terms.
-/
syntax (name := depRewriteSeq) "rewrite!" optConfig rwRuleSeq (location)? : tactic

/--
`rw!` is like `rewrite!`, but also calls `dsimp` to simplify the result after every substitution.
It is available as an ordinary tactic and a `conv` tactic.
-/
syntax (name := depRwSeq) "rw!" optConfig rwRuleSeq (location)? : tactic

/-- Apply `rewrite!` to the goal. -/
def depRewriteTarget (stx : Syntax) (symm : Bool) (config : DepRewrite.Config := {}) :
    TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).depRewrite (← getMainTarget) e symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

/-- Apply `rewrite!` to a local declaration. -/
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

/-- Elaborate `DepRewrite.Config`. -/
declare_config_elab elabDepRewriteConfig Config

@[tactic depRewriteSeq, inherit_doc depRewriteSeq]
def evalDepRewriteSeq : Tactic := fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (depRewriteLocalDecl term symm · cfg)
      (depRewriteTarget term symm cfg)
      (throwTacticEx `depRewrite · "did not find instance of the pattern in the current goal")

@[tactic depRwSeq, inherit_doc depRwSeq]
def evalDepRwSeq : Tactic := fun stx => do
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

/-- Apply `rewrite!` to the goal. -/
def depRewriteTarget (stx : Syntax) (symm : Bool) (config : DepRewrite.Config := {}) :
    TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ←  (← getMainGoal).depRewrite (← getLhs) e symm (config := config)
    updateLhs r.eNew r.eqProof
    replaceMainGoal ((← getMainGoal) :: r.mvarIds)

/-- Apply `rw!` to the goal. -/
def depRwTarget (stx : Syntax) (symm : Bool) (config : DepRewrite.Config := {}) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ←  (← getMainGoal).depRewrite (← getLhs) e symm (config := config)
    updateLhs r.eNew r.eqProof
    -- copied from Lean.Elab.Conv.Simp
    changeLhs (← dsimp (← getLhs) (← depRwContext)).1
    replaceMainGoal ((← getMainGoal) :: r.mvarIds)

/-- Apply `rw!` to a local declaration. -/
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

@[tactic depRewrite, inherit_doc depRewriteSeq]
def evalDepRewriteSeq : Tactic := fun stx => do
  let cfg ← elabDepRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (DepRewrite.depRewriteLocalDecl term symm · cfg)
      (depRewriteTarget term symm cfg)
      (throwTacticEx `depRewrite · "did not find instance of the pattern in the current goal")

@[tactic depRw, inherit_doc depRwSeq]
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
