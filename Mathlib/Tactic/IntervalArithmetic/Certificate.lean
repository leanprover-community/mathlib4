module

public meta import Mathlib.Tactic.IntervalArithmetic.Environment

set_option linter.style.header false

public meta section

namespace IntervalArithmetic

open Lean Expr Meta Elab Command Tactic

section IntervalM

/-- Custom settings for `IntervalOps` -/
structure OpConfig where
  /-- If `ignore` then do not match on this operation. -/
  ignore : Bool
  /-- If `approxParam = some n` then use `n` as approximation parameter for this operation. -/
  approxParam : Option Expr

/-- A (static) context for the `IntervalM` monad. -/
structure Context where
  /-- The `IntervalArithmeticDecl` name. -/
  declName : Name
  /-- The expression for the type of interval. -/
  intervalTypeExpr : Expr
  /-- The expression for the target type. -/
  targetTypeExpr : Expr
  /-- The expression for the embedding -/
  embeddingExpr : Expr
  /-- The expression for the strict mono theorem -/
  strictMonoExpr : Expr
  /-- Global approximation parameter. -/
  approxParam : ℕ
  /-- Custom approximation parameters. -/
  opsConfig : NameMap OpConfig

/-- Make a `Context` for the `IntervalM` monad -/
def mkContext (declName : Name) (approxParam : ℕ)
    (opsConfig : NameMap OpConfig) : MetaM Context := do
  let some decl ← getIntervalArithmeticDecl? declName
    | throwError m!"Unknown interval arithmetic declaration `{declName}`."
  return {
    declName := declName
    intervalTypeExpr := ← mkConstWithFreshMVarLevels decl.intervalTypeName,
    targetTypeExpr := ← mkConstWithFreshMVarLevels decl.targetTypeName,
    embeddingExpr := ← mkConstWithFreshMVarLevels decl.embeddingName,
    strictMonoExpr := ← mkConstWithFreshMVarLevels decl.strictMonoName,
    approxParam := approxParam,
    opsConfig := opsConfig
    }

structure IntervalCertificate (α : Type) where
  /- The interval that the expression is verified to be contained in. -/
  interval : Interval α
  /- `interval` as an `Expr`. -/
  intervalExpr : Expr
  /- proof that `e ∈ interval.toSet φ` in the context of the goal. -/
  proof : Expr
  deriving Inhabited

/- A (mutable) state for the `IntervalM` monad. -/
structure State (α : Type) where
  hyps : FVarIdMap (IntervalCertificate α) := {}
  deriving Inhabited

/-- Monad to run interval arithmetic computations in. -/
abbrev IntervalM (α : Type) := ReaderT Context <| StateT (State α) MetaM

end IntervalM

section Certificate

structure CertificateGenerator (α : Type) where
  /- `compExpr` is an expression of the form
    `∀ (approxParam : ℕ) (x₁ : Interval α) ... (xₙ : Interval α), f n x₁ ... xₙ` -/
  compExpr : Expr
  /- `comp` a is "compiled" version of `compExpr` -/
  comp : ℕ → Array (Interval α) → Interval α
  /- `fvars` is the array `#[r₁, ..., rₙ]` of fvarIds that appear in the expression. -/
  fvars : Array FVarId
  /-- `proof` is a proof of:
  `∀ (approxParam : ℕ) (x₁ : Interval α) ... (xₙ : Interval α),`
    `(h₁ : r₁ ∈ x₁.toSet φ) ... (hₙ : rₙ ∈ xₙ.toSet φ) : e ∈ (f n x₁ .. xₙ).toSet φ` -/
  proof : Expr
  deriving Inhabited

def CertificateGenerator.toCertificate {α : Type} (certGen : CertificateGenerator α)
    : IntervalM α (IntervalCertificate α) := do
  let ctx ← read
  let mut xs := #[]
  let mut xExprs := #[]
  let mut hrxs := #[]
  for rId in certGen.fvars do
    let cert := (← get).hyps.get! rId
    xs := xs.push cert.interval
    xExprs := xExprs.push cert.intervalExpr
    hrxs := hrxs.push cert.proof
  let eval_interval := certGen.comp ctx.approxParam xs
  let intervalExpr ←
    instantiateMVars <| mkAppN certGen.compExpr (#[mkNatLit ctx.approxParam] ++ xExprs)
  let proof ←
    instantiateMVars <| mkAppN certGen.proof (#[mkNatLit ctx.approxParam] ++ xExprs ++ hrxs)
  return ⟨eval_interval, intervalExpr, proof⟩

def Interval.toExpr {α : Type} [ToExpr α] (x : Interval α) : IntervalM α Expr := do
  let ctx ← read
  let lb ← match x.lb with
    | none => mkAppOptM ``Option.none #[← mkAppM ``FiniteLowerBound #[ctx.intervalTypeExpr]]
    | some ⟨c, a⟩ =>
        mkAppM ``Option.some #[← mkAppM ``FiniteLowerBound.mk #[ToExpr.toExpr c, ToExpr.toExpr a]]
  let ub ← match x.ub with
    | none => mkAppOptM ``Option.none #[← mkAppM ``FiniteUpperBound #[ctx.intervalTypeExpr]]
    | some ⟨c, a⟩ =>
        mkAppM ``Option.some #[← mkAppM ``FiniteUpperBound.mk #[ToExpr.toExpr c, ToExpr.toExpr a]]
  mkAppM ``Interval.mk #[lb, ub]

private def compile (α : Type) (compExpr : Expr) :
    IntervalM α (ℕ → Array (Interval α) → Interval α) := do
  lambdaTelescope compExpr fun vars body => do
    let IsType := ← mkAppM ``Array #[← mkAppM ``Interval #[(← read).intervalTypeExpr]]
    let approx_param := vars[0]!
    let intervals := vars.extract 1 vars.size
    withLocalDeclD `Is IsType fun Is => do
      let indexed_intervals ← intervals.mapIdxM fun i _ => do
        mkAppM ``getElem! #[Is, mkNatLit i]
      let body' := body.replaceFVars intervals indexed_intervals
      let lambda ← mkLambdaFVars #[approx_param, Is] body'
      -- **TODO** probably just construct this explicitly
      let lambda_type ← inferType lambda
      let compiled ← unsafe (evalExpr (ℕ → Array (Interval α) → Interval α) lambda_type lambda)
      return compiled

partial def _root_.Lean.Expr.toIntervalArithmeticCertificateGeneratorAux
    (α : Type) (hyps : FVarIdMap (Expr × Expr)) (e : Expr) :
    IntervalM α (Expr × Expr × Expr) := do
  let ctx ← read
  if let some rId := e.fvarId? then
    let ⟨x, proof⟩ := hyps.get! rId
    let thm ← mkMemInterval e x (← read).embeddingExpr
    return ⟨x, thm, proof⟩
  else
    let e ← whnfR e
    let some headName := e.getAppFn.constName?
    | throwError m!"`{e}` does not have a constant head"
    let some opNames ← getIntervalOpNames? ctx.declName headName
    | throwError m!"There is no interval operation with head `{headName}` registered for \
        the `{ctx.declName}` interval arithmetic declaration."
    for opName in opNames do
      let mut approxParam := mkNatLit ctx.approxParam
      if let some opConfig := ctx.opsConfig.get? opName then
        if opConfig.ignore then
          continue
        if let some n := opConfig.approxParam then
          approxParam := n
      let some op ← getIntervalOp? ctx.declName opName | unreachable!
      let s ← liftM Lean.Meta.saveState
      let inc ← mkConstWithFreshMVarLevels op.incName
      let (ms, _, conc) ← forallMetaTelescopeReducing (← inferType inc)
      let some (e', x, _) := memIntervaltoSet? (← instantiateMVars conc) | unreachable!
      -- check that `e` matches the lhs of the conclusion of `inc` (and assign non interval
      -- hypothesis metavariables)
      unless ← isDefEq e' e do
        s.restore
        continue
      if let some n := op.approxParam? then
        let n_id := ms[n]!.mvarId!
        n_id.assign approxParam
      for (i, j) in op.hyps do
        let r ← instantiateMVars ms[i]!
        let (_, thm, proof) ← r.toIntervalArithmeticCertificateGeneratorAux α hyps
        let hyp ← instantiateMVars ms[j]!
        if hyp.isMVar then
          let hypId := hyp.mvarId!
          let expected ← instantiateMVars (← hypId.getType)
          unless ← isDefEq expected thm do
            throwError m!"{expected} is not definitionally equal to {thm}"
          hypId.assign proof
      let proof ← instantiateMVars (mkAppN inc ms)
      let thm ← instantiateMVars conc
      if proof.hasMVar then
        throwError m!"{proof} contains a metavariable"
      if thm.hasMVar then
        throwError m!"{thm} contains a metavariable"
      else
        return ⟨x, thm, proof⟩
    throwError "No interval operation with head `{headName}` matched"

def _root_.Lean.Expr.toIntervalArithmeticCertificateGenerator (α : Type) (e : Expr) :
    IntervalM α (CertificateGenerator α) := do
  let ctx ← read
  let r_ids := Lean.collectFVars {} e |>.fvarIds
  withLocalDeclD Name.anonymous (mkConst ``Nat) fun approx_param => do
    let x_t ← mkAppM ``Interval #[ctx.intervalTypeExpr]
    let x_binders := Array.replicate r_ids.size (Name.anonymous, fun _ ↦ pure x_t)
    withLocalDeclsD x_binders fun xs => do
      let hrx_binders := Array.range r_ids.size |>.map fun i ↦
        (Name.anonymous,
          fun _ => do return ← mkMemInterval (mkFVar r_ids[i]!) xs[i]! ctx.embeddingExpr)
      withLocalDeclsD hrx_binders fun hrxs => do
        let mut hyps : FVarIdMap (Expr × Expr) := {}
        for i in [:r_ids.size] do
          hyps := hyps.insert r_ids[i]! (xs[i]!, hrxs[i]!)
        let (interval, _, proof) ← e.toIntervalArithmeticCertificateGeneratorAux α hyps
        let compExpr ← mkLambdaFVars (#[approx_param] ++ xs) interval
        let comp ← compile α compExpr
        let proof ← mkLambdaFVars (#[approx_param] ++ xs ++ hrxs) proof
        return {fvars := r_ids, compExpr := compExpr, comp := comp, proof := proof}

end Certificate

end IntervalArithmetic
