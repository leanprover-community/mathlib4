module

public import Mathlib.Tactic.IntervalArithmetic.Environment

set_option linter.style.header false

public meta section

namespace IntervalArithmetic

open Lean Expr Meta Elab Command

section Certificate

structure Certificate where
  /- `fvars` is the array `#[r₁, ..., rₙ]` of fvarIds that appear in the expression. -/
  fvars : Array FVarId
  /- `comp` is an expression of the form
    `∀ (n : ℕ) (x₁ : Interval α) ... (xₙ : Interval α), f n x₁ ... xₙ` -/
  comp : Expr
  /-- `proof` is a proof of:
  `∀ (n : ℕ) (x₁ : Interval α) ... (xₙ : Interval α),`
    `(h₁ : r₁ ∈ x₁.toSet φ) ... (hₙ : rₙ ∈ xₙ.toSet φ) : e ∈ (f n x₁ .. xₙ).toSet φ` -/
  proof : Expr
  deriving Inhabited

partial def _root_.Lean.Expr.toIntervalArithmeticCertificateAux (decl : IntervalArithmeticDecl)
    (hyps : FVarIdMap (Expr × Expr)) (e φ n : Expr) : MetaM (Expr × Expr) := do
  if let some r_id := e.fvarId? then
    return hyps.get! r_id
  else
    let some ref_name := e.getAppFn.constName?
    | throwError m!"`{e}` does not have a constant head"
    let some op ← getIntervalOp? decl.name ref_name
    | throwError m!"`{ref_name}` is not a supported interval operation"
    let mut xs ← e.getExplicitAppArgs
    let inc ← mkConstWithFreshMVarLevels op.incName
    let (ms, _, conc) ← forallMetaTelescopeReducing (← inferType inc)
    for (i, j) in op.args do
      let (interval, proof) ← xs[i]!.toIntervalArithmeticCertificateAux decl hyps φ n
      xs := xs.set! i interval
      let m ← instantiateMVars ms[j]!
      if m.isMVar then
        let m_id := m.mvarId!
        m_id.assign proof
    let interval ← if op.isApprox then mkAppM op.opName (#[n] ++ xs) else mkAppM op.opName xs
    let thm ← mkMemInterval e interval φ
    unless ← isDefEq conc thm do
      throwError m!"{conc} is not definitionally equal to {thm}"
    let proof ← instantiateMVars (mkAppN inc ms)
    if proof.hasMVar then
      throwError m!"{proof} contains a metavariable"
    else
      return ⟨interval, proof⟩

def _root_.Lean.Expr.toIntervalArithmeticCertificate (decl : IntervalArithmeticDecl) (e : Expr) :
    MetaM Certificate := do
  let α ← mkConstWithFreshMVarLevels decl.intervalType
  let φ ← mkConstWithFreshMVarLevels decl.embedding
  let r_ids := Lean.collectFVars {} e |>.fvarIds
  withLocalDeclD Name.anonymous (.const ``Nat []) fun n => do
    let x_t ← mkAppM ``Interval #[α]
    let x_binders := Array.replicate r_ids.size (Name.anonymous, fun _ ↦ pure x_t)
    withLocalDeclsD x_binders fun xs => do
      let hrx_binders := Array.range r_ids.size |>.map fun i ↦
        (Name.anonymous,
          fun _ => do return ← mkMemInterval (mkFVar r_ids[i]!) xs[i]! φ)
      withLocalDeclsD hrx_binders fun hrxs => do
        let mut hyps : FVarIdMap (Expr × Expr) := {}
        for i in [:r_ids.size] do
          hyps := hyps.insert r_ids[i]! (xs[i]!, hrxs[i]!)
        let (interval, proof) ← e.toIntervalArithmeticCertificateAux decl hyps φ n
        return {
          fvars := r_ids,
          comp := (← mkLambdaFVars (#[n] ++ xs) interval),
          proof := (← mkLambdaFVars (#[n] ++ xs ++ hrxs) proof)
        }

end Certificate

def _root_.Lean.Expr.ineqToIntervalHyp? (decl : IntervalArithmeticDecl) (e n : Expr) :
    MetaM (Option (FVarId × Expr × Expr)) := do
  let α ← mkConstWithFreshMVarLevels decl.intervalType
  let some ⟨ineq, _, r, s⟩ := IntervalArithmetic.ineq? (← inferType e) | return none
  if r.isFVar then
    let cert ← s.toIntervalArithmeticCertificate decl
    if cert.fvars.isEmpty then
      match ineq with
      | .le =>
        let ub := proj ``Interval 1 (app cert.comp n)
        let bot ← mkAppOptM ``Option.none #[some (← mkAppM ``FiniteLowerBound #[α])]
        let x ← mkAppM ``Interval.mk #[bot, ub]
        let h ← mkAppM ``mem_toSet_of_le_mem_toSet #[e, app cert.proof n]
        return some (r.fvarId!, x, h)
      | .lt =>
        let ub ← mkAppM ``UpperBound.open #[proj ``Interval 1 (app cert.comp n)]
        let bot ← mkAppOptM ``Option.none #[some (← mkAppM ``FiniteLowerBound #[α])]
        let x ← mkAppM ``Interval.mk #[bot, ub]
        let h ← mkAppM ``mem_toSet_of_lt_mem_toSet #[e, app cert.proof n]
        return some (r.fvarId!, x, h)
    else
      return none
  else if s.isFVar then
    let cert ← r.toIntervalArithmeticCertificate decl
    if cert.fvars.isEmpty then
      match ineq with
      | .le =>
        let lb := proj ``Interval 0 (app cert.comp n)
        let top ← mkAppOptM ``Option.none #[some (← mkAppM ``FiniteUpperBound #[α])]
        let x ← mkAppM ``Interval.mk #[lb, top]
        let h ← mkAppM ``mem_toSet_of_mem_toSet_le #[e, app cert.proof n]
        return some (s.fvarId!, x, h)
      | .lt =>
        let lb ← mkAppM ``LowerBound.open #[proj ``Interval 0 (app cert.comp n)]
        let top ← mkAppOptM ``Option.none #[some (← mkAppM ``FiniteUpperBound #[α])]
        let x ← mkAppM ``Interval.mk #[lb, top]
        let h ← mkAppM ``mem_toSet_of_mem_toSet_lt #[e, app cert.proof n]
        return some (s.fvarId!, x, h)
    else
      return none
  else
    return none


end IntervalArithmetic
