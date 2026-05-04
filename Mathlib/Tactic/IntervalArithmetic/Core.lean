module
public meta import Mathlib.Tactic.IntervalArithmetic.Certificate
public meta import Lean.AddDecl

set_option linter.style.header false

@[expose] public meta section

namespace IntervalArithmetic

open Lean Expr Meta Elab Command Tactic

def mkIntervalHyps (α : Type) (g : MVarId) : IntervalM α Unit := g.withContext do
  let ctx ← read
  let lctx ← getLCtx
  let mut rs : Array FVarId := #[]
  let mut hs : FVarIdMap (Array (Expr × Expr)) := {}
  for ldecl in lctx do
    let t ← instantiateMVars ldecl.type
    if ← isDefEq t ctx.targetTypeExpr then
      let rId := ldecl.fvarId
      rs := rs.push rId
    else if let some ⟨r, x, φ⟩ := memIntervaltoSet? t then
      if let some rId := r.fvarId? then
        if ! x.hasFVar && (← withNewMCtxDepth <| isDefEq ctx.embeddingExpr φ) then
        hs := hs.alter rId fun
          | some xs => xs.push (x, ldecl.toExpr)
          | none => #[(x, ldecl.toExpr)]
    else
      let mut trys := #[]
      let (h₁?, h₂?) ← ldecl.toExpr.memSetIntervalToIneqs?
      if let some h₁ := h₁? then
        trys := trys.push h₁
      if let some h₂ := h₂? then
        trys := trys.push h₂
      if trys.isEmpty then
        trys := trys.push ldecl.toExpr
      for e in trys do
        if let some ⟨rId, x, hrx⟩ ← e.ineqToIntervalHyp? α then
        hs := hs.alter rId fun
          | some xs => xs.push (x, hrx)
          | none => #[(x, hrx)]
  for rId in rs do
    let mut x ← mkAppM ``Interval.univ #[ctx.intervalTypeExpr]
    let mut h ← mkAppM ``Interval.mem_toSet_univ #[ctx.embeddingExpr, mkFVar rId]
    if hc : hs.contains rId then
      for (y, hry) in hs.get rId hc do
        x := ← mkAppM ``Interval.inter #[x, y]
        h := ← mkAppM ``Interval.inter_inclusion #[h, hry]
    -- temp fix, we will come up with better solutions
    let x' ← unsafe (evalExpr (Interval α) (← mkAppM ``Interval #[ctx.intervalTypeExpr]) x)
    modify fun s => {s with hyps := s.hyps.insert (g, rId) ⟨x', x, h⟩}

-- def mkMemIntervalProof {α : Type} (g : MVarId) (certGen : CertificateGenerator α) :
--     IntervalM α (Expr × Expr) := g.withContext do
--   let ctx ← read
--   let mut xs := #[]
--   let mut hrxs := #[]
--   for rId in cert.fvars do
--     let (x, hrx) := (← get).hyps.get! (g, rId)
--     xs := xs.push x
--     hrxs := hrxs.push hrx
--   let x ← instantiateMVars <| mkAppN cert.comp (#[ctx.approxParam] ++ xs)
--   let hrx ← instantiateMVars <| mkAppN cert.proof (#[ctx.approxParam] ++ xs ++ hrxs)
--   return ⟨x, hrx⟩

section Core

inductive IntervalGoal
  | ineq : Mathlib.Ineq → Expr → Expr → IntervalGoal
  | mem : Expr → Option Expr → Option Expr → IntervalGoal

def _root_.Lean.Expr.intervalGoal? (α : Type) (e : Expr) : IntervalM α IntervalGoal := do
  let ctx ← read
  if let some ⟨ineq, β, e₁, e₂⟩ := e.ineq?? then
    unless ← isDefEq ctx.targetTypeExpr β do
      throwError m!"Goal is an (in)equality in type: `{β}`, but expected: `{ctx.targetTypeExpr}`."
    return .ineq ineq e₁ e₂
  else
      throwError m!"{e} is not a supported interval arithmetic goal."

def intervalIneqCore (α : Type) [LinearOrder α] [Repr α] [DecidableLE α] [DecidableLT α]
    (g : MVarId) (ineq : Mathlib.Ineq) (lhs : Expr) (rhs : Expr) : IntervalM α Expr := do
  let ctx ← read
  mkIntervalHyps α g
  let lcert ← (← lhs.toIntervalArithmeticCertificateGenerator α).toCertificate g
  let rcert ← (← rhs.toIntervalArithmeticCertificateGenerator α).toCertificate g
  match ineq with
  | .eq =>
    unless lcert.interval.strict_eq rcert.interval do
      throwError m!"TODO"
    let lhs_strict_eq_rhs ← mkAppM ``Interval.strict_eq #[lcert.intervalExpr, rcert.intervalExpr]
    let h ← mkDecideProof lhs_strict_eq_rhs
    let g_proof ← mkAppM ``Interval.eq_of_strict_eq #[lcert.proof, rcert.proof, h]
    return g_proof
  | .le =>
    unless lcert.interval.le rcert.interval do
      throwError m!"TODO"
    let lhs_le_rhs ← mkAppM ``Interval.le #[lcert.intervalExpr, rcert.intervalExpr]
    let h ← mkDecideProof lhs_le_rhs
    let g_proof ← mkAppM ``Interval.le_of_le
      #[ctx.strictMonoExpr, lcert.proof, rcert.proof, h]
    return g_proof
  | .lt =>
    unless lcert.interval.lt rcert.interval do
      throwError m!"TODO"
    let lhs_lt_rhs ← mkAppM ``Interval.lt #[lcert.intervalExpr, rcert.intervalExpr]
    let h ← mkDecideProof lhs_lt_rhs
    let g_proof ← mkAppM ``Interval.lt_of_lt
      #[ctx.strictMonoExpr, lcert.proof, rcert.proof, h]
    return g_proof

-- def intervalMemSetCore (α : Type) [LinearOrder α] [Repr α] [DecidableLE α] [DecidableLT α]
--     (g : MVarId) (r : Expr) (Ixx : IntervalClass) : IntervalM Expr := do
--   let ctx ← read
--   mkIntervalHyps g
--   let rcert ← r.toIntervalArithmeticCertificate
--   let ⟨x, hrx⟩ ← mkMemIntervalProof g rcert
--   let x_eval ← unsafe (evalExpr (Interval α) (← mkAppM ``Interval #[ctx.intervalTypeExpr]) x)
--   match Ixx with
--   | .Ici a =>
--     let acert ← a.toIntervalArithmeticCertificate
--     let ⟨y, hay⟩ ← mkMemIntervalProof g acert
--     let y_eval ← unsafe (evalExpr (Interval α) (← mkAppM ``Interval #[ctx.intervalTypeExpr]) y)
--     unless y_eval.le x_eval do
--       throwError m!"TODO"
--     let y_le_x ← mkAppM ``Interval.le #[y, x]
--     let hxy ← mkDecideProof y_le_x
--     let g_proof ← mkAppM ``Interval.me
--   | .Ioi a =>
--     sorry
--   | .Iic b =>
--     sorry
--   | .Iio b =>
--     sorry
--   | .Ico a b =>
--     sorry
--   | .Ioc a b =>
--     sorry
--   | .Icc a b =>
--     sorry
--   | .Ioo a b =>
--     sorry

def intervalCore (α : Type) [LinearOrder α] [Repr α] [DecidableLE α] [DecidableLT α] (g : MVarId) :
    IntervalM α Expr := do
  let t ← whnfR (← instantiateMVars (← g.getType))
  match ← t.intervalGoal? α with
    | .ineq ineq lhs rhs => intervalIneqCore α g ineq lhs rhs
    | .mem _ _ _ => unreachable!

end Core
section Tactic

def intervalTactic (α : Type) [LinearOrder α] [Repr α] [DecidableLE α] [DecidableLT α]
  (declName : Name) (opConfig : NameMap OpConfig) (n : ℕ) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ctx ← mkContext declName n opConfig
  let ⟨g_proof, _⟩ ← intervalCore α g ctx |>.run {}
  g.assign g_proof
  replaceMainGoal []

declare_syntax_cat interval_setting (behavior := symbol)

syntax (name := local_approxParam)
  &"approx" ":=" num "for" ident : interval_setting

syntax (name := global_approxParam)
  &"approx" ":=" num : interval_setting

syntax (name := ignore)
  &"ignore" ident : interval_setting

def intervalSettingParser (declName : Name) (settings : Array Syntax) :
    MetaM (NameMap OpConfig × Option Nat) := do
  let mut opConfigs : NameMap OpConfig := {}
  let mut approxParam : Option Nat := none
  for setting in settings do
    match setting with
    | `(interval_setting| approx := $n for $ident) =>
      let opName := ident.getId
      unless (← getIntervalOp? declName opName).isSome do
        throwError m!"There is no interval operation with name: `{opName}` registered for \
          the `{declName}` interval arithmetic declaration."
      opConfigs := opConfigs.alter opName fun
        | some opConfig => some {opConfig with approxParam := some (mkNatLit n.getNat)}
        | none => some {ignore := false, approxParam := some (mkNatLit n.getNat)}
    | `(interval_setting| ignore $ident) =>
      let opName := ident.getId
      unless (← getIntervalOp? declName opName).isSome do
        throwError m!"There is no interval operation with name: {opName} registered for \
          the {declName} interval arithmetic declaration."
      opConfigs := opConfigs.alter ident.getId fun
        | some opConfig => some {opConfig with ignore := true}
        | none => some {ignore := true, approxParam := none}
    | `(interval_setting| approx := $n) => approxParam := n.getNat
    | _ => throwUnsupportedSyntax
  return (opConfigs, approxParam)

end Tactic

end IntervalArithmetic
