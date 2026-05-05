module

public meta import Mathlib.Tactic.IntervalArithmetic.IntervalHyps
public meta import Lean.AddDecl

set_option linter.style.header false

@[expose] public meta section

namespace IntervalArithmetic

open Lean Expr Meta Elab Command Tactic

inductive IntervalGoal
  | ineq : Mathlib.Ineq → Expr → Expr → IntervalGoal
  | mem :  Expr → IntervalClass →  IntervalGoal

def _root_.Lean.Expr.intervalGoal? (α : Type) (e : Expr) : IntervalM α IntervalGoal := do
  let ctx ← read
  if let some ⟨ineq, β, e₁, e₂⟩ := e.ineq?? then
    unless ← isDefEq ctx.targetTypeExpr β do
      throwError m!"Goal is an (in)equality in type: `{β}`, but expected: `{ctx.targetTypeExpr}`."
    return .ineq ineq e₁ e₂
  else if let some (r, Ixx) := e.memSetInterval? then
    let β ← inferType r
    unless ← isDefEq ctx.targetTypeExpr β do
      throwError m!"Goal is an interval containment in type: `{β}`, but expected:
        `{ctx.targetTypeExpr}`."
    return .mem r Ixx
  else
      throwError m!"{e} is not a supported interval arithmetic goal."


def intervalIneqCore (α : Type) [LinearOrder α] [DecidableLE α] [DecidableLT α]
    (ineq : Mathlib.Ineq) (lhs : Expr) (rhs : Expr) : IntervalM α Expr := do
  let ctx ← read
  mkIntervalHyps α
  let lcert ← (← lhs.toIntervalArithmeticCertificateGenerator α).toCertificate
  let rcert ← (← rhs.toIntervalArithmeticCertificateGenerator α).toCertificate
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

def intervalMemSetCore (α : Type) [LinearOrder α] [Repr α] [ToExpr α] [DecidableLE α]
    [DecidableLT α] (r : Expr) (Ixx : IntervalClass) : IntervalM α Expr := do
  let ctx ← read
  mkIntervalHyps α

  let mkCert : Expr → IntervalM α (IntervalCertificate α) := fun e => do
    (← e.toIntervalArithmeticCertificateGenerator α).toCertificate

  let mkLe : IntervalCertificate α → IntervalCertificate α → IntervalM α Expr :=
    fun x y => do
      unless x.interval.le y.interval do
        throwError m!"TODO"
      let x_le_y ← mkAppM ``Interval.le #[x.intervalExpr, y.intervalExpr]
      mkDecideProof x_le_y

  let mkLt : IntervalCertificate α → IntervalCertificate α → IntervalM α Expr :=
    fun x y => do
      unless x.interval.lt y.interval do
        throwError m!"TODO"
      let x_lt_y ← mkAppM ``Interval.lt #[x.intervalExpr, y.intervalExpr]
      mkDecideProof x_lt_y

  let rcert ← mkCert r

  match Ixx with
  | .Ici a =>
      let acert ← mkCert a
      let har ← mkLe acert rcert
      mkAppM ``mem_Ici_of_interval_le
        #[ctx.strictMonoExpr, acert.proof, rcert.proof, har]
  | .Ioi a =>
      let acert ← mkCert a
      let har ← mkLt acert rcert
      mkAppM ``mem_Ioi_of_interval_lt
        #[ctx.strictMonoExpr, acert.proof, rcert.proof, har]
  | .Iic b =>
      let bcert ← mkCert b
      let hrb ← mkLe rcert bcert
      mkAppM ``mem_Iic_of_interval_le
        #[ctx.strictMonoExpr, rcert.proof, bcert.proof, hrb]
  | .Iio b =>
      let bcert ← mkCert b
      let hrb ← mkLt rcert bcert
      mkAppM ``mem_Iio_of_interval_lt
        #[ctx.strictMonoExpr, rcert.proof, bcert.proof, hrb]
  | .Ico a b =>
      let acert ← mkCert a
      let bcert ← mkCert b
      let har ← mkLe acert rcert
      let hrb ← mkLt rcert bcert
      mkAppM ``mem_Ico_of_interval_le_lt
        #[ctx.strictMonoExpr, acert.proof, rcert.proof, bcert.proof, har, hrb]
  | .Ioc a b =>
      let acert ← mkCert a
      let bcert ← mkCert b
      let har ← mkLt acert rcert
      let hrb ← mkLe rcert bcert
      mkAppM ``mem_Ioc_of_interval_lt_le
        #[ctx.strictMonoExpr, acert.proof, rcert.proof, bcert.proof, har, hrb]
  | .Icc a b =>
      let acert ← mkCert a
      let bcert ← mkCert b
      let har ← mkLe acert rcert
      let hrb ← mkLe rcert bcert
      mkAppM ``mem_Icc_of_interval_le_le
        #[ctx.strictMonoExpr, acert.proof, rcert.proof, bcert.proof, har, hrb]
  | .Ioo a b =>
      let acert ← mkCert a
      let bcert ← mkCert b
      let har ← mkLt acert rcert
      let hrb ← mkLt rcert bcert
      mkAppM ``mem_Ioo_of_interval_lt_lt
        #[ctx.strictMonoExpr, acert.proof, rcert.proof, bcert.proof, har, hrb]

def intervalCore (α : Type) [LinearOrder α] [Repr α] [ToExpr α] [DecidableLE α] [DecidableLT α]
    (g : MVarId) : IntervalM α Expr := do
  let t ← whnfR (← g.getType)
  match ← t.intervalGoal? α with
    | .ineq ineq lhs rhs => intervalIneqCore α ineq lhs rhs
    | .mem r Ixx => intervalMemSetCore α r Ixx
section Tactic

def intervalTactic (α : Type) [LinearOrder α] [Repr α] [ToExpr α] [DecidableLE α] [DecidableLT α]
  (declName : Name) (opConfig : NameMap OpConfig) (n : ℕ) : TacticM Unit := withMainContext do
  let ctx ← mkContext declName n opConfig
  let g ← getMainGoal
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
