/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.IntervalArithmetic.IntervalHyps
public meta import Lean.AddDecl

/-!
## Interval Hypothesis Helpers for Interval Arithmetic Tactics

This file defines the core functions for the interval arithmetic tactics.

-/

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

def mkCertificate2 (α : Type) (e₁ e₂ : Expr) :
    IntervalM α (IntervalCertificate α × IntervalCertificate α) := do
  let certGen₁ ← e₁.toIntervalArithmeticCertificateGenerator α
  let certGen₂ ← e₂.toIntervalArithmeticCertificateGenerator α
  mkIntervalHyps α (certGen₁.fvarsSet.union certGen₂.fvarsSet)
  let cert₁ ← certGen₁.toCertificate
  let cert₂ ← certGen₂.toCertificate
  return (cert₁, cert₂)

def mkCertificate3 (α : Type) (e₁ e₂ e₃ : Expr) :
    IntervalM α (IntervalCertificate α × IntervalCertificate α × IntervalCertificate α) := do
  let certGen₁ ← e₁.toIntervalArithmeticCertificateGenerator α
  let certGen₂ ← e₂.toIntervalArithmeticCertificateGenerator α
  let certGen₃ ← e₃.toIntervalArithmeticCertificateGenerator α
  mkIntervalHyps α (certGen₁.fvarsSet.union certGen₂.fvarsSet |>.union certGen₃.fvarsSet)
  let cert₁ ← certGen₁.toCertificate
  let cert₂ ← certGen₂.toCertificate
  let cert₃ ← certGen₃.toCertificate
  return (cert₁, cert₂, cert₃)

def proveIntervalStrictEq (α : Type) [LinearOrder α] [Repr α]
    (xCert yCert : IntervalCertificate α) : IntervalM α Expr := do
  unless xCert.interval.strictEq yCert.interval do
    throwError m! "{repr xCert.interval}.strictEq {repr yCert.interval} is false."
  let x_strictEq_y ← mkAppM ``Interval.strictEq #[xCert.intervalExpr, yCert.intervalExpr]
  mkDecideProof x_strictEq_y

def proveIntervalLe (α : Type) [LinearOrder α] [Repr α] (xCert yCert : IntervalCertificate α) :
    IntervalM α Expr := do
  unless xCert.interval.le yCert.interval do
    throwError m! "{repr xCert.interval}.le {repr yCert.interval} is false."
  let x_le_y ← mkAppM ``Interval.le #[xCert.intervalExpr, yCert.intervalExpr]
  mkDecideProof x_le_y

def proveIntervalLt (α : Type) [LinearOrder α] [Repr α] (xCert yCert : IntervalCertificate α) :
    IntervalM α Expr := do
  unless xCert.interval.lt yCert.interval do
    throwError m! "{repr xCert.interval}.lt {repr yCert.interval} is false."
  let x_lt_y ← mkAppM ``Interval.lt #[xCert.intervalExpr, yCert.intervalExpr]
  mkDecideProof x_lt_y

def intervalIneqCore (α : Type) [Repr α] [LinearOrder α] [DecidableLE α] [DecidableLT α]
    (ineq : Mathlib.Ineq) (lhs : Expr) (rhs : Expr) : IntervalM α Expr := do
  let ctx ← read
  let (lcert, rcert) ← mkCertificate2 α lhs rhs
  match ineq with
  | .eq =>
      let h_x_strictEq_y ← proveIntervalStrictEq α lcert rcert
      mkAppM ``Interval.eq_of_strictEq #[lcert.proof, rcert.proof, h_x_strictEq_y]
  | .le =>
      let h_x_le_y ← proveIntervalLe α lcert rcert
      mkAppM ``Interval.le_of_le #[ctx.strictMonoExpr, lcert.proof, rcert.proof, h_x_le_y]
  | .lt =>
      let h_x_lt_y ← proveIntervalLt α lcert rcert
      mkAppM ``Interval.lt_of_lt #[ctx.strictMonoExpr, lcert.proof, rcert.proof, h_x_lt_y]

def intervalMemSetCore (α : Type) [LinearOrder α] [Repr α] [DecidableLE α]
    [DecidableLT α] (r : Expr) (Ixx : IntervalClass) : IntervalM α Expr := do
  let ctx ← read
  match Ixx with
  | .Ici a =>
      let (acert, rcert) ← mkCertificate2 α a r
      let har ← proveIntervalLe α acert rcert
      mkAppM ``mem_Ici_of_interval_le
        #[ctx.strictMonoExpr, acert.proof, rcert.proof, har]
  | .Ioi a =>
      let (acert, rcert) ← mkCertificate2 α a r
      let har ← proveIntervalLt α acert rcert
      mkAppM ``mem_Ioi_of_interval_lt
        #[ctx.strictMonoExpr, acert.proof, rcert.proof, har]
  | .Iic b =>
      let (rcert, bcert) ← mkCertificate2 α r b
      let hrb ← proveIntervalLe α rcert bcert
      mkAppM ``mem_Iic_of_interval_le
        #[ctx.strictMonoExpr, rcert.proof, bcert.proof, hrb]
  | .Iio b =>
      let (rcert, bcert) ← mkCertificate2 α r b
      let hrb ← proveIntervalLt α rcert bcert
      mkAppM ``mem_Iio_of_interval_lt
        #[ctx.strictMonoExpr, rcert.proof, bcert.proof, hrb]
  | .Ico a b =>
      let (acert, rcert, bcert) ← mkCertificate3 α a r b
      let har ← proveIntervalLe α acert rcert
      let hrb ← proveIntervalLt α rcert bcert
      mkAppM ``mem_Ico_of_interval_le_lt
        #[ctx.strictMonoExpr, acert.proof, rcert.proof, bcert.proof, har, hrb]
  | .Ioc a b =>
      let (acert, rcert, bcert) ← mkCertificate3 α a r b
      let har ← proveIntervalLt α acert rcert
      let hrb ← proveIntervalLe α rcert bcert
      mkAppM ``mem_Ioc_of_interval_lt_le
        #[ctx.strictMonoExpr, acert.proof, rcert.proof, bcert.proof, har, hrb]
  | .Icc a b =>
      let (acert, rcert, bcert) ← mkCertificate3 α a r b
      let har ← proveIntervalLe α acert rcert
      let hrb ← proveIntervalLe α rcert bcert
      mkAppM ``mem_Icc_of_interval_le_le
        #[ctx.strictMonoExpr, acert.proof, rcert.proof, bcert.proof, har, hrb]
  | .Ioo a b =>
      let (acert, rcert, bcert) ← mkCertificate3 α a r b
      let har ← proveIntervalLt α acert rcert
      let hrb ← proveIntervalLt α rcert bcert
      mkAppM ``mem_Ioo_of_interval_lt_lt
        #[ctx.strictMonoExpr, acert.proof, rcert.proof, bcert.proof, har, hrb]

def intervalCore (α : Type) [LinearOrder α] [Repr α] [DecidableLE α] [DecidableLT α]
    (g : MVarId) : IntervalM α Expr := do
  let t ← whnfR (← g.getType)
  match ← t.intervalGoal? α with
    | .ineq ineq lhs rhs => intervalIneqCore α ineq lhs rhs
    | .mem r Ixx => intervalMemSetCore α r Ixx

section Tactic

def intervalTactic (α : Type) [LinearOrder α] [Repr α] [DecidableLE α] [DecidableLT α]
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
