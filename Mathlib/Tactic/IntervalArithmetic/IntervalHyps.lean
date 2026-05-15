/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.IntervalArithmetic.Certificate
public meta import Lean.AddDecl

/-!
# Interval Hypothesis Helpers for Interval Arithmetic Tactics

This file defines functions that preprocess hypothesis for the interval arithmetic tactics.

-/

@[expose] public meta section

namespace IntervalArithmetic

open Lean Expr Meta Elab Command Tactic

def _root_.Lean.Expr.ineqToIntervalHyp? (α : Type) (e : Expr) :
    IntervalM α (Option (FVarId × Expr × Expr)) := do
  let ctx ← read
  let ⟨ineq, _, r, s⟩ ← try Expr.ineq? (← whnfR (← inferType e)) catch _ => return none
  if r.isFVar then
    let certGen ← s.toIntervalArithmeticCertificateGenerator α
    if certGen.fvarIds.isEmpty then
      let cert ← certGen.toCertificate
      match ineq with
      | .eq =>
        let x := cert.intervalExpr
        let h ← mkAppM ``mem_toSet_of_eq_mem_toSet #[e, cert.proof]
        return some ⟨r.fvarId!, x, h⟩
      | .le =>
        let ub := proj ``Interval 1 cert.intervalExpr
        let bot ←
          mkAppOptM ``Option.none #[some (← mkAppM ``FiniteLowerBound #[ctx.intervalTypeExpr])]
        let x ← mkAppM ``Interval.mk #[bot, ub]
        let h ← mkAppM ``mem_toSet_of_le_mem_toSet #[e, cert.proof]
        return some (r.fvarId!, x, h)
      | .lt =>
        let ub ← mkAppM ``UpperBound.open #[proj ``Interval 1 cert.intervalExpr]
        let bot ←
          mkAppOptM ``Option.none #[some (← mkAppM ``FiniteLowerBound #[ctx.intervalTypeExpr])]
        let x ← mkAppM ``Interval.mk #[bot, ub]
        let h ← mkAppM ``mem_toSet_of_lt_mem_toSet #[e, cert.proof]
        return some (r.fvarId!, x, h)
    else
      return none
  else if s.isFVar then
    let certGen ← r.toIntervalArithmeticCertificateGenerator α
    if certGen.fvarIds.isEmpty then
      let cert ← certGen.toCertificate
      match ineq with
      | .eq =>
        let h ← mkAppM ``mem_toSet_of_mem_toSet_eq #[e, cert.proof]
        return some ⟨s.fvarId!, cert.intervalExpr, h⟩
      | .le =>
        let lb := proj ``Interval 0 cert.intervalExpr
        let top ←
          mkAppOptM ``Option.none #[some (← mkAppM ``FiniteUpperBound #[ctx.intervalTypeExpr])]
        let x ← mkAppM ``Interval.mk #[lb, top]
        let h ← mkAppM ``mem_toSet_of_mem_toSet_le #[e, cert.proof]
        return some (s.fvarId!, x, h)
      | .lt =>
        let lb ← mkAppM ``LowerBound.open #[proj ``Interval 0 cert.intervalExpr]
        let top ←
          mkAppOptM ``Option.none #[some (← mkAppM ``FiniteUpperBound #[ctx.intervalTypeExpr])]
        let x ← mkAppM ``Interval.mk #[lb, top]
        let h ← mkAppM ``mem_toSet_of_mem_toSet_lt #[e, cert.proof]
        return some (s.fvarId!, x, h)
    else
      return none
  else
    return none

def mkIntervalHyps (α : Type) (rs : FVarIdSet) : IntervalM α Unit := do
  let ctx ← read
  let lctx ← getLCtx
  let mut hs : FVarIdMap (Array (Expr × Expr)) := {}
  for ldecl in lctx do
    let t ← instantiateMVars ldecl.type
    if let some ⟨r, x, φ⟩ := memIntervaltoSet? t then
      if let some rId := r.fvarId? then
        if rs.contains rId && !x.hasFVar && (← pureIsDefEq ctx.embeddingExpr φ) then
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
          if rs.contains rId then
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
    let eval_x ← unsafe (evalExpr (Interval α) (← mkAppM ``Interval #[ctx.intervalTypeExpr]) x)
    modify fun s => {s with hyps := s.hyps.insert rId ⟨eval_x, x, h⟩}

end IntervalArithmetic
