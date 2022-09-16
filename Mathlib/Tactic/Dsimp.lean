
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Core

namespace Lean.Parser.Tactic.Conv
open Lean.Elab.Tactic Elab.Tactic.Conv Parser.Tactic.Conv

/- N -/ syntax (name := dsimp) "dsimp" (&" only")? (dsimpArgs)? : conv

def evalDSimp : Tactic := fun stx => withMainContext do
  let { ctx, .. } ← mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
  let lhs ← getLhs
  let result ← Lean.Meta.dsimp lhs ctx
  changeLhs result

elab "dsimp" : conv => evalDSimp Lean.Syntax.missing

example : (1 + 0) = 1 := by
  dsimp

example : (1 + 0) = 1 := by
  conv =>
    lhs
    dsimp


  --dsimpLocation ctx (expandOptLocation stx[5])
  --let result ← dischargeWrapper.with fun d? => simp lhs ctx (discharge? := d?)
  --applySimpResult result

/-
def applyDSimpResult (result : Simp.Result) : TacticM Unit := do
  if result.proof?.isNone then
    changeLhs result.expr
  else
    updateLhs result.expr (← result.getProof)

def evalDSimp : Tactic := fun stx => withMainContext do
  let { ctx, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
  let lhs ← getLhs
  let result ← dischargeWrapper.with fun d? => simp lhs ctx (discharge? := d?)
  applySimpResult result

def evalDSimpMatch : Tactic := fun _ => withMainContext do
  applySimpResult (← Split.simpMatch (← getLhs))-/



example : (1 + 0) = 1 := by
  dsimp

example : (1 + 0) = 1 := by
  conv =>
    lhs
    dsimp

example : (1 + 0) = 1 := by
  conv =>
    lhs
    simp
