/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Yuyang Zhao
-/
import Lean.Elab.SyntheticMVars
import Lean.Meta.Tactic.Delta
import Mathlib.Lean.Expr.Basic
import Mathlib.Util.Term.Beta

/-!
# Basic term elaborators
-/

namespace Mathlib.Util.Term.Basic

open Lean Elab Term Meta

/-- `delta% t` elaborates to a head-delta reduced version of `t`. -/
elab "delta% " t:term : term <= expectedType => do
  let t ← elabTerm t expectedType
  synthesizeSyntheticMVars
  let t ← instantiateMVars t
  let some t ← delta? t | throwError "cannot delta reduce {t}"
  pure t

/-- `zeta% t` elaborates to a head-zeta reduced version of `t`. -/
elab "zeta% " t:term : term <= expectedType => do
  let t ← elabTerm t expectedType
  synthesizeSyntheticMVars
  let t ← instantiateMVars t
  let t ← zetaReduce t
  pure t

/-- `reduceProj% t` apply `Expr.reduceProjStruct?` to all subexpressions of `t`. -/
elab "reduceProj% " t:term : term <= expectedType => do
  let t ← withSynthesize do
    elabTermEnsuringType t expectedType
  synthesizeSyntheticMVars
  let t ← instantiateMVars t
  let t ← Lean.Core.transform t (post := fun e ↦ do
    return .continue (← Expr.reduceProjStruct? e))
  pure t
