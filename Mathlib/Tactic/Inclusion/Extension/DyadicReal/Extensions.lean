/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Basic
public import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Splitting
public meta import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Basic
public meta import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Splitting
public meta import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Hypotheses
public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Basic

/-!
# Inclusion extensions for dyadic real intervals
-/

public meta section

open Lean Meta

namespace Inclusion

@[inclusionParam]
meta def binSplitParam : InclusionParamDecl where
  name := `binSplit
  type := mkConst ``Nat

private def mkRealCover (iExpr : IExpr) : InclusionM (Option Expr) := do
  let some depth ← InclusionM.getParam? `binSplit | return none
  return some (← mkAppOptM ``Splitter.cover
    #[iExpr.iType.setType, iExpr.iType.elemType, iExpr.iType.toSetInst, none, depth])

@[inclusionExt real.dyadic | (_ : ℝ)]
meta def mkRealIVar : InclusionExt :=
  mkNDIVarExt
    { elemType := mkConst ``Real
      setType := mkApp (mkConst ``Interval [.zero]) (mkConst ``Dyadic)
      toSetInst := mkConst ``instToSetIntervalDyadicReal }
    mkRealCover

end Inclusion
