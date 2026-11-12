/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Init

/-!
# Datatypes for the `inclusion` tactic

This file defines several datatypes and monads (and some basic API for them) that are used
throughout the core of the `inclusion` tactic.
-/

public meta section

open Lean Meta

namespace Inclusion

/-- An `IType` is a structure that holds the types of an inclusion expression `x ∈ s`, where
the type of `x` is `elemType`, the type of `s` is `setType` and the `ToSet setType elemType`
instance used is `toSetInst`. -/
structure IType where
  /-- The element type of an inclusion expression. -/
  elemType : Expr
  /-- The set type of an inclusion expression. -/
  setType : Expr
  /-- The `ToSet setType elemType` instance of an inclusion expression. -/
  toSetInst : Expr
  deriving Inhabited

/-- An `IExpr` is an expression `expr` together with a choice of `IType` used to represent
inclusion expressions of the form `expr ∈ s`. -/
structure IExpr where
  /-- The types of an `IExpr`. -/
  iType : IType
  /-- The underlying expression of an `IExpr`. -/
  expr : Expr
  deriving Inhabited

/-- An `IVar` is a structure that holds the data of a "free inclusion variable" associated to an
inclusion expression `iExpr`. This includes a pair of variables `setVar`, `hypVar` (which are
sometimes free variables but often synthetic opaque metavariables), where `setVar` is a variable for
an inclusion set and `hypVar` is a (variable) proof of `iExpr.expr ∈ setVar`. -/
structure IVar where
  /-- The inclusion expression represented by the inclusion variable. -/
  iExpr : IExpr
  /-- The inclusion set variable. -/
  setVar : Expr
  /-- The variable `hypVar : iExpr.expr ∈ setVar`. -/
  hypVar : Expr
  /-- An optional expression of type `Cover iVar.type.setType iVar.type.elemType`. When present,
  the inclusion computation is mapped over this cover to reduce the "dependency effect". -/
  cover? : Option Expr

/-- The `IType` of an `IVar`. -/
def IVar.type (iVar : IVar) : IType := iVar.iExpr.iType

/-- The associated expression of an `IVar`. -/
def IVar.expr (iVar : IVar) : Expr := iVar.iExpr.expr

/-- An `ExprInclusion` is a structure associated with an expression `e`, containing a computed
inclusion set for `e` and a proof that this inclusion is correct. -/
structure ExprInclusion where
  /-- The expression computing an inclusion set for `e`. -/
  inclusion : Expr
  /-- A proof of `e ∈ inclusion`, where `e` is the represented expression. -/
  proof : Expr
  deriving Inhabited

/-- An `ExprInclusionBody` is an intermediate structure used in the process of building the
`ExprInclusion` associated to an expression `e`. It contains an `inclusionBody` and `proofBody`
which contain the (possibly partially completed) body of the `inclusion` and `proof` expressions
of the `ExprInclusion` respectively. -/
structure ExprInclusionBody where
  /-- The (possibly partially completed) body of the inclusion expression. -/
  inclusionBody : Expr
  /-- The (possibly partially completed) proof of `e ∈ inclusionBody`. -/
  proofBody : Expr
  deriving Inhabited

/-- Convert an `IVar` to an `ExprInclusionBody`. -/
def IVar.toExprInclusionBody (iVar : IVar) : ExprInclusionBody := ⟨iVar.setVar, iVar.hypVar⟩

section InclusionM

/-- The fixed context of the `InclusionM` monad. -/
structure InclusionM.Context where
  /-- The initial `LocalContext`. -/
  localContext : LocalContext
  /-- The `LocalInstances` associated with `localContext`. -/
  localInstances : LocalInstances
  /-- A map from inclusion parameter names to their user-supplied values. -/
  paramSettings : NameMap Expr
  /-- The names of the inclusion extension families to use. -/
  families : Array Name
  /-- If `noIVars` is `true` then inclusion extensions should not register `IVar`s. -/
  noIVars : Bool := false

/-- The mutable state of the `InclusionM` monad. -/
structure InclusionM.State where
  /-- A map from expressions to their inclusion variables. -/
  iVars : ExprMap IVar := {}
  /-- A map from inclusion set variables to the expressions used to display them in traces. -/
  iVarDisplays : ExprMap Expr := {}

/-- The monad used by the `inclusion` tactic during the construction of `ExprInclusion`s. -/
abbrev InclusionM := ReaderT InclusionM.Context <| StateT InclusionM.State MetaM

instance : MonadBacktrack (Meta.SavedState × InclusionM.State) InclusionM where
  saveState := do return ⟨← Meta.saveState, ← get⟩
  restoreState s := do
    s.1.restore
    set s.2

/-- Run the `InclusionM` monad with an explicit context and initial state. -/
def InclusionM.runWith {α : Type} (x : InclusionM α) (context : InclusionM.Context)
    (state : InclusionM.State := {}) : MetaM (α × InclusionM.State) :=
  StateT.run (ReaderT.run x context) state

/-- Run the `InclusionM` monad using the current local context. -/
def InclusionM.run {α : Type} (x : InclusionM α) (paramSettings : NameMap Expr := {})
    (families : Array Name := #[]) : MetaM α := do
  let localContext ← getLCtx
  let localInstances ← getLocalInstances
  return (← x.runWith { localContext, localInstances, paramSettings, families }).1

end InclusionM

section HypothesisM

/-- The fixed context of the `HypothesisM` monad. -/
structure HypothesisM.Context extends InclusionM.Context where
  /-- The inclusion variables indexed by their associated expressions. -/
  iVarsMap : ExprMap IVar
  /-- The inclusion variables whose hypotheses are being constructed. -/
  iVars : Array IVar

/-- The mutable state of the `HypothesisM` monad. -/
structure HypothesisM.State where
  /-- The candidate inclusion bodies derived for each requested expression. -/
  inclusions : ExprMap (Array ExprInclusionBody) := {}

/-- The monad used by the `inclusion` tactic to construct initial inclusion hypotheses. -/
abbrev HypothesisM := ReaderT HypothesisM.Context <| StateT HypothesisM.State MetaM

instance : MonadBacktrack (Meta.SavedState × HypothesisM.State) HypothesisM where
  saveState := do return ⟨← Meta.saveState, ← get⟩
  restoreState s := do
    s.1.restore
    set s.2

/-- Run the `HypothesisM` monad using the context and state of the current `InclusionM`
computation. -/
def HypothesisM.run {α : Type} (x : HypothesisM α) : InclusionM α := do
  let inclusionContext ← read
  let inclusionState ← get
  let iVarsMap := inclusionState.iVars
  let iVars := iVarsMap.valuesArray
  liftM <| StateT.run' (ReaderT.run x { toContext := inclusionContext, iVarsMap, iVars }) {}

end HypothesisM

end Inclusion
