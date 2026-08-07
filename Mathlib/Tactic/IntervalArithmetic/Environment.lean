/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Lean.Meta.Basic
public import Mathlib.Tactic.IntervalArithmetic.Expr

/-!
## Environment Setup for Interval Arithmetic Tactics

This file declares an initialzes the environments that carry interval arithmetic declarations
and interval arithmetic operations.

-/

public meta section

namespace IntervalArithmetic

open Lean Expr Meta Elab Command Std

section IntervalArithmeticDecl

/-- The data of an Interval Arithmetic Declaration. -/
structure IntervalArithmeticDecl where
  /-- Name of the declaration. -/
  name : Name
  /-- Name of `α` where `Interval α` is the type of intervals used for computation. -/
  intervalTypeName : Name
  /-- Name of the type that the tactic proves inequalities or interval containment statements in. -/
  targetTypeName : Name
  /-- Name of the embedding from the interval type to the target type. -/
  embeddingName : Name
  /-- Name of the theorem which states that the embedding is `StrictMono`. -/
  strictMonoName : Name
  deriving Inhabited

/-- Structure storing all `IntervalArithmeticDecl`s indexed by their names. -/
structure IntervalArithmeticDecls where
  decls : NameMap IntervalArithmeticDecl := {}
  deriving Inhabited

/-- Environment extension for storing `IntervalArithmeticDecl`s. -/
abbrev IntervalArithmeticDeclsExt :=
  SimpleScopedEnvExtension IntervalArithmeticDecl IntervalArithmeticDecls

initialize intervalArithmeticDeclsExt : IntervalArithmeticDeclsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with decls := d.decls.insert e.name e}
  }

/-- Get an `IntervalArithmeticDecl` from the environment. -/
def getIntervalArithmeticDecl? (declName : Name) : MetaM (Option IntervalArithmeticDecl) := do
  let s := intervalArithmeticDeclsExt.getState (← getEnv)
  return s.decls.find? declName

/-- Register a new `IntervalArithmeticDecl`. This function takes in the name `declName` of the
new `IntervalArithmeticDecl` and the name `strictMonoName` of a theorem proving that an embedding
from an interval type to a target type is `StrictMono`. Using the theorem it extracts the data
necessary to register the `IntervalArithmeticDecl` and checks whether its a valid declaration. -/
def addIntervalArithmeticDecl (declName strictMonoName : Name) (kind : AttributeKind := .global) :
    MetaM Unit := do
  if (← getIntervalArithmeticDecl? declName).isSome then
    throwError m!"Interval arithmetic declaration `{declName}` is already registered."
  let thm ← mkConstWithFreshMVarLevels strictMonoName
  let thmType ← inferType thm
  match thmType.getAppFnArgs with
  | (`StrictMono, #[α, β, dα, dβ, φ]) =>
    let some intervalTypeName := α.constName? | throwError m! "{α} is not a constant"
    let some targetTypeName := β.constName? | throwError m! "{β} is not a constant"
    let some embeddingName := φ.constName? | throwError m! "{φ} is not a constant"
    -- check that `α` has type `Type`
    unless ← isDefEq (← inferType α) (sort 1) do
      throwError m!"{α} does not have type `Type`."
    -- check that `dα` and `dβ` match the preorders you get from inferring linear orders
    -- on `α` and `β` respectively.
    let dαLinear ← synthInstance (← mkAppM ``LinearOrder #[α])
    let dαPartial ← mkAppOptM ``LinearOrder.toPartialOrder #[α, dαLinear]
    let dα' ← mkAppOptM ``PartialOrder.toPreorder #[α, dαPartial]
    let dβLinear ← synthInstance (← mkAppM ``LinearOrder #[β])
    let dβPartial ← mkAppOptM ``LinearOrder.toPartialOrder #[β, dβLinear]
    let dβ' ← mkAppOptM ``PartialOrder.toPreorder #[β, dβPartial]
    unless ← pureIsDefEq dα dα' do
      throwError m!"{dα} does not match inferred {dα'}"
    unless ← pureIsDefEq dβ dβ' do
      throwError m!"{dβ} does not match inferred {dβ'}"
    let decl : IntervalArithmeticDecl := {
      name := declName
      intervalTypeName := intervalTypeName
      targetTypeName := targetTypeName
      embeddingName := embeddingName
      strictMonoName := strictMonoName
    }
    intervalArithmeticDeclsExt.add decl kind
  | _ => throwError m!"Type of `{strictMonoName}` is not of the form: `StrictMono _`"

syntax (name := interval_arithmetic_decl) "interval_arithmetic_decl" ident :  attr

/-- Intialization of `interval_arithmetic_decl` attribute. -/
initialize
  registerBuiltinAttribute {
    name  := `interval_arithmetic_decl
    descr := "Registers an `IntervalArithmeticDecl`"
    applicationTime := .afterTypeChecking
    add := fun thm stx kind => do
      match stx with
      | `(attr | interval_arithmetic_decl $decl:ident) =>
        (addIntervalArithmeticDecl decl.getId thm kind).run'
      | _ => throwUnsupportedSyntax
  }

end IntervalArithmeticDecl

section IntervalOps

/- The data of an Interval Operation. -/
structure IntervalOp where
  /-- Name of the interval operation declaration. -/
  opName : Name
  /-- The interval arithmetic declaration that the `IntervalOp` belongs to. -/
  declName : Name
  /-- Name of the head of the expression to match on. -/
  headName : Name
  /-- Name of the inclusion theorem -/
  incName : Name
  /-- The position of each set fvar and its corresponding interval hypothesis in `incName` -/
  hyps : Array (Nat × Nat)
  /-- If the interval operation has an approximation parameter than `approxParam?` is the
    position of the parameter (otherwise `none`). -/
  approxParam? : Option Nat
  deriving Inhabited

/-- Structure storing all `IntervalOps`. -/
structure IntervalOps where
  /-- Map from `(declName, headName)` to the Array of `Names` registered for `declName` that
  match `headname`. -/
  map : HashMap (Name × Name) (Array Name) := {}
  /-- Map from `(declName, opName)` to the `IntervalOp`. -/
  ops : HashMap (Name × Name) IntervalOp := {}
  deriving Inhabited

/-- Environment extension for storing `IntervalOps` -/
abbrev IntervalOpsExt := SimpleScopedEnvExtension IntervalOp IntervalOps

initialize intervalOpsExt : IntervalOpsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun os o =>
      {os with
        map := os.map.alter (o.declName, o.headName) fun
        | none => some #[o.opName]
        | some arr => some (arr.push o.opName),
        ops := os.ops.insert (o.declName, o.opName) o}}

/-- Returns the Array of `opName`s matching the given `declName` and `refName`. -/
def getIntervalOpNames? (declName : Name) (headName : Name) : MetaM (Option (Array Name)) := do
  let s := intervalOpsExt.getState (← getEnv)
  return s.map.get? (declName, headName)

/-- Returns the `IntervalOp` with name `opName`. -/
def getIntervalOp? (declName opName : Name) : MetaM (Option IntervalOp) := do
  let s := intervalOpsExt.getState (← getEnv)
  return s.ops.get? (declName, opName)

/-- Register a new `IntervalOp`. This function takes in the name `declName` of the
`IntervalArithmeticDecl` the operation is being added to and the name `incName` of a theorem
proving that an expression of `targetType` is contained in the set computed by the interval
operation. Using the theorem it extracts the data necessary to register the `IntervalOp`
and check whether its valid. -/
def addIntervalOp (declName opName incName : Name) (kind : AttributeKind := .global) :
    MetaM Unit := do
  let some decl ← getIntervalArithmeticDecl? declName
    | throwError m!"Unknown interval arithmetic declaration `{declName}`."
  unless (← getIntervalOp? declName opName).isNone do
    throwError m!"Interval operation with name: {opName} already registered for decl: {declName}."
  let φ ← mkConstWithFreshMVarLevels decl.embeddingName
  forallTelescope (← getConstInfo incName).type fun hs conc => do
    -- check that the conclusion is of the form `_ ∈ _.toSet _`
    let some ⟨r₀, x₀, φ'⟩ := conc.memIntervaltoSet?
      | throwError m!"The conclusion of `{incName}` is not of the form `_ ∈ _.toSet _.`"
    -- check that the embedding in the conclusion matches the embedding in the declaration
    if !(← withNewMCtxDepth <| isDefEq φ φ') then
      throwError m!"{φ'} is not definitionally equal to `{decl.embeddingName}`."
    let some headName := r₀.getAppFn.constName?
      | throwError m!"`{r₀}` is not an application of a constant"
    let r₀Ids := Lean.collectFVars {} r₀ |>.fvarSet
    let x₀Ids := Lean.collectFVars {} x₀ |>.fvarSet
    let mut setFVars : FVarIdMap Nat := {}
    let mut intervalFVars : HashSet FVarId := {}
    let mut hypIds : HashSet FVarId := {}
    for i in [:hs.size] do
      let h := hs[i]!
      if let some (r, x, φ') := intervalHyp? (← inferType h) then
        if (← pureIsDefEq φ φ') then
          if x₀Ids.contains r then
            throwError m!"{mkFVar r} appears as a variable in an interval hypothesis but also \
              in the interval formula: {indentExpr x₀}"
          unless r₀Ids.contains r do
            throwError m!"{mkFVar r} appears as a variable in an interval hypothesis but not in \
              the target expression: {indentExpr r₀}"
          if setFVars.contains r then
            throwError m!"{mkFVar r} appears in more than one interval hypothesis."
          else
            setFVars := setFVars.insert r i
          if r₀Ids.contains x then
            throwError m!"{mkFVar x} appears as an interval in an interval hypothesis but also \
              in target expression: {indentExpr r₀}."
          unless x₀Ids.contains x do
            throwError m!"{mkFVar x} appears as an interval in an interval hypothesis but not in \
              the interval formula: {indentExpr x₀}"
          if intervalFVars.contains x then
            throwError m!"{mkFVar x} appears in more than one interval hypothesis."
          else
            intervalFVars := intervalFVars.insert x
          hypIds := hypIds.insert h.fvarId!
    let mut hyps := #[]
    let mut approxParam? : Option Nat := none
    for i in [:hs.size] do
      let h := hs[i]!
      if let some hId := h.fvarId? then
        if let some j := setFVars.get? hId then
          hyps := hyps.push (i, j)
        else if hypIds.contains hId then
          if r₀Ids.contains hId then
            throwError m!"{mkFVar hId} appears in the target expression: {indentExpr r₀}"
          if x₀Ids.contains hId then
            throwError m!"{mkFVar hId} appears in the interval formula: {indentExpr x₀}"
        else if (← hId.getDecl).userName == `approxParam then
          if r₀Ids.contains hId then
            throwError m!"`approxParam` appears in the target expression: {indentExpr r₀}"
          unless x₀Ids.contains hId do
            throwError m!"`approxParam` does not appear in the interval formula: {indentExpr x₀}"
          unless approxParam?.isNone do
            throwError "The theorem contains more than one `approx_param`"
          let approx_param_type ← inferType h
          let nat := mkConst ``Nat
          unless ← isDefEq nat approx_param_type do
            throwError m!"`approx_param` has type: {indentExpr approx_param_type}
              but expected: {indentExpr nat}"
          approxParam? := some i
        else unless r₀Ids.contains hId || x₀Ids.contains hId do
          throwError m!"{mkFVar hId} does not appear in the target expression or interval formula"
    let op : IntervalOp := {
      opName := opName
      declName := declName
      headName := headName
      incName := incName
      hyps := hyps
      approxParam? := approxParam?
    }
    intervalOpsExt.add op kind

syntax (name := interval_op) "interval_op" ident ident : attr

initialize
  registerBuiltinAttribute {
    name  := `interval_op
    descr := "Registers an `IntervalOp`"
    applicationTime := .afterTypeChecking
    add := fun op stx kind => do
      match stx with
      | `(attr | interval_op $decl:ident $name:ident) =>
        (addIntervalOp decl.getId name.getId op kind).run'
      | _ => throwUnsupportedSyntax
  }

end IntervalOps

end IntervalArithmetic
