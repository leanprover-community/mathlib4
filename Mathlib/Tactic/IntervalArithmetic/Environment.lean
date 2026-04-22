module

public import Mathlib.Tactic.IntervalArithmetic.Expr

set_option linter.style.header false
public meta section
namespace IntervalArithmetic

open Lean Expr Meta Elab Command

section IntervalArithmeticDecl

structure IntervalArithmeticDecl where
  name : Name
  intervalType : Name
  setType : Name
  embedding : Name
  strictMono : Name
  deriving Inhabited

structure IntervalArithmeticDecls where
  decls : NameMap IntervalArithmeticDecl := {}
  deriving Inhabited

abbrev IntervalArithmeticDeclsExt :=
  SimpleScopedEnvExtension IntervalArithmeticDecl IntervalArithmeticDecls

initialize intervalArithmeticDeclsExt : IntervalArithmeticDeclsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with decls := d.decls.insert e.name e}
  }

def getIntervalArithmeticDecl? (declName : Name) : MetaM (Option IntervalArithmeticDecl) := do
  let s := intervalArithmeticDeclsExt.getState (← getEnv)
  return s.decls.find? declName

def addIntervalArithmeticDecl (declName strictMono : Name) (kind : AttributeKind := .global) :
    MetaM Unit := do
  if (← getIntervalArithmeticDecl? declName).isSome then
    throwError m!"Interval arithmetic declaration `{declName}` is already registered."
  let thm ← mkConstWithFreshMVarLevels strictMono
  let thm_type ← inferType thm
  match thm_type.getAppFnArgs with
  | (`StrictMono, #[α, β, dα, dβ, φ]) =>
    let some intervalType := α.constName? | throwError m! "{α} is not a constant"
    let some setType := β.constName? | throwError m! "{β} is not a constant"
    let some embedding := φ.constName? | throwError m! "{φ} is not a constant"
    -- check that `dα` and `dβ` are the instances you get from inference and `dα` comes from a
    -- partial order.
    let dα_partial ← synthInstance (← mkAppM ``PartialOrder #[α])
    let dα' ← mkAppOptM ``PartialOrder.toPreorder #[none, dα_partial]
    let dβ' ← synthInstance (← mkAppM ``Preorder #[β])
    unless ← withNewMCtxDepth <| isDefEq dα dα' do
      throwError m!"{dα} does not match inferred {dα'}"
    unless ← withNewMCtxDepth <| isDefEq dβ dβ' do
      throwError m!"{dβ} does not match inferred {dβ'}"
    let decl : IntervalArithmeticDecl := {
      name := declName
      intervalType := intervalType
      setType := setType
      embedding := embedding
      strictMono := strictMono
    }
    intervalArithmeticDeclsExt.add decl kind
  | _ => throwError m!"Type of `{strictMono}` must be of the form: `StrictMono _`"

syntax (name := interval_arithmetic_decl) "interval_arithmetic_decl" ident :  attr

initialize
  registerBuiltinAttribute {
    name  := `interval_arithmetic_decl
    descr := "TODO"
    applicationTime := .afterTypeChecking
    add := fun thm stx kind => do
      match stx with
      | `(attr | interval_arithmetic_decl $decl:ident) =>
        (addIntervalArithmeticDecl decl.getId thm kind).run'
      | _ => throwUnsupportedSyntax
  }

end IntervalArithmeticDecl

section IntervalOps

structure IntervalOp where
  /-- The interval arithmetic declaration that the `IntervalOp` belongs to -/
  declName : Name
  /-- Name of the `Interval` operation -/
  opName : Name
  /-- Name of the reference operation -/
  refName : Name
  /-- Name of the inclusion theorem -/
  incName : Name
  /-- The position of the interval arguments in `refName` and their hypotheses in `incName` -/
  args : Array (Nat × Nat)
  /-- If the interval operation has an approximation parameter than `isApprox = true`. -/
  isApprox : Bool
  deriving Inhabited

structure IntervalOps where
  ops : Std.HashMap (Name × Name) IntervalOp := {}
  deriving Inhabited

abbrev IntervalOpsExt := SimpleScopedEnvExtension IntervalOp IntervalOps

initialize intervalOpsExt : IntervalOpsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun os o =>
      {os with ops := os.ops.insert (o.declName, o.refName) o}
  }

def getIntervalOp? (declName : Name) (refName : Name) : MetaM (Option IntervalOp) := do
  let s := intervalOpsExt.getState (← getEnv)
  return s.ops.get? (declName, refName)

def addIntervalOp (declName : Name) (incName : Name) (isApprox : Bool)
    (kind : AttributeKind := .global) : MetaM Unit := do
  let some decl ← getIntervalArithmeticDecl? declName
    | throwError m!"Unknown interval arithmetic declaration `{declName}`."
  let φ ← mkConstWithFreshMVarLevels decl.embedding
  forallTelescope (← getConstInfo incName).type fun hs conc => do
    -- check that the conclusion is of the form `_ ∈ _.toSet _`
    let some ⟨f_rs, f'_xs, φ'⟩ := conc.memIntervaltoSet?
      | throwError m!"The conclusion of `{incName}` is not of the form `_ ∈ _.toSet _."
    -- check that the embedding in the conclusion matches the embedding in the declaration
    if !(← withNewMCtxDepth <| isDefEq φ φ') then
      throwError m!"{φ'} is not definitionally equal to `{decl.embedding}`."
    -- `hyps` is an `FVarIdMap` which keeps track of interval hypothesis in the `IntervalOp`
    -- declaration. For each hypotheses of the form `r ∈ x.toSet φ` with `r, x` free variables
    -- we have an entry in `hyps` with key `r` and value `(x, pos)` where `pos` is the position of
    -- the interval hypothesis in the inclusion theorem.
    let mut hyps : FVarIdMap (FVarId × Nat) := {}
    for i in [:hs.size] do
      let h := hs[i]!
      if let some (r, x, φ') := intervalHyp? (← inferType h) then
        if (← withNewMCtxDepth <| isDefEq φ φ') then
          if hyps.contains r then
            throwError m!"{mkFVar r} appears in more than one interval hypothesis."
          else
            hyps := hyps.insert r (x, i)
    let some f_name := f_rs.getAppFn.constName?
      | throwError m!"`{f_rs}` is not an application of a constant"
    let some f'_name := f'_xs.getAppFn.constName?
      | throwError m!"`{f'_xs}` is not an application of a constant"
    let rs ← f_rs.getExplicitAppArgs
    let xs ← f'_xs.getExplicitAppArgs
    if isApprox then
      unless xs.size = rs.size + 1 do
        throwError m!"{f'_name} does not have exactly one more explicit argument than {f_name}."
      let some n := xs[0]? | throwError m!"`{f'_name}` has no explicit arguments."
      let nat := const ``Nat []
      if !(← withNewMCtxDepth <| isDefEq nat (← inferType n)) then
        throwError m!"The first argument of `{f'_name}` (the approximation parameter) must have
          type {nat}"
      if ! n.isFVar then
        throwError m!"The first argument of `{f'_name}` (the approximation parameter) must be a
          free variable."
    else
      unless xs.size = rs.size do
        throwError m!"{f'_name} does not have the same number of explicit arguments as {f_name}"
    let c := if isApprox then 1 else 0
    let mut args : Array (Nat × Nat) := #[]
    for i in [:rs.size] do
      let r := rs[i]!
      let x := xs[i + c]!
      -- check if `r` is a `fvar` from an interval hypotheses in `hyps`
      if let some (x_id, pos) := r.fvarId? >>= hyps.get?
      then
        -- if `x` is an `fvar` in an interval hypothesis we need to check its replaced by its
        -- corresponding interval `fvar` in `xs`
        let some x'_id := x.fvarId?
          | throwError m!"`{x}` does not replace `{r}` in `{f'_name}`."
        if !(x_id == x'_id) then
          throwError m!"`{x}` does not replace `{r}` in `{f'_name}`."
        args := args.push (i, pos)
      else
        -- if `r` is not an `fvar` in an interval hypothesis it should be identical in its
        -- corresponding position in `xs`
        if !(← withNewMCtxDepth <| isDefEq r x) then
          throwError m!"`{r}` is not definitionally equal to `{x}`."
    let op : IntervalOp := {
      declName := declName
      opName := f'_name
      refName := f_name
      args := args
      incName := incName
      isApprox := isApprox
    }
    intervalOpsExt.add op kind

syntax (name := interval_op) ("approx_interval_op " <|> "exact_interval_op") ident : attr

initialize
  registerBuiltinAttribute {
    name  := `interval_op
    descr := "TODO"
    applicationTime := .afterTypeChecking
    add := fun op stx kind => do
      match stx with
      | `(attr | approx_interval_op $decl:ident) => (addIntervalOp decl.getId op true kind).run'
      | `(attr | exact_interval_op $decl:ident) => (addIntervalOp decl.getId op false kind).run'
      | _ => throwUnsupportedSyntax
  }

end IntervalOps

end IntervalArithmetic
