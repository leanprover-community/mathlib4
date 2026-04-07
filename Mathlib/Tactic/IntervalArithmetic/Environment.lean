module

public import Mathlib.Order.Interval.Set.Defs

public section

open Set

namespace IntervalArithmetic

variable {α β : Type*}

structure Interval (α : Type*) where
  lb : α
  ub : α

def Interval.toSet [Preorder β] (φ : α → β) (x : Interval α) : Set β := Set.Icc (φ x.lb) (φ x.ub)

section Environment

open Lean Meta

structure IntervalArithmeticDecl where
  name : Name
  intervalType : Name
  setType : Name
  embedding : Name
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

def addIntervalArithmeticDecl
    (intervalType : Name) (setType : Name) (embedding : Name) (declName : Name) :
    MetaM Unit := do
  let α ← mkConstWithFreshMVarLevels intervalType
  let β ← mkConstWithFreshMVarLevels setType
  let embedding_type ← inferType (← mkConstWithFreshMVarLevels embedding)
  let expected_type ← mkArrow α β
  /- check that `embedding` is the name of a function from a type of name `intervalType`
  to a type of name `setType` -/
  unless ← isDefEq embedding_type (expected_type) do
    throwError m!"`{embedding}` has type {embedding_type}, but expected {expected_type}"
  -- check that we can infer `Preorder β`
  let _ ← synthInstance (← mkAppM ``Preorder #[β])
  let decl : IntervalArithmeticDecl := {
    name := declName
    intervalType := intervalType
    setType := setType
    embedding := embedding
  }
  intervalArithmeticDeclsExt.add decl

def getIntervalArithmeticDecl? (declName : Name) : MetaM (Option IntervalArithmeticDecl) := do
  let s := intervalArithmeticDeclsExt.getState  (← getEnv)
  return s.decls.find? declName

structure IntervalOp where
  /-- The interval arithmetic declaration that the `IntervalOp` belongs to. -/
  declName : Name
  /-- Name of the `Interval` operation. -/
  opName : Name
  /-- Name of the reference operation. -/
  refName : Name
  /-- The position of the interval arguments in `refName` -/
  args : Array Nat
  /-- Name of the inclusion theorem. -/
  incName : Name
  /-- The position of the interval hypotheses in `incName` -/
  intervalHypPos : Array Nat
  deriving Inhabited

structure IntervalOps where
  ops : Std.HashMap (Name × Name) IntervalOp := {}

abbrev IntervalOpsExt := SimpleScopedEnvExtension IntervalOp IntervalOps

initialize intervalOpsExt : IntervalOpsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun os o =>
      {os with ops := os.ops.insert (o.declName, o.refName) o}
  }
def IntervaltoSet? (e : Expr) : Option (Expr × Expr) :=
  if !(e.isAppOfArity' ``Interval.toSet 5) then none
  else some ⟨e.getArg!' 4, e.getArg!' 3⟩

def memSet? (e : Expr) : Option (Expr × Expr) :=
  if !(e.isAppOfArity' ``Membership.mem 5) then none
  else some ⟨e.getArg!' 4, e.getArg!' 3⟩

def memIntervaltoSet? (e : Expr) : Option (Expr × Expr × Expr) := do
  let (x,s) ← memSet? e
  let (I, φ) ← IntervaltoSet? s
  return (x, I, φ)

def intervalHyp? (e : Expr) : Option (FVarId × FVarId × Expr) := do
  let (x, I, φ) ← memIntervaltoSet? e
  return (← x.fvarId?, ← I.fvarId?, φ)

def _root_.Lean.Expr.getExplicitAppArgs (e : Expr) : MetaM (Array Expr) := do
  let args := e.getAppArgs
  let param_info := (← getFunInfo e.getAppFn).paramInfo
  return Prod.fst <$> (args.zip param_info).filter (fun ⟨_, p⟩ ↦ p.isExplicit)

/- TODO Notes:

- May want to allow for no Nat parameter (when approximation not needed) and handle both cases
  seperately
- Maybe use the name or expression for `Nat` in errors so that it is pretty printed based on
  context.

-/

def addIntervalOp (declName : Name) (incName : Name) :
    MetaM Unit := do
  let some decl ← getIntervalArithmeticDecl? declName
    | throwError m!"Unknown interval arithmetic declaration `{declName}`."
  let φ ← mkConstWithFreshMVarLevels decl.embedding
  let (hs, _, conc) ← forallMetaTelescope (← getConstInfo incName).type
  -- check that the conclusion is of the form `_ ∈ _.toSet _`
  let some ⟨fx, f'I, φ'⟩ := memIntervaltoSet? conc
    | throwError m!"The conclusion of `{incName}` is not of the form `_ ∈ _.toSet _."
  -- check that the embedding in the conclusion matches the embedding in the declaration
  if !(← withNewMCtxDepth <| isDefEq φ φ') then
    throwError m!"{φ'} is not definitionally equal to `{decl.embedding}.`"
  -- identify interval hypotheses
  let mut hyps : FVarIdMap FVarId := {}
  let mut hyps_used : FVarIdMap (Bool × Nat) := {}
  for i in [:hs.size] do
    let h := hs[i]!
    if let some (x, I, φ') := intervalHyp? (← inferType h) then
      if (← withNewMCtxDepth <| isDefEq φ φ') then
        if hyps.contains x then
          throwError m!"`{mkFVar x}` appears in more than one interval hypotheses."
        else
          hyps := hyps.insert x I
          hyps_used := hyps_used.insert x (false, i)
  let some f_name := fx.getAppFn.constName?
    | throwError m!"`{fx}` is not application of a constant."
  let some f'_name := f'I.getAppFn.constName?
    | throwError m!"`{f'I}` is not an application of a constant."
  -- We get the explicit arguments in `fx` and `f'I`.
  let xs ← fx.getExplicitAppArgs
  let Is ← f'I.getExplicitAppArgs
  -- check that `I` has exactly one more argument than `x`
  if Is.size ≠ xs.size + 1 then
    throwError m!"`{f'_name}` does not have exactly one more argument than `{f_name}`"
  -- check that the first entry of `I` is a `fvar` of type `Nat`
  let some n := Is[0]? | throwError m!"`{f'_name}` must have a Nat argument."
  if !(← withNewMCtxDepth <| isDefEq (.const ``Nat []) (← inferType n)) then
    throwError m!"The first argument of `{f'_name}` must have type `Nat`."
  if ! n.isFVar then
    throwError m!"{n} must be a free-variable `Nat`."
  let mut interval_args := #[]
  let mut intervalHypPos := #[]
  for i in [:xs.size] do
    let arg := xs[i]!
    let interval := Is[i+1]!
    if let some arg_id := arg.fvarId? then
      if let some interval_id := hyps.get? arg_id then
        /- if `arg` is an `fvar` in an interval hypotheses we need to check its replaced by its
        corresponding interval `fvar` in `Is` -/
        let some interval'_id := interval.fvarId?
          | throwError m!"`{interval}` must replace `{arg}` in `{f'_name}`."
        if !(interval_id == interval'_id) then
          throwError m!"`{interval}` must replace `{arg}` in `{f'_name}`."
        interval_args := interval_args.push i
        let ⟨is_used, pos⟩ := hyps_used.get! arg_id
        if ! is_used then
          intervalHypPos := intervalHypPos.push pos
          hyps_used := hyps_used.modify arg_id (fun (_, j) ↦ (true, j))
    /- if `arg` is not an `fvar` in an interval hypotheses it should be identical in its
    corresponding position in `Is`. -/
    else if !(← withNewMCtxDepth <| isDefEq interval arg) then
      throwError m!"`{arg}` and `{interval}` must match."
  let op : IntervalOp := {
    declName := declName
    opName := f'_name
    refName := f_name
    args := interval_args
    incName := incName
    intervalHypPos := intervalHypPos
  }
  intervalOpsExt.add op

end Environment

end IntervalArithmetic
