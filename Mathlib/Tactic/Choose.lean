import Lean
import Mathlib.Util.Tactic
import Mathlib.Tactic.ShowTerm


open Lean Lean.Meta Elab.Term Elab.Tactic

namespace function

open Classical in
/-- `sometimes f` evaluates to some value of `f`, if it exists. This function is especially
interesting in the case where `α` is a proposition, in which case `f` is necessarily a
constant function, so that `sometimes f = f a` for all `a`. -/
noncomputable def sometimes {α β} [Nonempty β] (f : α → β) : β :=
if h : Nonempty α then f (choice h) else choice ‹_›

theorem sometimes_eq {p : Prop} {α} [Nonempty α] (f : p → α) (a : p) : sometimes f = f a :=
dif_pos ⟨a⟩

theorem sometimes_spec {p : Prop} {α} [Nonempty α]
  (P : α → Prop) (f : p → α) (a : p) (h : P (f a)) : P (sometimes f) :=
(sometimes_eq f a).symm ▸ h

end function

namespace Lean /- MOVE THIS -/

namespace MVarId

/-- `asserts g l` asserts all the tuples in `l`,
where `l` is a list of tuples of the form `(name, type, val)`.
It returns the resulting goal.

The first element in the list `l` will be asserted first,
and the last element in the list `l` will be asserted last.
In particular, the last element will correspond to the outmost lambda
in the goal that is returned. -/
def asserts (g : MVarId) : List (Name × Expr × Expr) → MetaM MVarId
| [] => pure g
| ((n, ty, val) :: l) => do
  let g₁ ← g.assert n ty val
  asserts g₁ l

end MVarId

end Lean

namespace Tactic

namespace Choose

def mk_sometimes (u : Level) (α nonemp p : Expr) :
  List Expr → Expr × Expr → MetaM (Expr × Expr)
| [], (val, spec) => pure (val, spec)
| (e :: ctxt), (val, spec) => do
  let (val, spec) ← mk_sometimes u α nonemp p ctxt (val, spec)
  let t ← inferType e
  let b ← isProp t
  if b then do
    let val' ← mkLambdaFVars #[e] val
    pure
      (mkApp4 (Expr.const ``function.sometimes [Level.zero, u]) t α nonemp val',
      mkApp7 (Expr.const ``function.sometimes_spec [u]) t α nonemp p val' e spec)
  else pure (val, spec)

/-- Results of searching for nonempty instances,
to eliminate dependencies on propositions (`choose!`).
`success` means we found at least one instance;
`failure ts` means we didn't find instances for any `t ∈ ts`.
(`failure []` means we didn't look for instances at all.)

Rationale:
`choose!` means we are expected to succeed at least once
in eliminating dependencies on propositions.
-/
inductive ElimStatus
| success
| failure (ts : List Expr)

/-- Combine two statuses, keeping a success from either side
or merging the failures. -/
def ElimStatus.merge : ElimStatus → ElimStatus → ElimStatus
| success, _ => success
| _, success => success
| failure ts₁, failure ts₂ => failure (ts₁ ++ ts₂)

def getBinderName (e : Expr) : MetaM (Option Name) := do
  match ← withReducible (whnf e) with
  | .forallE (binderName := n) .. | .lam (binderName := n) .. => pure (some n)
  | _ => pure none

def mkFreshNameFrom (orig base : Name) : CoreM Name :=
  if orig = `_ then mkFreshUserName base else pure orig

def choose1 (g : MVarId) (nondep : Bool) (h : Option Expr) (data : Name) :
  MetaM (ElimStatus × Expr × MVarId) := do
  let (g, h) ← match h with
  | some e => pure (g, e)
  | none   => do
    let (e, g) ← g.intro1P
    pure (g, .fvar e)
  g.withContext do
    let h ← instantiateMVars h
    let t ← inferType h
    forallTelescopeReducing t fun ctxt t => do
      (← withTransparency .all (whnf t)).withApp fun
      | .const ``Exists [u], #[α, p] => do
        let data ← mkFreshNameFrom data ((← getBinderName p).getD `h)
        let ((neFail : ElimStatus), (nonemp : Option Expr)) ← if nondep then
          let ne := (Expr.const ``Nonempty [u]).app α
          let m ← mkFreshExprMVar ne
          let L : List (Name × Expr × Expr) ← ctxt.toList.filterMapM $ fun e => do
            let ty ← (inferType e >>= whnf)
            if (← isProof e) then return none
            pure $ some (.anonymous, (Expr.const ``Nonempty [u]).app ty, mkApp2 (Expr.const ``Nonempty.intro [u]) ty e)
          let (_, g') ← (m.mvarId!.asserts L >>= MVarId.intros)
          g'.withContext do
          match ← synthInstance? (← g'.getType) with
          | some e => do
            g'.assign e
            let m ← instantiateMVars m
            pure (.success, some m)
          | none   => pure (.failure [ne], none)
        else pure (.failure [], none)
        let ctxt' ← if nonemp.isSome then ctxt.filterM (fun e => not <$> isProof e) else pure ctxt
        let dataTy ← mkForallFVars ctxt' α
        let mut dataVal := mkApp3 (.const ``Classical.choose [u]) α p (mkAppN h ctxt)
        let mut specVal := mkApp3 (.const ``Classical.choose_spec [u]) α p (mkAppN h ctxt)
        if let some nonemp := nonemp then
          (dataVal, specVal) ← mk_sometimes u α nonemp p ctxt.toList (dataVal, specVal)
        dataVal ← mkLambdaFVars ctxt' dataVal
        specVal ← mkLambdaFVars ctxt specVal
        let (fvar, g) ← withLocalDeclD .anonymous dataTy fun d => do
          let specTy ← mkForallFVars ctxt (p.app (mkAppN d ctxt')).headBeta
          g.withContext do
          withLocalDeclD data dataTy fun d' => do
          let mvarTy ← mkArrow (specTy.replaceFVar d d') (← g.getType)
          let newMVar ← mkFreshExprSyntheticOpaqueMVar mvarTy (← g.getTag)
          g.assign <| mkApp2 (← mkLambdaFVars #[d'] newMVar) dataVal specVal
          pure (d', newMVar.mvarId!)
        let g ← match h with
        | .fvar v => g.clear v
        | _ => pure g
        return (neFail, fvar, g)
      | .const ``And _, #[p, q] => do
        let data ← mkFreshNameFrom data `h
        let e1 ← mkLambdaFVars ctxt $ mkApp3 (.const ``And.left  []) p q (mkAppN h ctxt)
        let e2 ← mkLambdaFVars ctxt $ mkApp3 (.const ``And.right []) p q (mkAppN h ctxt)
        let t1 ← inferType e1
        let t2 ← inferType e2
        let (fvar, g) ← (g.asserts [(.anonymous, t2, e2), (data, t1, e1)] >>= MVarId.intro1P)
        let g ← match h with
        | .fvar v => g.clear v
        | _ => pure g
        return (.success, .fvar fvar, g)
      -- TODO: support Σ, × ?
      | _, _ => throwError "expected a term of the shape `∀xs, ∃a, p xs a` or `∀xs, p xs ∧ q xs`"

def SourceInfo.fromRef' (ref : Syntax) (synthetic := true) : SourceInfo :=
  match ref.getPos?, ref.getTailPos? with
  | some pos, some tailPos =>
    if synthetic then .synthetic pos tailPos
    else .original "".toSubstring pos "".toSubstring tailPos
  | _,        _            => .none

def addLocalVarInfoForBinderIdent (fvar : Expr) : TSyntax ``binderIdent → TermElabM Unit
| `(binderIdent| $n:ident) =>
  Elab.Term.addLocalVarInfo n fvar
| tk => do
  let stx := mkNode ``Parser.Term.hole #[Syntax.atom (SourceInfo.fromRef' tk false) "_"] -- HACK
  Elab.Term.addLocalVarInfo stx fvar

def choose1WithInfo (g : MVarId) (nondep : Bool) (h : Option Expr) (data : TSyntax ``binderIdent) :
  TermElabM (ElimStatus × MVarId) := do
  let n := if let `(binderIdent| $n:ident) := data then n.getId else `_
  let (status, fvar, g) ← choose1 g nondep h n
  g.withContext <| addLocalVarInfoForBinderIdent fvar data
  pure (status, g)

def elabChoose (nondep : Bool) (h : Option Expr) :
  List (TSyntax ``binderIdent) → ElimStatus → MVarId → TermElabM (Except (List Expr) MVarId)
| [], _, _ => throwError "expect list of variables"
| [n], status, g =>
  match nondep, status with
  | true, .failure tys => pure (.error tys)   -- We expected some elimination, but it didn't happen.
  | _, _ => do
    let (fvar, g) ← match n with
    | `(binderIdent| $n:ident) => g.intro n.getId
    | _ => g.intro1
    g.withContext <| addLocalVarInfoForBinderIdent (.fvar fvar) n
    return .ok g
| (n::ns), status, g => do
  let (status', g) ← choose1WithInfo g nondep h n
  elabChoose nondep none ns (status.merge status') g

/-- TODO -/
syntax (name := choose) "choose" "!"? (colGt binderIdent)+ (" using " term)? : tactic
elab_rules : tactic
| `(tactic| choose $[!%$b]? $[$ids]* $[using $h]?) => withMainContext do
  let h ← h.mapM fun h => Elab.Tactic.elabTerm h none
  match ← elabChoose b.isSome h ids.toList (.failure []) (← getMainGoal) with
  | .ok g => replaceMainGoal [g]
  | .error tys =>
    let gs ← tys.mapM fun ty => Expr.mvarId! <$> mkFreshExprMVar (some ty)
    setGoals gs
    throwError "choose!: failed to synthesize any nonempty instances"

@[inheritDoc choose]
syntax "choose!" (colGt binderIdent)+ (" using " term)? : tactic
macro_rules
  | `(tactic| choose! $[$ids]* $[using $h]?) => `(tactic| choose ! $[$ids]* $[using $h]?)

example {α : Type} (h : ∀n m : α, ∀ (h : n = m), ∃i j : α, i ≠ j ∧ h = h) : True :=
by
  choose! i j _x _y using h
  trivial
