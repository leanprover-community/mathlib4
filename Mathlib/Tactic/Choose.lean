import Lean
import Mathlib.Util.Tactic
import Mathlib.Lean.Expr.Basic


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
        let ((neFail : ElimStatus), (nonemp : Option Expr)) ← if nondep
          then do
          let ne := (Expr.const ``Nonempty [u]).app α
          match ← synthInstance? ne with
          | some e => pure (.success, some e)
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
        let e1 ← mkLambdaFVars ctxt $ mkApp (.const ``And.left []) (mkAppN h ctxt)
        _
      -- TODO: support Σ, × ?
      | _, _ => throwError "expected a term of the shape `∀xs, ∃a, p xs a` or `∀xs, p xs ∧ q xs`"

def choose1WithInfo (g : MVarId) (nondep : Bool) (h : Option Expr) (data : Ident) :
  TermElabM (ElimStatus × MVarId) := do
  let (status, fvar, g) ← choose1 g nondep h data.getId
  g.withContext do
    Elab.Term.addLocalVarInfo data fvar
  pure (status, g)

def choose (nondep : Bool) (h : Option Expr) :
  List Ident → ElimStatus → MVarId → TermElabM (Except (List Expr) MVarId)
| [], _, _ => throwError "expect list of variables"
| [n], status, g =>
  match nondep, status with
  | true, .failure tys => pure (.error tys)   -- We expected some elimination, but it didn't happen.
  | _, _ => do
    let (fvar, g) ← g.intro n.getId
    g.withContext do
      Elab.Term.addLocalVarInfo n (.fvar fvar)
    return .ok g
| (n::ns), status, g => do
  let (status', g) ← choose1WithInfo g nondep h n
  choose nondep none ns (status.merge status') g

elab "choose1 " data:ident spec:ident " using " h:term : tactic =>
  withMainContext do
    let h ← Elab.Tactic.elabTerm h none
    replaceMainGoal [(← choose1WithInfo (← getMainGoal) false h data).2]
    evalTactic $ ← `(tactic|intro $spec:ident)

elab "choose" b:"!"? ids:ident+ " using " h:term : tactic =>
  withMainContext do
    let h ← Elab.Tactic.elabTerm h none
    match ← choose b.isSome h ids.toList (.failure []) (← getMainGoal) with
    | .ok g => replaceMainGoal [g]
    | .error tys =>
      let gs ← tys.mapM (fun ty => Expr.mvarId! <$> (mkFreshExprMVar (some ty)))
      setGoals gs
      throwError "choose!: failed to synthesize any nonempty instances"

-- elab "choose!" ids:ident+ " using " h:term : tactic =>
--   withMainContext do
--     let h ← Elab.Tactic.elabTerm h none
--     match ← choose true h ids.toList (.failure []) (← getMainGoal) with
--     | .ok g => replaceMainGoal [g]
--     | .error tys =>
--       let gs ← tys.mapM (fun ty => Expr.mvarId! <$> (mkFreshExprMVar (some ty)))
--       setGoals gs
--       throwError "choose!: failed to synthesize any nonempty instances"

example {α : Type} (h : ∀n m : α, n = m → ∃i j : Nat, i ≠ j) : True :=
by
  -- revert h
  -- choose i j h
  choose ! i j h' using h
  -- choose1 i h' using h
  -- choose1 j ignoreme using h'
  -- clear ignoreme
  sorry
  -- guard_hyp i : ∀n m : ℕ, n < m → ℕ,
  -- guard_hyp j : ∀n m : ℕ, n < m → ℕ,
  -- guard_hyp h : ∀ (n m : ℕ) (h : n < m), m = n + i n m h ∨ m + j n m h = n,
  -- trivial
