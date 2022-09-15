import Lean
import Mathlib.Util.Tactic
import Mathlib.Lean.Expr.Basic


open Lean Lean.Meta Elab.Term Elab.Tactic

namespace Tactic

namespace Choose

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

def choose1 (nondep : Bool) (h : Option Expr) (data : Name) :
  TacticM ElimStatus := do
  let g ← getMainGoal
  let (g, h) ← match h with
  | some e => pure (g, e)
  | none   => do
    let (e, g) ← g.intro1P
    pure (g, .fvar e)
  g.withContext do
    let h ← instantiateMVars h
    let t ← inferType h
    forallTelescopeReducing t $ fun ctxt t => do
      let t ← withTransparency .all (whnf t)
      match t.getAppFnArgs with
      | (`Exists, #[α, p]) => do
        let ne_fail : ElimStatus := .failure []
        let nonemp : Option Expr := none
        let ctxt' ← if nonemp.isSome then ctxt.filterM (fun e => not <$> isProof e) else pure ctxt
        let data_ty ← mkForallFVars ctxt' α
        let data_val ← mkAppM ``Classical.choose #[mkAppN h ctxt]
        let (d, g) ← (← g.assert data data_ty data_val).intro1P
        let spec_ty ← mkForallFVars ctxt (p.app (mkAppN (.fvar d) ctxt')).headBeta
        let spec_val ← mkAppM ``Classical.choose_spec #[mkAppN h ctxt]
        let mut g ← g.assert .anonymous spec_ty spec_val
        match h with
        | .fvar v => g ← g.clear v
        | _ => pure ()
        replaceMainGoal [g]
        return ne_fail
        | (`And, #[p, q]) => throwError "not implemented yet"
        -- TODO: support Σ, × ?
        | _ => throwError "expected a term of the shape `∀xs, ∃a, p xs a` or `∀xs, p xs ∧ q xs`"

def choose (nondep : Bool) (h : Option Expr) : List Name → ElimStatus → TacticM Unit
| [], _ => throwError "expect list of variables"
| [n], status => match nondep, status with
  | true, .failure tys => do    -- We expected some elimination, but it didn't happen.
    let gs ← tys.mapM (fun ty => Expr.mvarId! <$> (mkFreshExprMVar (some ty)))
    setGoals gs
    throwError "choose!: failed to synthesize any nonempty instances"
  | _, _ => do
    let g ← getMainGoal
    replaceMainGoal [(← g.intro n).2]
| (n::ns), status => do
  let status' ← choose1 nondep h n
  choose nondep none ns (status.merge status')

elab "choose1 " data:ident spec:ident " using " h:term : tactic =>
  withMainContext do
    let h ← Elab.Tactic.elabTerm h none
    _ ← choose1 false h data.getId
    evalTactic $ ← `(tactic|intro $spec:ident)

elab "choose" first:ident rest:ident* " using " h:term : tactic =>
  withMainContext do
    let h ← Elab.Tactic.elabTerm h none
    _ ← choose false h ((first :: rest.toList).map (fun i => i.getId)) (.failure [])


example (h : ∀n m : Nat, n < m → ∃i j, m = n + i ∨ m + j = n) : True :=
by
  choose i j h' using h
  -- choose1 i h' using h
  -- choose1 j ignoreme using h'
  -- clear ignoreme
  trivial
  -- guard_hyp i : ∀n m : ℕ, n < m → ℕ,
  -- guard_hyp j : ∀n m : ℕ, n < m → ℕ,
  -- guard_hyp h : ∀ (n m : ℕ) (h : n < m), m = n + i n m h ∨ m + j n m h = n,
  -- trivial
