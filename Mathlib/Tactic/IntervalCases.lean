/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Mario Carneiro
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Data.Set.Intervals.Basic

/-!
# Case bash on variables in finite intervals

This file provides the tactic `interval_cases`. `interval_cases n` will:
1. inspect hypotheses looking for lower and upper bounds of the form `a ≤ n` and `n < b`
   (in `ℕ`, `ℤ`, `ℕ+`, bounds of the form `a < n` and `n ≤ b` are also allowed),
   and also makes use of lower and upper bounds found via `le_top` and `bot_le`
   (so for example if `n : ℕ`, then the bound `0 ≤ n` is automatically found).
2. call `fin_cases` on the synthesised hypothesis `n ∈ set.Ico a b`,
   assuming an appropriate `fintype` instance can be found for the type of `n`.

The variable `n` can belong to any type `α`, with the following restrictions:
* only bounds on which `expr.to_rat` succeeds will be considered "explicit" (TODO: generalise this?)
* an instance of `decidable_eq α` is available,
* an explicit lower bound can be found among the hypotheses, or from `bot_le n`,
* an explicit upper bound can be found among the hypotheses, or from `le_top n`,
* if multiple bounds are located, an instance of `linear_order α` is available, and
* an instance of `fintype set.Ico l u` is available for the relevant bounds.

You can also explicitly specify a lower and upper bound to use, as `interval_cases using hl hu`,
where the hypotheses should be of the form `hl : a ≤ n` and `hu : n < b`. In that case,
`interval_cases` calls `fin_cases` on the resulting hypothesis `h : n ∈ set.Ico a b`.
-/

set_option linter.unusedVariables false

namespace Mathlib.Tactic

open Lean Meta Elab Tactic Term Qq Int

namespace IntervalCases

structure IntervalCasesSubgoal where
  /-- The target expression, a numeral in the input type -/
  rhs : Expr
  /-- The new subgoal, of the form `⊢ x = rhs → tgt` -/
  goal : MVarId

inductive Bound
  | lt (n : ℤ)
  | le (n : ℤ)

def Bound.asLower : Bound → Int
  | .lt n => n + 1
  | .le n => n

def Bound.asUpper : Bound → Int
  | .lt n => n - 1
  | .le n => n

def parseBound (ty : Expr) : MetaM (Expr × Expr × Bool × Bool) := do
  let ty ← whnfR ty
  if ty.isAppOfArity ``Not 1 then
    let ty ← whnfR ty.appArg!
    if ty.isAppOfArity ``LT.lt 4 then
      pure (ty.appArg!, ty.appFn!.appArg!, true, false)
    else if ty.isAppOfArity ``LE.le 4 then
      pure (ty.appArg!, ty.appFn!.appArg!, false, false)
    else failure
  else if ty.isAppOfArity ``LT.lt 4 then
    pure (ty.appFn!.appArg!, ty.appArg!, true, true)
  else if ty.isAppOfArity ``LE.le 4 then
    pure (ty.appFn!.appArg!, ty.appArg!, false, true)
  else failure

structure Methods where
  initLB (e : Expr) : MetaM (Bound × Expr × Expr) := failure
  initUB (e : Expr) : MetaM (Bound × Expr × Expr) := failure
  proveLE : Expr → Expr → MetaM Expr
  proveLT : Expr → Expr → MetaM Expr
  eval : Expr → MetaM (Int × Expr × Expr)
  mkNumeral : Int → MetaM Expr

theorem of_not_lt_left [LinearOrder α] (h : ¬(a:α) < b) (eq : a = a') : b ≤ a' := eq ▸ not_lt.1 h
theorem of_not_lt_right [LinearOrder α] (h : ¬(a:α) < b) (eq : b = b') : b' ≤ a := eq ▸ not_lt.1 h
theorem of_not_le_left [LE α] (h : ¬(a:α) ≤ b) (eq : a = a') : ¬a' ≤ b := eq ▸ h
theorem of_not_le_right [LE α] (h : ¬(a:α) ≤ b) (eq : b = b') : ¬a ≤ b' := eq ▸ h
theorem of_lt_left [LinearOrder α] (h : (a:α) < b) (eq : a = a') : ¬b ≤ a' := eq ▸ not_le.2 h
theorem of_lt_right [LinearOrder α] (h : (a:α) < b) (eq : b = b') : ¬b' ≤ a := eq ▸ not_le.2 h
theorem of_le_left [LE α] (h : (a:α) ≤ b) (eq : a = a') : a' ≤ b := eq ▸ h
theorem of_le_right [LE α] (h : (a:α) ≤ b) (eq : b = b') : a ≤ b' := eq ▸ h

def Methods.getBound (m : Methods) (n : Expr) (pf : Expr) (lb : Bool) :
    MetaM (Bound × Expr × Expr) := do
  let (n', c) ← match ← parseBound (← inferType pf), lb with
    | (b, a, true, false), false =>
      let (z, a', eq) ← m.eval a; pure (b, .le z, a', ← mkAppM ``of_not_lt_left #[pf, eq])
    | (b, a, true, false), true =>
      let (z, b', eq) ← m.eval b; pure (a, .le z, b', ← mkAppM ``of_not_lt_right #[pf, eq])
    | (b, a, false, false), false =>
      let (z, a', eq) ← m.eval a; pure (b, .lt z, a', ← mkAppM ``of_not_le_left #[pf, eq])
    | (b, a, false, false), true =>
      let (z, b', eq) ← m.eval b; pure (a, .lt z, b', ← mkAppM ``of_not_le_right #[pf, eq])
    | (a, b, true, true), false =>
      let (z, b', eq) ← m.eval b; pure (a, .lt z, b', ← mkAppM ``of_lt_right #[pf, eq])
    | (a, b, true, true), true =>
      let (z, a', eq) ← m.eval a; pure (b, .lt z, a', ← mkAppM ``of_lt_left #[pf, eq])
    | (a, b, false, true), false =>
      let (z, b', eq) ← m.eval b; pure (a, .le z, b', ← mkAppM ``of_le_right #[pf, eq])
    | (a, b, false, true), true =>
      let (z, a', eq) ← m.eval a; pure (b, .le z, a', ← mkAppM ``of_le_left #[pf, eq])
  let .true ← withNewMCtxDepth <| withReducible <| isDefEq n n' | failure
  pure c

theorem le_of_not_le_of_le [LinearOrder α] (h1 : ¬hi ≤ n) (h2 : hi ≤ lo) : (n:α) ≤ lo :=
  le_trans (le_of_not_le h1) h2

def Methods.inconsistentBounds (m : Methods) (z1 z2 : Bound) (e1 e2 p1 p2 : Expr) : MetaM Expr := do
  match z1, z2 with
  | .le lo, .lt hi =>
    if lo == hi then return p2.app p1
    return p2.app (← mkAppM ``le_trans #[← m.proveLE e2 e1, p1])
  | .lt lo, .le hi =>
    if lo == hi then return p1.app p2
    return p1.app (← mkAppM ``le_trans #[p2, ← m.proveLE e2 e1])
  | .le _, .le _ => return (← m.proveLT e2 e1).app (← mkAppM ``le_trans #[p1, p2])
  | .lt lo, .lt hi =>
    if hi ≤ lo then return p1.app (← mkAppM ``le_of_not_le_of_le #[p2, ← m.proveLE e2 e1])
    throwError "TODO: hi + 1 == lo case"

def Methods.bisect (m : Methods) (g : MVarId)
    (off : ℤ) (cases : Array IntervalCasesSubgoal)
    (z1 z2 : Bound) (e1 e2 p1 p2 : Expr) : MetaM Unit := do
  g.admit

def natMethods : Methods where
  initLB (e : Q(ℕ)) :=
    pure (.le 0, q(0), q(Nat.zero_le $e))
  eval e := do
    let ⟨z, e, p⟩ := (← NormNum.derive (α := (q(ℕ) : Q(Type))) e).toRawEq
    pure (z, e, p)
  proveLE (lhs rhs : Q(ℕ)) := mkDecideProof q($lhs ≤ $rhs)
  proveLT (lhs rhs : Q(ℕ)) := mkDecideProof q($lhs < $rhs)
  mkNumeral
    | (i : Nat) => pure q($i)
    | _ => failure

def intMethods : Methods where
  eval e := do
    let ⟨z, e, p⟩ := (← NormNum.derive (α := (q(ℤ) : Q(Type))) e).toRawEq
    pure (z, e, p)
  proveLE (lhs rhs : Q(ℤ)) := mkDecideProof q($lhs ≤ $rhs)
  proveLT (lhs rhs : Q(ℤ)) := mkDecideProof q($lhs < $rhs)
  mkNumeral
    | (i : Nat) => let n : Q(ℕ) := mkRawNatLit i; pure q(OfNat.ofNat $n : ℤ)
    | .negSucc i => let n : Q(ℕ) := mkRawNatLit (i+1); pure q(-OfNat.ofNat $n : ℤ)

def intervalCases (g : MVarId) (e e' : Expr) (lbs ubs : Array Expr) (mustUseBounds := false) :
    MetaM (Array IntervalCasesSubgoal) := g.withContext do
  let α ← whnfR (← inferType e)
  let m ←
    if α.isConstOf ``Nat then pure natMethods else
    if α.isConstOf ``Int then pure intMethods else
    -- if α.isConstOf ``PNat then pure pnatMethods else
    throwError "interval_cases failed: unsupported type {α}"
  let mut lb ← try? (m.initLB e)
  for pf in lbs do
    if let some lb1 ← try? (m.getBound e pf true) then
      if lb.all (·.1.asLower < lb1.1.asLower) then
        lb := some lb1
    else if mustUseBounds then
      throwError "interval_cases failed: provided bound '{← inferType pf}' cannot be evaluated"
  let mut ub ← try? (m.initUB e)
  for pf in ubs do
    if let some ub1 ← try? (m.getBound e pf false) then
      if ub.all (·.1.asUpper > ub1.1.asUpper) then
        ub := some ub1
    else if mustUseBounds then
      throwError "interval_cases failed: provided bound '{← inferType pf}' cannot be evaluated"
  match lb, ub with
  | some (z1, e1, p1), some (z2, e2, p2) =>
    if z1.asLower > z2.asUpper then
      (← g.exfalso).assign (← m.inconsistentBounds z1 z2 e1 e2 p1 p2)
      pure #[]
    else
      let mut goals := #[]
      let lo := z1.asLower
      let tgt ← g.getType
      let tag ← g.getTag
      for i in [:(z2.asUpper-lo+1).toNat] do
        let z := lo+i
        let rhs ← m.mkNumeral z
        let ty ← mkArrow (← mkEq e rhs) tgt
        let goal ← mkFreshExprMVar ty .syntheticOpaque (appendTag tag (toString z))
        goals := goals.push { rhs, goal := goal.mvarId! }
      m.bisect g lo goals z1 z2 e1 e2 p1 p2
      pure goals
  | none, some _ => throwError "interval_cases failed: could not find lower bound on {e'}"
  | some _, none => throwError "interval_cases failed: could not find upper bound on {e'}"
  | none, none => throwError "interval_cases failed: could not find bounds on {e'}"

end IntervalCases

open IntervalCases

/--
`interval_cases n` searches for upper and lower bounds on a variable `n`,
and if bounds are found,
splits into separate cases for each possible value of `n`.

As an example, in
```
example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
begin
  interval_cases n,
  all_goals {simp}
end
```
after `interval_cases n`, the goals are `3 = 3 ∨ 3 = 4` and `4 = 3 ∨ 4 = 4`.

You can also explicitly specify a lower and upper bound to use,
as `interval_cases using hl, hu`.
The hypotheses should be in the form `hl : a ≤ n` and `hu : n < b`,
in which case `interval_cases` calls `fin_cases` on the resulting fact `n ∈ set.Ico a b`.

You can specify a name `h` for the new hypothesis,
as `interval_cases h : n` or `interval_cases h : n using hl, hu`.
-/
syntax (name := intervalCases) "interval_cases" (ppSpace colGt atomic(binderIdent " : ")? term)?
  (" using " term ", " term)? : tactic

elab_rules : tactic
  | `(tactic| interval_cases $[$[$h :]? $e]? $[using $lb, $ub]?) => do
    let g ← getMainGoal
    let cont x g e lbs ubs mustUseBounds : TacticM Unit := do
      let goals ← IntervalCases.intervalCases g (.fvar x) e lbs ubs mustUseBounds
      let gs ← goals.mapM fun { goal, .. } => do
        if let some h := h.getD none then
          let (fv, g) ← match h with
            | `(binderIdent| $n:ident) => goal.intro n.getId
            | _ => goal.intro1
          g.withContext <| (Expr.fvar fv).addLocalVarInfoForBinderIdent h
          pure (← substCore g fv (clearH := false)).2
        else
          let (fv, g) ← goal.intro1
          pure (← substCore g fv (clearH := true)).2
      replaceMainGoal gs.toList
    match e, lb, ub with
    | e, some lb, some ub =>
      let e ← if let some e := e then Tactic.elabTerm e none else mkFreshExprMVar none
      let lb' ← Tactic.elabTerm lb none
      let ub' ← Tactic.elabTerm ub none
      let lbTy ← inferType lb'
      let ubTy ← inferType ub'
      try
        let (_, hi, _) ← parseBound lbTy
        let .true ← isDefEq e hi | failure
      catch _ => throwErrorAt lb "expected a term of the form _ < {e} or _ ≤ {e}, got {lbTy}"
      try
        let (lo, _) ← parseBound ubTy
        let .true ← isDefEq e lo | failure
      catch _ => throwErrorAt ub "expected a term of the form {e} < _ or {e} ≤ _, got {ubTy}"
      let (subst, #[x], g) ← g.generalizeHyp #[{ expr := e }] (← getLCtx).getFVarIds | unreachable!
      g.withContext do
      cont x g e #[subst.apply lb'] #[subst.apply ub'] (mustUseBounds := true)
    | some e, none, none =>
      let e ← Tactic.elabTerm e none
      let (subst, #[x], g) ← g.generalizeHyp #[{ expr := e }] (← getLCtx).getFVarIds | unreachable!
      g.withContext do
      let e := subst.apply e
      let mut lbs := #[]
      let mut ubs := #[]
      for ldecl in ← getLCtx do
        try
          let (lo, hi, _) ← parseBound ldecl.type
          if ← withNewMCtxDepth <| withReducible <| isDefEq (.fvar x) lo then
            ubs := ubs.push (.fvar ldecl.fvarId)
          else if ← withNewMCtxDepth <| withReducible <| isDefEq (.fvar x) hi then
            lbs := lbs.push (.fvar ldecl.fvarId)
          else failure
        catch _ => pure ()
      cont x g e lbs ubs (mustUseBounds := false)
    | _, _, _ => throwUnsupportedSyntax
