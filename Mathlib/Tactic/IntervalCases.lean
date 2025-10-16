/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Mario Carneiro
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Control.Basic

/-!
# Case bash on variables in finite intervals

This file provides the tactic `interval_cases`. `interval_cases n` will:
1. inspect hypotheses looking for lower and upper bounds of the form `a ≤ n` or `a < n` and `n < b`
   or `n ≤ b`, including the bound `0 ≤ n` for `n : ℕ` automatically.
2. call `fin_cases` on the synthesised hypothesis `n ∈ Set.Ico a b`,
   assuming an appropriate `Fintype` instance can be found for the type of `n`.

Currently, `n` must be of type `ℕ` or `ℤ` (TODO: generalize).

You can also explicitly specify a lower and upper bound to use, as `interval_cases using hl hu`,
where the hypotheses should be of the form `hl : a ≤ n` and `hu : n < b`. In that case,
`interval_cases` calls `fin_cases` on the resulting hypothesis `h : n ∈ Set.Ico a b`.
-/

namespace Mathlib.Tactic

open Lean Meta Elab Term Qq Int

namespace IntervalCases

/-- The result of `interval_cases` is a list of goals,
one for each integer value between the bounds. -/
structure IntervalCasesSubgoal where
  /-- The target expression, a numeral in the input type -/
  rhs : Expr
  /-- The numeric value of the target expression -/
  value : Int
  /-- The new subgoal, of the form `⊢ x = rhs → tgt` -/
  goal : MVarId

/--
A `Bound` represents the result of analyzing a lower or upper bound expression.
If `e` is the scrutinee expression, then a lower bound expression like `3 < e`
is normalized to `¬e ≤ 3` and represented as `.lt 3`, and an upper bound expression
like `e ≤ 5` is represented as `.le 5`.
-/
inductive Bound
  /-- A strictly less-than lower bound `n ≱ e` or upper bound `e ≱ n`. (`interval_cases` uses
  less-equal exclusively, so less-than bounds are actually written as not-less-equal
  with flipped arguments.) -/
  | lt (n : ℤ)
  /-- A less-than-or-equal lower bound `n ≤ e` or upper bound `e ≤ n`. -/
  | le (n : ℤ)

/--
Assuming `Bound` represents a lower bound, this returns the (inclusive)
least integer value which is allowed. So `3 ≤ e` means the lower bound is 3 and
`3 < e` means the lower bound is `4`.
-/
def Bound.asLower : Bound → ℤ
  | .lt n => n + 1
  | .le n => n

/--
Assuming `Bound` represents an upper bound, this returns the (inclusive)
greatest integer value which is allowed. So `e ≤ 3` means the lower bound is 3 and
`e < 3` means the upper bound is `2`. Note that in the case of `e < 0` on `Nat`
the upper bound is `-1`, which is not representable as a `Nat`;
this is why we have to treat the `.lt` and `.le` cases separately instead of normalizing
everything to `.le` bounds.
-/
def Bound.asUpper : Bound → ℤ
  | .lt n => n - 1
  | .le n => n

/--
Given a type `ty` (the type of a hypothesis in the context or a provided expression),
attempt to parse it as an inequality, and return `(a, b, strict, positive)`, where
`positive` means it is a negated inequality and `strict` means it is a strict inequality
(`a < b` or `a ≱ b`). `a` is always the lesser argument and `b` the greater one.
-/
def parseBound (ty : Expr) : MetaM (Expr × Expr × Bool × Bool) := do
  let ty ← whnfR ty
  if ty.isAppOfArity ``Not 1 then
    let ty ← whnfR ty.appArg!
    if ty.isAppOfArity ``LT.lt 4 then
      pure (ty.appArg!, ty.appFn!.appArg!, false, false)
    else if ty.isAppOfArity ``LE.le 4 then
      pure (ty.appArg!, ty.appFn!.appArg!, true, false)
    else failure
  else if ty.isAppOfArity ``LT.lt 4 then
    pure (ty.appFn!.appArg!, ty.appArg!, true, true)
  else if ty.isAppOfArity ``LE.le 4 then
    pure (ty.appFn!.appArg!, ty.appArg!, false, true)
  else failure

/-- A "typeclass" (not actually a class) of methods for the type-specific handling of
`interval_cases`. To add support for a new type, you have to implement this interface and add
a dispatch case for it in `intervalCases`. -/
structure Methods where
  /-- Given `e`, construct `(bound, n, p)` where `p` is a proof of `n ≤ e` or `n < e`
  (characterized by `bound`), or `failure` if the type is not lower-bounded. -/
  initLB (e : Expr) : MetaM (Bound × Expr × Expr) := failure
  /-- Given `e`, construct `(bound, n, p)` where `p` is a proof of `e ≤ n` or `e < n`
  (characterized by `bound`), or `failure` if the type is not upper-bounded. -/
  initUB (e : Expr) : MetaM (Bound × Expr × Expr) := failure
  /-- Given `a, b`, prove `a ≤ b` or fail. -/
  proveLE : Expr → Expr → MetaM Expr
  /-- Given `a, b`, prove `a ≱ b` or fail. -/
  proveLT : Expr → Expr → MetaM Expr
  /-- Given `a, b, a', p` where `p` proves `a ≱ b` and `a' := a+1`, prove `a' ≤ b`. -/
  roundUp : Expr → Expr → Expr → Expr → MetaM Expr
  /-- Given `a, b, b', p` where `p` proves `a ≱ b` and `b' := b-1`, prove `a ≤ b'`. -/
  roundDown : Expr → Expr → Expr → Expr → MetaM Expr
  /-- Given `e`, return `(z, n, p)` where `p : e = n` and `n` is a numeral
  appropriate for the type denoting the integer `z`. -/
  eval : Expr → MetaM (Int × Expr × Expr)
  /-- Construct the canonical numeral for integer `z`, or fail if `z` is out of range. -/
  mkNumeral : Int → MetaM Expr

variable {α : Type*} {a b a' b' : α}

theorem of_not_lt_left [LinearOrder α] (h : ¬(a : α) < b) (eq : a = a') : b ≤ a' := eq ▸ not_lt.1 h
theorem of_not_lt_right [LinearOrder α] (h : ¬(a : α) < b) (eq : b = b') : b' ≤ a := eq ▸ not_lt.1 h
theorem of_not_le_left [LE α] (h : ¬(a : α) ≤ b) (eq : a = a') : ¬a' ≤ b := eq ▸ h
theorem of_not_le_right [LE α] (h : ¬(a : α) ≤ b) (eq : b = b') : ¬a ≤ b' := eq ▸ h
theorem of_lt_left [LinearOrder α] (h : (a : α) < b) (eq : a = a') : ¬b ≤ a' := eq ▸ not_le.2 h
theorem of_lt_right [LinearOrder α] (h : (a : α) < b) (eq : b = b') : ¬b' ≤ a := eq ▸ not_le.2 h
theorem of_le_left [LE α] (h : (a : α) ≤ b) (eq : a = a') : a' ≤ b := eq ▸ h
theorem of_le_right [LE α] (h : (a : α) ≤ b) (eq : b = b') : a ≤ b' := eq ▸ h

/--
Given a proof `pf`, attempts to parse it as an upper (`lb = false`) or lower (`lb = true`)
bound on `n`. If successful, it returns `(bound, n, pf')` where `n` is a numeral and
`pf'` proves `n ≤ e` or `n ≱ e` (as described by `bound`).
-/
def Methods.getBound (m : Methods) (e : Expr) (pf : Expr) (lb : Bool) :
    MetaM (Bound × Expr × Expr) := do
  let (e', c) ← match ← parseBound (← inferType pf), lb with
    | (b, a, false, false), false =>
      let (z, a', eq) ← m.eval a; pure (b, .le z, a', ← mkAppM ``of_not_lt_left #[pf, eq])
    | (b, a, false, false), true =>
      let (z, b', eq) ← m.eval b; pure (a, .le z, b', ← mkAppM ``of_not_lt_right #[pf, eq])
    | (a, b, false, true), false =>
      let (z, b', eq) ← m.eval b; pure (a, .le z, b', ← mkAppM ``of_le_right #[pf, eq])
    | (a, b, false, true), true =>
      let (z, a', eq) ← m.eval a; pure (b, .le z, a', ← mkAppM ``of_le_left #[pf, eq])
    | (b, a, true, false), false =>
      let (z, a', eq) ← m.eval a; pure (b, .lt z, a', ← mkAppM ``of_not_le_left #[pf, eq])
    | (b, a, true, false), true =>
      let (z, b', eq) ← m.eval b; pure (a, .lt z, b', ← mkAppM ``of_not_le_right #[pf, eq])
    | (a, b, true, true), false =>
      let (z, b', eq) ← m.eval b; pure (a, .lt z, b', ← mkAppM ``of_lt_right #[pf, eq])
    | (a, b, true, true), true =>
      let (z, a', eq) ← m.eval a; pure (b, .lt z, a', ← mkAppM ``of_lt_left #[pf, eq])
  let .true ← withNewMCtxDepth <| withReducible <| isDefEq e e' | failure
  pure c

theorem le_of_not_le_of_le {hi n lo : α} [LinearOrder α] (h1 : ¬hi ≤ n) (h2 : hi ≤ lo) :
    (n:α) ≤ lo :=
  le_trans (le_of_not_ge h1) h2

/--
Given `(z1, e1, p1)` a lower bound on `e` and `(z2, e2, p2)` an upper bound on `e`,
such that the distance between the bounds is negative, returns a proof of `False`.
-/
def Methods.inconsistentBounds (m : Methods)
    (z1 z2 : Bound) (e1 e2 p1 p2 e : Expr) : MetaM Expr := do
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
    let e3 ← m.mkNumeral (hi - 1)
    let p3 ← m.roundDown e e2 e3 p2
    return p1.app (← mkAppM ``le_trans #[p3, ← m.proveLE e3 e1])

/--
Given `(z1, e1, p1)` a lower bound on `e` and `(z2, e2, p2)` an upper bound on `e`, such that the
distance between the bounds matches the number of `cases` in the subarray (which must be positive),
proves the goal `g` using the metavariables in the array by recursive bisection.
This is the core of the tactic, producing a case tree of if statements which bottoms out
at the `cases`.
-/
partial def Methods.bisect (m : Methods) (g : MVarId) (cases : Subarray IntervalCasesSubgoal)
    (z1 z2 : Bound) (e1 e2 p1 p2 e : Expr) : MetaM Unit := g.withContext do
  if 1 < cases.size then
    let tgt ← g.getType
    let mid := cases.size / 2
    let z3 := z1.asLower + mid
    let e3 ← m.mkNumeral z3
    let le ← mkAppM ``LE.le #[e3, e]
    let g₁ ← mkFreshExprMVar (← mkArrow (mkNot le) tgt) .syntheticOpaque
    let g₂ ← mkFreshExprMVar (← mkArrow le tgt) .syntheticOpaque
    g.assign <| ← mkAppM ``dite #[le, g₂, g₁]
    let (x₁, g₁) ← g₁.mvarId!.intro1
    m.bisect g₁ cases[:mid] z1 (.lt z3) e1 e3 p1 (.fvar x₁) e
    let (x₂, g₂) ← g₂.mvarId!.intro1
    m.bisect g₂ cases[mid:] (.le z3) z2 e3 e2 (.fvar x₂) p2 e
  else if _x : 0 < cases.size then
    let { goal, rhs, .. } := cases[0]
    let pf₁ ← match z1 with | .le _ => pure p1 | .lt _ => m.roundUp e1 e rhs p1
    let pf₂ ← match z2 with | .le _ => pure p2 | .lt _ => m.roundDown e e2 rhs p2
    g.assign (.app (.mvar goal) (← mkAppM ``le_antisymm #[pf₂, pf₁]))
  else panic! "no goals"

/-- A `Methods` implementation for `ℕ`.
This tells `interval_cases` how to work on natural numbers. -/
def natMethods : Methods where
  initLB (e : Q(ℕ)) :=
    pure (.le 0, q(0), q(Nat.zero_le $e))
  eval (e : Q(ℕ)) := do
    let ⟨z, e, p⟩ := (← NormNum.derive q($e)).toRawIntEq.get!
    pure (z, e, p)
  proveLE (lhs rhs : Q(ℕ)) := mkDecideProofQ q($lhs ≤ $rhs)
  proveLT (lhs rhs : Q(ℕ)) := mkDecideProofQ q(¬$rhs ≤ $lhs)
  roundUp (lhs rhs _ : Q(ℕ)) (p : Q(¬$rhs ≤ $lhs)) := pure q(Nat.gt_of_not_le $p)
  roundDown (lhs _ rhs' : Q(ℕ)) (p : Q(¬Nat.succ $rhs' ≤ $lhs)) := pure q(Nat.ge_of_not_lt $p)
  mkNumeral
    | (i : ℕ) => pure q($i)
    | _ => failure

theorem _root_.Int.add_one_le_of_not_le {a b : ℤ} (h : ¬b ≤ a) : a + 1 ≤ b :=
  Int.add_one_le_iff.2 (Int.not_le.1 h)
theorem _root_.Int.le_sub_one_of_not_le {a b : ℤ} (h : ¬b ≤ a) : a ≤ b - 1 :=
  Int.le_sub_one_iff.2 (Int.not_le.1 h)

/-- A `Methods` implementation for `ℤ`.
This tells `interval_cases` how to work on integers. -/
def intMethods : Methods where
  eval (e : Q(ℤ)) := do
    let ⟨z, e, p⟩ := (← NormNum.derive q($e)).toRawIntEq.get!
    pure (z, e, p)
  proveLE (lhs rhs : Q(ℤ)) := mkDecideProofQ q($lhs ≤ $rhs)
  proveLT (lhs rhs : Q(ℤ)) := mkDecideProofQ q(¬$rhs ≤ $lhs)
  roundUp (lhs rhs _ : Q(ℤ)) (p : Q(¬$rhs ≤ $lhs)) := pure q(Int.add_one_le_of_not_le $p)
  roundDown (lhs rhs _ : Q(ℤ)) (p : Q(¬$rhs ≤ $lhs)) := pure q(Int.le_sub_one_of_not_le $p)
  mkNumeral
    | (i : Nat) => let n : Q(ℕ) := mkRawNatLit i; pure q(OfNat.ofNat $n : ℤ)
    | .negSucc i => let n : Q(ℕ) := mkRawNatLit (i+1); pure q(-OfNat.ofNat $n : ℤ)

/--
`intervalCases` proves goal `g` by splitting into cases for each integer between the given bounds.

Parameters:
* `g`: the goal, which can have any type `⊢ tgt` (it works in both proofs and programs)
* `e`: the scrutinee, the expression we are proving is bounded between integers
* `e'`: a version of `e` used for error messages. (This is used by the `interval_cases` frontend
  tactic because it uses a fresh variable for `e`, so it is more helpful to show the
  pre-generalized expression in error messages.)
* `lbs`: A list of candidate lower bound expressions.
  The tactic will automatically pick the best lower bound it can find from the list.
* `ubs`: A list of candidate upper bound expressions.
  The tactic will automatically pick the best upper bound it can find from the list.
* `mustUseBounds`: If true, the tactic will fail if it is unable to parse any of the
  given `ubs` or `lbs` into bounds. If false (the default), these will be silently skipped
  and an error message is only produced if we could not find any bounds (including those supplied
  by the type itself, e.g. if we are working over `Nat` or `Fin n`).

Returns an array of `IntervalCasesSubgoal`, one per subgoal. A subgoal has the following fields:
* `rhs`: the numeral expression for this case
* `value`: the integral value of `rhs`
* `goal`: the subgoal of type `⊢ e = rhs → tgt`

Note that this tactic does not perform any substitution or introduction steps -
all subgoals are in the same context as `goal` itself.
-/
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
      (← g.exfalso).assign (← m.inconsistentBounds z1 z2 e1 e2 p1 p2 e)
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
        let goal ← mkFreshExprMVar ty .syntheticOpaque (appendTag tag (.mkSimple (toString z)))
        goals := goals.push { rhs, value := z, goal := goal.mvarId! }
      m.bisect g goals.toSubarray z1 z2 e1 e2 p1 p2 e
      pure goals
  | none, some _ => throwError "interval_cases failed: could not find lower bound on {e'}"
  | some _, none => throwError "interval_cases failed: could not find upper bound on {e'}"
  | none, none => throwError "interval_cases failed: could not find bounds on {e'}"

end IntervalCases

open IntervalCases Tactic

/--
`interval_cases n` searches for upper and lower bounds on a variable `n`,
and if bounds are found,
splits into separate cases for each possible value of `n`.

As an example, in
```
example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 := by
  interval_cases n
  all_goals simp
```
after `interval_cases n`, the goals are `3 = 3 ∨ 3 = 4` and `4 = 3 ∨ 4 = 4`.

You can also explicitly specify a lower and upper bound to use,
as `interval_cases using hl, hu`.
The hypotheses should be in the form `hl : a ≤ n` and `hu : n < b`,
in which case `interval_cases` calls `fin_cases` on the resulting fact `n ∈ Set.Ico a b`.

You can specify a name `h` for the new hypothesis,
as `interval_cases h : n` or `interval_cases h : n using hl, hu`.
-/
syntax (name := intervalCases) "interval_cases" (ppSpace colGt atomic(binderIdent " : ")? term)?
  (" using " term ", " term)? : tactic

elab_rules : tactic
  | `(tactic| interval_cases $[$[$h :]? $e]? $[using $lb, $ub]?) => do
    let g ← getMainGoal
    let cont x h? subst g e lbs ubs mustUseBounds : TacticM Unit := do
      let goals ← IntervalCases.intervalCases g (.fvar x) e lbs ubs mustUseBounds
      let gs ← goals.mapM fun { goal, .. } => do
        let (fv, g) ← goal.intro1
        let (subst, g) ← substCore g fv (fvarSubst := subst)
        if let some hStx := h.getD none then
          if let some fv := h? then
            g.withContext <| (subst.get fv).addLocalVarInfoForBinderIdent hStx
        pure g
      replaceMainGoal gs.toList
    g.withContext do
    let hName? := (h.getD none).map fun
      | `(binderIdent| $n:ident) => n.getId
      | _ => `_
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
      let (subst, xs, g) ← g.generalizeHyp #[{ expr := e, hName? }] (← getFVarIdsAt g)
      g.withContext do
      cont xs[0]! xs[1]? subst g e #[subst.apply lb'] #[subst.apply ub'] (mustUseBounds := true)
    | some e, none, none =>
      let e ← Tactic.elabTerm e none
      let (subst, xs, g) ← g.generalizeHyp #[{ expr := e, hName? }] (← getFVarIdsAt g)
      let x := xs[0]!
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
      cont x xs[1]? subst g e lbs ubs (mustUseBounds := false)
    | _, _, _ => throwUnsupportedSyntax

end Mathlib.Tactic
