/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Simon Hudon, Thomas Murrills
-/
import Lean
import Mathlib.Tactic.Have
import Mathlib.Tactic.SolveByElim
import Mathlib.Data.List.TFAE
import Qq

/-!
# The Following Are Equivalent (TFAE)

This file provides the tactics `tfae_have` and `tfae_finish` for proving goals of the form
`TFAE [P₁, P₂, ...]`.
-/

open List Lean Meta Expr Elab.Term Elab.Tactic Mathlib.Tactic Qq

namespace Mathlib.Tactic.TFAE

/-- An arrow of the form `←`, `→`, or `↔`. -/
syntax impArrow := " → " <|> " ↔ " <|> " ← "

/--
`tfae_have` introduces hypotheses for proving goals of the form `TFAE [P₁, P₂, ...]`. Specifically,
`tfae_have i arrow j` introduces a hypothesis of type `Pᵢ arrow Pⱼ` to the local context,
where `arrow` can be `→`, `←`, or `↔`. Note that `i` and `j` are natural number indices (beginning
at 1) used to specify the propositions `P₁, P₂, ...` that appear in the `TFAE` goal list. A proof
is required afterward, typically via a tactic block.

```lean
example (h : P → R) : TFAE [P, Q, R] := by
  tfae_have 1 → 3
  · exact h
  ...
```
The resulting context now includes `tfae_1_to_3 : P → R`.

The introduced hypothesis can be given a custom name, in analogy to `have` syntax:
```lean
tfae_have h : 2 ↔ 3
```

Once sufficient hypotheses have been introduced by `tfae_have`, `tfae_finish` can be used to close
the goal.

```lean
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2
  · /- proof of P → Q -/
  tfae_have 2 → 1
  · /- proof of Q → P -/
  tfae_have 2 ↔ 3
  · /- proof of Q ↔ R -/
  tfae_finish
```
-/
syntax (name := tfaeHave) "tfae_have " (ident " : ")? num impArrow num : tactic

/--
`tfae_finish` is used to close goals of the form `TFAE [P₁, P₂, ...]` once a sufficient collection
of hypotheses of the form `Pᵢ → Pⱼ` or `Pᵢ ↔ Pⱼ` have been introduced to the local context.

`tfae_have` can be used to conveniently introduce these hypotheses; see `tfae_have`.

Example:
```lean
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2
  · /- proof of P → Q -/
  tfae_have 2 → 1
  · /- proof of Q → P -/
  tfae_have 2 ↔ 3
  · /- proof of Q ↔ R -/
  tfae_finish
```
-/
syntax (name := tfaeFinish) "tfae_finish" : tactic

/-! # Setup -/

/-- Extract a list of `Prop` expressions from an expression of the form `TFAE [P₁, P₂, ...]` as
long as `[P₁, P₂, ...]` is an explicit list. -/
partial def getTFAEList (t : Expr) : MetaM (Q(List Prop) × List Q(Prop)) := do
  let .app tfae (l : Q(List Prop)) ← whnfR t |
    throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  unless (← withNewMCtxDepth <| isDefEq tfae q(TFAE)) do
    throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  return (l, ← getExplicitList l)
where
  /-- Convert an expression representing an explicit list into a list of expressions. -/
  getExplicitList (l : Q(List Prop)) : MetaM (List Q(Prop)) := do
    match l with
    | ~q([]) => return ([] : List Expr)
    | ~q($a :: $l') => return (a :: (← getExplicitList l'))
    | e => throwError "{e} must be an explicit list of propositions"

/-! # Proof construction -/

/-- Prove an implication via solve_by_elim. -/
def proveImpl (maxDepth : Nat) (hyps : List Expr) (P P' : Q(Prop)) : MetaM Q($P → $P') := do
  let t ← mkFreshExprMVar q($P → $P')
  try
    let (h, t) ← t.mvarId!.intro (← mkFreshUserName `h)
    let [] ← SolveByElim.solveByElim { maxDepth } [] (pure (.fvar h :: hyps)) [t] | failure
  catch _ =>
    throwError "couldn't prove {P} → {P'}"
  instantiateMVars t

/-- Generate a proof of `Chain (· → ·) P l`. We assume `P : Prop` and `l : List Prop`, and that `l`
is an explicit list. -/
partial def proveChain (depth : Nat) (hyps : List Expr) (P : Q(Prop)) (l : Q(List Prop)) :
    MetaM Q(Chain (· → ·) $P $l) := do
  match l with
  | ~q([]) => return q(Chain.nil)
  | ~q($P' :: $l') =>
    have cl' : Q(Chain (· → ·) $P' $l') := ← proveChain depth hyps q($P') q($l')
    let p ← proveImpl depth hyps P P'
    return q(Chain.cons $p $cl')

/-- Attempt to prove `ilast' P' l → P` given an explicit list `l`. -/
partial def proveILast'Impl (depth : Nat) (hyps : List Expr) (P P' : Q(Prop)) (l : Q(List Prop)) :
    MetaM Q(ilast' $P' $l → $P) := do
  match l with
  | ~q([]) => proveImpl depth hyps P' P
  | ~q($P'' :: $l') => proveILast'Impl depth hyps P P'' l'

/-- Attempt to prove a statement of the form `TFAE [P₁, P₂, ...]`. -/
def proveTFAE (depth : Nat) (hyps : List Expr) (l : Q(List Prop)) : MetaM Q(TFAE $l) := do
  match l with
  | ~q([]) => return q(tfae_nil)
  | ~q([$P]) => return q(tfae_singleton $P)
  | ~q($P :: $P' :: $l') =>
    let c ← proveChain depth hyps P q($P' :: $l')
    let il ← proveILast'Impl depth hyps P P' l'
    return q(tfae_of_cycle $c $il)

/-! # `tfae_have` components -/

/-- Construct a name for a hypothesis introduced by `tfae_have`. -/
def mkTFAEHypName (i j : TSyntax `num) (arr : TSyntax ``impArrow) : MetaM Name := do
  let arr ← match arr with
  | `(impArrow| ← ) => pure "from"
  | `(impArrow| → ) => pure "to"
  | `(impArrow| ↔ ) => pure "iff"
  | _ => throwErrorAt arr "expected '←', '→', or '↔'"
  return String.intercalate "_" ["tfae", s!"{i.getNat}", arr, s!"{j.getNat}"]

open Elab in
/-- The core of `tfae_have`, which behaves like `haveLetCore` in `Mathlib.Tactic.Have`. -/
def tfaeHaveCore (goal : MVarId) (name : Option (TSyntax `ident)) (i j : TSyntax `num)
    (arrow : TSyntax ``impArrow) (t : Expr) : TermElabM (MVarId × MVarId) :=
  goal.withContext do
    let n := (Syntax.getId <$> name).getD <|← mkTFAEHypName i j arrow
    let (goal1, t, p) ← do
      let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
      pure (p.mvarId!, t, p)
    let (fv, goal2) ← (← MVarId.assert goal n t p).intro1P
    if let some stx := name then
      goal2.withContext do
        Term.addTermInfo' (isBinder := true) stx (mkFVar fv)
    pure (goal1, goal2)

/-- Turn syntax for a given index into a natural number, as long as it lies between `1` and
`maxIndex`. -/
def elabIndex (i : TSyntax `num) (maxIndex : ℕ) : TacticM ℕ := do
  let i' := i.getNat
  unless Nat.ble 1 i' && Nat.ble i' maxIndex do
    throwError "{i} must be between 1 and {maxIndex}"
  return i'

/-- Construct an expression for the type `Pj → Pi`, `Pi → Pj`, or `Pi ↔ Pj` given expressions
`Pi Pj : Q(Prop)` and `impArrow` syntax `arr`, depending on whether `arr` is `←`, `→`, or `↔`
respectively. -/
def mkImplType (Pi : Q(Prop)) (arr : TSyntax ``impArrow) (Pj : Q(Prop)) : MetaM Q(Prop) := do
  match arr with
  | `(impArrow| ← ) => pure q($Pj → $Pi)
  | `(impArrow| → ) => pure q($Pi → $Pj)
  | `(impArrow| ↔ ) => pure q($Pi ↔ $Pj)
  | _ => throwErrorAt arr "expected '←', '→', or '↔'"

/-! # Tactic implementation -/

elab_rules : tactic
| `(tactic| tfae_have $[$h:ident : ]? $i:num $arr:impArrow $j:num) => do
  let goal ← getMainGoal
  let (_, tfaeList) ← getTFAEList (← goal.getType)
  let l₀ := tfaeList.length
  let i' ← elabIndex i l₀
  let j' ← elabIndex j l₀
  let Pi := tfaeList.get! (i'-1)
  let Pj := tfaeList.get! (j'-1)
  let type ← mkImplType Pi arr Pj
  let (goal1, goal2) ← tfaeHaveCore goal h i j arr type
  replaceMainGoal [goal1, goal2]

elab_rules : tactic
| `(tactic| tfae_finish) => do
  let goal ← getMainGoal
  let (tfaeListQ, tfaeList) ← getTFAEList (← goal.getType)
  goal.withContext do
    let mut hyps := #[]
    for hyp in ← getLocalHyps do
      let ty ← inferType hyp
      if ty.isAppOfArity ``Iff 2 then
        hyps := hyps.push (← mkAppM ``Iff.mp #[hyp]) |>.push (← mkAppM ``Iff.mpr #[hyp])
      else if ty.isArrow then
        hyps := hyps.push hyp
    closeMainGoal (← proveTFAE (tfaeList.length + 1) hyps.toList tfaeListQ)
