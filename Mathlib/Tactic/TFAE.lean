import Lean
import Mathlib.Tactic.Have
import Mathlib.Tactic.SolveByElim
import Mathlib.Data.List.TFAE
import QQ.match

/-!
# The Following Are Equivalent (TFAE)

This file provides the tactics `tfae_have` and `tfae_finish` for proving goals of the form
`TFAE [P₁, P₂, ...]`.
-/

open List Lean Meta Expr Elab.Term Elab.Tactic Mathlib.Tactic Qq

namespace Mathlib.TFAE

/-- An arrow of the form `←`, `→`, or `↔`. -/
declare_syntax_cat impArrow
syntax (" → " <|> " ↔ " <|> " ← ") : impArrow

/--
`tfae_have` introduces hypotheses for proving goals of the form `TFAE [P₁, P₂, ...]`. Specifically,
`tfae_have : i arrow j` introduces a hypothesis of the form `Pᵢ arrow Pⱼ` to the tactic state,
where `arrow` can be `→`, `←`, or `↔`. Note that `i` and `j` are natural number indices (beginning
at 1) used to specify the propositions `P₁, P₂, ...` that appear in the `TFAE` goal list. A proof
is required afterward, typically via a tactic block.

Example:
```lean
example (h : P → R) : TFAE [P, Q, R] := by
  tfae_have : 1 → 3
  { exact h }
  ...
```

The introduced hypothesis can be given a name, in analogy to `have` syntax:
```lean
tfae_have h : 2 ↔ 3
```

Once sufficient hypotheses have been introduced by `tfae_have`, `tfae_finish` can be used to close
the goal.

Example:
```lean
variable (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → P) (h₃ Q ↔ R)
example : TFAE [P, Q, R] := by
  tfae_have : 1 → 2
  { exact h₁ }
  tfae_have : 2 → 1
  { exact h₁ }
  tfae_have : 2 ↔ 3
  { exact h₃ }
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
variable (P Q R : Prop)
variable (h₁ : P → Q) (h₂ : Q → P) (h₃ Q ↔ R)

example : TFAE [P, Q, R] := by
  tfae_have : 1 → 2
  { exact h₁ }
  tfae_have : 2 → 1
  { exact h₁ }
  tfae_have : 2 ↔ 3
  { exact h₃ }
  tfae_finish
```
-/
syntax (name := tfaeFinish) "tfae_finish" : tactic

partial def getTFAEList (t : Expr) : MetaM (List Q(Prop)) := do
  let .app tfae (l : Q(List Prop)) ← whnfR t |
    throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  unless (← withNewMCtxDepth <| isDefEq tfae q(TFAE)) do
    throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  let rec getExplicitList (l : Expr) : MetaM (List Expr) := do
    have l : Q(List Prop) := l
    match l with
    | ~q([]) => return ([] : List Expr)
    | ~q($a :: $l') => return (q($a) :: (← getExplicitList l'))
    | ~q($e) => throwError "{e} must be an explicit list of propositions"
  getExplicitList l

partial def getTFAEListQ (t : Expr) : MetaM Q(List Prop) := do
  let .app tfae (l : Q(List Prop)) ← whnfR t |
    throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  unless (← withNewMCtxDepth <| isDefEq tfae q(TFAE)) do
    throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  let rec guardExplicitList (l : Q(List Prop)) : MetaM Unit := do
    match l with
    | ~q([]) => return ()
    | ~q(_ :: $l') => guardExplicitList l'
    | ~q($e) => throwError "{e} must be an explicit list of propositions"
  guardExplicitList l
  return l

/-- Prove an implication via solve_by_elim. -/
def proveImpl (P P' : Q(Prop)) : TacticM Q($P → $P') := do
  let t ← mkFreshExprMVar q($P → $P')
  try
    let [] ← run t.mvarId! <| evalTactic (← `(tactic| intro; solve_by_elim [Iff.mp, Iff.mpr])) |
      failure
  catch _ =>
    throwError "couldn't prove {P} → {P'}"
  instantiateMVars t

/-- Generate a proof of `Chain (· → ·) P l`. We assume `P : Prop` and `l : List Prop`, and that `l`
is an explicit list. -/
partial def proveChain (P : Q(Prop)) (l : Q(List Prop)) :
    TacticM Q(Chain (· → ·) $P $l) := do
  match l with
  | ~q([]) => return q(Chain.nil)
  | ~q($P' :: $l') =>
    have cl' : Q(Chain (· → ·) $P' $l') := ← proveChain q($P') q($l')
    let p ← proveImpl P P'
    return q(Chain.cons $p $cl')

/-- Attempt to prove `ilast' P' l → P` given an explicit list `l`. -/
partial def proveILast'Imp (P P' : Q(Prop)) (l : Q(List Prop)) :
    TacticM Q(ilast' $P' $l → $P) := do
  match l with
  | ~q([]) => proveImpl P' P
  | ~q($P'' :: $l') => proveILast'Imp P P'' l'

/-- Attempt to prove a statement of the form `TFAE l`, with `l` an explicit list. -/
def proveTFAE (l : Q(List Prop)) : TacticM Q(TFAE $l) := do
  match l with
  | ~q([]) => return q(tfae_nil)
  | ~q([$P]) => return q(tfae_singleton $P)
  | ~q($P :: $P' :: $l) =>
    let c ← proveChain P q($P' :: $l)
    let il ← proveILast'Imp P P' l
    return q(tfae_of_cycle $c $il)

def mkHypName (i j : TSyntax `num) (arr : TSyntax `impArrow) : TermElabM Name := do
  let arr ← match arr with
  | `(impArrow| ← ) => pure "from"
  | `(impArrow| → ) => pure "to"
  | `(impArrow| ↔ ) => pure "iff"
  | _ => throwErrorAt arr "expected '←', '→', or '↔'"
  return String.intercalate "_" ["tfae", s!"{i.getNat}", arr, s!"{j.getNat}"]

open Elab Term in
def tfaeHaveCore (goal : MVarId) (name : Option (TSyntax `ident)) (i j : TSyntax `num)
    (arrow : TSyntax `impArrow) (t : Expr) : TermElabM (MVarId × MVarId) :=
  goal.withContext do
    let n := (Syntax.getId <$> name).getD <|← mkHypName i j arrow
    let (goal1, t, p) ← do
      let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
      pure (p.mvarId!, t, p)
    let (fv, goal2) ← (← MVarId.assert goal n t p).intro1P
    if let some stx := name then
      goal2.withContext do
        Term.addTermInfo' (isBinder := true) stx (mkFVar fv)
    pure (goal1, goal2)

def elabIndex (i : TSyntax `num) (maxIndex : ℕ) : TacticM ℕ := do
  let i' := i.getNat
  unless Nat.ble 1 i' && Nat.ble i' maxIndex do
    throwError "{i} must be between 1 and {maxIndex}"
  return i'

def mkType (Pi : Q(Prop)) (arr : TSyntax `impArrow) (Pj : Q(Prop)) : TacticM Q(Prop) := do
  match arr with
  | `(impArrow| ← ) => pure q($Pj → $Pi)
  | `(impArrow| → ) => pure q($Pi → $Pj)
  | `(impArrow| ↔ ) => pure q($Pi ↔ $Pj)
  | _ => throwErrorAt arr "expected '←', '→', or '↔'"

elab_rules : tactic
| `(tactic| tfae_have $[$h:ident : ]? $i:num $arr:impArrow $j:num) => do
  let target ← getMainTarget
  let tfaeList ← getTFAEList target
  let l₀ := tfaeList.length
  let i' ← elabIndex i l₀
  let j' ← elabIndex j l₀
  let Pi := tfaeList.get! (i'-1)
  let Pj := tfaeList.get! (j'-1)
  let type ← mkType Pi arr Pj
  let (goal1, goal2) ← tfaeHaveCore (← getMainGoal) h i j arr type
  replaceMainGoal [goal1, goal2]

elab_rules : tactic
| `(tactic| tfae_finish) => do
  let goal ← getMainGoal
  let target ← goal.getType
  let tfaeListQ ← getTFAEListQ target
  goal.withContext do
    closeMainGoal (← proveTFAE tfaeListQ)
