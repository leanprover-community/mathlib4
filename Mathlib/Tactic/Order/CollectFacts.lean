/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public meta import Qq
public import Mathlib.Order.BoundedOrder.Basic  -- shake: keep (Qq dependency)
public import Mathlib.Order.Lattice  -- shake: keep (Qq dependency)
public import Mathlib.Util.AtomM

/-!
# Facts collection for the `order` Tactic

This file implements the collection of facts for the `order` tactic.
-/

public meta section

namespace Mathlib.Tactic.Order

open Lean Qq Elab Meta Tactic

/-- A structure for storing facts about variables. -/
inductive AtomicFact
| eq (lhs : Nat) (rhs : Nat) (proof : Expr)
| ne (lhs : Nat) (rhs : Nat) (proof : Expr)
| le (lhs : Nat) (rhs : Nat) (proof : Expr)
| nle (lhs : Nat) (rhs : Nat) (proof : Expr)
| lt (lhs : Nat) (rhs : Nat) (proof : Expr)
| nlt (lhs : Nat) (rhs : Nat) (proof : Expr)
| isTop (idx : Nat)
| isBot (idx : Nat)
| isInf (lhs : Nat) (rhs : Nat) (res : Nat)
| isSup (lhs : Nat) (rhs : Nat) (res : Nat)
deriving Inhabited, BEq

-- For debugging purposes.
instance : ToString AtomicFact where
  toString fa := match fa with
  | .eq lhs rhs _ => s!"#{lhs} = #{rhs}"
  | .ne lhs rhs _ => s!"#{lhs} ≠ #{rhs}"
  | .le lhs rhs _ => s!"#{lhs} ≤ #{rhs}"
  | .nle lhs rhs _ => s!"¬ #{lhs} ≤ #{rhs}"
  | .lt lhs rhs _ => s!"#{lhs} < #{rhs}"
  | .nlt lhs rhs _ => s!"¬ #{lhs} < #{rhs}"
  | .isTop idx => s!"#{idx} := ⊤"
  | .isBot idx => s!"#{idx} := ⊥"
  | .isInf lhs rhs res => s!"#{res} := #{lhs} ⊓ #{rhs}"
  | .isSup lhs rhs res => s!"#{res} := #{lhs} ⊔ #{rhs}"

/-- State for `CollectFactsM`. It contains a map that maps a type to atomic facts collected for
this type. -/
abbrev CollectFactsState := Std.HashMap Expr <| Array AtomicFact

/-- Monad for the fact collection procedure. -/
abbrev CollectFactsM := StateT CollectFactsState AtomM

/-- Adds `type` to the state. It checks if the type has already been added up to
`reducible_and_instances` transparency. Returns the type that is added to the state and
defenitionally equal (but may be not syntactically equal) to `type`. -/
def addType {u : Level} (type : Q(Type u)) : CollectFactsM Q(Type u) := do
  match ← (← get).keys.findM? (withReducibleAndInstances <| isDefEq type ·) with
  | none =>
    modify fun res => res.insert type #[]
    pure type
  | some t => pure t

/-- Adds `fact` to the state. Assumes that `type` is already added by `addType`. -/
def addFact (type : Expr) (fact : AtomicFact) : CollectFactsM Unit :=
  modify fun res => res.modify type fun facts => facts.push fact

/-- Updates the state with the atom `x`. If `x` is `⊤` or `⊥`, adds the corresponding fact. If `x`
is `y ⊔ z`, adds a fact about it, then recursively calls `addAtom` on `y` and `z`.
Similarly for `⊓`. Assumes that `type` is already added by `addType`. -/
partial def addAtom {u : Level} (type : Q(Type u)) (x : Q($type)) : CollectFactsM Nat := do
  match ← AtomM.containsThenAddQ x with
  | (true, idx, _) => return idx
  | (false, idx, ⟨x', _⟩) =>
    match x' with
    | ~q((@OrderTop.toTop _ $instLE $instTop).top) =>
      addFact type (.isTop idx)
    | ~q((@OrderBot.toBot _ $instLE $instBot).bot) =>
      addFact type (.isBot idx)
    | ~q((@SemilatticeSup.toMax _ $inst).max $a $b) =>
      let aIdx ← addAtom type a
      let bIdx ← addAtom type b
      addFact type (.isSup aIdx bIdx idx)
    | ~q((@SemilatticeInf.toMin _ $inst).min $a $b) =>
      let aIdx ← addAtom type a
      let bIdx ← addAtom type b
      addFact type (.isInf aIdx bIdx idx)
    | _ => pure ()
    return idx

-- TODO: The linter claims `u` is unused, but it used on the next line.
set_option linter.unusedVariables false in
/-- Implementation for `collectFacts` in `CollectFactsM` monad. -/
partial def collectFactsImp (only? : Bool) (hyps : Array Expr) (negGoal : Expr) :
    CollectFactsM Unit := do
  let ctx ← getLCtx
  for expr in hyps do
    processExpr expr
  processExpr negGoal
  if !only? then
    for ldecl in ctx do
      if ldecl.isImplementationDetail then
        continue
      let e := ldecl.toExpr
      if e == negGoal then
        continue
      processExpr e
where
  /-- Extracts facts and atoms from the expression. -/
  processExpr (expr : Expr) : CollectFactsM Unit := do
    let type ← inferType expr
    if !(← isProp type) then
      return
    let ⟨u, type, expr⟩ ← inferTypeQ expr
    let _ : u =QL 0 := ⟨⟩
    match type with
    | ~q(@Eq ($α : Type _) $x $y) =>
      if (← synthInstance? (q(Preorder $α))).isSome then
        let α ← addType α
        let xIdx ← addAtom α x
        let yIdx ← addAtom α y
        addFact α <| .eq xIdx yIdx expr
    | ~q(@LE.le $α $inst $x $y) =>
      let α ← addType α
      let xIdx ← addAtom α x
      let yIdx ← addAtom α y
      addFact α <| .le xIdx yIdx expr
    | ~q(@LT.lt $α $inst $x $y) =>
      let α ← addType α
      let xIdx ← addAtom α x
      let yIdx ← addAtom α y
      addFact α <| .lt xIdx yIdx expr
    | ~q(@Ne ($α : Type _) $x $y) =>
      if (← synthInstance? (q(Preorder $α))).isSome then
        let α ← addType α
        let xIdx ← addAtom α x
        let yIdx ← addAtom α y
        addFact α <| .ne xIdx yIdx expr
    | ~q(Not $p) =>
      match p with
      | ~q(@LE.le $α $inst $x $y) =>
        let α ← addType α
        let xIdx ← addAtom α x
        let yIdx ← addAtom α y
        addFact α <| .nle xIdx yIdx expr
      | ~q(@LT.lt $α $inst $x $y) =>
        let α ← addType α
        let xIdx ← addAtom α x
        let yIdx ← addAtom α y
        addFact α <| .nlt xIdx yIdx expr
      | _ => return
    | ~q($p ∧ $q) =>
      processExpr q(And.left $expr)
      processExpr q(And.right $expr)
    | ~q(Exists $P) =>
      processExpr q(Exists.choose_spec $expr)
    | _ => return

/-- Collects facts from the local context. `negGoal` is the negated goal, `hyps` is the expressions
passed to the tactic using square brackets. If `only?` is true, we collect facts only from `hyps`
and `negGoal`, otherwise we also use the local context.

For each occurring type `α`, the returned map contains an array containing all collected
`AtomicFact`s about atoms of type `α`. -/
def collectFacts (only? : Bool) (hyps : Array Expr) (negGoal : Expr) :
    AtomM <| Std.HashMap Expr <| Array AtomicFact := do
  return (← (collectFactsImp only? hyps negGoal).run ∅).snd

end Mathlib.Tactic.Order
