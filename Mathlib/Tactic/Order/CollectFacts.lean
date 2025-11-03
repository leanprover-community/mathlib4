/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Lattice
import Qq

/-!
# Facts collection for the `order` Tactic

This file implements the collection of facts for the `order` tactic.
-/

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

/-- State for `CollectFactsM`. It contains a map where the key `t` maps to a
pair `(atomToIdx, facts)`. `atomToIdx` is a `DiscrTree` containing atomic expressions with their
indices, and `facts` stores `AtomicFact`s about them. -/
abbrev CollectFactsState := Std.HashMap Expr <| DiscrTree (Nat × Expr) × Array AtomicFact

/-- Monad for the fact collection procedure. -/
abbrev CollectFactsM := StateT CollectFactsState MetaM

/-- Adds `fact` to the state. -/
def addFact (type : Expr) (fact : AtomicFact) : CollectFactsM Unit :=
  modify fun res => res.modify type fun (atomToIdx, facts) =>
    (atomToIdx, facts.push fact)

/-- Updates the state with the atom `x`. If `x` is `⊤` or `⊥`, adds the corresponding fact. If `x`
is `y ⊔ z`, adds a fact about it, then recursively calls `addAtom` on `y` and `z`.
Similarly for `⊓`. -/
partial def addAtom {u : Level} (type : Q(Type u)) (x : Q($type)) : CollectFactsM Nat := do
  modify fun res => res.insertIfNew type (.empty, #[])
  let (atomToIdx, facts) := (← get).get! type
  match ← (← atomToIdx.getUnify x).findM? fun (_, e) => isDefEq x e with
  | some (idx, _) => return idx
  | none =>
    let idx := atomToIdx.size
    let atomToIdx ← atomToIdx.insert x (idx, x)
    modify fun res => res.insert type (atomToIdx, facts)
    match x with
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

-- The linter claims `u` is unused, but it used on the next line.
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
        let xIdx ← addAtom α x
        let yIdx ← addAtom α y
        addFact α <| .eq xIdx yIdx expr
    | ~q(@LE.le $α $inst $x $y) =>
      let xIdx ← addAtom α x
      let yIdx ← addAtom α y
      addFact α <| .le xIdx yIdx expr
    | ~q(@LT.lt $α $inst $x $y) =>
      let xIdx ← addAtom α x
      let yIdx ← addAtom α y
      addFact α <| .lt xIdx yIdx expr
    | ~q(@Ne ($α : Type _) $x $y) =>
      if (← synthInstance? (q(Preorder $α))).isSome then
        let xIdx ← addAtom α x
        let yIdx ← addAtom α y
        addFact α <| .ne xIdx yIdx expr
    | ~q(Not $p) =>
      match p with
      | ~q(@LE.le $α $inst $x $y) =>
        let xIdx ← addAtom α x
        let yIdx ← addAtom α y
        addFact α <| .nle xIdx yIdx expr
      | ~q(@LT.lt $α $inst $x $y) =>
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

For each occurring type `α`, the returned map contains a pair `(idxToAtom, facts)`,
where the map `idxToAtom` converts indices to found atomic expressions of type `α`,
and `facts` contains all collected `AtomicFact`s about them. -/
def collectFacts (only? : Bool) (hyps : Array Expr) (negGoal : Expr) :
    MetaM <| Std.HashMap Expr <| Std.HashMap Nat Expr × Array AtomicFact := do
  let res := (← (collectFactsImp only? hyps negGoal).run ∅).snd
  return res.map fun _ (atomToIdx, facts) =>
    let idxToAtom : Std.HashMap Nat Expr := atomToIdx.fold (init := ∅) fun acc _ value =>
      acc.insert value.fst value.snd
    (idxToAtom, facts)

end Mathlib.Tactic.Order
