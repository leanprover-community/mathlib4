/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public meta import Mathlib.Tactic.Order.CollectFacts

/-!
# Facts preprocessing for the `order` tactic

In this file we implement the preprocessing procedure for the `order` tactic.
See `Mathlib/Tactic/Order.lean` for details of preprocessing.
-/

public meta section

namespace Mathlib.Tactic.Order

universe u

open Lean Expr Meta

section Lemmas

lemma not_lt_of_not_le {α : Type u} [Preorder α] {x y : α} (h : ¬(x ≤ y)) : ¬(x < y) :=
  (h ·.le)

lemma le_of_not_lt_le {α : Type u} [Preorder α] {x y : α} (h1 : ¬(x < y)) (h2 : x ≤ y) :
    y ≤ x :=
  not_lt_iff_le_imp_ge.mp h1 h2

end Lemmas

/-- Supported order types: linear, partial, and preorder. -/
inductive OrderType
| lin | part | pre
deriving BEq

instance : ToString OrderType where
  toString
  | .lin => "linear order"
  | .part => "partial order"
  | .pre => "preorder"

/-- Find the "best" instance of an order on a given type. A linear order is preferred over a partial
order, and a partial order is preferred over a preorder. -/
def findBestOrderInstance (type : Expr) : MetaM <| Option OrderType := do
  if (← synthInstance? (← mkAppM ``LinearOrder #[type])).isSome then
    return some .lin
  if (← synthInstance? (← mkAppM ``PartialOrder #[type])).isSome then
    return some .part
  if (← synthInstance? (← mkAppM ``Preorder #[type])).isSome then
    return some .pre
  return none

/-- Replaces facts of the form `x = ⊤` with `y ≤ x` for all `y`, and similarly for `x = ⊥`. -/
def replaceBotTop (facts : Array AtomicFact) (idxToAtom : Std.HashMap Nat Expr) :
    MetaM <| Array AtomicFact := do
  let mut res : Array AtomicFact := #[]
  let nAtoms := idxToAtom.size
  for fact in facts do
    match fact with
    | .isBot idx =>
      for i in [:nAtoms] do
        if i != idx then
          res := res.push <| .le idx i (← mkAppOptM ``bot_le #[none, none, none, idxToAtom.get! i])
    | .isTop idx =>
      for i in [:nAtoms] do
        if i != idx then
          res := res.push <| .le i idx (← mkAppOptM ``le_top #[none, none, none, idxToAtom.get! i])
    | _ =>
      res := res.push fact
  return res

/-- Preprocesses facts for preorders. Replaces `x < y` with two equivalent facts: `x ≤ y` and
`¬ (y ≤ x)`. Replaces `x = y` with `x ≤ y`, `y ≤ x` and removes `x ≠ y`. -/
def preprocessFactsPreorder (facts : Array AtomicFact) : MetaM <| Array AtomicFact := do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_lt #[proof])
      res := res.push <| .nle rhs lhs (← mkAppM ``not_le_of_gt #[proof])
    | .eq lhs rhs proof =>
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_eq #[proof])
      res := res.push <| .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .ne _ _ _ =>
      continue
    | _ =>
      res := res.push fact
  return res

/-- Preprocesses facts for partial orders. Replaces `x < y`, `¬ (x ≤ y)`, and `x = y` with
equivalent facts involving only `≤`, `≠`, and `≮`. For each fact `x = y ⊔ z` adds `y ≤ x`
and `z ≤ x` facts, and similarly for `⊓`. -/
def preprocessFactsPartial (facts : Array AtomicFact) (idxToAtom : Std.HashMap Nat Expr) :
    MetaM <| Array AtomicFact := do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
      res := res.push <| .ne lhs rhs (← mkAppM ``ne_of_lt #[proof])
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_lt #[proof])
    | .nle lhs rhs proof =>
      res := res.push <| .ne lhs rhs (← mkAppM ``ne_of_not_le #[proof])
      res := res.push <| .nlt lhs rhs (← mkAppM ``not_lt_of_not_le #[proof])
    | .eq lhs rhs proof =>
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_eq #[proof])
      res := res.push <| .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .isSup lhs rhs sup =>
      res := res.push <| .le lhs sup
        (← mkAppOptM ``le_sup_left #[none, none, idxToAtom.get! lhs, idxToAtom.get! rhs])
      res := res.push <| .le rhs sup
        (← mkAppOptM ``le_sup_right #[none, none, idxToAtom.get! lhs, idxToAtom.get! rhs])
      res := res.push fact
    | .isInf lhs rhs inf =>
      res := res.push <| .le inf lhs
        (← mkAppOptM ``inf_le_left #[none, none, idxToAtom.get! lhs, idxToAtom.get! rhs])
      res := res.push <| .le inf rhs
        (← mkAppOptM ``inf_le_right #[none, none, idxToAtom.get! lhs, idxToAtom.get! rhs])
      res := res.push fact
    | _ =>
      res := res.push fact
  return res

/-- Preprocesses facts for linear orders. Replaces `x < y`, `¬ (x ≤ y)`, `¬ (x < y)`, and `x = y`
with equivalent facts involving only `≤` and `≠`. For each fact `x = y ⊔ z` adds `y ≤ x`
and `z ≤ x` facts, and similarly for `⊓`. -/
def preprocessFactsLinear (facts : Array AtomicFact) (idxToAtom : Std.HashMap Nat Expr) :
    MetaM <| Array AtomicFact := do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
      res := res.push <| .ne lhs rhs (← mkAppM ``ne_of_lt #[proof])
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_lt #[proof])
    | .nle lhs rhs proof =>
      res := res.push <| .ne lhs rhs (← mkAppM ``ne_of_not_le #[proof])
      res := res.push <| .le rhs lhs (← mkAppM ``le_of_not_ge #[proof])
    | .nlt lhs rhs proof =>
      res := res.push <| .le rhs lhs (← mkAppM ``le_of_not_gt #[proof])
    | .eq lhs rhs proof =>
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_eq #[proof])
      res := res.push <| .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .isSup lhs rhs sup =>
      res := res.push <| .le lhs sup
        (← mkAppOptM ``le_sup_left #[none, none, idxToAtom.get! lhs, idxToAtom.get! rhs])
      res := res.push <| .le rhs sup
        (← mkAppOptM ``le_sup_right #[none, none, idxToAtom.get! lhs, idxToAtom.get! rhs])
      res := res.push fact
    | .isInf lhs rhs inf =>
      res := res.push <| .le inf lhs
        (← mkAppOptM ``inf_le_left #[none, none, idxToAtom.get! lhs, idxToAtom.get! rhs])
      res := res.push <| .le inf rhs
        (← mkAppOptM ``inf_le_right #[none, none, idxToAtom.get! lhs, idxToAtom.get! rhs])
      res := res.push fact
    | _ =>
      res := res.push fact
  return res

/-- Preprocesses facts for order of `orderType` using either `preprocessFactsPreorder` or
`preprocessFactsPartial` or `preprocessFactsLinear`. -/
def preprocessFacts (facts : Array AtomicFact) (idxToAtom : Std.HashMap Nat Expr)
    (orderType : OrderType) : MetaM <| Array AtomicFact :=
  match orderType with
  | .pre => preprocessFactsPreorder facts
  | .part => preprocessFactsPartial facts idxToAtom
  | .lin => preprocessFactsLinear facts idxToAtom

end Mathlib.Tactic.Order
