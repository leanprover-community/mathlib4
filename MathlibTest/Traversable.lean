import Mathlib.Tactic.DeriveTraversable
import Mathlib.Control.Traversable.Instances

set_option linter.style.commandStart false

namespace Testing

universe u

structure MyStruct (α : Type) where
  y : ℤ
  deriving LawfulTraversable

#guard_msgs (drop info) in #synth LawfulTraversable MyStruct

inductive Either (α : Type u)
  | left : α → ℤ → Either α
  | right : α → Either α
  deriving LawfulTraversable

#guard_msgs (drop info) in #synth LawfulTraversable Either

structure MyStruct2 (α : Type u) : Type u where
  x : α
  y : ℤ
  η : List α
  k : List (List α)
  deriving LawfulTraversable

#guard_msgs (drop info) in #synth LawfulTraversable MyStruct2

inductive RecData (α : Type u) : Type u
  | nil : RecData α
  | cons : ℕ → α → RecData α → RecData α → RecData α
  deriving LawfulTraversable

#guard_msgs (drop info) in #synth LawfulTraversable RecData

unsafe structure MetaStruct (α : Type u) : Type u where
  x : α
  y : ℤ
  z : List α
  k : List (List α)
  w : Lean.Expr
  deriving Traversable

#guard_msgs (drop info) in #synth Traversable MetaStruct

inductive MyTree (α : Type)
  | leaf : MyTree α
  | node : MyTree α → MyTree α → α → MyTree α
  deriving LawfulTraversable

#guard_msgs (drop info) in #synth LawfulTraversable MyTree

inductive MyTree' (α : Type)
  | leaf : MyTree' α
  | node : MyTree' α → α → MyTree' α → MyTree' α
  deriving LawfulTraversable

#guard_msgs (drop info) in #synth LawfulTraversable MyTree'

section
open MyTree hiding traverse

def x : MyTree (List Nat) :=
  node
    leaf
    (node
      (node leaf leaf [1,2,3])
      leaf
      [3,2])
    [1]

/-- demonstrate the nested use of `traverse`. It traverses each node of the tree and
in each node, traverses each list. For each `ℕ` visited, apply an action `ℕ → StateM (List ℕ) Unit`
which adds its argument to the state. -/
def ex : StateM (List ℕ) (MyTree <| List Unit) := do
  let xs ← traverse (traverse fun a => modify <| List.cons a) x
  return xs

example : (ex.run []).1 = node leaf (node (node leaf leaf [(), (), ()]) leaf [(), ()]) [()] := rfl
example : (ex.run []).2 = [1, 2, 3, 3, 2, 1] := rfl

end

end Testing
