import Mathlib.Data.Nondet.Basic
import Std.Tactic.GuardMsgs

set_option autoImplicit true

open Lean Meta

def M := StateT (List Nat) MetaM

deriving instance Monad for M
deriving instance Alternative for M

instance : MonadBacktrack (List Nat) M where
  saveState := StateT.get
  restoreState := StateT.set

def record (n : Nat) : M Unit := do
  discard <| restoreState (n :: (← saveState))

def iota (n : Nat) : Nondet M Nat := Nondet.ofList (List.iota n)

/-- info: (52, []) -/
#guard_msgs in
#eval show MetaM (Nat × List Nat) from StateT.run (iota 52).head []

/-- info: ((), [52]) -/
#guard_msgs in
#eval show MetaM (Unit × List Nat) from StateT.run (((iota 52).mapM record).head) []

def x : Nondet M Nat :=
  (iota 52).filterMapM fun x => do
    record x
    if x % 7 = 0 then
      return some (x^2)
    else
      return none

/-- info: (2401, [49]) -/
#guard_msgs in
#eval show MetaM (Nat × List Nat) from StateT.run x.head []

def divisors (n : Nat) : List Nat := List.iota n |>.filter fun m => n % m = 0
example : divisors 52 = [52, 26, 13, 4, 2, 1] := rfl

/-- Take the numbers `15, ..., 1`, replace each with their divisors, then replace again. -/
def y : Nondet M Nat :=
  (iota 15)
  |>.bind fun x => do
    record x
    Nondet.ofList (divisors x)
  |>.bind fun x => do
    record x
    Nondet.ofList (divisors x)

/-- info: [15, 5, 3, 1, 5, 1, 3, 1, 1, 14, 7, 2, 1, 7, 1, 2, 1, 1, 13, 1, 1] -/
#guard_msgs in
#eval show MetaM (List Nat) from StateT.run' (y.toMLList'.takeAsList 21) []

-- All ways to find `4 ∣ a ∣ b`, with `b = 15, ..., 1`.
/-- info: ([(4, [12, 12]), (4, [4, 12]), (4, [8, 8]), (4, [4, 8]), (4, [4, 4])], [1, 1]) -/
#guard_msgs in
#eval show MetaM (List (Nat × List Nat) × List Nat) from
  StateT.run (y.filter (· = 4)).toMLList.force []
