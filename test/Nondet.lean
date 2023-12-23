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

def iotaM [Monad m] [Alternative m] [MonadBacktrack σ m] (n : Nat) : Nondet m Nat :=
  Nondet.ofList (List.iota n)

/-- info: (52, []) -/
#guard_msgs in
#eval show MetaM (Nat × List Nat) from StateT.run (iotaM 52 : Nondet M Nat).head []

/-- info: ((), [52]) -/
#guard_msgs in
#eval show MetaM (Unit × List Nat) from StateT.run (((iotaM 52).mapM record).head) []

def x : Nondet M Nat :=
  (iotaM 52).filterMapM fun x => do
    record x
    if x % 7 = 0 then
      return some (x^2)
    else
      return none

/-- info: (2401, [49]) -/
#guard_msgs in
#eval show MetaM (Nat × List Nat) from StateT.run x.head []

def divisors (n : Nat) : List Nat := List.iota (n - 1) |>.filter fun m => n % m = 0
example : divisors 52 = [26, 13, 4, 2, 1] := rfl

def divisorsM [Monad m] [MonadBacktrack σ m] (n : Nat) : Nondet m Nat :=
  Nondet.ofList (divisors n)

/-- Take the numbers `32, ..., 1`, replace each with their divisors, then replace again. -/
def y : Nondet M Nat :=
  (iotaM 32)
  |>.bind fun x => do
    record x
    divisorsM x
  |>.bind fun x => do
    record x
    divisorsM x

/-- info: [8, 4, 2, 1, 4, 2, 1, 2, 1, 1, 5, 3, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 7] -/
#guard_msgs in
#eval show MetaM (List Nat) from StateT.run' (y.toMLList'.takeAsList 23) []

-- All ways to find `4 ∣ a ∣ b`, with `b = 32, ..., 1`.
/-- info: ([(4, [16, 32]), (4, [8, 32]), (4, [12, 24]), (4, [8, 24]), (4, [8, 16])], [1]) -/
#guard_msgs in
#eval show MetaM (List (Nat × List Nat) × List Nat) from
  StateT.run (y.filter (· = 4)).toMLList.force []

/-- info: [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1] -/
#guard_msgs in
#eval (iotaM 15 : Nondet MetaM Nat).toList'

-- Depth first search of the divisors of 255.
/-- info: [255, 85, 17, 1, 5, 1, 1, 51, 17, 1, 3, 1, 1, 17, 1, 15, 5, 1, 3, 1, 1, 5, 1, 3, 1, 1] -/
#guard_msgs in
#eval (Nondet.iterate divisorsM 255 : Nondet Id Nat).toList'
