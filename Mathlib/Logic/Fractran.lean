import Mathlib.Data.PNat.Defs
import Mathlib.Tactic.NormNum

open Nat

def FRACTRAN := List (PNat × PNat)

namespace FRACTRAN

def mul? (n a b : PNat) : Option PNat :=
  if h : (n * a % b : Nat) = 0 then
    some ⟨n * a / b, Nat.div_pos (le_of_dvd (Nat.mul_pos n.2 a.2) (dvd_of_mod_eq_zero h)) b.2⟩
 else
   none

def step (f : FRACTRAN) (n : PNat) : Option PNat :=
  f.findSome? fun ⟨a, b⟩ => mul? n a b

def listStep (f : FRACTRAN) (n : List PNat) : List PNat :=
  match n with
  | [] => []
  | n :: ns =>
    match step f n with
    | some n' => n' :: n :: ns
    | none => n :: ns

def runSteps (f : FRACTRAN) (n : PNat) (k : Nat) : List PNat :=
  List.range k |>.foldl (fun r _ => listStep f r) [n]

def runFor (f : FRACTRAN) (n : PNat) : Nat → PNat
  | 0 => n
  | k + 1 => match step f n with
    | some n' => runFor f n' k
    | none => n

-- Check that `[(3, 2)]` is the program for addition.
example : (runFor [(3, 2)] ⟨2^37 * 3^42, by norm_num⟩ 1000).val = 3^(37+42) := rfl

def PRIMEGAME : FRACTRAN := [(17, 91), (78, 85), (19, 51), (23, 38), (29, 33), (77, 29), (95, 23),
  (77, 19), (1, 17), (11, 13), (13, 11), (15, 2), (1, 7), (55, 1)]

def twoPow? (n : Nat) : Option Nat :=
  if _ : n = 0 then none else
  if _ : n = 1 then some 0 else
  if h : n % 2 = 0 then
    twoPow? (n / 2) |>.map (· + 1)
  else
    none

example : twoPow? 1024 = some 10 := by native_decide

#eval runSteps PRIMEGAME ⟨2, by norm_num⟩ 100000 |>.map PNat.val|>.filterMap twoPow?

end FRACTRAN
