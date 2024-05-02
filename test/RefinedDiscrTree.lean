import Mathlib.Lean.Meta.RefinedDiscrTree
import Qq
import Mathlib.Data.Rat.Defs
import Mathlib.GroupTheory.GroupAction.Defs


open Qq Lean Meta RefinedDiscrTree

macro "#" e:term : command => `(command| #eval format <$> mkDTExprs q($e) {} false)

-- eta reduction:
/-- info: [Int.succ] -/
#guard_msgs in
# fun x => Int.succ x

-- potential eta reduction:
/--
info: [Function.Bijective (Int, Int, λ Int.succ (*)), Function.Bijective (Int, Int, Int.succ)]
-/
#guard_msgs in
#eval format <$> do
  let m ← mkFreshExprMVarQ q(ℤ → ℤ)
  mkDTExprs q(Function.Bijective fun x : Int => Int.succ ($m x)) {} false

/-- info: [OfNat.ofNat (Nat, 2, *)] -/
#guard_msgs in
# let x := 2; x

-- unfolding reducible constants:
/-- info: [LE.le (Nat, *, 3, 2)] -/
#guard_msgs in
# 2 ≥ 3


-- identity:
/-- info: [λ #0] -/
#guard_msgs in
# fun x : Nat => x
/-- info: [Function.Bijective (Nat, Nat, id (Nat))] -/
#guard_msgs in
# Function.Bijective fun x : Nat => x


/-- info: [HAdd.hAdd (Nat → Nat, Nat → Nat, *, *, id (Nat), id (Nat), 4)] -/
#guard_msgs in
# ((@id Nat) + fun x : Nat => x) 4

/-- info: [Nat.sqrt (HAdd.hAdd (Nat, Nat, *, *, id (Nat, 4), 4))] -/
#guard_msgs in
# Nat.sqrt $ ((@id Nat) + fun x : Nat => x) 4

/-- info: [Nat.sqrt (HPow.hPow (Nat, Nat, *, *, id (Nat, 6), 3))] -/
#guard_msgs in
# Nat.sqrt $ (id ^ 3 : Nat → Nat) 6


-- only distibute the sum function application if the instance is Pi.instAdd:
private instance (priority := high) : Add (Nat → Nat) where
  add a _ := a

/-- info: [Nat.sqrt (HAdd.hAdd (Nat → Nat, Nat → Nat, *, *, id (Nat), id (Nat), 4))] -/
#guard_msgs in
# Nat.sqrt $ ((@id Nat) + fun x : Nat => x) 4



-- eta-redution is automatically reverted:
/-- info: [Function.Bijective (Nat, Nat, HAdd.hAdd (Nat → Nat, Nat → Nat, *, *, 1, id (Nat)))] -/
#guard_msgs in
# Function.Bijective (HAdd.hAdd 1)

/-- info: [Function.Bijective (Nat, Nat, HMul.hMul (Nat → Nat, Nat → Nat, *, *, 1, id (Nat)))] -/
#guard_msgs in
# Function.Bijective (HMul.hMul 1)

/-- info: [Function.Bijective (Nat, Nat, HSub.hSub (Nat → Nat, Nat → Nat, *, *, 1, id (Nat)))] -/
#guard_msgs in
# Function.Bijective (HSub.hSub 1)

/-- info: [Function.Bijective (Nat, Nat, HDiv.hDiv (Nat → Nat, Nat → Nat, *, *, 1, id (Nat)))] -/
#guard_msgs in
# Function.Bijective (HDiv.hDiv 1)

/-- info: [Function.Bijective (Rat, Rat, Inv.inv (Rat → Rat, *, id (Rat)))] -/
#guard_msgs in
# Function.Bijective (Inv.inv : ℚ → ℚ)

/-- info: [Function.Bijective (Rat, Rat, Neg.neg (Rat → Rat, *, id (Rat)))] -/
#guard_msgs in
# Function.Bijective (Neg.neg : ℚ → ℚ)

/-- info: [Function.Bijective (Int, Int, HSMul.hSMul (Nat, Int → Int, *, *, 4, id (Int)))] -/
#guard_msgs in
# Function.Bijective (HSMul.hSMul 4 : Int → Int)
/--
info: [Function.Bijective (Int, Int, HVAdd.hVAdd (Additive (Nat), Int → Int, *, *, DFunLike.coe (Equiv (Nat, Additive (Nat)), *, *, *, Additive.ofMul (Nat), 4), id (Int)))]
-/
#guard_msgs in
# Function.Bijective (HVAdd.hVAdd (Additive.ofMul (4 : Nat)) : Int → Int)



/--
info: [Function.Bijective (Nat, Nat, HAdd.hAdd (Nat → Nat, Nat → Nat, *, *, HMul.hMul (Nat → Nat, Nat → Nat, *, *, id (Nat), 3), HDiv.hDiv (Nat → Nat, Nat → Nat, *, *, 4, HPow.hPow (Nat, Nat, *, *, HVAdd.hVAdd (Nat, Nat, *, *, 3, HSMul.hSMul (Nat, Nat, *, *, 2, 5))))))]
-/
#guard_msgs in
# Function.Bijective fun x => x*3+4/(3+ᵥ2•5)^x

/--
info: [Nat.sqrt (HAdd.hAdd (Nat → Nat, Nat → Nat, *, *, HVAdd.hVAdd (Nat, Nat → Nat, *, *, HSMul.hSMul (Nat, Nat, *, *, 2, 1), id (Nat)), HDiv.hDiv (Nat → Nat, Nat → Nat, *, *, HMul.hMul (Nat → Nat, Nat → Nat, *, *, 4, 5), HPow.hPow (Nat → Nat, Nat, *, *, id (Nat), 9)), 5))]
-/
#guard_msgs in
# Nat.sqrt $ (2•1+ᵥid+4*5/id^9 : Nat → Nat) 5


-- don't distrubute a lambda when the bound variable appears in the exponent/multiplier:
/-- info: [Function.Bijective (Nat, Nat, λ HPow.hPow (Nat, Nat, *, *, #0, #0))] -/
#guard_msgs in
# Function.Bijective fun x => x^x

/-- info: [Function.Bijective (Nat, Nat, λ HSMul.hSMul (Nat, Nat, *, *, #0, 5))] -/
#guard_msgs in
# Function.Bijective fun x : Nat => x•5

/-- info: [Function.Bijective (Nat, Nat, λ HVAdd.hVAdd (Nat, Nat, *, *, #0, #0))] -/
#guard_msgs in
# Function.Bijective fun x : Nat => x+ᵥx

-- don't distribute a lambda when the bound variable appears in the instance:
/-- info: [id (Sort → Ring (#0) → #1, λ λ HAdd.hAdd (#1, #1, *, *, 1, 2))] -/
#guard_msgs in
# id fun (α : Type) [Ring α] => (1+2 : α)

/-- info: [id (Sort → Ring (#0) → #1, λ λ HSMul.hSMul (Nat, #1, *, *, 2, 3))] -/
#guard_msgs in
# id fun (α : Type) [Ring α] => (2•3 : α)



-- index constant number literal functions as just the number literal:
/-- info: [Function.Bijective (Nat, Nat, 4)] -/
#guard_msgs in
# Function.Bijective fun _ : Nat => 4

-- but not at the root:
/-- info: [λ OfNat.ofNat (Nat, 4, *)] -/
#guard_msgs in
# fun _ : Nat => 4

-- index constant functions as just a star pattern:
/-- info: [Function.Bijective (Nat, Nat, *)] -/
#guard_msgs in
#eval format <$> do
  let m ← mkFreshExprMVarQ q(ℕ)
  mkDTExprs q(Function.Bijective fun _ : Nat => $m) {} false

-- but not at the root:
/-- info: [λ *] -/
#guard_msgs in
#eval format <$> do
  let m ← mkFreshExprMVarQ q(ℕ)
  mkDTExprs q(fun _ : Nat => $m) {} false
