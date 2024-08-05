import Mathlib.Lean.Meta.RefinedDiscrTree
import Qq
import Mathlib.Data.Rat.Defs
import Mathlib.GroupTheory.GroupAction.Basic


open Qq Lean Meta RefinedDiscrTree

macro "#" e:term : command =>
  `(command| run_meta do
    for keys in ← mkKeys q($e) {} false do
      logInfo m! "{← keysAsPattern keys}")

-- eta reduction:
/-- info: Int.succ -/
#guard_msgs in
# fun x => Int.succ x

-- potential eta reduction:
/--
info: @Function.Bijective ℤ ℤ (λ, Int.succ _0)
---
info: @Function.Bijective ℤ ℤ Int.succ
-/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVarQ q(ℤ → ℤ)
  for keys in ← mkKeys q(Function.Bijective fun x : Int => Int.succ ($m x)) {} false do
      logInfo m! "{← keysAsPattern keys}"

/-- info: @OfNat.ofNat ℕ 2 _0 -/
#guard_msgs in
# let x := 2; x

-- unfolding reducible constants:
/-- info: @LE.le ℕ _0 3 2 -/
#guard_msgs in
# 2 ≥ 3


-- identity:
/-- info: λ, #0 -/
#guard_msgs in
# fun x : Nat => x

/-- info: @Function.Bijective ℕ ℕ (@id ℕ) -/
#guard_msgs in
# Function.Bijective fun x : Nat => x

/-- info: @Nat.fold ℕ (@HAdd.hAdd (ℕ → ℕ → ℕ) (ℕ → ℕ → ℕ) _0 _1 (λ, @id ℕ) (λ, λ, #1)) 10 1 -/
#guard_msgs in
# (10).fold (init := 1) (fun x y => y + x)

/-- info: @HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) _0 _1 (@id ℕ) (@id ℕ) 4 -/
#guard_msgs in
# ((@id Nat) + fun x : Nat => x) 4

/-- info: Nat.sqrt (@HAdd.hAdd ℕ ℕ _0 _1 (@id ℕ 4) 4) -/
#guard_msgs in
# Nat.sqrt $ ((@id Nat) + fun x : Nat => x) 4

/-- info: Nat.sqrt (@HPow.hPow ℕ ℕ _0 _1 (@id ℕ 6) 3) -/
#guard_msgs in
# Nat.sqrt $ (id ^ 3 : Nat → Nat) 6


-- only distibute the sum function application if the instance is Pi.instAdd:
private instance (priority := high) : Add (Nat → Nat) where
  add a _ := a

/-- info: Nat.sqrt (@HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) _0 _1 (@id ℕ) (@id ℕ) 4) -/
#guard_msgs in
# Nat.sqrt $ ((@id Nat) + fun x : Nat => x) 4



-- eta-redution is automatically reverted:
/-- info: @Function.Bijective ℕ ℕ (@HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) _0 _1 1 (@id ℕ)) -/
#guard_msgs in
# Function.Bijective (HAdd.hAdd 1)

/-- info: @Function.Bijective ℕ ℕ (@HMul.hMul (ℕ → ℕ) (ℕ → ℕ) _0 _1 1 (@id ℕ)) -/
#guard_msgs in
# Function.Bijective (HMul.hMul 1)

/-- info: @Function.Bijective ℕ ℕ (@HSub.hSub (ℕ → ℕ) (ℕ → ℕ) _0 _1 1 (@id ℕ)) -/
#guard_msgs in
# Function.Bijective (HSub.hSub 1)

/-- info: @Function.Bijective ℕ ℕ (@HDiv.hDiv (ℕ → ℕ) (ℕ → ℕ) _0 _1 1 (@id ℕ)) -/
#guard_msgs in
# Function.Bijective (HDiv.hDiv 1)

/-- info: @Function.Bijective ℚ ℚ (@Inv.inv (ℚ → ℚ) _0 (@id ℚ)) -/
#guard_msgs in
# Function.Bijective (Inv.inv : ℚ → ℚ)

/-- info: @Function.Bijective ℚ ℚ (@Neg.neg (ℚ → ℚ) _0 (@id ℚ)) -/
#guard_msgs in
# Function.Bijective (Neg.neg : ℚ → ℚ)

/-- info: @Function.Bijective ℤ ℤ (@HSMul.hSMul ℕ (ℤ → ℤ) _0 _1 4 (@id ℤ)) -/
#guard_msgs in
# Function.Bijective (HSMul.hSMul 4 : Int → Int)
/--
info: @Function.Bijective ℤ ℤ (@HVAdd.hVAdd (Additive ℕ) (ℤ → ℤ) _0 _1 (@DFunLike.coe (Equiv ℕ (Additive ℕ)) _2 _3 _4 (@Additive.ofMul ℕ) 4) (@id ℤ))
-/
#guard_msgs in
# Function.Bijective (HVAdd.hVAdd (Additive.ofMul (4 : Nat)) : Int → Int)



/--
info: @Function.Bijective ℕ ℕ (@HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) _0 _1 (@HMul.hMul (ℕ → ℕ) (ℕ → ℕ) _2 _3 (@id ℕ) 3) (@HDiv.hDiv (ℕ → ℕ) (ℕ → ℕ) _4 _5 4 (@HPow.hPow ℕ ℕ _6 _7 (@HVAdd.hVAdd ℕ ℕ _8 _9 3 (@HSMul.hSMul ℕ ℕ _10 _11 2 5)))))
-/
#guard_msgs in
# Function.Bijective fun x => x*3+4/(3+ᵥ2•5)^x

/--
info: Nat.sqrt (@HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) _0 _1 (@HVAdd.hVAdd ℕ (ℕ → ℕ) _2 _3 (@HSMul.hSMul ℕ ℕ _4 _5 2 1) (@id ℕ)) (@HDiv.hDiv (ℕ → ℕ) (ℕ → ℕ) _6 _7 (@HMul.hMul (ℕ → ℕ) (ℕ → ℕ) _8 _9 4 5) (@HPow.hPow (ℕ → ℕ) ℕ _10 _11 (@id ℕ) 9)) 5)
-/
#guard_msgs in
# Nat.sqrt $ (2•1+ᵥid+4*5/id^9 : Nat → Nat) 5


-- don't distrubute a lambda when the bound variable appears in the exponent/multiplier:
/-- info: @Function.Bijective ℕ ℕ (λ, @HPow.hPow ℕ ℕ _0 _1 #0 #0) -/
#guard_msgs in
# Function.Bijective fun x => x^x

/-- info: @Function.Bijective ℕ ℕ (λ, @HSMul.hSMul ℕ ℕ _0 _1 #0 5) -/
#guard_msgs in
# Function.Bijective fun x : Nat => x•5

/-- info: @Function.Bijective ℕ ℕ (λ, @HVAdd.hVAdd ℕ ℕ _0 _1 #0 #0) -/
#guard_msgs in
# Function.Bijective fun x : Nat => x+ᵥx

-- don't distribute a lambda when the bound variable appears in the instance:
/-- info: @id (Sort → (Ring #0) → #1) (λ, λ, @HAdd.hAdd #1 #1 _0 _1 1 2) -/
#guard_msgs in
# id fun (α : Type) [Ring α] => (1+2 : α)

/-- info: @id (Sort → (Ring #0) → #1) (λ, λ, @HSMul.hSMul ℕ #1 _0 _1 2 3) -/
#guard_msgs in
# id fun (α : Type) [Ring α] => (2•3 : α)



-- index constant number literal functions as just the number literal:
/-- info: @Function.Bijective ℕ ℕ 4 -/
#guard_msgs in
# Function.Bijective fun _ : Nat => 4

-- but not at the root:
/-- info: λ, @OfNat.ofNat ℕ 4 _0 -/
#guard_msgs in
# fun _ : Nat => 4

-- index constant functions as just a star pattern:
/-- info: @Function.Bijective ℕ ℕ _0 -/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVarQ q(ℕ)
  for keys in ← mkKeys q(Function.Bijective fun _ : Nat => $m) {} false do
    logInfo m! "{← keysAsPattern keys}"

-- but not at the root:
/-- info: λ, _0 -/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVarQ q(ℕ)
  for keys in ← mkKeys q(fun _ : Nat => $m) {} false do
    logInfo m! "{← keysAsPattern keys}"
