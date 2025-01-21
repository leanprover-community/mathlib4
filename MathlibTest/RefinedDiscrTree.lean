import Mathlib.Lean.Meta.RefinedDiscrTree.Encode
import Mathlib

open Qq Lean Meta RefinedDiscrTree

macro "#" e:term : command =>
  `(command| run_meta do
    for keys in ← encodeExpr q($e) do
      logInfo m! "{← keysAsPattern keys}")

-- eta reduction:
/-- info: Int.succ -/
#guard_msgs in
# fun x => Int.succ x

-- potential eta reduction:
/--
info: @Function.Bijective ℤ ℤ Int.succ
---
info: @Function.Bijective ℤ ℤ (λ, Int.succ *0)
-/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVarQ q(ℤ → ℤ)
  for keys in ← encodeExpr q(Function.Bijective fun x : Int => Int.succ ($m x)) do
      logInfo m! "{← keysAsPattern keys}"

-- caching the way in which eta reduction is done:
/--
info: And (@Function.Bijective ℤ ℤ Int.succ) (@Function.Bijective ℤ ℤ Int.succ)
---
info: And (@Function.Bijective ℤ ℤ (λ, Int.succ *0)) (@Function.Bijective ℤ ℤ (λ, Int.succ *0))
-/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVarQ q(ℤ → ℤ)
  for keys in ← encodeExpr q((Function.Bijective fun x : Int => Int.succ ($m x)) ∧
      Function.Bijective fun x : Int => Int.succ ($m x)) do
    logInfo m! "{← keysAsPattern keys}"

--
/--
info: @Eq *0 (@HAdd.hAdd *0 *0 *1 *2 (@HAdd.hAdd *0 *0 *3 *4 *5 *5) *6) (@HAdd.hAdd *0 *0 *7 *8 *5 a)
-/
#guard_msgs in
run_meta do
  let t ← mkFreshExprMVarQ q(Type)
  let _ ← mkFreshExprMVarQ q(Add $t)
  let m ← mkFreshExprMVarQ q($t)
  let m' ← mkFreshExprMVarQ q($t)
  withLocalDeclDQ `a q($t) fun n => do
  for keys in ← encodeExpr q($m+$m + $m' = $m + $n) do
    logInfo m! "{← keysAsPattern keys}"

/-- info: @Function.Bijective *0 *0 (@HAdd.hAdd (*0 → *0) (*0 → *0) *1 *2 *3 *4) -/
#guard_msgs in
run_meta do
  let t ← mkFreshExprMVarQ q(Type)
  let _ ← mkFreshExprMVarQ q(Add $t)
  let m ← mkFreshExprMVarQ q($t → $t)
  let m' ← mkFreshExprMVarQ q($t → $t)
  for keys in ← encodeExpr q(Function.Bijective fun x => $m x + $m' x) do
    logInfo m! "{← keysAsPattern keys}"

/-- info: @OfNat.ofNat ℕ 2 *0 -/
#guard_msgs in
# let x := 2; x

-- unfolding reducible constants:
/-- info: @LE.le ℕ *0 3 2 -/
#guard_msgs in
# 2 ≥ 3


-- identity:
/-- info: λ, #0 -/
#guard_msgs in
# fun x : Nat => x

open BigOperators Finset in
/-- info: @Finset.sum ℕ ℕ *0 (range 10) (@id ℕ) -/
#guard_msgs in
# ∑ i ∈ range 10, i

/--
info: @Nat.fold ℕ 10 (@HAdd.hAdd (ℕ → (@LT.lt ℕ *0 #0 10) → ℕ → ℕ) (ℕ → (@LT.lt ℕ *1 #0 10) → ℕ → ℕ) *2 *3 (λ, λ, @id ℕ) (λ, λ, λ, #2)) 1
-/
#guard_msgs in
# (10).fold (init := 1) (fun x _ y => y + x)

/-- info: @HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) *0 *1 (@id ℕ) (@id ℕ) 4 -/
#guard_msgs in
# ((@id Nat) + fun x : Nat => x) 4

/-- info: Nat.sqrt (@HAdd.hAdd ℕ ℕ *0 *1 (@id ℕ 4) 4) -/
#guard_msgs in
# Nat.sqrt $ ((@id Nat) + fun x : Nat => x) 4

/-- info: Nat.sqrt (@HPow.hPow ℕ ℕ *0 *1 (@id ℕ 6) 3) -/
#guard_msgs in
# Nat.sqrt $ (id ^ 3 : Nat → Nat) 6

/-- info: Nat.sqrt (@HVAdd.hVAdd ℕ ℕ *0 *1 4 (@id ℕ 6)) -/
#guard_msgs in
# Nat.sqrt $ (4 +ᵥ id : Nat → Nat) 6

/-- info: Int.sqrt (@Neg.neg ℤ *0 (@id ℤ 6)) -/
#guard_msgs in
# Int.sqrt $ (-id : Int → Int) 6


-- only distibute the sum function application if the instance is Pi.instAdd:
private instance (priority := high) : Add (Nat → Nat) where
  add a _ := a

/-- info: Nat.sqrt (@HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) *0 *1 (@id ℕ) (@id ℕ) 4) -/
#guard_msgs in
# Nat.sqrt $ ((@id Nat) + fun x : Nat => x) 4



-- eta-redution is automatically reverted:
/-- info: @Function.Bijective ℕ ℕ (@HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) *0 *1 1 (@id ℕ)) -/
#guard_msgs in
# Function.Bijective (HAdd.hAdd 1)

/-- info: @Function.Bijective ℕ ℕ (@HMul.hMul (ℕ → ℕ) (ℕ → ℕ) *0 *1 1 (@id ℕ)) -/
#guard_msgs in
# Function.Bijective (HMul.hMul 1)

/-- info: @Function.Bijective ℕ ℕ (@HSub.hSub (ℕ → ℕ) (ℕ → ℕ) *0 *1 1 (@id ℕ)) -/
#guard_msgs in
# Function.Bijective (HSub.hSub 1)

/-- info: @Function.Bijective ℕ ℕ (@HDiv.hDiv (ℕ → ℕ) (ℕ → ℕ) *0 *1 1 (@id ℕ)) -/
#guard_msgs in
# Function.Bijective (HDiv.hDiv 1)

/-- info: @Function.Bijective ℚ ℚ (@Inv.inv (ℚ → ℚ) *0 (@id ℚ)) -/
#guard_msgs in
# Function.Bijective (Inv.inv : ℚ → ℚ)

/-- info: @Function.Bijective ℚ ℚ (@Neg.neg (ℚ → ℚ) *0 (@id ℚ)) -/
#guard_msgs in
# Function.Bijective (Neg.neg : ℚ → ℚ)

/-- info: @Function.Bijective ℤ ℤ (@HSMul.hSMul ℕ (ℤ → ℤ) *0 *1 4 (@id ℤ)) -/
#guard_msgs in
# Function.Bijective (HSMul.hSMul 4 : Int → Int)
/--
info: @Function.Bijective ℤ ℤ (@HVAdd.hVAdd (Additive ℕ) (ℤ → ℤ) *0 *1 (@DFunLike.coe (Equiv ℕ (Additive ℕ)) *2 *3 *4 (@Additive.ofMul ℕ) 4) (@id ℤ))
-/
#guard_msgs in
# Function.Bijective (HVAdd.hVAdd (Additive.ofMul (4 : Nat)) : Int → Int)



/--
info: @Function.Bijective ℕ ℕ (@HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) *0 *1 (@HMul.hMul (ℕ → ℕ) (ℕ → ℕ) *2 *3 (@id ℕ) 3) (@HDiv.hDiv (ℕ → ℕ) (ℕ → ℕ) *4 *5 4 (@HPow.hPow ℕ ℕ *6 *7 (@HVAdd.hVAdd ℕ ℕ *8 *9 3 (@HSMul.hSMul ℕ ℕ *10 *11 2 5)))))
-/
#guard_msgs in
# Function.Bijective fun x => x*3+4/(3+ᵥ2•5)^x

/--
info: Nat.sqrt (@HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) *0 *1 (@HVAdd.hVAdd ℕ (ℕ → ℕ) *2 *3 (@HSMul.hSMul ℕ ℕ *4 *5 2 1) (@id ℕ)) (@HDiv.hDiv (ℕ → ℕ) (ℕ → ℕ) *6 *7 (@HMul.hMul (ℕ → ℕ) (ℕ → ℕ) *8 *9 4 5) (@HPow.hPow (ℕ → ℕ) ℕ *10 *11 (@id ℕ) 9)) 5)
-/
#guard_msgs in
# Nat.sqrt $ ((2•1+ᵥid)+4*5/id^9 : Nat → Nat) 5


-- don't distrubute a lambda when the bound variable appears in the exponent/multiplier:
/-- info: @Function.Bijective ℕ ℕ (λ, @HPow.hPow ℕ ℕ *0 *1 #0 #0) -/
#guard_msgs in
# Function.Bijective fun x => x^x

/-- info: @Function.Bijective ℕ ℕ (λ, @HSMul.hSMul ℕ ℕ *0 *1 #0 5) -/
#guard_msgs in
# Function.Bijective fun x : Nat => x•5

/-- info: @Function.Bijective ℕ ℕ (λ, @HVAdd.hVAdd ℕ ℕ *0 *1 #0 #0) -/
#guard_msgs in
# Function.Bijective fun x : Nat => x+ᵥx

-- don't distribute a lambda when the bound variable appears in the instance:
/-- info: @id (Sort → (Ring #0) → #1) (λ, λ, @HAdd.hAdd #1 #1 *0 *1 1 2) -/
#guard_msgs in
# id fun (α : Type) [Ring α] => (1+2 : α)

/-- info: @id (Sort → (Ring #0) → #1) (λ, λ, @HSMul.hSMul ℕ #1 *0 *1 2 3) -/
#guard_msgs in
# id fun (α : Type) [Ring α] => (2•3 : α)



-- index constant number literal functions as just the number literal:
/-- info: @Function.Bijective ℕ ℕ 4 -/
#guard_msgs in
# Function.Bijective fun _ : Nat => 4

-- but not at the root:
/-- info: λ, @OfNat.ofNat ℕ 4 *0 -/
#guard_msgs in
# fun _ : Nat => 4

-- index metavariable constant functions as just a star pattern:
/-- info: @Function.Bijective ℕ ℕ *0 -/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVarQ q(ℕ)
  for keys in ← encodeExpr q(Function.Bijective fun _ : Nat => $m) do
    logInfo m! "{← keysAsPattern keys}"

-- but not at the root:
/-- info: λ, *0 -/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVarQ q(ℕ)
  for keys in ← encodeExpr q(fun _ : Nat => $m) do
    logInfo m! "{← keysAsPattern keys}"
