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

/--
info: @Function.Bijective *0 *0 (@HAdd.hAdd *0 *0 *1 *2 *3)
---
info: @Function.Bijective *0 *0 (λ, @HAdd.hAdd *0 *0 *1 *2 *3 *4)
-/
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


/-- info: λ, #0 -/
#guard_msgs in
# fun x : Nat => x

open BigOperators Finset in
/-- info: @Finset.sum ℕ ℕ *0 (range 10) (λ, #0) -/
#guard_msgs in
# ∑ i ∈ range 10, i

/-- info: @Nat.fold ℕ 10 (λ, λ, λ, @HAdd.hAdd ℕ ℕ *0 *1 #0 #2) 1 -/
#guard_msgs in
# (10).fold (init := 1) (fun x _ y => y + x)

/-- info: @HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) *0 *1 (@id ℕ) (λ, #0) 4 -/
#guard_msgs in
# ((@id Nat) + fun x : Nat => x) 4

/-- info: Nat.sqrt (@HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) *0 *1 (@id ℕ) (λ, #0) 4) -/
#guard_msgs in
# Nat.sqrt $ ((@id Nat) + fun x : Nat => x) 4

/-- info: Nat.sqrt (@HPow.hPow (ℕ → ℕ) ℕ *0 *1 (@id ℕ) 3 6) -/
#guard_msgs in
# Nat.sqrt $ (id ^ 3 : Nat → Nat) 6

/-- info: Nat.sqrt (@HVAdd.hVAdd ℕ (ℕ → ℕ) *0 *1 4 (@id ℕ) 6) -/
#guard_msgs in
# Nat.sqrt $ (4 +ᵥ id : Nat → Nat) 6

/-- info: Int.sqrt (@Neg.neg (ℤ → ℤ) *0 (@id ℤ) 6) -/
#guard_msgs in
# Int.sqrt $ (-id : Int → Int) 6



/--
info: @Function.Bijective ℕ ℕ (λ, @HAdd.hAdd ℕ ℕ *0 *1 (@HMul.hMul ℕ ℕ *2 *3 #0 3) (@HDiv.hDiv ℕ ℕ *4 *5 4 (@HPow.hPow ℕ ℕ *6 *7 (@HVAdd.hVAdd ℕ ℕ *8 *9 3 (@HSMul.hSMul ℕ ℕ *10 *11 2 5)) #0)))
-/
#guard_msgs in
# Function.Bijective fun x => x*3+4/(3+ᵥ2•5)^x

/--
info: Nat.sqrt (@HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) *0 *1 (@HVAdd.hVAdd ℕ (ℕ → ℕ) *2 *3 (@HSMul.hSMul ℕ ℕ *4 *5 2 1) (@id ℕ)) (@HDiv.hDiv (ℕ → ℕ) (ℕ → ℕ) *6 *7 (@HMul.hMul (ℕ → ℕ) (ℕ → ℕ) *8 *9 4 5) (@HPow.hPow (ℕ → ℕ) ℕ *10 *11 (@id ℕ) 9)) 5)
-/
#guard_msgs in
# Nat.sqrt $ ((2•1+ᵥid)+4*5/id^9 : Nat → Nat) 5


/-- info: @Function.Bijective ℕ ℕ (λ, @HPow.hPow ℕ ℕ *0 *1 #0 #0) -/
#guard_msgs in
# Function.Bijective fun x => x^x

/-- info: @Function.Bijective ℕ ℕ (λ, @HSMul.hSMul ℕ ℕ *0 *1 #0 5) -/
#guard_msgs in
# Function.Bijective fun x : Nat => x•5

/-- info: @Function.Bijective ℕ ℕ (λ, @HVAdd.hVAdd ℕ ℕ *0 *1 #0 #0) -/
#guard_msgs in
# Function.Bijective fun x : Nat => x+ᵥx

/-- info: @id (Sort → (Ring #0) → #1) (λ, λ, @HAdd.hAdd #1 #1 *0 *1 1 2) -/
#guard_msgs in
# id fun (α : Type) [Ring α] => (1+2 : α)

/-- info: @id (Sort → (Ring #0) → #1) (λ, λ, @HSMul.hSMul ℕ #1 *0 *1 2 3) -/
#guard_msgs in
# id fun (α : Type) [Ring α] => (2•3 : α)



/-- info: @Function.Bijective ℕ ℕ (λ, 4) -/
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
