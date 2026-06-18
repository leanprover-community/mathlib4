import Mathlib.Lean.Meta.RefinedDiscrTree.Encode
import Mathlib

open Qq Lean Meta RefinedDiscrTree

macro "#log_keys" e:term : command =>
  `(command| run_meta do
    for keys in ← encodeExprWithEta (labelledStars := true) q($e) do
      logInfo m! "{← keysAsPattern keys}")

-- eta reduction:
/-- info: Int.succ -/
#guard_msgs in
#log_keys fun x => Int.succ x

-- potential eta reduction:
/--
info: @Function.Bijective ℤ ℤ Int.succ
---
info: @Function.Bijective ℤ ℤ (λ, Int.succ *)
-/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVarQ q(ℤ → ℤ)
  for keys in ← encodeExprWithEta (labelledStars := true) q(Function.Bijective fun x : Int => Int.succ ($m x)) do
      logInfo m! "{← keysAsPattern keys}"

/--
info: And (@Function.Bijective ℤ ℤ Int.succ) (@Function.Bijective ℤ ℤ Int.succ)
---
info: And (@Function.Bijective ℤ ℤ Int.succ) (@Function.Bijective ℤ ℤ (λ, Int.succ *))
---
info: And (@Function.Bijective ℤ ℤ (λ, Int.succ *)) (@Function.Bijective ℤ ℤ Int.succ)
---
info: And (@Function.Bijective ℤ ℤ (λ, Int.succ *)) (@Function.Bijective ℤ ℤ (λ, Int.succ *))
-/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVarQ q(ℤ → ℤ)
  for keys in ← encodeExprWithEta (labelledStars := true) q((Function.Bijective fun x : Int => Int.succ ($m x)) ∧
      Function.Bijective fun x : Int => Int.succ ($m x)) do
    logInfo m! "{← keysAsPattern keys}"

/--
info: @Eq *0 (@HAdd.hAdd *0 *0 * * (@HAdd.hAdd *0 *0 * * *1 *1) *2) (@HAdd.hAdd *0 *0 * * *1 a)
-/
#guard_msgs in
run_meta do
  let t ← mkFreshExprMVarQ q(Type)
  let _ ← mkFreshExprMVarQ q(Add $t)
  let m ← mkFreshExprMVarQ q($t)
  let m' ← mkFreshExprMVarQ q($t)
  withLocalDeclDQ `a q($t) fun n => do
  for keys in ← encodeExprWithEta (labelledStars := true) q($m+$m + $m' = $m + $n) do
    logInfo m! "{← keysAsPattern keys}"

/--
info: @Function.Bijective *0 *0 (@HAdd.hAdd *0 *0 * * *)
---
info: @Function.Bijective *0 *0 (λ, @HAdd.hAdd *0 *0 * * * *)
-/
#guard_msgs in
run_meta do
  let t ← mkFreshExprMVarQ q(Type)
  let _ ← mkFreshExprMVarQ q(Add $t)
  let m ← mkFreshExprMVarQ q($t → $t)
  let m' ← mkFreshExprMVarQ q($t → $t)
  for keys in ← encodeExprWithEta (labelledStars := true) q(Function.Bijective fun x => $m x + $m' x) do
    logInfo m! "{← keysAsPattern keys}"

/-- info: @OfNat.ofNat ℕ 2 * -/
#guard_msgs in
#log_keys let x := 2; x

-- unfolding reducible constants:
/-- info: @LE.le ℕ * 3 2 -/
#guard_msgs in
#log_keys 2 ≥ 3


/-- info: ℕ → @Eq ℕ #0 5 -/
#guard_msgs in
#log_keys ∀ x : Nat, x = 5

/-- info: ℕ → ℤ -/
#guard_msgs in
#log_keys Nat → Int

/-- info: λ, #0 -/
#guard_msgs in
#log_keys fun x : Nat => x

open Finset in
/-- info: @Finset.sum ℕ ℕ * (range 10) (λ, #0) -/
#guard_msgs in
#log_keys ∑ i ∈ range 10, i

/-- info: @Nat.fold ℕ 10 (λ, λ, λ, @HAdd.hAdd ℕ ℕ * * #0 #2) 1 -/
#guard_msgs in
#log_keys (10).fold (init := 1) (fun x _ y => y + x)

/-- info: @HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) * * (@id ℕ) (λ, #0) 4 -/
#guard_msgs in
#log_keys ((@id Nat) + fun x : Nat => x) 4

/-- info: Nat.sqrt (@HAdd.hAdd (ℕ → ℕ) (ℕ → ℕ) * * (@id ℕ) (λ, #0) 4) -/
#guard_msgs in
#log_keys Nat.sqrt $ ((@id Nat) + fun x : Nat => x) 4

/-- info: Nat.sqrt (@HPow.hPow (ℕ → ℕ) ℕ * * (@id ℕ) 3 6) -/
#guard_msgs in
#log_keys Nat.sqrt $ (id ^ 3 : Nat → Nat) 6

/-- info: Nat.sqrt (@HVAdd.hVAdd ℕ (ℕ → ℕ) * * 4 (@id ℕ) 6) -/
#guard_msgs in
#log_keys Nat.sqrt $ (4 +ᵥ id : Nat → Nat) 6

/-- info: Int.sqrt (@Neg.neg (ℤ → ℤ) * (@id ℤ) 6) -/
#guard_msgs in
#log_keys Int.sqrt $ (-id : Int → Int) 6



/--
info: @Function.Bijective
  ℕ
  ℕ
  (λ, @HAdd.hAdd
     ℕ
     ℕ
     *
     *
     (@HMul.hMul ℕ ℕ * * #0 3)
     (@HDiv.hDiv ℕ ℕ * * 4 (@HPow.hPow ℕ ℕ * * (@HVAdd.hVAdd ℕ ℕ * * 3 (@HSMul.hSMul ℕ ℕ * * 2 5)) #0)))
-/
#guard_msgs in
#log_keys Function.Bijective fun x => x*3+4/(3+ᵥ2•5)^x

/--
info: Nat.sqrt
  (@HAdd.hAdd
     (ℕ → ℕ)
     (ℕ → ℕ)
     *
     *
     (@HVAdd.hVAdd ℕ (ℕ → ℕ) * * (@HSMul.hSMul ℕ ℕ * * 2 1) (@id ℕ))
     (@HDiv.hDiv (ℕ → ℕ) (ℕ → ℕ) * * (@HMul.hMul (ℕ → ℕ) (ℕ → ℕ) * * 4 5) (@HPow.hPow (ℕ → ℕ) ℕ * * (@id ℕ) 9))
     5)
-/
#guard_msgs in
#log_keys Nat.sqrt $ ((2•1+ᵥid)+4*5/id^9 : Nat → Nat) 5


/-- info: @Function.Bijective ℕ ℕ (λ, @HPow.hPow ℕ ℕ * * #0 #0) -/
#guard_msgs in
#log_keys Function.Bijective fun x => x^x

/-- info: @Function.Bijective ℕ ℕ (λ, @HSMul.hSMul ℕ ℕ * * #0 5) -/
#guard_msgs in
#log_keys Function.Bijective fun x : Nat => x•5

/-- info: @Function.Bijective ℕ ℕ (λ, @HVAdd.hVAdd ℕ ℕ * * #0 #0) -/
#guard_msgs in
#log_keys Function.Bijective fun x : Nat => x+ᵥx

/-- info: @id (Sort → (Ring #0) → #1) (λ, λ, @HAdd.hAdd #1 #1 * * 1 2) -/
#guard_msgs in
#log_keys id fun (α : Type) [Ring α] => (1+2 : α)

/-- info: @id (Sort → (Ring #0) → #1) (λ, λ, @HSMul.hSMul ℕ #1 * * 2 3) -/
#guard_msgs in
#log_keys id fun (α : Type) [Ring α] => (2•3 : α)


/-- info: @Function.Bijective ℕ ℕ (λ, 4) -/
#guard_msgs in
#log_keys Function.Bijective fun _ : Nat => 4

/-- info: λ, @OfNat.ofNat ℕ 4 * -/
#guard_msgs in
#log_keys fun _ : Nat => 4


-- metavariables in a lambda body
/-- info: @Function.Bijective ℕ ℕ (λ, *0) -/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVarQ q(ℕ)
  for keys in ← encodeExprWithEta (labelledStars := true) q(Function.Bijective fun _ : Nat => $m) do
    logInfo m! "{← keysAsPattern keys}"

/-- info: λ, *0 -/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVarQ q(ℕ)
  for keys in ← encodeExprWithEta (labelledStars := true) q(fun _ : Nat => $m) do
    logInfo m! "{← keysAsPattern keys}"

/-- info: @Function.Bijective ℕ ℕ (λ, *) -/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVarQ q(ℕ → ℕ → ℕ)
  for keys in ← encodeExprWithEta (labelledStars := true) q(Function.Bijective fun x : Nat => $m x x) do
    logInfo m! "{← keysAsPattern keys}"

/-- info: λ, * -/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVarQ q(ℕ → ℕ → ℕ)
  for keys in ← encodeExprWithEta (labelledStars := true) q(fun x : Nat => $m x x) do
    logInfo m! "{← keysAsPattern keys}"
