/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Mathlib.Data.Nat.MaxPowDiv
public meta import Mathlib.Tactic.Primality.Lucas
public import Mathlib.Init
public import Mathlib.Tactic.Primality.Cert

/-!
# Producers

This file defines the producers of the witnesses of primality certificates.

- Factorizers: find prime factors of `p - 1`.
- Primitive root search: finds a primitive root mod `p`.
-/

public meta section

open Lean

namespace Mathlib.Tactic.Primality

/-- Numbers below this bound are proved prime by `norm_num`'s evaluation of `Nat.minFac`. -/
def normNumBound : ℕ := 2 ^ 10

section Factorizer

/-- Returns an array of distinct prime factors of the input (not necessarily complete).
Works in `CoreM` to check heartbeats and handle cancellation. -/
abbrev Factorizer := ℕ → CoreM (Array ℕ)

/-- Returns the prime factors of `n` that `f` finds, plus the remaining factor with all of the
found prime factors divided out. -/
def Factorizer.decompose (f : Factorizer) (n : ℕ) : CoreM (Array ℕ × ℕ) := do
  let ps ← f n
  return (ps, ps.foldl Nat.divMaxPow n)

/-- Returns the candidates in `factors` that divide its input. To ensure that the returned array
consists of primes only, the array of factors should ideally all be prime. -/
def Factorizer.ofArray (factors : Array ℕ) : Factorizer := fun n ↦
  pure (factors.foldl (init := (#[], n)) fun (found, rest) p ↦
    if 1 < p && rest % p == 0 then (found.push p, rest.divMaxPow p) else (found, rest)).1

/-- Runs `f₁` on `n`, then `f₂` on what is left after dividing out the factors `f₁` returned. -/
def Factorizer.then (f₁ f₂ : Factorizer) : Factorizer := fun n ↦ do
  let (ps, rest) ← f₁.decompose n
  return ps ++ (← f₂ rest)

/-- The primes below `bound`. This is currently called once per tactic run. -/
def smallPrimes (bound : ℕ) : Array ℕ := Id.run do
  let mut composite := Array.replicate bound false
  let mut primes := #[]
  for k in 2...bound do
    unless composite[k]! do
      primes := primes.push k
      let mut j := k * k
      while j < bound do
        composite := composite.set! j true
        j := j + k
  return primes

/-- Trial division by `smallPrimes normNumBound`. -/
def trialDivision : Factorizer := .ofArray (smallPrimes normNumBound)

section PollardRho

/-- Whether `n` passes the Miller–Rabin test to the prime bases `bases`. -/
def millerRabin (bases : Array ℕ) (n : ℕ) : Bool := Id.run do
  if n < 2 then return false
  if let some a := bases.find? (n % · == 0) then return n == a
  let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
  for a in bases do
    let mut x := Nat.powMod a d n
    if x == 1 then continue
    for _ in 1...s do
      if x == n - 1 then break
      x := x * x % n
    if x != n - 1 then return false
  return true

/-- Whether `n` passes the Miller–Rabin test to the prime bases up to `41` (no false-positive up to
`3.3 * 10 ^ 24`). -/
def isProbablePrime (n : ℕ) : Bool :=
  millerRabin #[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41] n

/-- Finds a nontrivial factor of `n` by Pollard's rho method with `x ↦ x ^ 2 + c` in at most
`steps` steps, starting with `c = 1` and moving to the next `c` when a run finds `n` itself. -/
def rhoFactor? (n steps : ℕ) : CoreM (Option ℕ) := do
  let mut c := 1
  let mut x := 2
  let mut y := 2
  for i in 0...steps do
    if i % 4096 == 0 then
      checkSystem "pollardRho"
    x := (x * x + c) % n
    y := (y * y + c) % n
    y := (y * y + c) % n
    let d := Nat.gcd (x + n - y) n
    if d == n then
      c := c + 1
      x := 2
      y := 2
    else if d != 1 then
      return some d
  return none

/-- Splits `n` by `rhoFactor?` into factors that pass `isProbablePrime`, and returns the distinct
ones. A part that it cannot split is left out. -/
partial def pollardRho (steps : ℕ) : Factorizer := fun n ↦ do
  if n < 2 then return #[]
  if isProbablePrime n then return #[n]
  let some d ← rhoFactor? n steps | return #[]
  let ps ← pollardRho steps d
  return ps ++ (← pollardRho steps (n / d)).filter (!ps.contains ·)

end PollardRho

/-- Options for factorizing `p - 1`. -/
structure FactorizerConfig where
  /-- Candidate prime factors, tried before trial division on `p - 1` and on `q - 1` for each prime
  `q` required on the way. -/
  factors : List ℕ := []
  /-- The number of steps of Pollard's rho method on each number before it gives up. -/
  rhoSteps : ℕ := 2 ^ 17

/-- Tries `factors`, then trial division up to `normNumBound`, then Pollard's rho method. -/
def FactorizerConfig.toFactorizer (cfg : FactorizerConfig) : Factorizer :=
  Factorizer.then (.ofArray cfg.factors.toArray) <|
    trialDivision.then (pollardRho cfg.rhoSteps)

end Factorizer

/-- Searches for the root and the factorization of `p - 1` of a Lucas witness for `p`, trying
`2, …, 1023` as primitive roots. The part of `p - 1` that the factorizer leaves is taken to be
prime. -/
def findLucasWitness (factorizer : Factorizer) (p : ℕ) : CoreM (ℕ × List (ℕ × ℕ)) := do
  let (factors, rest) ← factorizer.decompose (p - 1)
  let primeFactors := (if rest == 1 then factors else factors.push rest).toList
  for root in 2...1024 do
    if let some factorization := LucasWitness.factorization? { root, primeFactors } p then
      return (root, factorization)
  throwError "primality failed to find a witness for {p}; provide the certificate at \
    `.witnesses […]`"

-- TODO: add more witness types (Pocklington variants).
/-- The witness of a primality certificate for one prime, tagged by the certificate type. -/
inductive Witness where
  /-- The witness of a Lucas certificate. -/
  | lucas (w : LucasWitness)

/-- Where the witnesses of a certificate come from. -/
inductive CertMode where
  /-- The witnesses are searched for, with the factorizer options `cfg`. -/
  | search (cfg : FactorizerConfig)
  /-- The certificate with a list of explicit witnesses in `witnesses`. A prime `p` takes the
  first entry whose factors are the prime factors of `p - 1` and whose root is a primitive root of
  `p`. -/
  | witnesses (witnesses : List Witness)

/-- Find the root and the factorization of `p - 1` given by the first entry of `witnesses` that is
a Lucas witness for the prime `p`. -/
def witnessFor (witnesses : List Witness) (p : ℕ) : CoreM (ℕ × List (ℕ × ℕ)) := do
  for .lucas w in witnesses do
    if let some factorization := w.factorization? p then
      return (w.root, factorization)
  throwError "no provided witness certifies the primality of {p}"

/-- Builds the certificate of `p` from the root and the factorization of `p - 1` that `witness`
gives for each prime, with `norm_num` below `normNumBound` and the user's proofs for the primes in
`known`. Each prime's certificate is built once. -/
partial def Cert.build (witness : ℕ → CoreM (ℕ × List (ℕ × ℕ))) (known : Std.HashSet ℕ)
    (p : ℕ) : CoreM Cert :=
  StateT.run' (go p) {}
where
  /-- Builds the certificate of `p`. The state caches the certificates constructed for each
  nontrivial intermediate result. -/
  go (p : ℕ) : StateT (Std.HashMap ℕ Cert) CoreM Cert := do
    if let some cert := (← get)[p]? then
      return cert
    if known.contains p then
      return .known
    if p < normNumBound then
      return .normNum
    let (root, factorization) ← witness p
    let cert : Cert := .lucas root (← factorization.mapM fun (q, e) ↦ return (q, e, ← go q))
    modify (·.insert p cert)
    return cert

/-- Builds the certificate of `p` from the first entry of `witnesses` that fits each prime. -/
def Cert.ofWitnesses (witnesses : List Witness) (known : Std.HashSet ℕ) (p : ℕ) : CoreM Cert :=
  Cert.build (witnessFor witnesses) known p

/-- Builds the certificate of `p` from witnesses searched for with the factorizer options `cfg`,
trying the user's primes in `known` as factors first. -/
def Cert.search (cfg : FactorizerConfig) (known : Std.HashSet ℕ) (p : ℕ) : CoreM Cert :=
  Cert.build (findLucasWitness ((Factorizer.ofArray known.toArray).then cfg.toFactorizer)) known p

end Mathlib.Tactic.Primality
