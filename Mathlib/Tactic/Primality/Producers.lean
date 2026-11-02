/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Init

/-!
# Producers

This file defines the producers of the witnesses of primality certificates.

- Factorizers: find prime factors of `p - 1`.
- Primitive root finders: find primitive roots mod `p`.
-/

public meta section

open Lean

namespace Mathlib.Tactic.Primality

section Factorizer

/-- Returns an array of distinct prime factors of the input (not necessarily complete).
Works in `CoreM` to check heartbeats and handle cancellation. -/
abbrev Factorizer := Nat → CoreM (Array Nat)

/-- Returns the prime factors of `n` that `f` finds, plus the remaining factor with all of the
found prime factors divided out. -/
def Factorizer.decompose (f : Factorizer) (n : Nat) : CoreM (Array Nat × Nat) := do
  let ps ← f n
  return (ps, ps.foldl Nat.divMaxPow n)

/-- Returns the candidates in `factors` that divide its input. To ensure that the returned array
consists of primes only, the array of factors should ideally all be prime. -/
def Factorizer.ofArray (factors : Array Nat) : Factorizer := fun n ↦
  pure (factors.foldl (init := (#[], n)) fun (found, rest) q ↦
    if 1 < q && rest % q == 0 then (found.push q, rest.divMaxPow q) else (found, rest)).1

/-- Runs `f₁` on `n`, then `f₂` on what is left after dividing out the factors `f₁` returned. -/
def Factorizer.then (f₁ f₂ : Factorizer) : Factorizer := fun n ↦ do
  let (ps, rest) ← f₁.decompose n
  return ps ++ (← f₂ rest)

/-- The primes below `1024`. This is currently called once per tactic run. -/
def smallPrimes : Array Nat := Id.run do
  let bound := 1024
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

/-- Trial division by `smallPrimes`. -/
def trialDivision : Factorizer := .ofArray smallPrimes

section PollardRho

/-- Whether `n` passes the Miller–Rabin test to the prime bases `bases`. -/
def millerRabin (bases : Array Nat) (n : Nat) : Bool := Id.run do
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

/-- Whether `n` passes the Miller–Rabin test to the prime bases up to `41`, which no composite below
`3.3 * 10 ^ 24` does. -/
def isProbablePrime (n : Nat) : Bool :=
  millerRabin #[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41] n

/-- Finds a nontrivial factor of `n` by Pollard's rho method with `x ↦ x ^ 2 + c`, trying
`c = 1, 2, 3` for at most `steps` steps each. -/
def rhoFactor? (n steps : Nat) : CoreM (Option Nat) := do
  for c in 1...=3 do
    let mut x := 2
    let mut y := 2
    for i in 0...steps do
      if i % 4096 == 0 then
        checkSystem "pollardRho"
      x := (x * x + c) % n
      y := (y * y + c) % n
      y := (y * y + c) % n
      let d := Nat.gcd (x + n - y) n
      if d == n then break
      if d != 1 then return some d
  return none

/-- Splits `n` by `rhoFactor?` into factors that pass `isProbablePrime`, and returns the distinct
ones. A part that it cannot split is left out. -/
partial def pollardRho (steps : Nat) : Factorizer := fun n ↦ do
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
  factors : List Nat := []
  /-- The number of steps of Pollard's rho method for each constant it tries. -/
  rhoSteps : Nat := 2 ^ 15

/-- Tries `factors`, then trial division up to `1024`, then Pollard's rho method. -/
def FactorizerConfig.toFactorizer (cfg : FactorizerConfig) : Factorizer :=
  Factorizer.then (.ofArray cfg.factors.toArray) <|
    trialDivision.then (pollardRho cfg.rhoSteps)

end Factorizer

section PrimitiveRootFinder

/-- Returns a primitive root of `p` given the prime factors of `p - 1`. -/
abbrev PrimitiveRootFinder := Nat → Array Nat → CoreM (Option Nat)

/-- Tries the candidates `roots` in order, each reduced modulo `p`, and stops at a candidate showing
that `p` is composite. -/
def PrimitiveRootFinder.ofArray (roots : Array Nat) : PrimitiveRootFinder := fun p factors ↦ do
  for a in roots do
    let a := a % p
    if a == 0 then continue
    if Nat.powMod a (p - 1) p != 1 then return none
    if factors.all fun q ↦ Nat.powMod a ((p - 1) / q) p != 1 then return some a
  return none

/-- Runs `f₁`, followed by `f₂` if `f₁` finds nothing. -/
def PrimitiveRootFinder.then (f₁ f₂ : PrimitiveRootFinder) : PrimitiveRootFinder :=
  fun p factors ↦ do
    if let some a ← f₁ p factors then
      return some a
    f₂ p factors

/-- Tries `2, …, 1023` as primitive roots. -/
def trialRoots : PrimitiveRootFinder := .ofArray (2...1024).toArray

/-- Options for finding primitive roots. -/
structure PrimitiveRootFinderConfig where
  /-- Candidate primitive roots, tried before the search for the input and the required
  intermediate primes. -/
  roots : List Nat := []

/-- Tries `roots`, then the numbers below `1024`. -/
def PrimitiveRootFinderConfig.toPrimitiveRootFinder (cfg : PrimitiveRootFinderConfig) :
    PrimitiveRootFinder :=
  .then (.ofArray cfg.roots.toArray) trialRoots

end PrimitiveRootFinder

end Mathlib.Tactic.Primality
