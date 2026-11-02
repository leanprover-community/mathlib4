/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.NormNum.Prime  -- shake: keep (`Nat.Prime` extension for `deriveBool`)
public import Mathlib.Tactic.Primality.Lucas

/-!
# Primality certificates

Certificates of primality, the search that finds one for a prime helped by user hints, and a
certifier that constructs a `Nat.Prime` proof term from a certificate.
-/

public meta section

open Lean Meta Qq Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Primality

/-- Numbers below this bound are proved prime by `norm_num`'s evaluation of `Nat.minFac`. -/
def normNumBound : Nat := 2 ^ 16

/-- The certificate family with its options. -/
inductive CertConfig where
  /-- Lucas certificates. -/
  | lucas (cfg : LucasConfig)

/-- A certificate that `p` is prime. -/
inductive Cert : Nat → Type where
  /-- `p` is proved prime by `norm_num`. -/
  | normNum {p : Nat} : Cert p
  /-- A proof that `p` is prime is provided. -/
  | known {p : Nat} : Cert p
  /-- A Lucas certificate with the primitive root `root` and the prime factors of `p - 1` with
  their certificates in `factors`. -/
  | lucas {p : Nat} (root : Nat) (factors : Array ((q : Nat) × Cert q)) : Cert p

/-- Finds a primality certificate for `p` with the witnesses from `factorizer` and `rootFinder`
using the Lucas test. Small numbers are handled by `norm_num`'s trial division. -/
partial def findLucasCert (factorizer : Factorizer) (rootFinder : PrimitiveRootFinder)
    (known : Std.HashSet Nat) (p : Nat) : CoreM (Cert p) :=
  StateT.run' (go p) {}
where
  /-- Finds a certificate for `q`. The state caches the certificates constructed for each
  nontrivial intermediate result. -/
  go (q : Nat) : StateT (Std.DHashMap Nat Cert) CoreM (Cert q) := do
    let cache ← get
    if let some cert := cache.get? q then
      return cert
    if known.contains q then
      return .known
    if q < normNumBound then
      return .normNum
    let w ← findLucasWitness factorizer rootFinder p q
    let cert : Cert q := .lucas w.root (← w.factors.mapM fun r ↦ return ⟨r, ← go r⟩)
    modify (·.insert q cert)
    return cert

/-- Finds a certificate for `p` with the options in `cfg`. The search of a certificate family
throws its own error at the first value it cannot find a witness. -/
def findCert (cfg : CertConfig) (known : Array Nat) (p : Nat) : CoreM (Cert p) :=
  match cfg with
  | .lucas lucasCfg =>
    findLucasCert ((Factorizer.ofArray known).then lucasCfg.toFactorizer)
      lucasCfg.toPrimitiveRootFinder (.ofArray known) p

/-- Proves `Nat.Prime p` from the certificate `cert`. The cache holds the proof of each prime, so
that each prime is proved only once. -/
partial def certifyPrime {p : Nat} (cert : Cert p) :
    MonadStateCacheT Nat Expr MetaM Q(Nat.Prime $p) :=
  checkCache (β := Expr) p fun _ ↦ do
    match cert with
    | .normNum =>
      let ⟨true, pf⟩ ← deriveBool q(Nat.Prime $p) | throwError "{p} is not prime"
      return pf
    | .known => throwError "no proof that {p} is prime is provided"
    | .lucas root factors =>
      return certifyLucas p root (← factors.mapM fun ⟨q, cert⟩ ↦ return ⟨q, ← certifyPrime cert⟩)

end Mathlib.Tactic.Primality
