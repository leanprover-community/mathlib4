/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Mathlib.Tactic.Primality.Lucas
public import Mathlib.Init
public import Mathlib.Tactic.Primality.Cert

/-!
# Producers

This file builds primality certificates from the witnesses the user provides.
-/

public meta section

open Lean

namespace Mathlib.Tactic.Primality

/-- Numbers below this bound are proved prime by `norm_num`'s evaluation of `Nat.minFac`. -/
def normNumBound : Nat := 2 ^ 10

-- TODO: add more witness classes (Pocklington variants).
/-- The witness of a primality certificate for one prime, tagged by the certificate type. -/
inductive Witness where
  /-- The witness of a Lucas certificate. -/
  | lucas (w : LucasWitness)

-- TODO: add a witness searching mode that factorises `p - 1` and constructs the primality
-- certificate.
/-- The witnesses of a certificate. -/
inductive CertConfig where
  /-- The certificate with a list of explicit witnesses in `witnesses`. A prime `p` takes the
  first entry whose factors are the prime factors of `p - 1` and whose root is a primitive root of
  `p`. Nothing is searched, so each prime needs an entry unless it is below `normNumBound` or
  proved by the user. -/
  | witnesses (witnesses : List Witness)

/-- Find the first entry of `witnesses` that is a Lucas witness for the prime `p`. -/
def witnessFor (witnesses : List Witness) (p : Nat) : CoreM LucasWitness := do
  for .lucas w in witnesses do
    if w.certifies p then
      return w
  throwError "no provided witness certifies the primality of {p}"

/-- Builds the certificate of `p` from the witness that `cfg` gives for each prime, with
`norm_num` below `normNumBound` and the user's proofs for the primes in `known`. Each prime's
certificate is built once. -/
partial def mkCert (cfg : CertConfig) (known : Std.HashSet Nat) (p : Nat) : CoreM (Cert p) :=
  StateT.run' (go p) {}
where
  /-- Builds the certificate of `p`. The state caches the certificates constructed for each
  nontrivial intermediate result. -/
  go (p : Nat) : StateT (Std.DHashMap Nat Cert) CoreM (Cert p) := do
    let cache ← get
    if let some cert := cache.get? p then
      return cert
    if known.contains p then
      return .known
    if p < normNumBound then
      return .normNum
    let w ← match cfg with
      | .witnesses witnesses => witnessFor witnesses p
    let cert : Cert p := .lucas w.root (← w.primeFactors.mapM fun q ↦ return ⟨q, ← go q⟩)
    modify (·.insert p cert)
    return cert

end Mathlib.Tactic.Primality
