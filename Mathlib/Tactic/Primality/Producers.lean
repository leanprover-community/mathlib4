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

/-- The witness of a primality certificate for one prime, tagged by the certificate type. -/
inductive Witness where
  /-- The witness of a Lucas certificate. -/
  | lucas (w : LucasWitness)

/-- The witnesses of a certificate. -/
inductive CertConfig where
  /-- The certificate with the witnesses in `witnesses`. A prime `q` takes the first entry whose
  factors are the prime factors of `q - 1` and whose root is a primitive root of `q`. Nothing is
  searched, so each prime needs an entry unless it is below `normNumBound` or proved by the
  user. -/
  | witnesses (witnesses : List Witness)

/-- The first entry of `witnesses` that is a Lucas witness for the prime `q`. -/
def witnessFor (witnesses : List Witness) (q : Nat) : CoreM LucasWitness := do
  for .lucas w in witnesses do
    if w.certifies q then
      return w
  throwError "no provided witness certifies the primality of {q}"

/-- Builds the certificate of `p` from the witness that `cfg` gives for each prime, with
`norm_num` below `normNumBound` and the user's proofs for the primes in `known`. Each prime's
certificate is built once. -/
partial def mkCert (cfg : CertConfig) (known : Std.HashSet Nat) (p : Nat) : CoreM (Cert p) :=
  StateT.run' (go p) {}
where
  /-- Builds the certificate of `q`. The state caches the certificates constructed for each
  nontrivial intermediate result. -/
  go (q : Nat) : StateT (Std.DHashMap Nat Cert) CoreM (Cert q) := do
    let cache ← get
    if let some cert := cache.get? q then
      return cert
    if known.contains q then
      return .known
    if q < normNumBound then
      return .normNum
    let w ← match cfg with
      | .witnesses witnesses => witnessFor witnesses q
    let cert : Cert q := .lucas w.root (← w.primeFactors.mapM fun r ↦ return ⟨r, ← go r⟩)
    modify (·.insert q cert)
    return cert

end Mathlib.Tactic.Primality
