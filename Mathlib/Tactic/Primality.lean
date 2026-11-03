/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Primality.Cert
public import Mathlib.Tactic.Primality.Producers

/-!
# `primality`

This file defines the `primality` tactic, which closes goals `Nat.Prime n` using a closed family of
primality certificates, with witnesses it finds itself or takes from the user.
-/

public meta section

open Lean Meta Elab Tactic Qq Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Primality

/-- Numbers below this bound are proved prime by `norm_num`'s evaluation of `Nat.minFac`. -/
def normNumBound : Nat := 2 ^ 16

/-- The witness of a primality certificate for one prime, tagged by the certificate type. -/
inductive Witness where
  /-- The witness of a Lucas certificate. -/
  | lucas (w : LucasWitness)

/-- The certificate family to search in with its options, or the witnesses of a certificate. -/
inductive CertConfig where
  /-- Lucas certificates. -/
  | lucas (cfg : LucasConfig)
  /-- The certificate with the witnesses in `witnesses`. A prime `q` takes the first entry whose
  factors are the prime factors of `q - 1` and whose root is a primitive root of `q`. Nothing is
  searched, so each prime needs an entry unless it is below `normNumBound` or proved by the
  user. -/
  | witnesses (witnesses : List Witness)

/-- Finds a primality certificate for `p` using the Lucas test, with the witness of each prime from
`witnessOf`. Small numbers are handled by `norm_num`'s trial division. -/
partial def findLucasCert (witnessOf : Nat → CoreM LucasWitness) (known : Std.HashSet Nat)
    (p : Nat) : CoreM (Cert p) :=
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
    let w ← witnessOf q
    let cert : Cert q := .lucas w.root (← w.factors.mapM fun r ↦ return ⟨r, ← go r⟩)
    modify (·.insert q cert)
    return cert

/-- Finds a certificate for `p` with the options in `cfg`. The search of a certificate family
throws its own error at the first value it cannot find a witness. -/
def findCert (cfg : CertConfig) (known : Array Nat) (p : Nat) : CoreM (Cert p) :=
  match cfg with
  | .lucas lucasCfg =>
    findLucasCert (findLucasWitness ((Factorizer.ofArray known).then lucasCfg.toFactorizer)
      lucasCfg.toPrimitiveRootFinder p) (.ofArray known) p
  | .witnesses witnesses =>
    findLucasCert (fun q ↦ do
      for .lucas w in witnesses do
        if w.factors.all (fun r ↦ (q - 1) % r == 0) && w.factors.foldl Nat.divMaxPow (q - 1) == 1 &&
            (← PrimitiveRootFinder.ofArray #[w.root] q w.factors).isSome then
          return w
      throwError "no provided witness certifies the primality of {q}") (.ofArray known) p

/-- Configuration for `primality`. -/
structure Config where
  /-- The certificate configuration to use. -/
  cert : CertConfig := .lucas {}

/-- Function elaborating `Config`. -/
declare_config_elab elabPrimalityConfig Config

/-- Evaluates `e` to a numeral with `norm_num`, if it can. -/
def evalNumeral? (e : Q(Nat)) : MetaM (Option (Nat × (nQ : Q(Nat)) × Q(IsNat $e $nQ))) := do
  let some ⟨nQ, pn⟩ ← try some <$> deriveNat e q(Nat.instAddMonoidWithOne) catch _ => pure none |
    return none
  let .lit (.natVal n) := nQ | return none
  return some ⟨n, nQ, pn⟩

/-- Store the proofs `hs` of `Nat.Prime n` in a hashmap. -/
def elabProofs (hs : Array Term) : TacticM (Std.HashMap Nat Expr) := do
  let mut known : Std.HashMap Nat Expr := {}
  for h in hs do
    let h ← elabTerm h none
    let_expr Nat.Prime e := ← instantiateMVars (← inferType h) |
      throwError "{h} is not recognized as a proof of `Nat.Prime n`"
    have e : Q(Nat) := e
    have h : Q(Nat.Prime $e) := h
    let some ⟨q, qQ, pn⟩ ← evalNumeral? e |
      throwError "{h} is not recognized as a proof of `Nat.Prime n`"
    known := known.insert q q(isNat.natElim (p := fun m ↦ Nat.Prime m → Nat.Prime $qQ) $pn id $h)
  return known

/-- `primality` tries to prove a goal `Nat.Prime n`, using the hints provided by the user if any.
Refer to `MathlibTest.Tactic.Primality` for a gallery of usages. -/
syntax (name := primality) "primality" optConfig (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| primality $cfg:optConfig $[[$hs,*]]?) => withMainContext do
    let cfg ← elabPrimalityConfig cfg
    let known ← elabProofs <| hs.map (·.getElems) |>.getD #[]
    liftMetaFinishingTactic fun g ↦ do
      let_expr Nat.Prime e := ← instantiateMVars (← g.getType) |
        throwError "the goal is not of the form `Nat.Prime n`"
      have e : Q(Nat) := e
      let some ⟨p, pQ, pn⟩ ← evalNumeral? e |
        throwError "{e} does not evaluate to a numeral; try simplifying it first"
      let cert ← findCert cfg.cert known.keysArray p
      let hp : Q(Nat.Prime $pQ) ← StateT.run' (certifyPrime cert) known
      g.assign q(isNat.natElim (p := Nat.Prime) $pn $hp)

end Mathlib.Tactic.Primality
