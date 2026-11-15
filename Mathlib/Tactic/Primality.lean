/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Primality.Producers

/-!
# `primality`

Defines the frontend of the `primality` tactic, which closes goals `Nat.Prime n` using a
certificate constructed from witnesses it takes from the user.
-/

public meta section

open Lean Meta Elab Tactic Qq Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Primality

/-- Configuration for `primality`. -/
structure Config where
  /-- The certificate configuration to use. -/
  cert : CertMode := .witnesses []

/-- Function elaborating `Config`. -/
declare_config_elab elabPrimalityConfig Config

/-- Evaluates `e` to a numeral with `norm_num`, if it can. -/
def evalNumeral? (e : Q(ℕ)) : MetaM (Option (ℕ × (nQ : Q(ℕ)) × Q(IsNat $e $nQ))) := do
  let some ⟨nQ, pn⟩ ← try some <$> deriveNat e q(Nat.instAddMonoidWithOne) catch _ => pure none |
    return none
  let .lit (.natVal n) := nQ | return none
  return some ⟨n, nQ, pn⟩

/-- Store the proofs `hs` of `Nat.Prime n` in a hashmap. -/
def elabKnownPrimes (hs : Array Term) : TacticM (Std.HashMap ℕ Expr) := do
  let mut known : Std.HashMap ℕ Expr := {}
  for h in hs do
    let h ← elabTerm h none
    let_expr Nat.Prime e := ← instantiateMVars (← inferType h) |
      throwError "{h} is not recognized as a proof of `Nat.Prime n`"
    have e : Q(ℕ) := e
    have h : Q(Nat.Prime $e) := h
    let some ⟨p, pQ, pn⟩ ← evalNumeral? e |
      throwError "the tactic cannot simplify {e} to a numeral"
    known := known.insert p q(isNat.natElim (p := fun m ↦ Nat.Prime m → Nat.Prime $pQ) $pn id $h)
  return known

/-- `primality` proves a goal `Nat.Prime n`, where `norm_num` evaluates `n` to a numeral, from a
Lucas certificate given as a list of witnesses.

A Lucas certificate proves `p` prime by a primitive root `a` of `p`, a number with
`a ^ (p - 1) % p = 1` and `a ^ ((p - 1) / q) % p ≠ 1` for each prime factor `q` of `p - 1`. Each
such `q` needs a certificate too, except for primes below `2 ^ 10` which are left to `norm_num`.

```lean
example : Nat.Prime 1000003 := by
  primality (cert := .witnesses [
    -- Proves `1000003` prime, since `1000003 - 1 = 2 * 3 * 166667` and `2` is a primitive root.
    .lucas { root := 2, primeFactors := [2, 3, 166667] },
    -- Proves `166667` prime, since `166667 - 1 = 2 * 167 * 499` and `2` is a primitive root.
    .lucas { root := 2, primeFactors := [2, 167, 499] }])
```

`primality (cert := …) [h₁, …]` takes proofs `hᵢ : Nat.Prime m` instead of a certificate.
See `MathlibTest/Tactic/Primality.lean` for more examples. -/
syntax (name := primality) "primality" optConfig (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| primality $cfg:optConfig $[[$hs,*]]?) => withMainContext do
    let .witnesses witnesses := (← elabPrimalityConfig cfg).cert
    let witnesses := witnesses.map fun (.lucas w) ↦
      Witness.lucas { w with primeFactors := w.primeFactors.eraseDups }
    let known ← elabKnownPrimes <| hs.map (·.getElems) |>.getD #[]
    liftMetaFinishingTactic fun g ↦ do
      let_expr Nat.Prime e := ← instantiateMVars (← g.getType) |
        throwError "the goal is not of the form `Nat.Prime n`"
      have e : Q(ℕ) := e
      let some ⟨p, pQ, pn⟩ ← evalNumeral? e |
        throwError "{e} does not evaluate to a numeral; try simplifying it first"
      let cert ← Cert.ofWitnesses witnesses (.ofArray known.keysArray) p
      let hp : Q(Nat.Prime $pQ) ← StateT.run' (certifyPrime p cert) known
      g.assign q(isNat.natElim (p := Nat.Prime) $pn $hp)

end Mathlib.Tactic.Primality
