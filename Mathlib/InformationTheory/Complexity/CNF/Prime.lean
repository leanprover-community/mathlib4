/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.InformationTheory.Complexity.CNF
public import Mathlib.Data.Nat.Prime.Infinite

@[expose] public section


/-!
# Prime Encoding for CNF Literals and Clauses

This file defines a prime-indexed encoding of CNF literals and clauses.
Each literal is mapped to a unique prime number via `primeIndexedAtom`,
and clauses are encoded as products of their literal primes.

## Main definitions

* `LiteralIndex` -- type alias for natural numbers representing literal indices.
* `LiteralToPrime` -- maps a literal to a positive natural number code.
* `primeIndexedAtom` -- a strictly increasing sequence of primes.
* `literalAtom` -- maps a literal to a unique prime via `primeIndexedAtom`.
* `ClauseComposite` -- type alias for the composite number encoding of a clause.
* `ClauseToComposite` -- encodes a clause as a product of literal codes.
* `clauseCompositePrime` -- encodes a clause as a product of prime-indexed atoms.
* `CNFToNumberList` / `CNFToPrimeNumberList` -- encode a CNF as a list of composites.

## Main results

* `primeIndexedAtom_prime` -- every term in the sequence is prime.
* `primeIndexedAtom_strictMono` -- the sequence is strictly increasing.
* `literalAtom_prime` -- the prime-indexed literal atom is prime.
* `literalAtom_injective` -- the prime-indexed literal atom map is injective.
-/

namespace InformationTheory

open InformationTheory

/-- A Literal is an atom of information (a Prime). -/
abbrev LiteralIndex := ℕ -- We use Nat, but conceptually it's a Prime

/-- Map a literal to a unique atom code (prime-like factor token). -/
def LiteralToPrime {k : ℕ} (lit : Literal k) : ℕ :=
  lit.toNat + 1

/--
`primeIndexedAtom n` is a strictly increasing prime sequence.
It starts at `2`, and each successor is chosen as a prime at least `prev + 1`.
-/
noncomputable def primeIndexedAtom : ℕ → ℕ
  | 0 => 2
  | n + 1 => Nat.find (Nat.exists_infinite_primes (primeIndexedAtom n + 1))

/-- Every term in `primeIndexedAtom` is prime. -/
lemma primeIndexedAtom_prime (n : ℕ) : Nat.Prime (primeIndexedAtom n) := by
  induction n with
  | zero =>
      simpa [primeIndexedAtom] using Nat.prime_two
  | succ n _ih =>
      simpa [primeIndexedAtom] using
        (Nat.find_spec
          (Nat.exists_infinite_primes
            (primeIndexedAtom n + 1))).2

/-- `primeIndexedAtom` is strictly increasing. -/
lemma primeIndexedAtom_strictMono : StrictMono primeIndexedAtom := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hbound : primeIndexedAtom n + 1 ≤ primeIndexedAtom (n + 1) := by
    simpa [primeIndexedAtom] using
      (Nat.find_spec
        (Nat.exists_infinite_primes
          (primeIndexedAtom n + 1))).1
  exact lt_of_lt_of_le (Nat.lt_succ_self (primeIndexedAtom n)) hbound

/-- `primeIndexedAtom` is injective. -/
lemma primeIndexedAtom_injective : Function.Injective primeIndexedAtom :=
  primeIndexedAtom_strictMono.injective

/--
Prime-indexed atom for literals.
This is the theorem-bearing encoding path used by SAT common-factor proofs.
-/
noncomputable def literalAtom {k : ℕ} (lit : Literal k) : ℕ :=
  primeIndexedAtom (Encodable.encode lit)

/-- The prime-indexed literal atom is prime. -/
lemma literalAtom_prime {k : ℕ} (lit : Literal k) : Nat.Prime (literalAtom lit) := by
  simpa [literalAtom] using primeIndexedAtom_prime (Encodable.encode lit)

/-- The prime-indexed literal atom map is injective. -/
lemma literalAtom_injective {k : ℕ} : Function.Injective (@literalAtom k) := by
  intro l₁ l₂ h
  apply Encodable.encode_injective
  exact primeIndexedAtom_injective (by simpa [literalAtom] using h)

/-!
## Computable Prime Sequence

Each literal must map to a unique PRIME — a vector, not a scalar.
The noncomputable `primeIndexedAtom` already does this via `Nat.find`.
Here we provide a computable version using `Nat.Prime` (which is
decidable via Mathlib) and bounded search.
-/

/-- Computable primality test. `Nat.Prime` is decidable in Mathlib. -/
instance : DecidablePred Nat.Prime := Nat.decidablePrime

/-- Find the smallest prime ≥ `n`, searching up to `bound`.
Returns `n` as fallback if bound is exhausted (should not happen
for reasonable inputs — Bertrand's postulate guarantees a prime
between n and 2n). -/
def findPrimeFrom (n bound : ℕ) : ℕ :=
  match bound with
  | 0 => n
  | bound + 1 =>
    if Nat.Prime n then n
    else findPrimeFrom (n + 1) bound

/-- The nth prime, computably. Uses `findPrimeFrom` with a generous
bound. The sequence starts: 2, 3, 5, 7, 11, 13, ... -/
def nthPrimeComputable : ℕ → ℕ
  | 0 => 2
  | n + 1 =>
    let prev := nthPrimeComputable n
    findPrimeFrom (prev + 1) (prev + 2)

/-!
## Variable Prime

`variablePrime` maps each variable index to a unique prime number via
`nthPrimeComputable`. Each variable maps to one prime, regardless of
polarity. `x₀` and `¬x₀` share the same prime — the sign is carried
separately as a Bool.
-/

/-- The prime for a variable index. Each variable maps to one prime,
regardless of polarity. `x₀` and `¬x₀` share the same prime. -/
def variablePrime {k : ℕ} (idx : Fin k) : ℕ :=
  nthPrimeComputable idx.val

/-- `Literal.toNat` is injective. -/
lemma Literal.toNat_injective {k : ℕ} :
    Function.Injective (@Literal.toNat k) := by
  intro ⟨idx₁, pol₁⟩ ⟨idx₂, pol₂⟩ h
  simp only [Literal.toNat] at h
  have h_pol : pol₁ = pol₂ := by
    by_contra hne
    cases pol₁ <;> cases pol₂ <;> simp_all <;> omega
  subst h_pol
  have h_idx : idx₁.val = idx₂.val := by
    cases pol₁ <;> omega
  congr 1; exact Fin.ext h_idx

/-- Clause composite: product of variable primes in the clause. -/
def clauseComposite {k : ℕ} (clause : Clause k) : ℕ :=
  (clause.map (fun lit => variablePrime lit.particle_idx)).prod

/-- Global composite: product of ALL variable primes in the CNF. -/
def cnfComposite {k : ℕ} (cnf : List (List (Literal k))) : ℕ :=
  ((cnf.flatMap id).map (fun lit => variablePrime lit.particle_idx)).prod

/-- A Clause is a Composite Number (product of its literals). -/
abbrev ClauseComposite := ℕ

/-- Encode a clause as a composite number (product of its literal codes). -/
noncomputable def ClauseToComposite {k : ℕ} (clause : Clause k) : ClauseComposite :=
  (clause.map LiteralToPrime).prod

/--
Clause composite using the prime-indexed atom encoding.
This is used for SAT-compatible common-factor predicates.
-/
noncomputable def clauseCompositePrime {k : ℕ} (clause : Clause k) : ClauseComposite :=
  (clause.map literalAtom).prod

/-- A CNF is a list of Composites. -/
noncomputable def CNFToNumberList {k : ℕ} (cnf : SyntacticCNF k) : List ClauseComposite :=
  cnf.map ClauseToComposite

/-- CNF number list built from prime-indexed clause composites. -/
noncomputable def CNFToPrimeNumberList {k : ℕ} (cnf : SyntacticCNF k) : List ClauseComposite :=
  cnf.map clauseCompositePrime

/-!
## Prime Dictionary

The deduplicated list of variable primes from a CNF. One prime per variable
that appears, regardless of polarity. Used by `StandardComplexity.lean` for
prime atom detection.
-/

/-- Extract the variable primes from a clause (ignoring polarity). -/
def clauseVariablePrimes {k : ℕ} (clause : Clause k) : List ℕ :=
  clause.map (fun lit => variablePrime lit.particle_idx)

/-- The prime dictionary: deduplicated variable primes from the CNF.
One prime per variable that appears, regardless of polarity.
Every entry is a genuine prime -- a vector, not a scalar. -/
def allVectors {k : ℕ} (cnf : SyntacticCNF k) : List ℕ :=
  (cnf.flatMap clauseVariablePrimes).eraseDups

/-- Backward-compatible alias: the deduplicated prime atoms. -/
abbrev cnfPrimeAtoms {k : ℕ} (cnf : SyntacticCNF k) : List ℕ :=
  allVectors cnf

/-- Does the CNF have extractable prime atoms? Returns `true` iff
at least one prime vector appears across the CNF's clauses. -/
def hasExtractableAtoms {k : ℕ} (cnf : SyntacticCNF k) : Bool :=
  (allVectors cnf).length > 0

/-- If `hasExtractableAtoms` returns `true`, the CNF has prime atoms. -/
theorem hasExtractableAtoms_sound {k : ℕ} (cnf : SyntacticCNF k)
    (h : hasExtractableAtoms cnf = true) :
    (cnfPrimeAtoms cnf).length > 0 := by
  simp [hasExtractableAtoms] at h
  exact h

/-- If the CNF has clauses with literals, then
`hasExtractableAtoms` returns `true`. -/
theorem hasExtractableAtoms_complete {k : ℕ} (cnf : SyntacticCNF k)
    (h : (cnfPrimeAtoms cnf).length > 0) :
    hasExtractableAtoms cnf = true := by
  simp [hasExtractableAtoms]
  exact h

/-- `hasExtractableAtoms` iff the CNF has at least one prime atom. -/
theorem hasExtractableAtoms_iff {k : ℕ} (cnf : SyntacticCNF k) :
    (cnfPrimeAtoms cnf).length > 0 ↔
    hasExtractableAtoms cnf = true :=
  ⟨hasExtractableAtoms_complete cnf, hasExtractableAtoms_sound cnf⟩

end InformationTheory
