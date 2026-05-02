/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module
public import Mathlib.InformationTheory.Complexity.CNF
public import Mathlib.Logic.Denumerable
public import Mathlib.Logic.Equiv.List
public import Mathlib.InformationTheory.EntropyNumber.Rat



/-!
# Encodable and Denumerable Instances for CNF Types

This file provides `Encodable`, `Denumerable`, and `Infinite` instances for
CNF types (`Clause`, `SyntacticCNF`, `UniversalCNF`), as well as equivalences
between CNF types and entropy-number types (`EntropyNat`, `EntropyRat`).

## Main definitions

* `Clause.encodable` / `SyntacticCNF.encodable` -- `Encodable` instances.
* `Clause.denumerable` / `SyntacticCNF.denumerable` -- `Denumerable` instances.
* `equivSyntacticCNF_to_EntropyNat` -- bijection `SyntacticCNF k ≃ EntropyNat`.
* `cnfToEntropyRat` / `EntropyRatToCnf` -- encode/decode between
  `Σ k, SyntacticCNF k` and `EntropyRat`.
* `UniversalCNF` -- sigma type `Σ k, SyntacticCNF k` with its instances.
* `equivUniversalCNF_to_EntropyNat` -- bijection `UniversalCNF ≃ EntropyNat`.
* `literal_le_prop` / `DecidableRel literal_le_prop` -- propositional literal ordering.

## Main results

* All CNF types are encodable, denumerable, and (where applicable) infinite.
-/

@[expose] public section

-- Cosmetic linters disabled for this initial drop of the InformationTheory
-- subtree. These do not affect correctness; reviewers may request a per-call
-- cleanup as a follow-up PR.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.style.emptyLine false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.longFile 0
set_option linter.style.show false
set_option linter.style.whitespace false
set_option linter.style.lambdaSyntax false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace InformationTheory

open InformationTheory

-- === Encodability and Equivalence to EntropyNat ===

/-- `Clause k` is an instance of `Encodable`. -/
instance Clause.encodable {k : ℕ} : Encodable (Clause k) :=
    inferInstance

/-- `SyntacticCNF k` is an instance of `Encodable`. -/
instance SyntacticCNF.encodable {k : ℕ} : Encodable (SyntacticCNF k) :=
    inferInstance

open Function

/-- A dummy literal needed to build an injection `ℕ → List (Literal k)`.
    We package the "`k ≠ 0`" assumption as a `Fact` so it can be found by
    type-class resolution. -/
instance {k : ℕ} [hk : Fact (0 < k)] : Inhabited (Literal k) where
  default := { particle_idx := ⟨0, hk.out⟩, polarity := false }

/-- Lists of literals are infinite whenever `k ≠ 0`. -/
instance Clause.infinite {k : ℕ} [Fact (0 < k)] :
    Infinite (Clause k) := by
  let lit : Literal k := default
  have inj : Injective (fun n : ℕ ↦ List.replicate n lit) := by
    intro m n hmn
    have h_len := congrArg List.length hmn
    simp only [List.length_replicate] at h_len
    exact h_len
  exact Infinite.of_injective _ inj

/-- `Clause` is denumerable (countably infinite) as soon as it is infinite. -/
instance Clause.denumerable {k : ℕ} [Fact (0 < k)] :
    Denumerable (Clause k) :=
  Denumerable.ofEncodableOfInfinite (Clause k)

/-- `SyntacticCNF` inherits `Infinite` and `Denumerable` in the same way. -/
instance SyntacticCNF.infinite {k : ℕ} : -- Removed [Fact (0 < k)]
    Infinite (SyntacticCNF k) :=
  -- SyntacticCNF k is List (Clause k).
  -- Clause k is List (Literal k).
  -- List (Literal k) is Nonempty (it contains []). (via List.instNonempty)
  -- Therefore, by instInfiniteListOfNonempty, List (Clause k) is Infinite.
  -- This should be found by typeclass inference.
  inferInstance

/-- `SyntacticCNF k` is an instance of `Denumerable`. -/
instance SyntacticCNF.denumerable {k : ℕ} : -- Removed [Fact (0 < k)]
    Denumerable (SyntacticCNF k) :=
  Denumerable.ofEncodableOfInfinite (SyntacticCNF k)

/--
**The New Equivalence (Un-Axiomatized):**
There exists a computable bijection between the syntactic representation of a
CNF formula and the `EntropyNat` type. We state its existence via `Encodable`.
-/
noncomputable def equivSyntacticCNF_to_EntropyNat {k : ℕ} :
    SyntacticCNF k ≃ InformationTheory.EntropyNat :=
  -- We use the power of Lean's typeclass synthesis for Denumerable types.
  -- `List`, `Fin k`, and `Bool` are all denumerable, so their product and list
  -- combinations are also denumerable. `EntropyNat` is denumerable via its equiv to `ℕ`.
  (Denumerable.eqv (SyntacticCNF k)).trans (InformationTheory.entropyNatEquivNat.symm)

/-- Encode a full CNF (with its variable count) into an `EntropyRat`. -/
noncomputable def cnfToEntropyRat
    (full_cnf : Σ k, SyntacticCNF k) :
    InformationTheory.EntropyRat :=
  -- 1. Encode the entire CNF structure (including k) into a single natural number.
  let n := Encodable.encode full_cnf

  -- 2. Convert the natural number to a rational using a simple construction
  -- We can use the fact that every natural number corresponds to a rational
  let q : ℚ := n

  -- 3. Convert this rational number into its canonical EntropyRat representation.
  InformationTheory.EntropyRat.ofRat q

/-- Decode an `EntropyRat` back into a full CNF (inverse of `cnfToEntropyRat`). -/
noncomputable def EntropyRatToCnf (pmf : InformationTheory.EntropyRat) : Σ k, SyntacticCNF k :=
  -- 1. Convert the EntropyRat into its mathlib rational value.
  let q := InformationTheory.EntropyRat.toRat pmf

  -- 2. Convert the rational back to a natural number (inverse of the injection we used)
  -- Since we used simple coercion ℕ → ℚ, we can extract the numerator if denominator is 1
  let n := q.num.natAbs -- This works for rationals that came from naturals

  -- 3. Decode this natural number back into the full CNF structure.
  -- The output is an Option; we can get the value because the encoding is total.
  match Encodable.decode n with
  | some cnf => cnf
  | none => ⟨0, []⟩ -- Default empty CNF in case of decode failure

/-!
### Canonical CNF Ordering (Propositional)

Propositional ordering predicates for literals, used by canonical form proofs.
-/

/--
**Propositional version of literal ordering for use with List.Sorted.**
`l₁ ≤ l₂` if the index of `l₁` is less than or equal to the index of `l₂`.
-/
def literal_le_prop {k : ℕ} (l₁ l₂ : Literal k) : Prop :=
  l₁.particle_idx.val ≤ l₂.particle_idx.val

/-- `literal_le_prop` is decidable since it reduces to `Nat.decLe`. -/
instance {k : ℕ} : DecidableRel (@literal_le_prop k) :=
  fun l₁ l₂ => by
    unfold literal_le_prop
    exact Nat.decLe l₁.particle_idx.val l₂.particle_idx.val

/-!
### Universal CNF
-/

/-- A Sigma type holding a CNF formula along with its variable count `k`. -/
abbrev UniversalCNF := Σ k : ℕ, SyntacticCNF k

/-- `UniversalCNF` is an instance of `Encodable`. -/
instance : Encodable UniversalCNF := by infer_instance

/-- `UniversalCNF` is an instance of `Denumerable`. -/
instance : Denumerable UniversalCNF := by infer_instance

/--
**The New Provable Equivalence.**
This defines a computable bijection from the space of all possible CNF formulas
(over any number of variables) to the natural numbers, and thus to `EntropyNat`.
-/
noncomputable def equivUniversalCNF_to_EntropyNat : UniversalCNF ≃ EntropyNat :=
  (Denumerable.eqv UniversalCNF).trans entropyNatEquivNat.symm

/-!
### Binary CNF Decoder

Functions to decode the binary encoding produced by `encodeCNF` back into
a `SyntacticCNF`. This inverts the encoding from `CNF.lean`.

**Encoding format recap:**
- `encodeNat n` = `List.replicate n true`
- `encodeLiteral l` = `polarity :: encodeNat l.particle_idx.val`
- `encodeClause c` = literals joined by single `[false]` delimiter after each
- `encodeCNF cnf` = `encodeNat k ++ [false, false] ++ (clauses.map (· ++ [false,false])).join`

**Known limitation:** The encoding is ambiguous for clauses containing a literal
with `polarity = false` and `particle_idx = 0`, since that literal's encoding
`[false]` followed by its delimiter `[false]` produces `[false, false]`, which
is indistinguishable from the clause separator.
-/

/-- Count leading `true` values in a boolean list.
    Returns `(count, remainder)` where `remainder` starts at the first `false`
    (or is empty). -/
def countLeadingTrue : List Bool → ℕ × List Bool
  | [] => (0, [])
  | true :: rest =>
    let (n, remainder) := countLeadingTrue rest
    (n + 1, remainder)
  | false :: rest => (0, false :: rest)

/-- Decode a natural number from unary encoding (leading `true` values). -/
def decodeNat (tape : List Bool) : ℕ × List Bool :=
  countLeadingTrue tape

/-- Decode a single literal from the binary encoding.
    Format: `polarity :: encodeNat index`.
    Returns `none` if the tape is empty or the decoded index is `≥ k`. -/
def decodeLiteral (k : ℕ) (tape : List Bool) : Option (Literal k × List Bool) :=
  match tape with
  | [] => none
  | polarity :: rest =>
    let (idx, remainder) := countLeadingTrue rest
    if h : idx < k then
      some (⟨⟨idx, h⟩, polarity⟩, remainder)
    else
      none

/-- The remainder returned by `countLeadingTrue` is a suffix of the input,
    hence no longer than the input. -/
private theorem countLeadingTrue_length_le (tape : List Bool) :
    (countLeadingTrue tape).2.length ≤ tape.length := by
  induction tape with
  | nil => simp [countLeadingTrue]
  | cons b rest ih =>
    cases b with
    | true =>
      unfold countLeadingTrue
      simp only
      have h1 : (countLeadingTrue rest).2.length ≤ rest.length := ih
      have h2 : rest.length ≤ (true :: rest).length := by simp [List.length]
      exact Nat.le_trans h1 h2
    | false =>
      simp [countLeadingTrue]

/-- The remainder of `countLeadingTrue` is strictly shorter than `b :: tape`. -/
private theorem countLeadingTrue_length_lt_cons (b : Bool) (tape : List Bool) :
    (countLeadingTrue tape).2.length < (b :: tape).length := by
  have := countLeadingTrue_length_le tape
  simp only [List.length_cons]
  omega

/-- `decodeLiteral` consumes at least one element from the tape when it
    succeeds, and its remainder is strictly shorter. -/
private theorem decodeLiteral_length_lt {k : ℕ} {tape : List Bool}
    {lit : Literal k} {remainder : List Bool}
    (h : decodeLiteral k tape = some (lit, remainder)) :
    remainder.length < tape.length := by
  match tape with
  | [] => simp [decodeLiteral] at h
  | b :: rest =>
    simp only [decodeLiteral] at h
    split at h
    · obtain ⟨-, rfl⟩ := h
      exact countLeadingTrue_length_lt_cons b rest
    · exact absurd h (by simp)

/-- Decode a clause from its binary encoding. Literals are each followed by a
    single `[false]` delimiter. The clause ends when we encounter `[false]`
    (forming a double-false with the literal's trailing delimiter, which is the
    clause separator from `encodeCNF`), or when the tape is exhausted.

    Returns `(clause, remainder)` where `remainder` is the tape after the
    clause separator has been consumed, or `none` on a parse error. -/
def decodeClause (k : ℕ) (tape : List Bool) : Option (Clause k × List Bool) :=
  go tape.length tape []
where
  /-- Accumulate decoded literals, with fuel to guarantee termination. -/
  go (fuel : ℕ) (tape : List Bool) (acc : List (Literal k)) :
      Option (Clause k × List Bool) :=
    match fuel with
    | 0 => some (acc.reverse, tape)
    | fuel' + 1 =>
      match tape with
      -- Empty tape: return what we have
      | [] => some (acc.reverse, [])
      -- Double false: clause separator, consume both and return
      | false :: false :: rest => some (acc.reverse, rest)
      -- Otherwise: decode a literal
      | _ =>
        match decodeLiteral k tape with
        | none => none
        | some (lit, remainder) =>
          -- Consume the mandatory [false] delimiter after the literal
          match remainder with
          | false :: rest => go fuel' rest (lit :: acc)
          | [] => some ((lit :: acc).reverse, [])
          | _ => none  -- Expected delimiter not found

/-- Decode all clauses from the remaining tape, with fuel for termination. -/
def decodeClauses (k : ℕ) (fuel : ℕ) (tape : List Bool) :
    Option (SyntacticCNF k) :=
  match fuel with
  | 0 => some []
  | fuel' + 1 =>
    if tape.isEmpty then
      some []
    else do
      let (clause, rest) ← decodeClause k tape
      let clauses ← decodeClauses k fuel' rest
      return clause :: clauses

/-- Decode a full CNF formula from its binary encoding.
    Format: `encodeNat k ++ [false, false] ++ clauseBody`
    where `clauseBody` contains clauses each followed by `[false, false]`.
    Returns `(k, cnf)` or `none` on parse error. -/
def decodeCNF (tape : List Bool) : Option (Σ k, SyntacticCNF k) :=
  let (k, rest1) := decodeNat tape
  -- Expect [false, false] separator after the unary k
  match rest1 with
  | false :: false :: rest2 => do
    let clauses ← decodeClauses k rest2.length rest2
    return ⟨k, clauses⟩
  | _ => none

end InformationTheory
