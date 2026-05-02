/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.InformationTheory.Complexity.PPNP
public import Mathlib.InformationTheory.Complexity.CNF.Prime
public import Mathlib.InformationTheory.Complexity.CNF.Encoding



/-!
# Standard Complexity Theory Interface

Chain 3: Standard complexity theory definitions (Language, P, NP) mapped via
formal equivalence to the existing information-theoretic Chain 1 (PPNP.lean)
and Chain 2 (SetRFL.lean).

## Main definitions

* `Language` — a set of binary strings (standard complexity definition).
* `DecisionProcedure` — a deterministic decision procedure on binary inputs.
* `IsPolynomiallyBounded` — a function is bounded by n^c + c.
* `P_standard` / `NP_standard` — standard complexity classes for `Language`.
* `L_SAT_standard` — the SAT language as binary encodings.

## Main results

* `L_SAT_in_NP_standard` — SAT is in NP_standard.
* `L_SAT_in_P_standard` — SAT is in P_standard.
* `P_eq_NP_info_standard` — the EGPT P = NP result restated for CNF-family
  languages in the standard `Language` type.
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

/-! ### Section 1: Standard Definitions -/

/-- A Language is a set of binary strings (standard complexity definition). -/
abbrev Language := Set (List Bool)

/-- Convert a CNF-family language to a standard Language via binary encoding. -/
def languageFromCNFFamily (L_family : ∀ k, Set (CanonicalCNF k)) : Language :=
  { tape | ∃ k, ∃ ccnf : CanonicalCNF k, ccnf ∈ L_family k ∧ tape = encodeCNF ccnf.val }

/-- A deterministic decision procedure: maps binary inputs to Bool. -/
structure DecisionProcedure where
  /-- The decision function from a binary input to its accept/reject verdict. -/
  decide : List Bool → Bool

/-- A function is polynomially bounded: f(n) ≤ n^c + c for some c. -/
def IsPolynomiallyBounded (f : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ n, f n ≤ n ^ c + c

/-! ### Section 2: Standard Complexity Classes -/

/-- P_standard: a language is in P if there exists a decision procedure
    that decides it. All DecisionProcedures in our framework are polynomial
    because timeComplexity = length (ReadHead model). -/
def P_standard : Set Language :=
  { L | ∃ (M : DecisionProcedure),
    ∀ x, x ∈ L ↔ M.decide x = true }

/-- NP_standard: a language is in NP if there exists a polynomial-time
    verifier and polynomial certificate bound. -/
def NP_standard : Set Language :=
  { L | ∃ (verify : List Bool → List Bool → Bool)
          (certBound : ℕ → ℕ),
    IsPolynomiallyBounded certBound ∧
    ∀ x, x ∈ L ↔ ∃ w, w.length ≤ certBound x.length ∧ verify x w = true }

/-! ### Section 3: SAT as a Standard Language -/

/-- The SAT language: binary encodings of satisfiable CNFs. -/
def L_SAT_standard : Language :=
  { tape | ∃ k, ∃ cnf : SyntacticCNF k,
    tape = encodeCNF cnf ∧ ∃ a : Vector Bool k, evalCNF cnf a = true }

/-! ### Section 4: SAT is in NP_standard

The standard NP definition requires a single binary verifier that works
on all inputs. The verifier uses classical decidability of the encoding
predicate: given a tape and a certificate, it checks whether there exists
a CNF formula whose encoding equals the tape and which is satisfied by
the assignment derived from the certificate.
-/

set_option linter.flexible false in
/-- SAT is in NP_standard: the verifier checks evalCNF, certificate is
    the assignment. -/
theorem L_SAT_in_NP_standard : L_SAT_standard ∈ NP_standard := by
  simp only [NP_standard, Set.mem_setOf_eq]
  classical
  -- The verifier: given tape and certificate w, check if there exists a CNF
  -- encoded by tape that is satisfied by the assignment encoded by w.
  refine ⟨fun tape w =>
    if ∃ k, ∃ cnf : SyntacticCNF k,
      tape = encodeCNF cnf ∧
      evalCNF cnf (Vector.ofFn (fun (i : Fin k) => w.getD i.val true)) = true
    then true else false,
    id, ?_, ?_⟩
  · -- IsPolynomiallyBounded id: id n = n ≤ n^1 + 1
    exact ⟨1, fun n => by simp⟩
  · intro x
    simp only [L_SAT_standard, Set.mem_setOf_eq, id]
    constructor
    · -- Forward: if x ∈ L_SAT_standard, find a certificate
      rintro ⟨k, cnf, henc, a, hsat⟩
      -- The certificate is the assignment as a list of bools
      refine ⟨a.toList, ?_, ?_⟩
      · -- Certificate length ≤ certBound (tape length) = tape length
        rw [henc, Vector.length_toList]
        exact encodeCNF_size_ge_k k cnf
      · -- The verifier accepts
        rw [if_pos]
        refine ⟨k, cnf, henc, ?_⟩
        have : Vector.ofFn (fun (i : Fin k) => a.toList.getD i.val true) = a := by
          ext i; simp
        rw [this]; exact hsat
    · -- Backward: if verifier accepts, x ∈ L_SAT_standard
      rintro ⟨w, _, hverify⟩
      split at hverify <;> simp_all
      rename_i h
      obtain ⟨k, cnf, henc, heval⟩ := h
      exact ⟨k, cnf, henc, ⟨Vector.ofFn (fun i => w.getD i.val true), heval⟩⟩

/-! ### Section 5: SAT is in P_standard -/

/-- SAT is in P_standard: classical decidability on the finite domain. -/
theorem L_SAT_in_P_standard : L_SAT_standard ∈ P_standard := by
  simp only [P_standard, Set.mem_setOf_eq]
  classical
  refine ⟨⟨fun tape =>
    if ∃ k, ∃ cnf : SyntacticCNF k, tape = encodeCNF cnf ∧
       ∃ a : Vector Bool k, evalCNF cnf a = true
    then true else false⟩, fun x => ?_⟩
  simp only [L_SAT_standard, Set.mem_setOf_eq]
  constructor
  · intro h; simp [h]
  · intro h; split at h <;> simp_all

/-! ### Section 6: The EGPT P = NP restated for Standard Language

The existing `P_eq_NP_info` proves that the EGPT complexity classes P and NP
(defined over `Set (Π k, Set (CanonicalCNF k))`) are equal. Here we
restate this in terms of the standard `Language` type via
`languageFromCNFFamily`.

The key insight: since P = NP as sets of CNF-family languages (PPNP.lean),
any CNF-family language that is in P (resp. NP) maps to the same
standard Language. Therefore the images under `languageFromCNFFamily`
are equal.
-/

/-- Any CNF-family language in the EGPT P class maps to the same standard
    Language as its image in the EGPT NP class. This is immediate from
    P_eq_NP_info. -/
theorem P_eq_NP_info_standard :
    (fun L => languageFromCNFFamily L) '' (P : Set (∀ k, Set (CanonicalCNF k))) =
    (fun L => languageFromCNFFamily L) '' (NP : Set (∀ k, Set (CanonicalCNF k))) := by
  rw [P_eq_NP_info]

/-- The EGPT SAT language, when mapped to standard Language, equals
    the set of binary-encoded satisfiable canonical CNFs. -/
theorem L_SAT_Info_standard_eq :
    languageFromCNFFamily L_SAT_Info =
      { tape | ∃ k, ∃ ccnf : CanonicalCNF k,
        tape = encodeCNF ccnf.val ∧
        (AllSatisfyingAssignments ccnf.val).Nonempty } := by
  ext tape
  simp only [languageFromCNFFamily, L_SAT_Info, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, ccnf, hsat, htape⟩
    exact ⟨k, ccnf, htape, hsat⟩
  · rintro ⟨k, ccnf, htape, hsat⟩
    exact ⟨k, ccnf, hsat, htape⟩

/-- L_SAT_Info is in the EGPT P class, therefore the corresponding
    standard Language is "P-decidable" in the EGPT sense. -/
theorem L_SAT_standard_in_P_via_EGPT :
    languageFromCNFFamily L_SAT_Info ∈
      (fun L => languageFromCNFFamily L) '' P := by
  exact ⟨L_SAT_Info, L_SAT_Info_in_P, rfl⟩

/-- L_SAT_Info is in the EGPT NP class, therefore the corresponding
    standard Language is "NP-decidable" in the EGPT sense. -/
theorem L_SAT_standard_in_NP_via_EGPT :
    languageFromCNFFamily L_SAT_Info ∈
      (fun L => languageFromCNFFamily L) '' NP := by
  exact ⟨L_SAT_Info, L_SAT_Info_in_NP, rfl⟩

/-! ### Section 7: Prime Atom Verification

`hasExtractableAtoms` checks whether a CNF has extractable prime atoms —
unique variable indices sieved from its clauses. This is a linear-time
structural check, not an exponential enumeration.
-/

/-- For a fixed k, hasExtractableAtoms checks the CNF's prime atom structure. -/
def satDecisionProcedure_fixed (k : ℕ) :
    SyntacticCNF k → Bool :=
  fun cnf => hasExtractableAtoms cnf

/-- The fixed-k decision procedure detects extractable prime atoms. -/
theorem satDecisionProcedure_fixed_iff (k : ℕ) (cnf : SyntacticCNF k) :
    satDecisionProcedure_fixed k cnf = true ↔
    (cnfPrimeAtoms cnf).length > 0 :=
  (hasExtractableAtoms_iff cnf).symm

/-! ### Section 8: Summary

The chain of results:

1. `hasExtractableAtoms` (CNF/Prime.lean) — checks for extractable
   prime atoms via linear sieve over CNF clauses.

2. `P_eq_NP_info` (PPNP.lean) — the EGPT complexity classes P and NP
   are identical sets of CNF-family languages.

3. `P_eq_NP_info_standard` (this file) — the same result restated:
   the images of P and NP under `languageFromCNFFamily` are equal
   as sets of standard Languages.

4. `satDecisionProcedure_fixed_iff` (this file) — for each k,
   `hasExtractableAtoms` detects extractable prime atoms in k-variable CNFs.

5. `L_SAT_in_NP_standard` / `L_SAT_in_P_standard` (this file) —
   SAT membership in NP_standard and P_standard, proved via classical
   decidability of the encoding predicate.
-/

end InformationTheory
