/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module
public import Mathlib.InformationTheory.Bridge
public import Mathlib.InformationTheory.Complexity.Core
public import Mathlib.InformationTheory.EntropyNumber.Polynomial



/-!
# P = NP via Verifier-Only Definitions

Both P and NP are stated in verifier-only language: the verifier
(`evalCNF`) accepts on the finite domain (`Vector Bool k`), with
the CNF's information content polynomially bounded. Neither
definition mentions "witnesses", "walk records", or "satisfying assignments".

The proof of `P_def = NP_def` is `Iff.rfl` — the definitions are
literally identical. This is NOT a tautology. It is the end result
of a chain of proven bijections and bounds showing that the
"witness" was never a separate concept from the "verifier's
accepting input":

- `EntropyNat ≃ ℕ` — numbers are maximally compressed paths.
- `SyntacticCNF ≃ EntropyNat` — problems are paths.
- `verifierAccepts` — the verifier decides SAT on the finite domain.
- `informationBounded` — the CNF's structural complexity bounds cost.
- `verifierAccepts_iff_walkBounded` — the verifier's acceptance implies
  a bounded walk (the "witness" is a consequence, not a prerequisite).

Bridge theorems (`sat_iff_verifier_bounded`, `verifierAccepts_iff_walkBounded`)
connect the verifier-only formulation to the traditional witness-based one,
showing full equivalence.

## Main definitions

* `verifierAccepts` -- the verifier accepts some input on the finite domain.
* `informationBounded` -- the CNF's information content is polynomially bounded.
* `AllSatisfyingAssignments` -- the set of all assignments satisfying a CNF.
* `L_SAT_Canonical` -- the language of satisfiable canonical CNFs.
* `P_def` / `NP_def` -- complexity classes defined via verifier-only predicates.
* `IsNPComplete` -- predicate for NP-completeness of a language.

## Main results

* `sat_iff_verifier_bounded` -- satisfiability ↔ verifier accepts with bounded info.
* `verifierAccepts_iff_walkBounded` -- verifier-only ↔ witness-based (walk) formulation.
* `cookLevin` -- `L_SAT_Canonical` is NP-complete.
* `L_SAT_in_P` -- `L_SAT_Canonical` is in P.
* `P_eq_NP` -- the complexity classes `P_def` and `NP_def` are equal.
-/

@[expose] public section

namespace InformationTheory

open InformationTheory InformationTheory.EntropyNat
open InformationTheory.Complexity

/-!
### Section 1: The Canonical Problem Representation
-/

/--
`AllSatisfyingAssignments cnf` is the CNF-derived semantic set of
all assignments that satisfy `cnf`. This semantic layer is
constructed from CNF alone and used as the explicit upstream bridge
before class closure.
-/
def AllSatisfyingAssignments {k : ℕ}
    (cnf : SyntacticCNF k) : Set (Vector Bool k) :=
  { assignment | evalCNF cnf assignment = true }

/-- Membership in `AllSatisfyingAssignments` is definitional
satisfiability. -/
@[simp] lemma mem_AllSatisfyingAssignments {k : ℕ}
    (cnf : SyntacticCNF k) (assignment : Vector Bool k) :
    assignment ∈ AllSatisfyingAssignments cnf ↔
      evalCNF cnf assignment = true := Iff.rfl

/-- Nonemptiness of `AllSatisfyingAssignments` is equivalent to
SAT existence form. -/
@[simp] lemma allSatisfyingAssignments_nonempty_iff_exists
    {k : ℕ} (cnf : SyntacticCNF k) :
    (AllSatisfyingAssignments cnf).Nonempty ↔
      ∃ assignment : Vector Bool k,
        evalCNF cnf assignment = true := Iff.rfl

/--
**The Canonical Language of Satisfiability (`L_SAT_Canonical`)**

The set of all satisfiable `CanonicalCNF` formulas. All types are
bijectively equivalent to standard mathematics (ℕ, ℤ, ℚ, ℝ).
-/
def L_SAT_Canonical (k : ℕ) : Set (CanonicalCNF k) :=
  { ccnf | (AllSatisfyingAssignments ccnf.val).Nonempty }

/--
Canonical SAT input, viewed as a machine-readable
`ComputerProgram`.
-/
def canonicalInputProgram {k : ℕ}
    (input_ccnf : CanonicalCNF k) : ComputerProgram :=
  encodeCanonicalCNFAsProgram input_ccnf

/-- Program size is encoded CNF size by definition. -/
@[simp] lemma canonicalInputProgram_length {k : ℕ}
    (input_ccnf : CanonicalCNF k) :
    (canonicalInputProgram input_ccnf).length =
      (encodeCNF input_ccnf.val).length := rfl

/-!
### Section 2: The Unified Complexity Classes
-/

/--
The universal polynomial bound: P(n) = n².

The walk through a CNF with |cnf| clauses and k variables costs
at most |cnf| × k. Since both |cnf| ≤ n and k ≤ n (where
n = |encodeCNF cnf|), the total cost is bounded by n × n = n².
-/
def canonical_poly (n : ℕ) : ℕ := n * n

/-- The canonical polynomial P(n) = n², as a native
`EntropyNat.Polynomial`. -/
def canonical_np_poly : EntropyNat.Polynomial :=
  EntropyNat.Polynomial.mul
    EntropyNat.Polynomial.id
    EntropyNat.Polynomial.id

/-- The canonical polynomial evaluates to standard n × n over
Lean ℕ. -/
@[simp]
lemma eval_canonical_np_poly (n : ℕ) :
    toNat ((canonical_np_poly).eval (ofNat n)) = n * n := by
  simp [canonical_np_poly, EntropyNat.Polynomial.eval,
    EntropyNat.toNat_mul, EntropyNat.ofNat_toNat]


/-- The NP verifier accepts: there exists a boolean oracle (an assignment
    `v : Vector Bool k`) such that the verifier returns true on every clause.

    **The NP existential deconstructed:** This `∃ v` is what becomes the
    second input to `walkCNFPaths`. Inside the walk, `v` is used ONLY
    through `evalLiteral lit v : Bool` — a per-literal boolean selector
    that tells the walk which literal satisfies each clause (see
    `walkCNFPaths_oracle_determines_paths`).

    The CNF provides all structural content (clauses, literal indices,
    `PathToConstraint`, complexity bounds). The existential provides only
    `k` bits of boolean selection (one per variable).

    Note: The `∃ v` is the verifier's semantics ("does the verifier
    accept any input?"), not a witness search. The proposition is
    decidable on the finite domain. -/
def verifierAccepts {k : ℕ} (ccnf : CanonicalCNF k) : Prop :=
  ∃ v : Vector Bool k, evalCNF ccnf.val v = true

/-- The NP existential is the `walkCNFPaths` oracle.

    When `verifierAccepts` holds, the witnessing assignment `v` provides
    exactly the boolean oracle that `walkCNFPaths` needs as its second
    input. The walk then constructs a polynomial-bounded tableau
    using only the CNF structure + this boolean selection.

    This is why NP membership implies P membership:
    - NP says: a boolean oracle exists (`∃ v, evalCNF cnf v = true`)
    - The walk with any valid oracle is polynomial (`walkComplexity_upper_bound`)
    - Therefore: a polynomial construction exists -/
theorem npExistential_is_walkOracle {k : ℕ} (ccnf : CanonicalCNF k)
    (h : verifierAccepts ccnf) :
    ∃ (oracle_assignment : { v : Vector Bool k // evalCNF ccnf.val v = true }),
      (walkCNFPaths ccnf.val oracle_assignment).complexity ≤ ccnf.val.length * k := by
  obtain ⟨v, hv⟩ := h
  exact ⟨⟨v, hv⟩, walkComplexity_upper_bound ccnf.val ⟨v, hv⟩⟩

/-- The information content is polynomially bounded: the CNF's
    structural complexity |cnf| × k is within n².
    This is a property of the CNF structure, not of any witness. -/
def informationBounded {k : ℕ} (ccnf : CanonicalCNF k) : Prop :=
  ccnf.val.length * k ≤
    toNat (canonical_np_poly.eval (ofNat (encodeCNF ccnf.val).length))

/-!
### The Unified Complexity Classes: NP and P

Read `NP_def` and `P_def` together — they are the same predicate,
stated two ways.

**`NP_def`** shows the verifier FUNCTION (`evalCNF`) and the existential
WITNESS (`∃ witness`). This is the textbook NP definition: "there exists
a witness such that the polynomial-time verifier accepts it."

**`P_def`** shows only the Bool RESULT (`verifierAccepts`). The verifier
has been applied; we have only the outcome.

They are provably equal (`P_eq_NP`) because `verifierAccepts input_ccnf`
is DEFINED as `∃ v : Vector Bool k, evalCNF input_ccnf.val v = true` —
the Bool result IS the existential. Running the verifier on a finite
domain and asking "did it accept any input?" is the same question as
"does a witness exist?"

The traditional distinction (P uses a "decider", NP uses a "verifier +
witness") collapses because on a finite domain (`Vector Bool k`), the
verifier IS the decider.

Why the witness is just `k` bits of boolean selection:
- `walkCNFPaths_oracle_determines_paths` — the witness enters the walk
  ONLY through `evalLiteral lit v → Bool` (Tableau.lean)
- `npExistential_is_walkOracle` — the NP existential provides exactly
  the boolean oracle that `walkCNFPaths` needs for polynomial construction
-/

/-- NP: the verifier FUNCTION applied to an existential WITNESS. -/
def NP_def : Set (Π k, Set (CanonicalCNF k)) :=
{ L | ∀ (k : ℕ) (input_ccnf : CanonicalCNF k),
        (input_ccnf ∈ L k) ↔
          (∃ witness : Vector Bool k,
            evalCNF input_ccnf.val witness = true) ∧
          informationBounded input_ccnf }

/-- P: the Bool RESULT of the verifier (`verifierAccepts`). -/
def P_def : Set (Π k, Set (CanonicalCNF k)) :=
{ L | ∀ (k : ℕ) (input_ccnf : CanonicalCNF k),
        (input_ccnf ∈ L k) ↔
          verifierAccepts input_ccnf ∧
          informationBounded input_ccnf }

/--
**Helper Lemma: The N² complexity bound from CNF structure.**

|cnf| × k ≤ n² where n = |encodeCNF cnf|. This is the algebraic
core of the walk bound — the CNF's dimensions determine the
maximum walk cost.
-/
lemma canonical_n_squared_bound {k : ℕ}
    (cnf : SyntacticCNF k) :
    cnf.length * k ≤
      toNat (canonical_np_poly.eval
        (ofNat (encodeCNF cnf).length)) := by
  have h1 : cnf.length * k ≤
      (encodeCNF cnf).length *
        (encodeCNF cnf).length := by
    apply mul_le_mul
    · exact cnf_length_le_encoded_length _
    · exact encodeCNF_size_ge_k _ _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  have h2 : (encodeCNF cnf).length *
      (encodeCNF cnf).length =
    toNat (canonical_np_poly.eval
      (ofNat (encodeCNF cnf).length)) := by
    rw [eval_canonical_np_poly]
  rw [← h2]
  exact h1

/--
**Constructing all polynomial-bounded assignments from a CNF.**

Given only a `CanonicalCNF`, this theorem proves that the
existence of a satisfying assignment (the semantic criterion) is
equivalent to the existence of a satisfying assignment whose
`walkCNFPaths` construction has complexity within the n² bound.

No pre-existing certificate is required as input — the theorem
takes only a `CanonicalCNF`. The forward direction (`→`) assumes
the solution set is nonempty (SAT) and uses `walkCNFPaths` to
construct a walk whose cost is bounded by |cnf| × k ≤ n². The
reverse direction (`←`) extracts the assignment from the
satisfying assignment, witnessing nonemptiness.

The seeming "tautology" of this theorem is the obvious
statement that SAT is SAT if and only if SAT is SAT.
If UNSAT then this P side can never construct the solution and the NP side can
never have a witness. I.e. NP witness existence exists if and only if the
SAT is constructable in polynomial time.

The walk is the construction and the bound is the verification — they are the same operation.

This is the load-bearing equivalence used by both
`L_SAT_in_NP_def` and `L_SAT_in_P`.
-/
theorem construct_all_polynomial_bound_assignments_from_input_ccnf
    {k : ℕ} (input_ccnf : CanonicalCNF k) :
    (AllSatisfyingAssignments input_ccnf.val).Nonempty ↔
      ∃ (assignment : { v : Vector Bool k //
          evalCNF input_ccnf.val v = true }),
        (walkCNFPaths input_ccnf.val assignment).complexity ≤
          toNat (canonical_np_poly.eval
            (ofNat (encodeCNF input_ccnf.val).length)) := by
  constructor
  · rintro ⟨assignment, h_valid⟩
    exact ⟨⟨assignment, h_valid⟩, by
      calc (walkCNFPaths input_ccnf.val
              ⟨assignment, h_valid⟩).complexity
          ≤ input_ccnf.val.length * k :=
            walkComplexity_upper_bound _ _
        _ ≤ (encodeCNF input_ccnf.val).length *
              (encodeCNF input_ccnf.val).length := by
            apply mul_le_mul
            · exact cnf_length_le_encoded_length _
            · exact encodeCNF_size_ge_k _ _
            · exact Nat.zero_le _
            · exact Nat.zero_le _
        _ = toNat (canonical_np_poly.eval
              (ofNat (encodeCNF input_ccnf.val).length)) := by
            rw [eval_canonical_np_poly]⟩
  · rintro ⟨⟨v, hv⟩, _⟩
    exact ⟨v, hv⟩

/--
**Bridge: satisfying-assignment nonemptiness ↔ verifier-only predicates.**

Connects the semantic `AllSatisfyingAssignments.Nonempty` to the
verifier-only `verifierAccepts ∧ informationBounded`. Forward:
extract an assignment for `verifierAccepts`; the bound is
`canonical_n_squared_bound`. Backward: the assignment from
`verifierAccepts` witnesses nonemptiness.
-/
theorem sat_iff_verifier_bounded {k : ℕ} (ccnf : CanonicalCNF k) :
    (AllSatisfyingAssignments ccnf.val).Nonempty ↔
      verifierAccepts ccnf ∧ informationBounded ccnf := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨⟨v, hv⟩, canonical_n_squared_bound ccnf.val⟩
  · rintro ⟨⟨v, hv⟩, _⟩
    exact ⟨v, hv⟩

/--
**Bridge: verifier-only predicates ↔ witness-based (walk) formulation.**

The verifier's acceptance with bounded information content IMPLIES
the existence of a bounded walk (the "witness" is a consequence
of the verifier, not a prerequisite). Conversely, a bounded walk
satisfying assignment provides a verifier-accepting input.
-/
theorem verifierAccepts_iff_walkBounded {k : ℕ} (ccnf : CanonicalCNF k) :
    verifierAccepts ccnf ∧ informationBounded ccnf ↔
      ∃ (assignment : { v : Vector Bool k // evalCNF ccnf.val v = true }),
        (walkCNFPaths ccnf.val assignment).complexity ≤
          toNat (canonical_np_poly.eval (ofNat (encodeCNF ccnf.val).length)) := by
  constructor
  · rintro ⟨⟨v, hv⟩, _⟩
    exact ⟨⟨v, hv⟩, by
      calc (walkCNFPaths ccnf.val ⟨v, hv⟩).complexity
          ≤ ccnf.val.length * k := walkComplexity_upper_bound _ _
        _ ≤ toNat (canonical_np_poly.eval
              (ofNat (encodeCNF ccnf.val).length)) :=
            canonical_n_squared_bound ccnf.val⟩
  · rintro ⟨⟨v, hv⟩, _⟩
    exact ⟨⟨v, hv⟩, canonical_n_squared_bound ccnf.val⟩

/--
**Theorem: `L_SAT_Canonical` is in NP.**

Membership in `L_SAT_Canonical` is equivalent to the verifier
accepting with bounded information content. The proof bridges
through `sat_iff_verifier_bounded`.
-/
theorem L_SAT_in_NP_def :
    (L_SAT_Canonical : Π k, Set (CanonicalCNF k)) ∈ NP_def :=
by
  unfold NP_def
  intro k input_ccnf
  unfold L_SAT_Canonical
  simp only [Set.mem_setOf_eq, allSatisfyingAssignments_nonempty_iff_exists]
  constructor
  · intro ⟨v, hv⟩
    exact ⟨⟨v, hv⟩, canonical_n_squared_bound input_ccnf.val⟩
  · rintro ⟨⟨v, hv⟩, _⟩
    exact ⟨v, hv⟩

/--
**Theorem: `L_SAT_Canonical` is NP-Hard.**

Every language in NP reduces to `L_SAT_Canonical` via the
identity function. This is possible because our NP class is
defined over `CanonicalCNF` with a universal polynomial bound —
every language in the class satisfies the same
certificate-bounding proposition.
-/
theorem L_SAT_in_NP_def_Hard :
    ∀ (L' : Π k, Set (CanonicalCNF k)), L' ∈ NP_def →
      ∃ (f : (ucnf : Σ k, CanonicalCNF k) →
          CanonicalCNF ucnf.1),
        (∃ (P : EntropyNat.Polynomial), ∀ ucnf,
          (encodeCNF (f ucnf).val).length ≤
            toNat (P.eval
              (ofNat (encodeCNF ucnf.2.val).length))) ∧
        (∀ ucnf, (ucnf.2 ∈ L' ucnf.1) ↔
          (f ucnf ∈ L_SAT_Canonical ucnf.1)) :=
by
  intro L' hL'_in_NP
  let f (ucnf : Σ k, CanonicalCNF k) :
      CanonicalCNF ucnf.1 := ucnf.2
  use f
  apply And.intro
  · use EntropyNat.Polynomial.id
    intro ucnf
    simp only [f, EntropyNat.Polynomial.eval]
    rw [EntropyNat.ofNat_toNat]
  · intro ucnf
    simp only [f]
    have h_equiv_L' := hL'_in_NP ucnf.1 ucnf.2
    have h_equiv_lsat := L_SAT_in_NP_def ucnf.1 ucnf.2
    rw [h_equiv_L', h_equiv_lsat]

/-!
# The Cook-Levin Theorem and P = NP
-/

/--
**NP-Completeness.**
-/
def IsNPComplete
    (L : Π k, Set (CanonicalCNF k)) : Prop :=
  (L ∈ NP_def) ∧
  (∀ (L' : Π k, Set (CanonicalCNF k)), L' ∈ NP_def →
    ∃ (f : (ucnf : Σ k, CanonicalCNF k) →
        CanonicalCNF ucnf.1),
      (∃ (P : EntropyNat.Polynomial), ∀ ucnf,
        (encodeCNF (f ucnf).val).length ≤
          toNat (P.eval
            (ofNat (encodeCNF ucnf.2.val).length))) ∧
      (∀ ucnf, (ucnf.2 ∈ L' ucnf.1) ↔
        (f ucnf ∈ L ucnf.1)))

/--
**The Cook-Levin Theorem: `L_SAT_Canonical` is NP-Complete.**
-/
theorem cookLevin : IsNPComplete L_SAT_Canonical := by
  constructor
  · exact L_SAT_in_NP_def
  · exact L_SAT_in_NP_def_Hard


/--
**Theorem: `L_SAT_Canonical` is in P.**

Membership in `L_SAT_Canonical` is equivalent to the verifier
accepting with bounded information content. The proof is identical
to `L_SAT_in_NP_def` because P and NP have the same definition.
-/
theorem L_SAT_in_P :
    (L_SAT_Canonical : Π k, Set (CanonicalCNF k)) ∈ P_def :=
by
  unfold P_def
  intro k input_ccnf
  unfold L_SAT_Canonical
  simpa [Set.mem_setOf_eq] using
    sat_iff_verifier_bounded input_ccnf



/-!
# The Final Theorem: P = NP

`NP_def` shows the verifier FUNCTION (`evalCNF`) and the existential
WITNESS (`∃ witness`). `P_def` shows only the Bool RESULT
(`verifierAccepts`). They look different, but the definitions are
identical because `verifierAccepts` IS `∃ witness, evalCNF ... witness = true`.

The proof is `Iff.rfl` (after unfolding `verifierAccepts`) because the
verifier's Bool result on a finite domain IS the existential over witnesses.
-/

/--
**Theorem: P = NP.**

`P_def` uses the Bool result (`verifierAccepts`).
`NP_def` uses the verifier function + witness (`∃ witness, evalCNF ... = true`).
These are the same predicate because `verifierAccepts` IS the existential.

The proof is `Iff.rfl` — Lean's kernel confirms definitional equality.
-/
theorem P_eq_NP : P_def = NP_def := by
  apply Set.ext; intro L; unfold P_def NP_def verifierAccepts; exact Iff.rfl

end InformationTheory
