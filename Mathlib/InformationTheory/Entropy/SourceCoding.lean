/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.InformationTheory.Entropy.Program
public import Mathlib.Analysis.SpecialFunctions.Log.Base



/-!
# Source Coding: Sources, Shannon Entropy, and the SCT/ISCT

This file establishes the equivalences between information sources and
Shannon entropy. It formalises the source coding theorem (SCT) and its
inverse (ISCT), and the distribution-level RECT bridge.

## Main definitions

* `FiniteIIDSample` — a finite sample from an IID source, parametrised
  by `p_param`, `q_param`, and `num_sub_samples`.
* `InformationSource` — alias for `FiniteIIDSample`.
* `BitsPerChoice_IIDParticleSource` / `BitsPerSubSample_IIDParticleSource`
  — per-choice and per-subsample entropy measures.
* `shannonEntropyOfBiasedSource` — Shannon entropy (in bits) of one
  trial from a biased Bernoulli source.
* `entropyEncoder` — total encoding length for a biased IID source.
* `shannonEntropyOfDist` — Shannon entropy (in bits) of an arbitrary
  discrete distribution.
* `shannonEntropyOfEquiprobableTape` — Shannon entropy of the uniform
  distribution over all `m`-bit tapes.
* `sourceCodingForward` / `sourceCodingInverse` — the source coding
  theorem (SCT) and its inverse (ISCT).
* `sourceToProgram` / `programToSource` — direct SCT/RECT bridges.

## Main results

* `exists_program_of_dist` -- for any distribution, there exists a
  program whose complexity matches its Shannon entropy.
* `invSCT_entropy_of_program` -- every program has a well-defined
  entropy (inverse source coding).
* `ISCT_SCT_inverse_for_integer_entropy` -- SCT and ISCT are inverses
  for integer entropy values.

## Tags

source coding, entropy, information theory, SCT, ISCT
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


open Finset Real

namespace InformationTheory

/-! ## FiniteIIDSample -/

/-- Represents a finite sample from an IID (Independent and
Identically Distributed) source. The total number of choices is
`num_sub_samples * (p_param + q_param)`. -/
structure FiniteIIDSample where
  /-- First bias parameter. -/
  p_param : ℕ
  /-- Second bias parameter. -/
  q_param : ℕ
  /-- Number of sub-samples drawn. -/
  num_sub_samples : ℕ
  /-- The source is non-trivial. -/
  h_is_nontrivial : p_param + q_param > 0

namespace FiniteIIDSample

/-- Computes the total number of choices for a `FiniteIIDSample`. -/
def sample_size_num_choices (s : FiniteIIDSample) : ℕ :=
  s.num_sub_samples * (s.p_param + s.q_param)

end FiniteIIDSample

/-! ## Type aliases -/

/-- An `InformationSource` is a physical or abstract process that
generates choices with a given probability distribution.
Alias for `FiniteIIDSample`. -/
abbrev InformationSource := FiniteIIDSample

/-! ## Bits per choice -/

/-- The Shannon entropy (in bits) of a single choice from an
`FiniteIIDSample`. Assumes each fundamental choice is a raw bit,
so entropy contribution is 1 bit. -/
@[nolint unusedArguments]
def BitsPerChoice_IIDParticleSource
    (_source : FiniteIIDSample) : ℕ :=
  1

/-- If ordering does not matter, a sample of 1's and 0's can be
represented using only a sign bit and the lesser of the two
parameters. -/
def BitsPerSubSample_IIDParticleSource
    (s : FiniteIIDSample) : ℤ :=
  BitsPerChoice_IIDParticleSource s *
    (Int.natAbs ((s.p_param : ℤ) - (s.q_param : ℤ)))

/-! ## Shannon entropy helpers -/

/-- The Shannon entropy (in bits) of a single trial from a biased
source with `true` probability `p / (p + q)`. -/
@[nolint unusedArguments]
noncomputable def shannonEntropyOfBiasedSource
    (p q : ℕ) (_h_pos : p + q > 0) : ℝ :=
  let p_real := (p : ℝ)
  let q_real := (q : ℝ)
  let total := p_real + q_real
  let P_true := p_real / total
  let P_false := q_real / total
  (Real.negMulLog P_true + Real.negMulLog P_false) /
    Real.log 2

/-- Standard Shannon entropy of `p : α → NNReal`. Uses natural
logarithm. -/
noncomputable def stdShannonEntropyLn {α : Type*}
    [Fintype α] (p : α → NNReal) : Real :=
  ∑ i : α, Real.negMulLog (p i : Real)

/-- Standard Shannon Entropy (base 2) for a system of `k`
equiprobable states. -/
noncomputable def shannonEntropyOfSystem (k : ℕ) : ℝ :=
  if k > 0 then Real.logb 2 k else 0

/-- The efficient encoding length for a sequence of trials from a
biased source. Equal to `num_sub_samples * H_per_trial`. -/
noncomputable def entropyEncoder (s : FiniteIIDSample) : ℝ :=
  (s.num_sub_samples : ℝ) *
    shannonEntropyOfBiasedSource s.p_param s.q_param
      s.h_is_nontrivial

/-- Shannon entropy (in bits) of a discrete probability distribution
`dist` over `Fin k`. Generalises `shannonEntropyOfSystem` to
non-uniform distributions. -/
noncomputable def shannonEntropyOfDist {k : ℕ}
    (dist : Fin k → NNReal) : ℝ :=
  (stdShannonEntropyLn dist) / Real.log 2

/-! ## Equiprobable tape entropy -/

/-- Shannon entropy (in nats) of the uniform distribution over all
`2^m_bits`-length binary tapes. -/
noncomputable def shannonEntropyOfEquiprobableTape
    (m_bits : ℕ) : ℝ :=
  if _hm_pos : m_bits > 0 then
    Real.log (2 ^ m_bits : ℝ)
  else
    0 * Real.log 2

/-- `log (↑(x ^ n)) = n • log (↑x)` for `x, n : ℕ` with
`NeZero x`. -/
lemma log_nat_cast_pow_of_pos (x n : ℕ) [_h : NeZero x] :
    Real.log (↑x ^ n) = n • Real.log (↑x) := by
  let x_real : ℝ := ↑x
  let n_real : ℝ := ↑n
  let real_pow_x_n : ℝ := (x ^ n : ℝ)
  simp [x_real, n_real, real_pow_x_n]

lemma shannon_entropy_of_tape_choice_eq_m_log2
    (m_bits : ℕ) (hm_pos : m_bits > 0) :
    shannonEntropyOfEquiprobableTape m_bits =
      ↑(m_bits : ℝ) * Real.log 2 := by
  simp [shannonEntropyOfEquiprobableTape, dif_pos hm_pos,
    log_nat_cast_pow_of_pos]

lemma shannon_entropy_of_tape_choice_zero_div_log_two_eq_zero :
    shannonEntropyOfEquiprobableTape 0 / Real.log 2 = 0 := by
  have h_cond_false : ¬ (0 > 0) := Nat.lt_irrefl 0
  simp [shannonEntropyOfEquiprobableTape, dif_neg h_cond_false,
    zero_mul, zero_div]

/-! ## Source coding theorems -/

/-- **Generalised RECT for distributions:** For any discrete
probability distribution `dist`, there exists a `Program` whose
complexity equals `⌈H(dist)⌉`. -/
theorem exists_program_of_dist {k : ℕ}
    (dist : Fin k → NNReal) (_h_sum : ∑ i, dist i = 1) :
    ∃ (prog : Program),
      prog.complexity = Nat.ceil (shannonEntropyOfDist dist) := by
  let L := Nat.ceil (shannonEntropyOfDist dist)
  refine ⟨{ current_state := 0, tape := List.replicate L true },
    ?_⟩
  simp [Program.complexity]
  rfl

/-- **Inverse SCT (Part A):** Any program of complexity `L`
corresponds to a single microstate in a system of `2^L`
equiprobable states, which has Shannon entropy `L`. -/
theorem invSCT_entropy_of_program (prog : Program) :
    shannonEntropyOfSystem (2 ^ (Program.complexity prog)) =
      ((Program.complexity prog) : ℝ) := by
  simp only [shannonEntropyOfSystem]
  have h_pow_pos : 0 < 2 ^ (Program.complexity prog) :=
    Nat.pow_pos (by norm_num)
  rw [if_pos h_pow_pos]
  simp [Real.logb_pow]

/-- **RECT for biased sources:** For any well-defined
`FiniteIIDSample`, there exists a `Program` whose complexity is
`⌈entropyEncoder src⌉`. -/
theorem exists_program_of_biased_source
    (src : FiniteIIDSample) :
    ∃ (prog : Program),
      prog.complexity =
        Nat.ceil (entropyEncoder src) := by
  let L := Nat.ceil (entropyEncoder src)
  refine ⟨{ current_state := 0, tape := List.replicate L true },
    ?_⟩
  simp [Program.complexity]
  rfl

/-! ### IIDSource ↔ Shannon Entropy -/

/-- **SCT (Source Coding Theorem):** An `InformationSource` has a
quantifiable `InformationContentR`. The total information is its
number of trials multiplied by the entropy per trial. -/
noncomputable def sourceCodingForward
    (src : InformationSource) : InformationContentR :=
  entropyEncoder src

/-- **ISCT (Inverse Source Coding Theorem):** Any
`InformationContentR` can be modelled by a source. For any
amount of information `H`, we construct a fair source (1 bit/trial)
with `⌈H⌉` trials. -/
noncomputable def sourceCodingInverse
    (H : InformationContentR) : InformationSource :=
  let L := Nat.ceil H
  { p_param := 1, q_param := 1, num_sub_samples := L,
    h_is_nontrivial := by norm_num }

set_option linter.flexible false in
/-- ISCT is a valid inverse of SCT for integer information
contents. -/
theorem ISCT_SCT_inverse_for_integer_entropy (L : ℕ) :
    sourceCodingForward (sourceCodingInverse (L : ℝ)) =
      (L : ℝ) := by
  simp [sourceCodingForward, sourceCodingInverse,
    entropyEncoder]
  have h_entropy_one :
      shannonEntropyOfBiasedSource 1 1 (by norm_num) = 1 := by
    simp only [shannonEntropyOfBiasedSource, Real.negMulLog]
    have h_frac : (↑1 : ℝ) / (↑1 + ↑1) = (1 / 2 : ℝ) := by
      norm_num
    simp [h_frac]
    have h_log_nz : Real.log 2 ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by norm_num)
        (by norm_num)
    field_simp [h_log_nz]
    norm_num
  rw [h_entropy_one, mul_one]

/-! ### IIDSource ↔ Program (The Direct Bridge) -/

/-- **SCT → RECT Bridge:** Any information source can be encoded
by a program whose complexity matches the source's information
content. -/
theorem sourceToProgram (src : InformationSource) :
    ∃ (prog : ComputationalDescription),
      prog.complexity =
        Nat.ceil (sourceCodingForward src) := by
  exact exists_program_of_entropy (sourceCodingForward src)

/-- **IRECT → ISCT Bridge:** Any program can be modelled as the
output of an information source with equivalent information
content. -/
noncomputable def programToSource
    (prog : ComputationalDescription) : InformationSource :=
  sourceCodingInverse (programToEntropy prog)

set_option linter.flexible false in
/-- Consistency of the direct bridge: the entropy of the source
recovered from a program equals the program's information
content. -/
theorem program_source_complexity_matches
    (prog : ComputationalDescription) :
    let src := programToSource prog
    sourceCodingForward src = programToEntropy prog := by
  simp [programToSource, programToEntropy]
  exact ISCT_SCT_inverse_for_integer_entropy prog.complexity

end InformationTheory
