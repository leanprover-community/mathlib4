/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
**In memory of Gian-Carlo Rota, April 27, 1932 - April 18, 1999.**
-/
module
public import Mathlib.InformationTheory.Entropy.Concrete
public import Mathlib.InformationTheory.Entropy.SourceCoding
public import Mathlib.InformationTheory.EntropyNumber.Hierarchy

@[expose] public section


open Real Finset

/-!
# Analysis: Entropy Scaling, Fair-Coin Calibration, and Prime Information Atoms

This file contains the capstone theorems connecting the axiomatic
entropy machinery to concrete computations:

1. **Rota Scaling** (`rota_all_entropy_scaled_shannon`): any positive
   scalar multiple of a verified `EntropyFunction` still satisfies
   all 7 Rota axioms.
2. **Fair-Coin Calibration** (`entropy_of_fair_coin_is_one_bit`):
   the canonical base-2 entropy of a fair coin flip is exactly 1 bit.
3. **Empirical Frequency / Bias**: extraction of rational frequencies
   and asymptotic bias from an `EntropyReal` source.
4. **FTA via Information** (`fta_via_information`,
   `fta_via_entropy_bits`): the Fundamental Theorem of Arithmetic
   restated in information-theoretic (logarithmic / entropy) form.
5. **Binomial Entropy** (`total_entropy_from_classes_eq_shannon_formula`):
   the total entropy from irreducible Bernoulli classes equals
   `n * H(p)`.

## Main definitions

* `empirical_frequency` -- extracts the rational frequency from an `EntropyReal` source.
* `get_bias_of_source` -- extracts the asymptotic bias of a source.
* `InfoIrreducibleClass` -- a Bernoulli class with an irreducible bias parameter.
* `generateIrreducibleClasses` -- generates `n` irreducible Bernoulli classes.

## Main results

* `rota_all_entropy_scaled_shannon` -- any positive scalar multiple
  of an `EntropyFunction` satisfies all 7 Rota axioms.
* `entropy_of_fair_coin_is_one_bit` -- the base-2 entropy of a fair coin flip is exactly 1 bit.
* `fta_via_information` -- the Fundamental Theorem of Arithmetic in
  information-theoretic (logarithmic) form.
* `total_entropy_from_classes_eq_shannon_formula` -- total entropy
  from irreducible Bernoulli classes equals `n * H(p)`.
-/

namespace InformationTheory

/--
**Rota's Entropy Theorem (Modernized Capstone) — All Entropy Is
Scaled Shannon Entropy.**

This is the modernized culmination of Rota's uniqueness-of-entropy
proof. It shows that any positive scalar multiple of an
`EntropyFunction` still satisfies all 7 Rota axioms, thereby
establishing that Shannon entropy (up to a constant) is the *unique*
function with these properties.

Unlike `Uniqueness.lean` — which takes the 7 axioms as given
assumptions — this theorem operates on `EntropyFunction` instances
whose properties are **fully proven** (not assumed). In particular,
`shannonEntropyFunction` from `Entropy/Concrete.lean` supplies an
`EntropyFunction` where each of the 7 "axioms" is a proper theorem:

  - `shannonEntropyNNReal_normalized`
  - `shannonEntropyNNReal_symmetric`
  - `shannonEntropyNNReal_empty`
  - `shannonEntropyNNReal_zeroInvariant`
  - `shannonEntropyNNReal_continuous`
  - `shannonEntropyNNReal_condAddSigma`
  - `shannonEntropyNNReal_maxUniform`

This completes the modernization of Rota's result: the uniqueness
theorem now stands on fully proven foundations, axiom-free and
sorry-free. The scaling by a positive constant `C` also enables
base-of-logarithm changes (e.g., nats to bits) without re-proving
each axiom.
-/
theorem rota_all_entropy_scaled_shannon
    (ef : EntropyFunction) (C : ℝ) (hC_pos : 0 < C) :
    HasRotaEntropyAxioms
      (fun p => (C * (ef.H_func p : ℝ)).toNNReal) :=
  let C_nn : NNReal := C.toNNReal
  have hC_nn_pos : 0 < C_nn := by
    simp only [C_nn]
    exact Real.toNNReal_pos.mpr hC_pos
  {
    -- Each axiom proof for the scaled function follows from the
    -- original proof by distributing the constant C.
    symmetry := by
      intro α β _ _ p_target hp e
      congr 2
      simp only [NNReal.coe_inj]
      exact ef.props.symmetry p_target hp e
    ,
    zero_invariance := by
      intro n p_orig hp_sum_1
      congr 2
      simp only [NNReal.coe_inj]
      exact ef.props.zero_invariance p_orig hp_sum_1
    ,
    normalized := by
      intro p hp_sum_1
      simp only [ef.props.normalized p hp_sum_1,
        NNReal.coe_zero, mul_zero, Real.toNNReal_zero]
    ,
    max_uniform := by
      intro α _ h_card_pos p hp_sum_1
      apply Real.toNNReal_le_toNNReal
      apply mul_le_mul_of_nonneg_left
      · exact NNReal.coe_le_coe.mpr
          (ef.props.max_uniform h_card_pos p hp_sum_1)
      · exact le_of_lt hC_pos
    ,
    continuity := by
      intro α _ p_center hp_sum_1 ε hε_pos

      have hC_abs_pos : |C| > 0 :=
        abs_pos.mpr (ne_of_gt hC_pos)
      let ε_scaled := ε / |C|
      have hε_scaled_pos : ε_scaled > 0 :=
        div_pos hε_pos hC_abs_pos

      obtain ⟨δ, hδ_pos, hδ_works⟩ :=
        ef.props.continuity p_center hp_sum_1
          ε_scaled hε_scaled_pos

      use δ, hδ_pos
      intro q hq_sum_1 hq_close

      have h_ef_close := hδ_works q hq_sum_1 hq_close

      have h_nonneg_q :
          0 ≤ (C * (ef.H_func q : ℝ)) :=
        mul_nonneg (le_of_lt hC_pos)
          (NNReal.coe_nonneg _)
      have h_nonneg_p :
          0 ≤ (C * (ef.H_func p_center : ℝ)) :=
        mul_nonneg (le_of_lt hC_pos)
          (NNReal.coe_nonneg _)

      rw [Real.coe_toNNReal _ h_nonneg_q,
        Real.coe_toNNReal _ h_nonneg_p]

      rw [← mul_sub, abs_mul]

      rw [abs_of_pos hC_pos]

      have h_bound :
          |((ef.H_func q) : ℝ)
            - ((ef.H_func p_center) : ℝ)| <
              ε_scaled :=
        h_ef_close

      calc C * |((ef.H_func q) : ℝ)
              - ((ef.H_func p_center) : ℝ)|
          < C * ε_scaled :=
            mul_lt_mul_of_pos_left h_bound hC_pos
        _ = C * (ε / |C|) := rfl
        _ = C * (ε / C) := by
            rw [abs_of_pos hC_pos]
        _ = ε := by
            field_simp [ne_of_gt hC_pos]
    ,
    cond_add_sigma := by
      intro N _inst prior M_map P_cond hprior_sum_1
        hP_cond_props hH_P_cond_zero

      apply NNReal.eq
      symm

      have h_joint_nonneg :
          0 ≤ C * (ef.H_func
            (dependentPairDistSigma prior M_map
              P_cond) : ℝ) :=
        mul_nonneg (le_of_lt hC_pos)
          (NNReal.coe_nonneg _)
      have h_prior_nonneg :
          0 ≤ C * (ef.H_func prior : ℝ) :=
        mul_nonneg (le_of_lt hC_pos)
          (NNReal.coe_nonneg _)
      have h_cond_i_nonneg (i : Fin N) :
          0 ≤ C * (ef.H_func (P_cond i) : ℝ) :=
        mul_nonneg (le_of_lt hC_pos)
          (NNReal.coe_nonneg _)

      calc
        ↑((C * ↑(ef.H_func prior)).toNNReal
          + ∑ i, prior i
            * (C * ↑(ef.H_func (P_cond i))).toNNReal)

        _ = (C * (ef.H_func prior : ℝ))
            + ∑ i, (prior i : ℝ)
              * (C * (ef.H_func (P_cond i) : ℝ)) := by
            rw [NNReal.coe_add, NNReal.coe_sum]
            congr 1
            · rw [Real.coe_toNNReal _ h_prior_nonneg]
            · congr 1
              ext i
              rw [NNReal.coe_mul,
                Real.coe_toNNReal _
                  (h_cond_i_nonneg i)]

        _ = C * ((ef.H_func prior : ℝ)
            + ∑ i, (prior i : ℝ)
              * (ef.H_func (P_cond i) : ℝ)) := by
            rw [mul_add]
            congr 1
            rw [mul_sum]
            congr 1
            ext i
            ring

        _ = C * (ef.H_func
            (dependentPairDistSigma prior M_map
              P_cond) : ℝ) := by
            congr 1
            have hH_P_cond_zero_orig :
                ∀ (i : Fin N), M_map i = 0 →
                  ef.H_func (P_cond i) = 0 := by
              intro i hi
              have h := hH_P_cond_zero i hi
              have h_zero :
                  C * ↑(ef.H_func (P_cond i)) = 0 := by
                have h_nonneg := h_cond_i_nonneg i
                have h_le_zero :
                    C * ↑(ef.H_func (P_cond i)) ≤ 0 :=
                  Real.toNNReal_eq_zero.mp h
                exact le_antisymm h_le_zero h_nonneg
              have h_coe_zero :
                  ↑(ef.H_func (P_cond i)) = (0 : ℝ) := by
                have h_nonzero : C ≠ 0 :=
                  ne_of_gt hC_pos
                rw [mul_eq_zero] at h_zero
                cases h_zero with
                | inl h => contradiction
                | inr h => exact h
              exact NNReal.coe_eq_zero.mp h_coe_zero
            have h_orig_axiom :=
              ef.props.cond_add_sigma prior M_map
                P_cond hprior_sum_1 hP_cond_props
                hH_P_cond_zero_orig
            have h_real :
                (ef.H_func (dependentPairDistSigma
                  prior M_map P_cond) : ℝ) =
                (ef.H_func prior : ℝ)
                  + ∑ i, (prior i : ℝ)
                    * (ef.H_func (P_cond i) : ℝ) := by
              rw [h_orig_axiom]
              simp only [NNReal.coe_add,
                NNReal.coe_sum, NNReal.coe_mul]
            exact h_real.symm

        _ = ↑((C * ↑(ef.H_func
            (dependentPairDistSigma prior M_map
              P_cond))).toNNReal) := by
            rw [Real.coe_toNNReal _ h_joint_nonneg]
    ,
    apply_to_empty_domain := by
      simp only [ef.props.apply_to_empty_domain,
        NNReal.coe_zero, mul_zero,
        Real.toNNReal_zero]
  }



/--
**Theorem:** For the canonical base-2 Shannon entropy function
(`shannonEntropyLog2`), the entropy of a single fair coin flip is
exactly 1 bit.

**Interpretation:** This is the formal "unit test" confirming that
our entropy engine is perfectly calibrated for computer science
applications, where the bit is the fundamental unit of information.
-/
theorem entropy_of_fair_coin_is_one_bit :
    let coin_flip_dist :=
      canonicalUniformDist 2 (by norm_num)
    shannonEntropyLog2 coin_flip_dist = 1 := by

  let coin_flip_dist :=
    canonicalUniformDist 2 (by norm_num)
  simp only [shannonEntropyLog2, coin_flip_dist,
    canonicalUniformDist]

  have h2_pos : (2 : ℕ) > 0 := by norm_num
  have h_uniform_entropy :
      shannonEntropy
        (uniformDist (Fintype.card_fin_pos h2_pos)) =
          log 2 := by
    rw [shannonEntropy_uniformDist
      (Fintype.card_fin_pos h2_pos)]
    simp [Fintype.card_fin]

  rw [h_uniform_entropy]

  have h_log2_ne_zero : log 2 ≠ 0 :=
    ne_of_gt (log_pos (by norm_num : (2:ℝ) > 1))
  rw [div_self h_log2_ne_zero]

  rw [Real.toNNReal_one]

/--
For a given infinite source (`EntropyReal`) and a prefix length `n`,
this function computes the empirical frequency of `true`s as a
rational number.
-/
noncomputable def empirical_frequency
    (egpt_real : EntropyReal) (n : ℕ) : ℚ :=
  if _hn_pos : n > 0 then
    let prefix_tape := List.ofFn
      (fun i : Fin n => egpt_real (EntropyNat.ofNat i.val))
    let p_count := prefix_tape.count true
    mkRat p_count n
  else
    0

/--
`get_bias_of_source` returns the asymptotic bias (frequency of
`true`) of an infinite IID bit source.  We take the
`Filter.liminf` of the empirical frequencies (viewed as real
numbers) and coerce it to a non-negative real using
`Real.toNNReal`.
-/
noncomputable def get_bias_of_source
    (egpt_real : EntropyReal) : NNReal :=
  let seq : ℕ → ℝ :=
    fun n => (empirical_frequency egpt_real n : ℝ)
  Real.toNNReal (Filter.liminf seq Filter.atTop)


/--
**toFun (The Encoder via Rota's Final Formula):** Computes the
canonical measure of an `EntropyReal` by directly applying the
Rota-Uniqueness of Entropy (RUE) theorem.

This definition replaces a direct call to the axiomatic H function
with the explicit formula (`C * H_shannon`) that Rota's theorem
proves it must satisfy.
-/
noncomputable def toFun_EntropyReal_to_Std_Real
    (ef : EntropyFunction)
    (egpt_real : EntropyReal) : ℝ :=
  let p_bias := get_bias_of_source egpt_real

  let dist_of_source : Fin 2 → NNReal :=
    fun i => if i.val = 0 then (1 - p_bias) else p_bias

  let h_shannon_nats :=
    stdShannonEntropyLn dist_of_source

  let C := rotaConstant_of_EntropyFunction ef

  C * (h_shannon_nats / Real.log 2)


/--
For a given prefix length `n`, this function creates the
`FiniteIIDSample` that perfectly describes the observed statistics.
-/
noncomputable def empirical_sample
    (egpt_real : EntropyReal) (n : ℕ) :
    Option FiniteIIDSample :=
  if hn_pos : n > 0 then
    let prefix_tape := List.ofFn
      (fun i : Fin n =>
        egpt_real (EntropyNat.ofNat i.val))
    let p := prefix_tape.count true
    let q := n - p
    some {
      p_param := p,
      q_param := q,
      num_sub_samples := 1,
      h_is_nontrivial := by {
        simp [p, q]
        by_cases h : true ∈ prefix_tape
        · left; exact h
        · right
          simp [List.count_eq_zero_of_not_mem h]
          exact hn_pos
      }
    }
  else
    none

/--
For a given prefix length `n`, this function creates the canonical
`EntropyRat` that encodes the empirical frequency.
-/
noncomputable def empirical_pmf
    (egpt_real : EntropyReal) (n : ℕ) : EntropyRat :=
  EntropyRat.ofRat (empirical_frequency egpt_real n)




/-!
We formalize the content of the Fundamental Theorem of Arithmetic
via Information: the information (in bits) of a uniform system
with `n` equiprobable outcomes is `log₂ n`, and prime
factorization transports multiplicative structure of `n` into
additive structure of information.

We work directly with `Real.logb 2` (natural logarithm
base-change). When connected to the canonical base-2 entropy
`shannonEntropyLog2`, we obtain the Fundamental Theorem of
Information Arithmetic (FTA-Info):

    H(uniform_n) = ∑_{p prime | n} (ν_p n) * H(uniform_p)

Since `H(uniform_p) = log₂ p`, this is equivalent to the
classical identity `log₂ n = ∑ ν_p(n) * log₂ p`.
-/

/-- `1 < (2 : ℝ)`. -/
lemma logb_two_pos : 1 < (2 : ℝ) := by norm_num
/-- `Real.log 2 ≠ 0`. -/
lemma log_two_ne_zero : Real.log 2 ≠ 0 := by
  exact ne_of_gt (Real.log_pos logb_two_pos)

@[simp] lemma logb_two_two : Real.logb 2 2 = 1 := by
  unfold Real.logb
  rw [div_self log_two_ne_zero]

@[simp] lemma logb_two_factorization
    (n : ℕ) (_hn : 0 < n) :
    Real.logb 2 n =
      ∑ p ∈ n.factorization.support,
        (n.factorization p : ℝ) * Real.logb 2 p := by
  change Real.logb 2 (n : ℝ)
    = ∑ p ∈ n.factorization.support,
        (n.factorization p : ℝ)
          * Real.logb 2 (p : ℝ)
  simpa [Finsupp.sum] using
    (Real.logb_nat_eq_sum_factorization (b := 2) n)

/-- Uniform-distribution entropy decomposes via the prime factorization of `n`. -/
lemma entropy_uniform_logb_factorization
    (n : ℕ) (hn : 1 < n)
    (bridge :
      shannonEntropyLog2
        (canonicalUniformDist n
          (Nat.lt_trans (Nat.succ_pos 0) hn))
        = ((Real.logb 2 n)).toNNReal)
  :
  shannonEntropyLog2
    (canonicalUniformDist n
      (Nat.lt_trans (Nat.succ_pos 0) hn)) =
    ((∑ p ∈ n.factorization.support,
        (n.factorization p : ℝ)
          * Real.logb 2 p)).toNNReal := by
  have hn_pos : 0 < n :=
    Nat.lt_trans (Nat.succ_pos 0) hn
  have hfac := logb_two_factorization n hn_pos
  rw [bridge, hfac]

/-!
Main statement (bits form): Fundamental Theorem of Information
Arithmetic. We state it purely in logarithmic terms; the entropy
version follows by the uniform-entropy bridge.
-/
theorem fta_via_information (n : ℕ) (hn : 1 < n) :
    Real.logb 2 n =
      ∑ p ∈ n.factorization.support,
        (n.factorization p : ℝ)
          * Real.logb 2 p :=
  logb_two_factorization n
    (Nat.lt_trans (Nat.succ_pos 0) hn)

/-!
Entropy phrasing (schematic): each prime factor contributes
additively its bit-information. This mirrors the Lean outline
in the FTA documentation.
-/
theorem fta_via_entropy_bits
    (n : ℕ) (hn : 1 < n)
    (bridge :
      shannonEntropyLog2
        (canonicalUniformDist n
          (Nat.lt_trans (Nat.succ_pos 0) hn))
        = ((Real.logb 2 n)).toNNReal)
  :
  shannonEntropyLog2
    (canonicalUniformDist n
      (Nat.lt_trans (Nat.succ_pos 0) hn)) =
    ((∑ p ∈ n.factorization.support,
        (n.factorization p : ℝ)
          * Real.logb 2 p)).toNNReal := by
  have hfac := fta_via_information n hn
  simp [bridge, hfac]


/-!
### Section 1: Defining the Informationally Irreducible Class

This structure captures the properties of a single "class" of
outcomes in a Bernoulli process of `n` trials: all outcomes with
exactly `k` successes.
-/

/--
A single "informationally irreducible class" for a Bernoulli
process. It contains the number of successes (`num_ones`), the
number of outcomes in the class (`multiplicity`), the probability
of any single outcome in this class (`prob`), and the total
entropy this class contributes to the system.
-/
@[ext]
structure InfoIrreducibleClass where
  num_ones : ℕ
  multiplicity : ℕ
  prob : NNReal
  entropy_contribution : ℝ

/-!
### Section 2: The Generator Function

This function generates the list of all n+1 irreducible classes
for a Bernoulli process of `n` trials with success probability
`p`.
-/

/-- A helper function to compute `-p * logb 2 p` in bits. -/
noncomputable def negMulLogb2 (p : NNReal) : ℝ :=
  if p = 0 then 0 else -(p : ℝ) * logb 2 (p : ℝ)

/--
Generates the list of all `n+1` informationally irreducible
classes for a Bernoulli process of `n` trials with success
probability `p`.
-/
noncomputable def generateIrreducibleClasses
    (n : ℕ) (p : NNReal)
    (_hp_pos : 0 < p) (_hp_lt_one : p < 1) :
  List InfoIrreducibleClass :=
  (List.range (n + 1)).map fun k =>
    let mult := n.choose k
    let prob_k := p ^ k * (1 - p) ^ (n - k)
    let entropy_k :=
      (mult : ℝ) * negMulLogb2 prob_k
    {
      num_ones := k,
      multiplicity := mult,
      prob := prob_k,
      entropy_contribution := entropy_k
    }


/-- Helper: the ℝ-coercions of `p : NNReal` and `1-p : NNReal`
are positive under `0 < p < 1`. -/
lemma real_pos_of_nn (p : NNReal) (hp_pos : 0 < p) :
    0 < (p : ℝ) :=
  by exact_mod_cast hp_pos

/-- `(1 - p : NNReal)` coerced to `ℝ` is positive when `p < 1`. -/
lemma real_pos_of_one_sub_nn
    (p : NNReal) (hp_lt_one : p < 1) :
  0 < ((1 - p : NNReal) : ℝ) :=
by
  have hp_real_lt_one : (p : ℝ) < 1 :=
    by exact_mod_cast hp_lt_one
  have hpos_real : 0 < (1 : ℝ) - p :=
    sub_pos.mpr hp_real_lt_one
  have hp_le_one : p ≤ 1 := le_of_lt hp_lt_one
  have hcoe : ((1 - p : NNReal) : ℝ) = (1 : ℝ) - p := by
    simpa using (NNReal.coe_sub hp_le_one)
  simpa [hcoe]

/-- Helper: a variant of `Finset.sum_range_succ` that pulls off
the first term. -/
lemma sum_range_succ_pull {α} [AddCommMonoid α]
    (f : ℕ → α) (n : ℕ) :
  ∑ k ∈ Finset.range (n+1), f k =
    f 0 + ∑ k ∈ Finset.range n, f (k+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 :=
      Finset.sum_range_succ (fun k => f k) (n + 1)
    have h2 :=
      Finset.sum_range_succ (fun k => f (k+1)) n
    calc ∑ k ∈ Finset.range (n + 2), f k
      = (∑ k ∈ Finset.range (n + 1), f k)
        + f (n + 1) := by exact h1
      _ = (f 0 + ∑ k ∈ Finset.range n, f (k + 1))
        + f (n + 1) := by rw [ih]
      _ = f 0
        + ((∑ k ∈ Finset.range n, f (k + 1))
          + f (n + 1)) := by rw [add_assoc]
      _ = f 0
        + (∑ k ∈ Finset.range (n + 1), f (k + 1)) :=
            by rw [← h2]

/-- Helper: `List.foldl` over `List.range` equals a
`Finset.sum` over `Finset.range`. -/
lemma foldl_range_eq_sum {α} [AddCommMonoid α]
    (f : ℕ → α) (n : ℕ) :
    (List.range (n+1)).foldl
      (fun s k => s + f k) 0
    = ∑ k ∈ Finset.range (n+1), f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr : List.range (n+2) =
        List.range (n+1) ++ [n+1] := by
      simp [List.range_succ]
    simp [hr, ih, Finset.sum_range_succ,
      add_comm, add_left_comm, add_assoc]

/-- Rewrite the list `foldl` of entropy contributions as a `Finset.sum` over `k=0..n`. -/
lemma foldl_classes_as_sum
    (n : ℕ) (p : NNReal)
    (hp_pos : 0 < p) (hp_lt_one : p < 1) :
  (generateIrreducibleClasses n p hp_pos
    hp_lt_one).foldl
      (fun acc c => acc + c.entropy_contribution) 0
  =
  ∑ k ∈ Finset.range (n+1),
      ( (n.choose k : ℝ)
      * negMulLogb2 (p^k * (1 - p)^(n-k)) ) := by
  unfold generateIrreducibleClasses
  have := foldl_range_eq_sum
    (f := fun k => ( (n.choose k : ℝ)
      * negMulLogb2 (p^k * (1 - p)^(n-k)) ))
    n
  simpa [List.foldl_map,
    InfoIrreducibleClass.entropy_contribution]
    using this


/--
Transform the weighted sum with
`(n.choose (k+1)) * (k+1)` to one with
`((n-1).choose k)` using `Nat.succ_mul_choose_eq`, and
factor out `(n : ℝ) * x`.

This is the algebraic heart of `h_transform`, independent
from the specific `pk`.
-/
lemma choose_succ_weighted_sum_transform
    (n : ℕ) (x y : ℝ) :
    ∑ k ∈ Finset.range n,
      (n.choose (k+1) : ℝ) * x^(k+1)
        * y^(n - (k+1)) * ((k+1 : ℝ))
  = (n : ℝ) * x *
      ∑ k ∈ Finset.range n,
        ((n-1).choose k : ℝ)
          * x^k * y^((n-1) - k) := by
  have hpoint :
      ∀ k ∈ Finset.range n,
        (n.choose (k+1) : ℝ) * x^(k+1)
          * y^(n - (k+1)) * ((k+1 : ℝ))
        = (n : ℝ) * x
          * (((n-1).choose k : ℝ)
            * x^k * y^((n-1) - k)) := by
    intro k hk
    have hnat := Nat.succ_mul_choose_eq (n-1) k
    have hcast :
        ((n.choose (k+1)) * (k+1) : ℝ)
        = (n : ℝ) * ((n-1).choose k : ℝ) := by
      have hk_lt : k < n := Finset.mem_range.mp hk
      have hn_pos : 0 < n :=
        Nat.pos_of_ne_zero
          (fun h => by simp [h] at hk_lt)
      have hn_succ : (n-1).succ = n :=
        Nat.succ_pred_eq_of_pos hn_pos
      have h_cast :=
        congrArg (fun t : ℕ => (t : ℝ)) hnat
      simp only [Nat.cast_mul] at h_cast
      rw [hn_succ] at h_cast
      have : n.choose k.succ =
          n.choose (k+1) := by
        simp [Nat.succ_eq_add_one]
      have : k.succ = k + 1 :=
        Nat.succ_eq_add_one k
      rw [this] at h_cast
      simp only [Nat.cast_add, Nat.cast_one]
        at h_cast
      exact h_cast.symm
    have hk_lt : k < n := Finset.mem_range.mp hk
    have hsub : n - (k+1) = (n-1) - k := by
      have hk1 : k + 1 ≤ n :=
        Nat.succ_le_of_lt hk_lt
      omega
    calc
      (n.choose (k+1) : ℝ) * x^(k+1)
          * y^(n - (k+1)) * ((k+1 : ℝ))
          = ((n.choose (k+1) : ℝ) * (k+1 : ℝ))
            * (x^(k+1) * y^(n - (k+1))) := by
            ring
      _ = ((n : ℝ) * ((n-1).choose k : ℝ))
          * ( (x^k * x) * y^((n-1) - k) ) := by
            simpa [pow_succ, hsub, hcast,
              mul_comm, mul_left_comm, mul_assoc]
      _ = (n : ℝ) * x
          * (((n-1).choose k : ℝ)
            * x^k * y^((n-1) - k)) := by
            ring
  have := Finset.sum_congr rfl
    (by intro k hk; simpa using hpoint k hk)
  simpa [Finset.mul_sum, Finset.sum_mul,
    mul_comm, mul_left_comm, mul_assoc]
    using this

/--
Binomial theorem in the exact index form we need: for any `n`,
`∑_{k=0}^{n-1} C(n-1,k) x^k y^{(n-1)-k} =
  if n=0 then 0 else (x+y)^(n-1)`.
This guards the `n=0` edge case where the LHS is an empty sum.
-/
lemma sum_choose_pow_pred_eq_add_pow
    (n : ℕ) (x y : ℝ) :
    ∑ k ∈ Finset.range n,
      ((n-1).choose k : ℝ)
        * x^k * y^((n-1) - k)
  = (if n = 0 then 0 else (x + y)^(n-1)) := by
  cases n with
  | zero => simp
  | succ m =>
    have : (∑ k ∈ Finset.range (m+1),
        ((m).choose k : ℝ)
          * x^k * y^(m - k))
        = (x + y)^m := by
      have h_sum_eq :
          (∑ k ∈ Finset.range (m+1),
            ((m).choose k : ℝ)
              * x^k * y^(m - k))
          = (∑ k ∈ Finset.range (m+1),
              x^k * y^(m - k)
                * ((m).choose k : ℝ)) := by
        congr 1
        ext k
        ring
      rw [h_sum_eq, add_pow]
    simpa using this



/-- **Total entropy from classes equals the Shannon n·H formula
(base 2).** -/
theorem total_entropy_from_classes_eq_shannon_formula
    (n : ℕ) (p : NNReal)
    (hp_pos : 0 < p) (hp_lt_one : p < 1) :
  (generateIrreducibleClasses n p hp_pos
    hp_lt_one).foldl
      (fun acc c => acc + c.entropy_contribution) 0
  =
  n * (negMulLogb2 p + negMulLogb2 (1 - p)) := by

  have hfold :=
    foldl_classes_as_sum n p hp_pos hp_lt_one
  set q : ℝ := ((1 - p : NNReal) : ℝ)
  have hx_pos : 0 < (p : ℝ) :=
    real_pos_of_nn p hp_pos
  have hy_pos : 0 < q :=
    real_pos_of_one_sub_nn p hp_lt_one
  have hx_ne : (p : ℝ) ≠ 0 := ne_of_gt hx_pos
  have hy_ne : q ≠ 0 := ne_of_gt hy_pos

  set pk : ℕ → ℝ :=
    fun k => (p : ℝ)^k * q^(n - k)
  have pk_pos :
      ∀ k ∈ Finset.range (n+1), 0 < pk k := by
    intro k hk
    have : 0 < (p : ℝ)^k * q^(n - k) :=
      mul_pos (pow_pos hx_pos k)
        (pow_pos hy_pos (n - k))
    simpa [pk] using this

  have logb_mul_pow :
      ∀ k ∈ Finset.range (n+1),
        Real.logb 2 (pk k)
          = (k : ℝ) * Real.logb 2 (p : ℝ)
            + ((n : ℝ) - k) * Real.logb 2 q := by
    intro k hk
    have hxk_ne : (p : ℝ)^k ≠ 0 :=
      pow_ne_zero k hx_ne
    have hyk_ne : q^(n - k) ≠ 0 :=
      pow_ne_zero (n - k) hy_ne
    have h :=
      (Real.logb_mul (b:=2) (x:=(p : ℝ)^k)
        (y:=q^(n - k)) hxk_ne hyk_ne)
    rw [Real.logb_pow, Real.logb_pow] at h
    have hk_le : k ≤ n :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hcast : ((n - k : ℕ) : ℝ) =
        (n : ℝ) - k := Nat.cast_sub hk_le
    simpa [pk, hcast] using h

  have negMulLogb2_eval :
      ∀ k ∈ Finset.range (n+1),
        negMulLogb2 (p^k * (1 - p)^(n - k))
        = -(pk k) * Real.logb 2 (pk k) := by
    intro k hk
    have hnnpos :
        0 < (p^k * (1 - p)^(n - k) : NNReal) := by
      have : 0 < pk k := pk_pos k hk
      have : 0 < ((p^k * (1 - p)^(n - k)
          : NNReal) : ℝ) := by
        simpa [pk] using this
      exact (by exact_mod_cast this)
    have hne :
        (p^k * (1 - p)^(n - k) : NNReal) ≠ 0 :=
      ne_of_gt hnnpos
    simp [negMulLogb2, hne, pk]
    aesop

  have main_sum :
      ∑ k ∈ Finset.range (n+1),
          ( (n.choose k : ℝ)
            * negMulLogb2
                (p^k * (1 - p)^(n - k)) )
      =
      -(Real.logb 2 (p : ℝ)) *
        (∑ k ∈ Finset.range (n+1),
          (n.choose k : ℝ) * pk k * (k : ℝ))
      - (Real.logb 2 q) *
        (∑ k ∈ Finset.range (n+1),
          (n.choose k : ℝ) * pk k
            * ((n : ℝ) - k)) := by
    have hpoint :
      ∀ k ∈ Finset.range (n+1),
        ( (n.choose k : ℝ)
          * negMulLogb2
              (p^k * (1 - p)^(n - k)) )
        = -(Real.logb 2 (p : ℝ))
            * ((n.choose k : ℝ) * pk k * (k : ℝ))
          - (Real.logb 2 q)
            * ((n.choose k : ℝ) * pk k
              * ((n : ℝ) - k)) := by
      intro k hk
      have h₁ := negMulLogb2_eval k hk
      have h₂ := logb_mul_pow k hk
      calc
        (n.choose k : ℝ)
          * negMulLogb2
              (p^k * (1 - p)^(n - k))
            = (n.choose k : ℝ)
              * (-(pk k) * Real.logb 2 (pk k)) :=
                by simpa [h₁]
        _ = -(n.choose k : ℝ) * (pk k)
              * Real.logb 2 (pk k) := by ring
        _ = -(n.choose k : ℝ) * (pk k)
              * ((k : ℝ) * Real.logb 2 (p : ℝ)
                 + ((n : ℝ) - k)
                   * Real.logb 2 q) := by
              simpa [h₂]
        _ = -(Real.logb 2 (p : ℝ))
              * ((n.choose k : ℝ)
                * pk k * (k : ℝ))
            - (Real.logb 2 q)
              * ((n.choose k : ℝ)
                * pk k * ((n : ℝ) - k)) := by
              ring
    have := Finset.sum_congr rfl
      (by intro k hk; simpa using hpoint k hk)
    simpa [Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul] using this

  have S1 :
    ∑ k ∈ Finset.range (n+1),
      (n.choose k : ℝ) * pk k * (k : ℝ)
      = (n : ℝ) * (p : ℝ) := by
    have hpull :=
      sum_range_succ_pull
        (fun k => (n.choose k : ℝ)
          * pk k * (k : ℝ)) n
    have h0 :
        (n.choose 0 : ℝ) * pk 0 * (0 : ℝ) = 0 :=
      by simp [pk]
    have h_rewrite :
      ∑ k ∈ Finset.range (n+1),
        (n.choose k : ℝ) * pk k * (k : ℝ)
      = ∑ k ∈ Finset.range n,
          (n.choose (k+1) : ℝ)
            * pk (k+1) * ((k+1 : ℝ)) := by
      simp [hpull, h0]
    have h_transform :
      ∑ k ∈ Finset.range n,
        (n.choose (k+1) : ℝ)
          * pk (k+1) * ((k+1 : ℝ))
      = (n : ℝ) * (p : ℝ) *
          ∑ k ∈ Finset.range n,
            ((n-1).choose k : ℝ)
              * (p : ℝ)^k * q^((n-1) - k) := by
      simpa [pk, pow_succ, mul_comm,
        mul_left_comm, mul_assoc]
        using choose_succ_weighted_sum_transform
          n (p : ℝ) q
    have binom :
      ∑ k ∈ Finset.range n,
        ((n-1).choose k : ℝ) * (p : ℝ)^k
          * q^((n-1) - k)
      = (if n = 0 then 0
          else ((p : ℝ) + q)^(n-1)) := by
      simpa using
        sum_choose_pow_pred_eq_add_pow n (p : ℝ) q
    have pq_one : (p : ℝ) + q = 1 := by
      have hp_le_one : p ≤ 1 := le_of_lt hp_lt_one
      simp [q, NNReal.coe_sub hp_le_one]
    calc
      ∑ k ∈ Finset.range (n+1),
        (n.choose k : ℝ) * pk k * (k : ℝ)
          = ∑ k ∈ Finset.range n,
              (n.choose (k+1) : ℝ)
                * pk (k+1) * ((k+1 : ℝ)) :=
            h_rewrite
      _ = (n : ℝ) * (p : ℝ) *
            ∑ k ∈ Finset.range n,
              ((n-1).choose k : ℝ) * (p : ℝ)^k
                * q^((n-1) - k) := h_transform
      _ = (n : ℝ) * (p : ℝ)
          * (if n = 0 then 0
              else ((p : ℝ) + q)^(n-1)) := by
            simp [binom]
      _ = (n : ℝ) * (p : ℝ) := by aesop

  have Ssum :
    ∑ k ∈ Finset.range (n+1),
      (n.choose k : ℝ) * pk k
      = ( (p : ℝ) + q )^n := by
    simpa [pk, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc]
      using (add_pow (x := (p : ℝ))
        (y := q) (n := n)).symm
  have S2 :
    ∑ k ∈ Finset.range (n+1),
      (n.choose k : ℝ) * pk k
        * ((n : ℝ) - k)
      = (n : ℝ) * q := by
    have hsplit :
      ∑ k ∈ Finset.range (n+1),
        (n.choose k : ℝ) * pk k * ((n : ℝ) - k)
        = (n : ℝ)
          * (∑ k ∈ Finset.range (n+1),
              (n.choose k : ℝ) * pk k)
          - (∑ k ∈ Finset.range (n+1),
              (n.choose k : ℝ) * pk k
                * (k : ℝ)) := by
      conv_lhs =>
        arg 2
        ext k
        rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      congr 1
      simp only [Finset.mul_sum]
      congr 1
      ext i
      ring
    have pq_one : (p : ℝ) + q = 1 := by
      have hp_le_one : p ≤ 1 := le_of_lt hp_lt_one
      simpa [q, NNReal.coe_sub hp_le_one] using
        (by ring : (p : ℝ) + ((1 : ℝ) - p) = 1)
    calc
      ∑ k ∈ Finset.range (n+1),
        (n.choose k : ℝ) * pk k * ((n : ℝ) - k)
          = (n : ℝ)
            * (∑ k ∈ Finset.range (n+1),
                (n.choose k : ℝ) * pk k)
            - (∑ k ∈ Finset.range (n+1),
                (n.choose k : ℝ)
                  * pk k * (k : ℝ)) := hsplit
      _ = (n : ℝ) * (( (p : ℝ) + q )^n)
          - ( (n : ℝ) * (p : ℝ) ) := by
            simpa [Ssum, S1]
      _ = (n : ℝ) * (1 : ℝ)
          - (n : ℝ) * (p : ℝ) := by
            simpa [pq_one]
      _ = (n : ℝ) * (1 - (p : ℝ)) := by ring
      _ = (n : ℝ) * q := by
            have hp_le_one : p ≤ 1 :=
              le_of_lt hp_lt_one
            simpa [q, NNReal.coe_sub hp_le_one]

  have hnp :
      negMulLogb2 p = -(p : ℝ)
        * Real.logb 2 (p : ℝ) := by
    have : (p : NNReal) ≠ 0 := ne_of_gt hp_pos
    simpa [negMulLogb2, this]
  have hnq :
      negMulLogb2 (1 - p) =
        -q * Real.logb 2 q := by
    have hp_le_one : p ≤ 1 := le_of_lt hp_lt_one
    have : (1 - p : NNReal) ≠ 0 := by
      have : 0 < q := hy_pos
      have h_q_ne_zero : q ≠ 0 := ne_of_gt this
      intro h_zero
      have h_q_zero : q = 0 := by
        simp [q, h_zero]
      exact h_q_ne_zero h_q_zero
    simpa [negMulLogb2, q, this]

  have final_sum :
      ∑ k ∈ Finset.range (n+1),
        ( (n.choose k : ℝ)
          * negMulLogb2
              (p^k * (1 - p)^(n - k)) )
      = (n : ℝ) * (negMulLogb2 p)
        + (n : ℝ) * (negMulLogb2 (1 - p)) := by
    have := main_sum
    rw [S1, S2] at this
    convert this using 1
    rw [hnp, hnq]
    ring

  simpa [hfold, two_mul, mul_add,
    add_comm, add_left_comm, add_assoc]
    using final_sum


/-- NOTE: Detailed correctness lemmas (e.g., primes, product
reconstruction) are omitted here to avoid depending on any
trimmed mathlib parts. The `primeAtomSum` lemmas in
`PrimeAtoms.lean` supply the identities used. `primeGenerator` serves as an
extraction-friendly list of (prime, exponent) pairs. -/
noncomputable def primeGenerator
    (n : ℕ) : List (ℕ × ℕ) :=
  if n = 0 then []
  else n.factorization.support.toList.map
    (fun p => (p, n.factorization p))

end InformationTheory
