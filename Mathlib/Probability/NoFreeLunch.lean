/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Measure-theoretic No-Free-Lunch via a finite-`k` adversary

This file formalizes the finite-`k` measurable version of the
Devroye–Györfi–Lugosi (DGL) No-Free-Lunch theorem in statistical
learning theory.

Fix a finite input type `K` of cardinality `k` and a deterministic
learning algorithm
`A : (Fin n → K × Bool) → (K → Bool)`. For a labeling
`r : K → Bool` and a sample-index pattern `x : Fin n → K`, the
*induced training sample* is `i ↦ (x i, r (x i))`, and the
*discrete risk* of a predictor `g : K → Bool` against `r` is the
uniform-`K` average of the `0/1` misclassification indicator
`if g j = r j then 0 else 1`.

The DGL adversary argument introduces uniform randomness over `r`
(equivalently, the uniform prior on the `2^k` boolean labelings of `K`)
and produces a lower bound on the average risk that is independent of
the algorithm `A`. The combinatorial heart is a bit-flip involution on
labelings: for any unsampled point `j ∉ Set.range x`, the algorithm's
output on the induced sample is invariant under flipping `r` at `j`,
so flipping pairs labelings into a sum that exactly equals one.

## Main definitions

* `ProbabilityTheory.NoFreeLunch.flipBitAt`: the bit-flip involution at
  one input.
* `ProbabilityTheory.NoFreeLunch.sampleFromLabeling`: the training
  sample `i ↦ (x i, r (x i))` induced by a sample-index pattern and a
  labeling.
* `ProbabilityTheory.NoFreeLunch.misclassIndicator`: the `0/1`
  misclassification indicator at one input.
* `ProbabilityTheory.NoFreeLunch.discreteRiskFinK`: the uniform-`K`
  average of the misclassification indicator over all inputs.
* `ProbabilityTheory.NoFreeLunch.unsampledIndicator`: the `0/1`
  indicator of the event `j ∉ Set.range x`.

## Main results

* `ProbabilityTheory.NoFreeLunch.nfl_finite_k_adversary`: for any
  deterministic algorithm `A` and any fixed sample-index pattern `x`,
  the average risk over the `2^k` uniformly random labelings is at
  least `(1 / 2) · (k - |range x|) / k`.
* `ProbabilityTheory.NoFreeLunch.nfl_finite_k_dgl_average`: averaging
  the previous bound over uniformly random `x : Fin n → K` recovers
  the classical DGL form `(1 / 2) · (1 - 1 / k) ^ n`.

## Implementation notes

The arguments are purely combinatorial over the finite types `K → Bool`
and `Fin n → K`; no measure-theoretic machinery beyond `Fintype` and
`Finset.sum` is needed. The uniform priors on labelings and on
sample-index patterns are encoded as ordinary `Finset.univ` sums divided
by the cardinality of the corresponding finite type, which equals the
integral against the counting probability measure
`ProbabilityTheory.uniformOn Set.univ` whenever a full measure-theoretic
reading is desired.

## References

* L. Devroye, L. Györfi, G. Lugosi, *A Probabilistic Theory of Pattern
  Recognition*, Springer, 1996, Section 7.2 (no-free-lunch adversary).
* S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning:
  From Theory to Algorithms*, Cambridge University Press, 2014,
  Section 5.1 / Theorem 5.1 (binary no-free-lunch).
* F. Bach, *Learning Theory from First Principles*, MIT Press, 2024,
  Section 2.5, p. 38 (the `(1 / 2)(1 - 1 / k)^n` form).
-/

public section

open Finset

namespace ProbabilityTheory.NoFreeLunch

variable {K : Type*} [Fintype K] [DecidableEq K]

/-! ### Bit-flip involution on boolean labelings -/

/-- `flipBitAt j r` is the labeling obtained from `r : K → Bool` by negating its value at `j`. -/
def flipBitAt (j : K) (r : K → Bool) : K → Bool :=
  Function.update r j (!r j)

omit [Fintype K] in
/-- `flipBitAt j` is an involution on `K → Bool`. -/
theorem flipBitAt_involutive (j : K) :
    Function.Involutive (flipBitAt (K := K) j) := by
  intro r
  unfold flipBitAt
  funext k
  by_cases h : k = j
  · subst h
    simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]

omit [Fintype K] in
/-- The value of `flipBitAt j r` at `j` is the negation of `r j`. -/
theorem flipBitAt_apply_self (j : K) (r : K → Bool) :
    flipBitAt j r j = !r j := by
  unfold flipBitAt
  exact Function.update_self ..

omit [Fintype K] in
/-- The value of `flipBitAt j r` at any point other than `j` agrees with `r`. -/
theorem flipBitAt_apply_of_ne {j k : K} (h : k ≠ j) (r : K → Bool) :
    flipBitAt j r k = r k := by
  unfold flipBitAt
  exact Function.update_of_ne h _ _

/-- The permutation form of `flipBitAt j`, used for reindexing sums over `K → Bool`. -/
def flipBitPerm (j : K) : Equiv.Perm (K → Bool) :=
  (flipBitAt_involutive (K := K) j).toPerm (flipBitAt j)

/-! ### Samples induced by labelings -/

/-- The training sample induced by a sample-index pattern `x` and a labeling `r`. -/
def sampleFromLabeling {n : ℕ} (x : Fin n → K) (r : K → Bool) :
    Fin n → K × Bool := fun i => (x i, r (x i))

omit [Fintype K] in
/-- If `j` does not appear in the image of `x`, flipping the labeling at `j` leaves the induced
sample unchanged. -/
theorem sampleFromLabeling_flipBitAt_of_notMem
    {n : ℕ} (x : Fin n → K) (r : K → Bool) {j : K}
    (hj : ∀ i : Fin n, x i ≠ j) :
    sampleFromLabeling x (flipBitAt j r) = sampleFromLabeling x r := by
  funext i
  unfold sampleFromLabeling
  congr 1
  exact flipBitAt_apply_of_ne (hj i) r

/-! ### Misclassification indicators and discrete risk -/

/-- The `0/1` misclassification indicator at input `j` for predictor `g` against labeling `r`. -/
def misclassIndicator (g : K → Bool) (r : K → Bool) (j : K) : ℝ :=
  if g j = r j then 0 else 1

omit [Fintype K] [DecidableEq K] in
/-- The misclassification indicator is nonnegative. -/
theorem misclassIndicator_nonneg (g r : K → Bool) (j : K) :
    0 ≤ misclassIndicator g r j := by
  unfold misclassIndicator
  split_ifs <;> norm_num

omit [Fintype K] in
/-- For any predictor `g` and any labeling `r`, the misclassification indicators of `r` and of
its bit-flip `flipBitAt j r` at `j` sum to one. -/
theorem misclassIndicator_add_flipped (g : K → Bool) (r : K → Bool)
    (j : K) :
    misclassIndicator g r j +
      misclassIndicator g (flipBitAt j r) j = 1 := by
  unfold misclassIndicator
  rw [flipBitAt_apply_self]
  cases g j <;> cases r j <;> simp

/-- Averaging the misclassification indicator at an unsampled point over the `2^k` uniformly
random labelings gives exactly `2^k / 2`. -/
theorem average_misclassIndicator_unsampled
    {n : ℕ} (A : (Fin n → K × Bool) → (K → Bool))
    (x : Fin n → K) {j : K} (hj : ∀ i : Fin n, x i ≠ j) :
    (∑ r : K → Bool,
        misclassIndicator (A (sampleFromLabeling x r)) r j) =
      (2 ^ Fintype.card K) / 2 := by
  classical
  set f : (K → Bool) → ℝ := fun r =>
    misclassIndicator (A (sampleFromLabeling x r)) r j with hf
  have hperm :
      (∑ r : K → Bool, f r) = ∑ r : K → Bool, f (flipBitAt j r) := by
    have := Equiv.sum_comp (flipBitPerm (K := K) j) f
    simpa [flipBitPerm,
      Function.Involutive.coe_toPerm (flipBitAt_involutive j)]
      using this.symm
  have hdouble :
      ((∑ r : K → Bool, f r) + ∑ r : K → Bool, f r) =
        ∑ r : K → Bool, (f r + f (flipBitAt j r)) := by
    rw [Finset.sum_add_distrib, ← hperm]
  have hpair : ∀ r : K → Bool, f r + f (flipBitAt j r) = 1 := by
    intro r
    have hsample :
        A (sampleFromLabeling x (flipBitAt j r)) =
          A (sampleFromLabeling x r) := by
      rw [sampleFromLabeling_flipBitAt_of_notMem x r hj]
    change misclassIndicator (A (sampleFromLabeling x r)) r j +
        misclassIndicator (A (sampleFromLabeling x (flipBitAt j r)))
          (flipBitAt j r) j = 1
    rw [hsample]
    exact misclassIndicator_add_flipped _ r j
  have hsum_one :
      (∑ _r : K → Bool, (1 : ℝ)) = (2 ^ Fintype.card K : ℕ) := by
    rw [Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_bool, mul_one]
  have h2 : ((∑ r : K → Bool, f r) + ∑ r : K → Bool, f r) =
      (2 ^ Fintype.card K : ℕ) := by
    rw [hdouble]
    have := Finset.sum_congr rfl
      (fun r (_ : r ∈ (Finset.univ : Finset (K → Bool))) => hpair r)
    rw [this, hsum_one]
  have h3 : (2 : ℝ) * (∑ r : K → Bool, f r) = (2 ^ Fintype.card K : ℕ) := by
    linarith [h2]
  have hpush :
      (∑ r : K → Bool, f r) = ((2 ^ Fintype.card K : ℕ) : ℝ) / 2 := by
    field_simp
    linarith [h3]
  change (∑ r : K → Bool, f r) = (2 ^ Fintype.card K) / 2
  rw [hpush]
  push_cast
  ring

/-- The discrete risk of a predictor `g` against labeling `r`, namely the uniform-`K` average
of the misclassification indicator. -/
noncomputable def discreteRiskFinK (g : K → Bool) (r : K → Bool) : ℝ :=
  (∑ j : K, misclassIndicator g r j) / (Fintype.card K : ℝ)

omit [DecidableEq K] in
/-- The discrete risk is nonnegative. -/
theorem discreteRiskFinK_nonneg (g r : K → Bool) :
    0 ≤ discreteRiskFinK g r := by
  unfold discreteRiskFinK
  apply div_nonneg
  · exact Finset.sum_nonneg fun j _ => misclassIndicator_nonneg _ _ _
  · exact Nat.cast_nonneg _

/-! ### Finite-`k` adversary, average-over-`r` form -/

/-- **No-Free-Lunch, finite-`k` adversary form.** For any deterministic learning algorithm
`A : (Fin n → K × Bool) → (K → Bool)` and any sample-index pattern `x : Fin n → K`, the
average discrete risk over the `2^k` uniformly random labelings `r : K → Bool` satisfies

  `(1 / 2) * (k - |range x|) / k ≤ Avg_r R(A (sample x r), r)`.

In particular, when `n ≤ k` and `x` is injective, the bound becomes `(1 / 2) * (1 - n / k)`. -/
theorem nfl_finite_k_adversary
    [Nonempty K] {n : ℕ}
    (A : (Fin n → K × Bool) → (K → Bool)) (x : Fin n → K) :
    let k := Fintype.card K
    let s := (Finset.univ.image x).card
    (1 : ℝ) / 2 * ((k : ℝ) - s) / k ≤
      (∑ r : K → Bool, discreteRiskFinK (A (sampleFromLabeling x r)) r)
        / (2 ^ k : ℝ) := by
  classical
  set k : ℕ := Fintype.card K with hk_def
  set s : ℕ := (Finset.univ.image x).card with hs_def
  have hk_pos : 0 < k := Fintype.card_pos
  have hk_pos_real : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hs_le_k : s ≤ k := by
    have : (Finset.univ.image x).card ≤ (Finset.univ : Finset K).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simpa [hk_def, Finset.card_univ] using this
  have hexpand :
      (∑ r : K → Bool, discreteRiskFinK (A (sampleFromLabeling x r)) r)
        = (∑ r : K → Bool, (∑ j : K,
            misclassIndicator (A (sampleFromLabeling x r)) r j))
            / (k : ℝ) := by
    unfold discreteRiskFinK
    rw [← Finset.sum_div]
  rw [hexpand, Finset.sum_comm]
  set imx : Finset K := Finset.univ.image x with himx_def
  set notImx : Finset K := Finset.univ \ imx with hnotImx_def
  have himx_sub : imx ⊆ (Finset.univ : Finset K) := Finset.subset_univ _
  have hsplit :
      (∑ j : K, ∑ r : K → Bool,
          misclassIndicator (A (sampleFromLabeling x r)) r j)
        = (∑ j ∈ imx, ∑ r : K → Bool,
            misclassIndicator (A (sampleFromLabeling x r)) r j)
          + (∑ j ∈ notImx, ∑ r : K → Bool,
              misclassIndicator (A (sampleFromLabeling x r)) r j) := by
    rw [hnotImx_def, ← Finset.sum_sdiff himx_sub, add_comm]
  rw [hsplit]
  have hnot_eq : ∀ j ∈ notImx, (∑ r : K → Bool,
      misclassIndicator (A (sampleFromLabeling x r)) r j)
        = ((2 ^ k : ℕ) : ℝ) / 2 := by
    intro j hj
    have hj_notMem : j ∉ imx := by
      rw [hnotImx_def, Finset.mem_sdiff] at hj
      exact hj.2
    have hj_unsampled : ∀ i : Fin n, x i ≠ j := by
      intro i heq
      apply hj_notMem
      rw [himx_def]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩
    have := average_misclassIndicator_unsampled A x hj_unsampled
    rw [this]
    push_cast
    ring
  have hnot_sum :
      (∑ j ∈ notImx, ∑ r : K → Bool,
          misclassIndicator (A (sampleFromLabeling x r)) r j)
        = notImx.card * (((2 ^ k : ℕ) : ℝ) / 2) := by
    rw [Finset.sum_congr rfl hnot_eq, Finset.sum_const, nsmul_eq_mul]
  have him_nonneg : 0 ≤ (∑ j ∈ imx, ∑ r : K → Bool,
      misclassIndicator (A (sampleFromLabeling x r)) r j) := by
    apply Finset.sum_nonneg
    intros j _
    apply Finset.sum_nonneg
    intros r _
    exact misclassIndicator_nonneg _ _ _
  rw [hnot_sum]
  have hcard_notImx : notImx.card = k - s := by
    rw [hnotImx_def, Finset.card_sdiff_of_subset himx_sub]
    simp [Finset.card_univ, hk_def, himx_def, hs_def]
  rw [hcard_notImx]
  have h2k_pos : (0 : ℝ) < (2 ^ k : ℝ) := by positivity
  have key :
      (1 : ℝ) / 2 * ((k : ℝ) - s) / k * (k * (2 ^ k : ℝ)) ≤
        ((∑ j ∈ imx, ∑ r : K → Bool,
            misclassIndicator (A (sampleFromLabeling x r)) r j)
          + ((k - s : ℕ) : ℝ) * (((2 ^ k : ℕ) : ℝ) / 2)) := by
    have hk_minus_s_real : ((k - s : ℕ) : ℝ) = ((k : ℝ) - (s : ℝ)) :=
      Nat.cast_sub hs_le_k
    rw [hk_minus_s_real]
    have hcast : ((2 ^ k : ℕ) : ℝ) = (2 ^ k : ℝ) := by push_cast; rfl
    rw [hcast]
    have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos_real
    have hlhs : (1 : ℝ) / 2 * ((k : ℝ) - s) / k * (k * (2 ^ k : ℝ))
        = ((k : ℝ) - s) * ((2 ^ k : ℝ) / 2) := by
      field_simp
    rw [hlhs]
    linarith [him_nonneg]
  have hmulpos : (0 : ℝ) < k * (2 ^ k : ℝ) := mul_pos hk_pos_real h2k_pos
  change (1 : ℝ) / 2 * ((k : ℝ) - s) / k ≤
      ((∑ j ∈ imx, ∑ r : K → Bool,
            misclassIndicator (A (sampleFromLabeling x r)) r j)
          + ((k - s : ℕ) : ℝ) * (((2 ^ k : ℕ) : ℝ) / 2))
            / (k : ℝ) / (2 ^ k : ℝ)
  rw [div_div, le_div_iff₀ hmulpos]
  exact key

/-! ### Averaging over uniformly random sample-index patterns -/

/-- The `0/1` indicator of the event "input `j` does not appear in the sample-index pattern `x`". -/
def unsampledIndicator {n : ℕ} (x : Fin n → K) (j : K) : ℝ :=
  if (∀ i : Fin n, x i ≠ j) then 1 else 0

omit [Fintype K] in
/-- The unsampled indicator factors as a product over coordinates: this is the
independence-across-coordinates step underlying the `(1 - 1 / k)^n` slack. -/
theorem unsampledIndicator_eq_prod {n : ℕ} (x : Fin n → K) (j : K) :
    unsampledIndicator x j =
      ∏ i : Fin n, (if x i ≠ j then (1 : ℝ) else 0) := by
  classical
  unfold unsampledIndicator
  by_cases h : ∀ i : Fin n, x i ≠ j
  · rw [if_pos h]
    refine (Finset.prod_eq_one (fun i _ => ?_)).symm
    rw [if_pos (h i)]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    rw [if_neg (by simpa using hi)]

/-- Summing the indicator `if a ≠ j then 1 else 0` over `a : K` equals `k - 1`. -/
theorem sum_indicator_ne [Nonempty K] {j : K} :
    (∑ a : K, (if a ≠ j then (1 : ℝ) else 0)) =
      ((Fintype.card K : ℝ) - 1) := by
  classical
  rw [Finset.sum_boole]
  have hfilter : {a ∈ (Finset.univ : Finset K) | a ≠ j}
      = (Finset.univ : Finset K) \ {j} := by
    ext a
    simp [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton]
  rw [hfilter]
  have hsub : ({j} : Finset K) ⊆ (Finset.univ : Finset K) :=
    fun _ _ => Finset.mem_univ _
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ,
    Finset.card_singleton]
  have hk_ge : 1 ≤ Fintype.card K := Fintype.card_pos
  push_cast [Nat.cast_sub hk_ge]
  rfl

/-- Summing the unsampled indicator over uniformly random `x : Fin n → K` equals `(k - 1)^n`. -/
theorem sum_unsampledIndicator_eq [Nonempty K] {n : ℕ} (j : K) :
    (∑ x : Fin n → K, unsampledIndicator x j) =
      ((Fintype.card K : ℝ) - 1) ^ n := by
  classical
  have hrewrite : (∑ x : Fin n → K, unsampledIndicator x j) =
      ∑ x : Fin n → K, ∏ i : Fin n,
        (if x i ≠ j then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    exact unsampledIndicator_eq_prod x j
  rw [hrewrite]
  have hpow := (Finset.sum_pow' (Finset.univ : Finset K)
      (fun a : K => (if a ≠ j then (1 : ℝ) else 0)) n).symm
  rw [Fintype.piFinset_univ] at hpow
  rw [hpow, sum_indicator_ne]

/-- The uniform-`x` probability that `j` is unsampled equals `(1 - 1 / k)^n`. -/
theorem prob_unsampled_in_uniform [Nonempty K] {n : ℕ} (j : K) :
    (∑ x : Fin n → K, unsampledIndicator x j) /
        ((Fintype.card K : ℝ) ^ n)
      = (1 - 1 / (Fintype.card K : ℝ)) ^ n := by
  classical
  have hk_pos : 0 < Fintype.card K := Fintype.card_pos
  have hk_pos_real : (0 : ℝ) < (Fintype.card K : ℝ) := by
    exact_mod_cast hk_pos
  have hk_ne : (Fintype.card K : ℝ) ≠ 0 := ne_of_gt hk_pos_real
  rw [sum_unsampledIndicator_eq, ← div_pow]
  congr 1
  field_simp

/-- Sum over `j : K` of the unsampled indicator at fixed `x` equals `k - |range x|`. -/
theorem sum_unsampledIndicator_eq_complement_image {n : ℕ}
    (x : Fin n → K) :
    (∑ j : K, unsampledIndicator x j) =
      ((Fintype.card K : ℝ) - (Finset.univ.image x).card) := by
  classical
  have hrewrite : ∀ j : K,
      unsampledIndicator x j =
        if j ∉ Finset.univ.image x then (1 : ℝ) else 0 := by
    intro j
    unfold unsampledIndicator
    by_cases h : ∀ i : Fin n, x i ≠ j
    · rw [if_pos h]
      have hj : j ∉ Finset.univ.image x := by
        intro hj
        obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hj
        exact h i heq
      rw [if_pos hj]
    · rw [if_neg h]
      push Not at h
      obtain ⟨i, hi⟩ := h
      have hj : j ∈ Finset.univ.image x :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
      rw [if_neg (not_not_intro hj)]
  rw [Finset.sum_congr rfl (fun j _ => hrewrite j), Finset.sum_boole]
  have hsub : (Finset.univ.image x) ⊆ (Finset.univ : Finset K) :=
    Finset.subset_univ _
  have hfilter_eq :
      {j ∈ (Finset.univ : Finset K) | j ∉ Finset.univ.image x}
        = (Finset.univ : Finset K) \ (Finset.univ.image x) := by
    ext j
    simp [Finset.mem_sdiff, Finset.mem_filter]
  rw [hfilter_eq, Finset.card_sdiff_of_subset hsub, Finset.card_univ]
  have hs_le : (Finset.univ.image x).card ≤ Fintype.card K := by
    have : (Finset.univ.image x).card ≤ (Finset.univ : Finset K).card :=
      Finset.card_le_card hsub
    simpa [Finset.card_univ] using this
  push_cast [Nat.cast_sub hs_le]
  rfl

/-- The aggregate average-over-`x` form of `prob_unsampled_in_uniform`: averaging
`k - |range x|` over `x : Fin n → K` equals `k · (1 - 1 / k)^n`. -/
theorem avg_complement_image [Nonempty K] {n : ℕ} :
    (∑ x : Fin n → K,
        ((Fintype.card K : ℝ) - (Finset.univ.image x).card))
        / ((Fintype.card K : ℝ) ^ n)
      = (Fintype.card K : ℝ) * (1 - 1 / (Fintype.card K : ℝ)) ^ n := by
  classical
  have hk_pos : 0 < Fintype.card K := Fintype.card_pos
  have hk_pos_real : (0 : ℝ) < (Fintype.card K : ℝ) := by
    exact_mod_cast hk_pos
  have hk_pow_pos : (0 : ℝ) < (Fintype.card K : ℝ) ^ n :=
    pow_pos hk_pos_real n
  have hsum_swap : (∑ x : Fin n → K,
      ((Fintype.card K : ℝ) - (Finset.univ.image x).card))
        = ∑ x : Fin n → K, ∑ j : K, unsampledIndicator x j := by
    refine Finset.sum_congr rfl ?_
    intro x _
    exact (sum_unsampledIndicator_eq_complement_image x).symm
  rw [hsum_swap, Finset.sum_comm]
  have hinner : ∀ j : K, (∑ x : Fin n → K, unsampledIndicator x j) =
      ((Fintype.card K : ℝ) - 1) ^ n :=
    fun j => sum_unsampledIndicator_eq j
  rw [Finset.sum_congr rfl (fun j _ => hinner j), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_div_assoc]
  congr 1
  rw [← div_pow]
  congr 1
  field_simp

/-- **No-Free-Lunch, DGL average-over-`x` form.** For any deterministic learning algorithm
`A : (Fin n → K × Bool) → (K → Bool)`, averaging the discrete risk over the `2^k` uniformly
random labelings `r : K → Bool` and the `k^n` uniformly random sample-index patterns
`x : Fin n → K` satisfies the classical DGL bound

  `(1 / 2) * (1 - 1 / k) ^ n ≤ Avg_x Avg_r R(A (sample x r), r)`. -/
theorem nfl_finite_k_dgl_average
    [Nonempty K] {n : ℕ}
    (A : (Fin n → K × Bool) → (K → Bool)) :
    let k := Fintype.card K
    (1 : ℝ) / 2 * (1 - 1 / (k : ℝ)) ^ n ≤
      (∑ x : Fin n → K,
          (∑ r : K → Bool,
              discreteRiskFinK (A (sampleFromLabeling x r)) r)
            / (2 ^ k : ℝ))
        / ((k : ℝ) ^ n) := by
  classical
  set k : ℕ := Fintype.card K with hk_def
  have hk_pos : 0 < k := Fintype.card_pos
  have hk_pos_real : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hk_pow_pos : (0 : ℝ) < (k : ℝ) ^ n := pow_pos hk_pos_real n
  have hpt : ∀ x : Fin n → K,
      (1 : ℝ) / 2 * ((k : ℝ) - (Finset.univ.image x).card) / k ≤
        (∑ r : K → Bool,
            discreteRiskFinK (A (sampleFromLabeling x r)) r)
          / (2 ^ k : ℝ) := by
    intro x
    have := nfl_finite_k_adversary (K := K) A x
    simpa [hk_def] using this
  have hsum_le :
      (∑ x : Fin n → K,
          (1 : ℝ) / 2 * ((k : ℝ) - (Finset.univ.image x).card) / k)
        ≤ ∑ x : Fin n → K,
            (∑ r : K → Bool,
                discreteRiskFinK (A (sampleFromLabeling x r)) r)
              / (2 ^ k : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro x _
    exact hpt x
  have hlhs_sum : (∑ x : Fin n → K,
      (1 : ℝ) / 2 * ((k : ℝ) - (Finset.univ.image x).card) / k)
        = (1 / 2 / k) * (∑ x : Fin n → K,
            ((k : ℝ) - (Finset.univ.image x).card)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x _
    ring
  rw [hlhs_sum] at hsum_le
  have havg : (∑ x : Fin n → K,
      ((k : ℝ) - (Finset.univ.image x).card)) / ((k : ℝ) ^ n)
        = (k : ℝ) * (1 - 1 / (k : ℝ)) ^ n := by
    simpa [hk_def] using avg_complement_image (K := K) (n := n)
  change (1 : ℝ) / 2 * (1 - 1 / (k : ℝ)) ^ n ≤
      (∑ x : Fin n → K,
          (∑ r : K → Bool,
              discreteRiskFinK (A (sampleFromLabeling x r)) r)
            / (2 ^ k : ℝ))
        / ((k : ℝ) ^ n)
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos_real
  have key : (1 / 2 / (k : ℝ)) * (∑ x : Fin n → K,
        ((k : ℝ) - (Finset.univ.image x).card)) / ((k : ℝ) ^ n) ≤
      (∑ x : Fin n → K,
        (∑ r : K → Bool,
            discreteRiskFinK (A (sampleFromLabeling x r)) r)
          / (2 ^ k : ℝ)) / ((k : ℝ) ^ n) :=
    div_le_div_of_nonneg_right hsum_le (le_of_lt hk_pow_pos)
  have hlhs_simp : (1 / 2 / (k : ℝ)) * (∑ x : Fin n → K,
        ((k : ℝ) - (Finset.univ.image x).card)) / ((k : ℝ) ^ n)
      = (1 : ℝ) / 2 * (1 - 1 / (k : ℝ)) ^ n := by
    rw [mul_div_assoc, havg]
    field_simp
  linarith [key, hlhs_simp.symm.le, hlhs_simp.le]

end ProbabilityTheory.NoFreeLunch

end
