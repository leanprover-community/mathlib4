/-
Copyright (c) 2024 Jana Göken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artur Szafarczyk, Suraj Krishna M S, Jean-Baptiste Stiegler, Isabelle Dubois,
Tomáš Jakl, Lorenzo Zanichelli, Alina Yan, Emilie Uthaiwat, Jana Göken,
Filippo A. E. Nuccio
-/
import Mathlib.Data.Real.OfDigits
import Mathlib.Data.Stream.Init
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Ternary Cantor Set

This file defines the Cantor ternary set and proves a few properties.

## Main Definitions

* `preCantorSet n`: The order `n` pre-Cantor set, defined inductively as the union of the images
  under the functions `(· / 3)` and `((2 + ·) / 3)`, with `preCantorSet 0 := Set.Icc 0 1`, i.e.
  `preCantorSet 0` is the unit interval [0,1].
* `cantorSet`: The ternary Cantor set, defined as the intersection of all pre-Cantor sets.
* `cantorToTernary`: given a number `x` in the Cantor set, returns its ternary representation
  `(d₀, d₁, ...)` consisting only of digits `0` and `2`, such that `x = 0.d₀d₁...`
  (see `ofDigits_cantorToTernary`).
* `zero_two_sequence_ofDigits_mem_cantorSet`: any such sequence corresponds to a number
  in the Cantor set.
* `zero_two_sequence_ofDigits_unique`: such a representation is unique.
-/

/-- The order `n` pre-Cantor set, defined starting from `[0, 1]` and successively removing the
    middle third of each interval. Formally, the order `n + 1` pre-Cantor set is the
    union of the images under the functions `(· / 3)` and `((2 + ·) / 3)` of `preCantorSet n`.
-/
def preCantorSet : ℕ → Set ℝ
  | 0 => Set.Icc 0 1
  | n + 1 => (· / 3) '' preCantorSet n ∪ (fun x ↦ (2 + x) / 3) '' preCantorSet n

@[simp] lemma preCantorSet_zero : preCantorSet 0 = Set.Icc 0 1 := rfl
@[simp] lemma preCantorSet_succ (n : ℕ) :
    preCantorSet (n + 1) = (· / 3) '' preCantorSet n ∪ (fun x ↦ (2 + x) / 3) '' preCantorSet n :=
  rfl

/-- The Cantor set is the subset of the unit interval obtained as the intersection of all
    pre-Cantor sets. This means that the Cantor set is obtained by iteratively removing the
    open middle third of each subinterval, starting from the unit interval `[0, 1]`.
-/
def cantorSet : Set ℝ := ⋂ n, preCantorSet n


/-!
## Simple Properties
-/

lemma quarters_mem_preCantorSet (n : ℕ) : 1/4 ∈ preCantorSet n ∧ 3/4 ∈ preCantorSet n := by
  induction n with
  | zero =>
    simp only [preCantorSet_zero, inv_nonneg]
    refine ⟨⟨ ?_, ?_⟩, ?_, ?_⟩ <;> norm_num
  | succ n ih =>
    apply And.intro
    · -- goal: 1 / 4 ∈ preCantorSet (n + 1)
      -- follows by the inductive hyphothesis, since 3 / 4 ∈ preCantorSet n
      exact Or.inl ⟨3 / 4, ih.2, by norm_num⟩
    · -- goal: 3 / 4 ∈ preCantorSet (n + 1)
      -- follows by the inductive hyphothesis, since 1 / 4 ∈ preCantorSet n
      exact Or.inr ⟨1 / 4, ih.1, by norm_num⟩

lemma quarter_mem_preCantorSet (n : ℕ) : 1/4 ∈ preCantorSet n := (quarters_mem_preCantorSet n).1

theorem quarter_mem_cantorSet : 1/4 ∈ cantorSet :=
  Set.mem_iInter.mpr quarter_mem_preCantorSet

lemma zero_mem_preCantorSet (n : ℕ) : 0 ∈ preCantorSet n := by
  induction n with
  | zero =>
    simp [preCantorSet]
  | succ n ih =>
    exact Or.inl ⟨0, ih, by simp only [zero_div]⟩

theorem zero_mem_cantorSet : 0 ∈ cantorSet := by simp [cantorSet, zero_mem_preCantorSet]

theorem preCantorSet_antitone : Antitone preCantorSet := by
  apply antitone_nat_of_succ_le
  intro m
  simp only [Set.le_eq_subset, preCantorSet_succ, Set.union_subset_iff]
  induction m with
  | zero =>
    simp only [preCantorSet_zero]
    constructor <;> intro x <;> simp only [Set.mem_image, Set.mem_Icc, forall_exists_index,
      and_imp] <;> intro y _ _ _ <;> constructor <;> linarith
  | succ m ih =>
    simp only [preCantorSet_succ, Set.union_subset_iff, Set.image_union]
    constructor
    · constructor <;> apply Set.subset_union_of_subset_left
      exacts [Set.image_mono ih.left, Set.image_mono ih.right]
    · constructor <;> apply Set.subset_union_of_subset_right
      exacts [Set.image_mono ih.left, Set.image_mono ih.right]

lemma preCantorSet_subset_unitInterval {n : ℕ} : preCantorSet n ⊆ Set.Icc 0 1 := by
  rw [← preCantorSet_zero]
  exact preCantorSet_antitone (by simp)

/-- The ternary Cantor set is a subset of [0,1]. -/
lemma cantorSet_subset_unitInterval : cantorSet ⊆ Set.Icc 0 1 :=
  Set.iInter_subset _ 0

/-- The ternary Cantor set satisfies the equation `C = C / 3 ∪ (2 / 3 + C / 3)`. -/
theorem cantorSet_eq_union_halves :
    cantorSet = (· / 3) '' cantorSet ∪ (fun x ↦ (2 + x) / 3) '' cantorSet := by
  simp only [cantorSet]
  rw [Set.image_iInter, Set.image_iInter]
  rotate_left
  · exact (mulRight_bijective₀ 3⁻¹ (by norm_num)).comp (AddGroup.addLeft_bijective 2)
  · exact mulRight_bijective₀ 3⁻¹ (by norm_num)
  rw [← Set.iInter_union_of_antitone
    (by exact Set.monotone_image.comp_antitone preCantorSet_antitone)
    (by exact Set.monotone_image.comp_antitone preCantorSet_antitone)]
  change ⋂ n, preCantorSet n = ⋂ n, preCantorSet (n + 1)
  exact (preCantorSet_antitone.iInter_nat_add _).symm

/-- The preCantor sets are closed. -/
lemma isClosed_preCantorSet (n : ℕ) : IsClosed (preCantorSet n) := by
  let f := Homeomorph.mulLeft₀ (1 / 3 : ℝ) (by norm_num)
  let g := (Homeomorph.addLeft (2 : ℝ)).trans f
  induction n with
  | zero => exact isClosed_Icc
  | succ n ih =>
    refine IsClosed.union ?_ ?_
    · simpa [f, div_eq_inv_mul] using f.isClosedEmbedding.isClosed_iff_image_isClosed.mp ih
    · simpa [g, f, div_eq_inv_mul] using g.isClosedEmbedding.isClosed_iff_image_isClosed.mp ih

/-- The ternary Cantor set is closed. -/
lemma isClosed_cantorSet : IsClosed cantorSet :=
  isClosed_iInter isClosed_preCantorSet

/-- The ternary Cantor set is compact. -/
lemma isCompact_cantorSet : IsCompact cantorSet :=
  isCompact_Icc.of_isClosed_subset isClosed_cantorSet cantorSet_subset_unitInterval

/-!
## The Cantor set as the set of 0–2 numbers in the ternary system.
-/

/-- If `x = 0.d₀d₁...` in base-3 (ternary), and none of the digits `dᵢ` is `1`,
then `x` belongs to the Cantor set. -/
theorem zero_two_sequence_ofDigits_mem_cantorSet {a : ℕ → Fin 3}
    (h : ∀ n, a n ≠ 1) : ofDigits a ∈ cantorSet := by
  simp only [cantorSet, Set.mem_iInter]
  intro i
  induction i generalizing a with
  | zero =>
    simp only [preCantorSet_zero, Set.mem_Icc]
    exact ⟨ofDigits_nonneg, ofDigits_le_one⟩
  | succ i ih =>
    simp only [preCantorSet, Set.mem_union, Set.mem_image, ← exists_or]
    use ofDigits (fun i ↦ a (i + 1))
    have : (ofDigits fun i ↦ a (i + 1)) ∈ preCantorSet i := ih (by solve_by_elim)
    simp only [this, ofDigits_eq_partial_sum_add_ofDigits a 1, Finset.range_one, ofDigitsTerm,
      Nat.cast_ofNat, Finset.sum_singleton, zero_add, pow_one, true_and]
    field_simp
    norm_cast
    specialize h 0
    generalize a 0 = x at h
    fin_cases x <;> simp at ⊢ h

/-- If two base-3 representations using only digits `0` and `2` define the same number,
then the sequences must be equal.
This uniqueness fails for general base-3 representations (e.g. `0.1000... = 0.0222...`). -/
theorem zero_two_sequence_ofDigits_unique {a b : ℕ → Fin 3}
    (ha : ∀ n, a n ≠ 1)
    (hb : ∀ n, b n ≠ 1)
    (h : ofDigits a = ofDigits b) :
    a = b := by
  by_contra! h
  rw [Function.ne_iff] at h
  let n0 := Nat.find h
  have h1 : ∀ n < n0, a n = b n := by
    intro n hn
    simpa using Nat.find_min h hn
  have h2 : a n0 ≠ b n0 := by
    simpa using Nat.find_spec h
  generalize n0 = n1 at h1 h2
  clear h n0
  wlog h3 : a n1 = 0 ∧ b n1 = 2 generalizing a b
  · replace h3 : a n1 = 2 ∧ b n1 = 0 := by
      specialize ha n1
      specialize hb n1
      generalize a n1 = u at *
      generalize b n1 = v at *
      fin_cases u <;> fin_cases v <;> simp at ha hb h2 h3 ⊢
    exact this hb ha h.symm (by intro n hn; symm; exact h1 n hn) h2.symm (by rwa [and_comm])
  obtain ⟨h3, h4⟩ := h3
  clear h2
  have : ∑ x ∈ Finset.range n1, ofDigitsTerm a x = ∑ x ∈ Finset.range n1, ofDigitsTerm b x := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [ofDigitsTerm]
    congr
    rw [h1]
    simpa using hi
  rw [ofDigits_eq_partial_sum_add_ofDigits a (n1 + 1),
    ofDigits_eq_partial_sum_add_ofDigits b (n1 + 1), Finset.sum_range_succ,
    Finset.sum_range_succ, this] at h
  replace h : ofDigitsTerm a n1 + (3⁻¹ ^ n1 * ofDigits fun i ↦ a (1 + n1 + i)) * (1 / 3) =
      (3⁻¹ ^ n1 * ofDigits fun i ↦ b (1 + n1 + i)) * (1 / 3) + ofDigitsTerm b n1 := by
    ring_nf at h
    linarith
  simp [ofDigitsTerm, h3, h4, pow_succ] at h
  replace h : (ofDigits fun i ↦ a (1 + n1 + i)) * 3⁻¹ =
      (ofDigits fun i ↦ b (1 + n1 + i)) * 3⁻¹ + 2 * 3⁻¹ := by
    rw [← mul_right_inj' (show ((3 : ℝ) ^ n1)⁻¹ ≠ 0 by positivity)]
    linarith
  linarith [ofDigits_nonneg (digits := fun i ↦ b (1 + n1 + i)),
    ofDigits_le_one (digits := fun i ↦ a (1 + n1 + i))]

/-- Given `x ∈ [0, 1/3] ∪ [2/3, 1]` (i.e. a level of the Cantor set),
this function rescales the interval containing `x` back to `[0, 1]`.
Used to iteratively extract the ternary representation of `x`. -/
noncomputable def cantorStep (x : ℝ) : ℝ :=
  if x ∈ Set.Icc 0 (1/3) then
    3 * x
  else
    3 * x - 2

theorem cantorStep_mem_cantorSet {x : ℝ} (hx : x ∈ cantorSet) : cantorStep x ∈ cantorSet := by
  simp only [cantorStep]
  rw [cantorSet_eq_union_halves] at hx
  simp at hx
  split_ifs with h
  · rcases hx with ⟨y, hy, hx⟩ | ⟨y, hy, hx⟩
    · rw [← hx]
      ring_nf
      exact hy
    · rw [← hx] at h
      apply cantorSet_subset_unitInterval at hy
      simp at h hy
      linarith
  · rcases hx with ⟨y, hy, hx⟩ | ⟨y, hy, hx⟩
    · rw [← hx] at h
      apply cantorSet_subset_unitInterval at hy
      absurd h
      simp only [one_div, Set.mem_Icc, not_and] at hy ⊢
      constructor <;> linarith
    · rw [← hx]
      ring_nf
      exact hy

/-- The infinite sequence obtained by repeatedly applying `cantorStep` to `x`. -/
noncomputable def cantorSequence (x : ℝ) : Stream' ℝ :=
  Stream'.iterate cantorStep x

theorem cantorSequence_mem_cantorSet {x : ℝ} (hx : x ∈ cantorSet) {n : ℕ} :
    (cantorSequence x).get n ∈ cantorSet := by
  induction n with
  | zero => simpa [cantorSequence]
  | succ n ih =>
    simp [cantorSequence, Stream'.get_succ_iterate'] at ih ⊢
    exact cantorStep_mem_cantorSet ih

/-- Points of the Cantor set correspond to infinite paths in the full binary tree.
at each level `n`, the set `preCantorSet (n + 1)` splits each interval in
`preCantorSet n` into two parts.
Given `x ∈ cantorSet`, the point `x` lies in one of the intervals of `preCantorSet n`.
This function tracks which of the two intervals in `preCantorSet (n + 1)`
contains `x` at each step, producing the corresponding path as a stream of booleans. -/
noncomputable def cantorToBinary (x : ℝ) : Stream' Bool :=
  (cantorSequence x).map fun x ↦
    if x ∈ Set.Icc 0 (1/3) then
      false
    else
      true

/-- Given `x` in the Cantor set, return its ternary representation `(d₀, d₁, …)`
using only digits `0` and `2`, such that `x = 0.d₀d₁...` in base-3. -/
noncomputable def cantorToTernary (x : ℝ) : Stream' (Fin 3) :=
  (cantorToBinary x).map (fun b ↦ cond b 2 0)

theorem cantorToTernary_ne_one {x : ℝ} {n : ℕ} : (cantorToTernary x).get n ≠ 1 := by
  simp only [cantorToTernary]
  intro h
  simp at h
  generalize (cantorToBinary x).get n = b at h
  cases b <;> simp at h

theorem partial_diff_eq_cantorSequence {x : ℝ} {n : ℕ} :
    (x - ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToTernary x).get i) * 3^n
      = (cantorSequence x).get n := by
  induction n with
  | zero =>
    simp [cantorSequence]
  | succ n ih =>
    calc
      _ = 3 * (((x - ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToTernary x).get i) * 3 ^ n) -
          3^n * ofDigitsTerm (cantorToTernary x).get n) := by
        rw [pow_succ, Finset.sum_range_succ]
        ring
      _ = 3 * ((cantorSequence x).get n - 3^n * ofDigitsTerm (cantorToTernary x).get n) := by
        rw [ih]
      _ = _ := by
        simp only [cantorSequence]
        conv => rhs; simp [Stream'.get_succ_iterate']
        simp only [cantorToTernary, cantorToBinary, cantorSequence, ofDigitsTerm, Stream'.get_map]
        set y := (Stream'.iterate cantorStep x).get n
        split_ifs with h_if <;> simp only [cantorStep, h_if] <;> simp
        rw [pow_succ, mul_inv]
        set a := (3 : ℝ) ^ n
        ring_nf
        rw [mul_inv_cancel₀ (by simp [a])]
        ring

theorem ofDigits_cantorToTernary_partial_sum_le {x : ℝ} (hx : x ∈ cantorSet) {n : ℕ} :
    ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToTernary x) i ≤ x := by
  have := partial_diff_eq_cantorSequence (x := x) (n := n)
  have h_mem := cantorSequence_mem_cantorSet hx (n := n)
  rw [← this] at h_mem
  apply cantorSet_subset_unitInterval at h_mem
  simp only [Set.mem_Icc] at h_mem
  simpa using h_mem.left

theorem ofDigits_cantorToTernary_partial_sum_ge {x : ℝ} (hx : x ∈ cantorSet) {n : ℕ} :
    x - (3⁻¹ : ℝ)^n ≤ ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToTernary x) i := by
  have := partial_diff_eq_cantorSequence (x := x) (n := n)
  have h_mem := cantorSequence_mem_cantorSet hx (n := n)
  rw [← this] at h_mem
  apply cantorSet_subset_unitInterval at h_mem
  simp only [Set.mem_Icc] at h_mem
  apply And.right at h_mem
  rw [← mul_le_mul_right (show 0 < (3 : ℝ)^n by positivity), sub_mul, inv_pow,
    inv_mul_cancel₀ (by simp)]
  linarith!

theorem ofDigits_cantorToTernary {x : ℝ} (hx : x ∈ cantorSet) :
    ofDigits (cantorToTernary x).get = x := by
  simp [ofDigits]
  rw [HasSum.tsum_eq]
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  swap
  · conv => arg 1; ext i; simp; rw [abs_of_nonneg (by simp [ofDigitsTerm])]
    exact ofDigitsTerm_Summable
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n ↦ x - (3⁻¹ : ℝ)^n) (h := fun _ ↦ x)
  · rw [← tendsto_sub_nhds_zero_iff]
    simp only [sub_sub_cancel_left]
    rw [show 0 = -(0 : ℝ) by simp]
    apply Filter.Tendsto.neg
    apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    rw [abs_lt]
    constructor <;> norm_num
  · exact tendsto_const_nhds
  · intro
    exact ofDigits_cantorToTernary_partial_sum_ge hx
  · intro
    exact ofDigits_cantorToTernary_partial_sum_le hx

theorem cantorSet_eq_zero_two_ofDigits :
    cantorSet = {x | ∃ a : ℕ → Fin 3, (∀ i, a i ≠ 1) ∧ ofDigits a = x} := by
  ext x
  refine ⟨fun h ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · use cantorToTernary x
    constructor
    · apply cantorToTernary_ne_one
    · apply ofDigits_cantorToTernary h
  · rw [← ha.2]
    exact zero_two_sequence_ofDigits_mem_cantorSet ha.1
