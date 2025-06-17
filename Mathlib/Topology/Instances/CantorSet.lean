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

theorem cantorRepr_HasSum_unique {a b : ℕ → Fin 3} {x : ℝ}
    (ha1 : HasSum (ofDigitsTerm a) x)
    (ha2 : ∀ n, a n ≠ 1)
    (hb1 : HasSum (ofDigitsTerm b) x)
    (hb2 : ∀ n, b n ≠ 1) :
    a = b := by
  by_contra! h
  replace h : ∃ n0, a n0 ≠ b n0 := by
    contrapose! h
    exact funext h
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
      specialize ha2 n1
      specialize hb2 n1
      generalize a n1 = u at *
      generalize b n1 = v at *
      fin_cases u <;> fin_cases v <;> simp at ha2 hb2 h2 h3 ⊢
    apply this hb1 hb2 ha1 ha2 (by intro n hn; symm; exact h1 n hn) h2.symm (by rwa [and_comm])
  obtain ⟨h3, h4⟩ := h3
  clear h2
  rw [← hasSum_nat_add_iff' n1] at ha1 hb1
  have : ∑ i ∈ Finset.range n1, ofDigitsTerm b i =
      ∑ i ∈ Finset.range n1, ofDigitsTerm a i := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [ofDigitsTerm]
    congr
    symm
    apply h1
    simpa using hn
  rw [this] at hb1
  generalize x - ∑ i ∈ Finset.range n1, ofDigitsTerm a i = y at ha1 hb1
  have hy_ge := sum_le_hasSum {0} (by intros; exact ofDigitsTerm_nonneg) hb1
  simp [h4, ofDigitsTerm] at hy_ge
  rw [← hasSum_nat_add_iff' 1] at ha1
  simp at ha1
  conv at ha1 => arg 2; simp [ofDigitsTerm, h3]
  let geom (n : ℕ) : ℝ := 2 * (3⁻¹) ^ (n + 1 + n1 + 1)
  have h_geom : HasSum geom ((3⁻¹)^(n1 + 1)) := by
    simp [geom, pow_succ', pow_add]
    ring_nf
    have := hasSum_geometric_of_lt_one (r := (3⁻¹ : ℝ)) (by norm_num) (by norm_num)
    apply HasSum.mul_right (3⁻¹ ^ n1 * (2 / 9)) at this
    convert this using 1
    · ext n
      ring
    · ring
  have := hasSum_mono ha1 h_geom
    (by intro n; simp [geom]; convert ofDigitsTerm_le; norm_num)
  simp at this
  replace this := hy_ge.trans this
  simp at this

theorem cantorRepr_ofDigits_unique {a b : ℕ → Fin 3}
    (ha : ∀ n, a n ≠ 1)
    (hb : ∀ n, b n ≠ 1)
    (h : ofDigits a = ofDigits b) :
    a = b := by
  set x := ofDigits a
  have ha2 : HasSum (ofDigitsTerm a) x := by
    simp [x, ofDigits]
    apply Summable.hasSum
    exact ofDigitsTerm_Summable
  have hb2 : HasSum (ofDigitsTerm b) x := by
    simp [h, ofDigits]
    apply Summable.hasSum
    exact ofDigitsTerm_Summable
  apply cantorRepr_HasSum_unique ha2 ha hb2 hb

theorem cantorRepr_HasSum_mem_cantorSet {a : ℕ → Fin 3} {x : ℝ}
    (h1 : HasSum (ofDigitsTerm a) x)
    (h2 : ∀ n, a n ≠ 1) : x ∈ cantorSet := by
  simp [cantorSet]
  intro i
  induction i generalizing a x with
  | zero =>
    simp
    constructor
    · apply h1.nonneg
      intros
      exact ofDigitsTerm_nonneg
    let geom (n : ℕ) : ℝ := 2 * (3⁻¹)^(n + 1)
    have h_geom : HasSum geom 1 := by
      simp [geom, pow_add]
      ring_nf
      have := hasSum_geometric_of_lt_one (r := (3⁻¹ : ℝ)) (by norm_num) (by norm_num)
      apply HasSum.mul_right (2 / 3) at this
      convert this using 1
      norm_num
    exact hasSum_mono h1 h_geom
      (by intro n; simp [geom]; convert ofDigitsTerm_le; norm_num)
  | succ i ih =>
    simp [preCantorSet]
    have h3 := h2 0
    replace h3 : a 0 = 0 ∨ a 0 = 2 := by
      generalize a 0 = v at *
      fin_cases v <;> simp at h3 ⊢
    rcases h3 with h3 | h3
    · left
      use 3 * x
      simp
      apply ih (a := fun n ↦ a (n + 1)) _ (by solve_by_elim)
      rw [← hasSum_nat_add_iff' 1] at h1
      simp [h3] at h1
      conv at h1 => arg 2; simp [ofDigitsTerm, h3]
      apply HasSum.mul_right 3 at h1
      convert h1 using 1
      · ext n
        simp [ofDigitsTerm]
        ring
      · ring
    · right
      -- copy-paste from above
      use 3 * x - 2
      simp
      apply ih (a := fun n ↦ a (n + 1)) _ (by solve_by_elim)
      rw [← hasSum_nat_add_iff' 1] at h1
      simp [h3] at h1
      conv at h1 => arg 2; simp [ofDigitsTerm, h3]
      apply HasSum.mul_right 3 at h1
      convert h1 using 1
      · ext n
        simp [ofDigitsTerm]
        ring
      · ring

theorem cantorRepr_ofDigits_mem_cantorSet {a : ℕ → Fin 3}
    (h : ∀ n, a n ≠ 1) : ofDigits a ∈ cantorSet := by
  have : HasSum (ofDigitsTerm a) (ofDigits a) := by
    simp [ofDigits]
    apply Summable.hasSum
    exact ofDigitsTerm_Summable
  exact cantorRepr_HasSum_mem_cantorSet this h

/-- Generates the first digit and scales x back to [0, 1]. -/
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

noncomputable def cantorSequence (x : ℝ) : Stream' ℝ :=
  Stream'.iterate cantorStep x

theorem cantorSequence_mem_cantorSet {x : ℝ} (hx : x ∈ cantorSet) {n : ℕ} :
    (cantorSequence x).get n ∈ cantorSet := by
  induction n with
  | zero => simpa [cantorSequence]
  | succ n ih =>
    simp [cantorSequence, Stream'.get_succ_iterate'] at ih ⊢
    exact cantorStep_mem_cantorSet ih

noncomputable def cantorToBinary (x : ℝ) : Stream' Bool :=
  (cantorSequence x).map fun x ↦
    if x ∈ Set.Icc 0 (1/3) then
      false
    else
      true

noncomputable def cantorToDigits (x : ℝ) : Stream' (Fin 3) :=
  (cantorToBinary x).map (fun b ↦ cond b 2 0)

theorem one_notMem_cantorToDigits {x : ℝ} : 1 ∉ cantorToDigits x := by
  simp [cantorToDigits]
  intro h
  apply Stream'.exists_of_mem_map at h
  obtain ⟨b, _, h⟩ := h
  cases b <;> simp at h

theorem cantorToDigits_ne_one {x : ℝ} {n : ℕ} : (cantorToDigits x).get n ≠ 1 := by
  simp only [cantorToDigits]
  intro h
  symm at h
  apply Stream'.mem_of_get_eq at h
  apply one_notMem_cantorToDigits h

theorem partial_diff_eq_cantorSequence {x : ℝ} {n : ℕ} :
    (x - ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToDigits x).get i) * 3^n
      = (cantorSequence x).get n := by
  induction n with
  | zero =>
    simp [cantorSequence]
  | succ n ih =>
    calc
      _ = 3 * (((x - ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToDigits x).get i) * 3 ^ n) -
          3^n * ofDigitsTerm (cantorToDigits x).get n) := by
        rw [pow_succ, Finset.sum_range_succ]
        ring
      _ = 3 * ((cantorSequence x).get n - 3^n * ofDigitsTerm (cantorToDigits x).get n) := by
        rw [ih]
      _ = _ := by
        simp [cantorSequence]
        conv => rhs; simp [Stream'.get_succ_iterate']
        simp only [cantorToDigits, cantorToBinary, cantorSequence, ofDigitsTerm, Stream'.get_map]
        set y := (Stream'.iterate cantorStep x).get n
        split_ifs with h_if <;> simp only [cantorStep, h_if] <;> simp
        rw [pow_succ, mul_inv]
        set a := (3 : ℝ) ^ n
        ring_nf
        rw [mul_inv_cancel₀ (by simp [a])]
        ring

theorem ofDigits_cantorToDigits_partial_sum_le {x : ℝ} (hx : x ∈ cantorSet) {n : ℕ} :
    ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToDigits x) i ≤ x := by
  have := partial_diff_eq_cantorSequence (x := x) (n := n)
  have h_mem := cantorSequence_mem_cantorSet hx (n := n)
  rw [← this] at h_mem
  apply cantorSet_subset_unitInterval at h_mem
  simp only [Set.mem_Icc] at h_mem
  simpa using h_mem.left

theorem ofDigits_cantorToDigits_partial_sum_ge {x : ℝ} (hx : x ∈ cantorSet) {n : ℕ} :
    x - (3⁻¹ : ℝ)^n ≤ ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToDigits x) i := by
  have := partial_diff_eq_cantorSequence (x := x) (n := n)
  have h_mem := cantorSequence_mem_cantorSet hx (n := n)
  rw [← this] at h_mem
  apply cantorSet_subset_unitInterval at h_mem
  simp only [Set.mem_Icc] at h_mem
  apply And.right at h_mem
  rw [← mul_le_mul_right (show 0 < (3 : ℝ)^n by positivity), sub_mul, inv_pow,
    inv_mul_cancel₀ (by simp)]
  linarith!

theorem ofDigits_cantorToDigits {x : ℝ} (hx : x ∈ cantorSet) :
    ofDigits (cantorToDigits x).get = x := by
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
  · intro n
    dsimp only
    exact ofDigits_cantorToDigits_partial_sum_ge hx
  · intro n
    dsimp only
    exact ofDigits_cantorToDigits_partial_sum_le hx

theorem cantorSet_eq_zero_two_set :
    cantorSet = {x | ∃ a : ℕ → Fin 3, (∀ i, a i ≠ 1) ∧ ofDigits a = x} := by
  ext x
  refine ⟨fun h ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · use cantorToDigits x
    constructor
    · apply cantorToDigits_ne_one
    · apply ofDigits_cantorToDigits h
  · rw [← ha.2]
    exact cantorRepr_ofDigits_mem_cantorSet ha.1
