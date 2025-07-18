/-
Copyright (c) 2024 Jana Göken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artur Szafarczyk, Suraj Krishna M S, Jean-Baptiste Stiegler, Isabelle Dubois,
Tomáš Jakl, Lorenzo Zanichelli, Alina Yan, Emilie Uthaiwat, Jana Göken,
Filippo A. E. Nuccio
-/
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

lemma quarters_mem_preCantorSet (n : ℕ) : 1 / 4 ∈ preCantorSet n ∧ 3 / 4 ∈ preCantorSet n := by
  induction n with
  | zero =>
    simp only [preCantorSet_zero]
    refine ⟨⟨ ?_, ?_⟩, ?_, ?_⟩ <;> norm_num
  | succ n ih =>
    apply And.intro
    · -- goal: 1 / 4 ∈ preCantorSet (n + 1)
      -- follows by the inductive hyphothesis, since 3 / 4 ∈ preCantorSet n
      exact Or.inl ⟨3 / 4, ih.2, by norm_num⟩
    · -- goal: 3 / 4 ∈ preCantorSet (n + 1)
      -- follows by the inductive hyphothesis, since 1 / 4 ∈ preCantorSet n
      exact Or.inr ⟨1 / 4, ih.1, by norm_num⟩

lemma quarter_mem_preCantorSet (n : ℕ) : 1 / 4 ∈ preCantorSet n := (quarters_mem_preCantorSet n).1

theorem quarter_mem_cantorSet : 1 / 4 ∈ cantorSet :=
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
    constructor <;> intro x <;>
      simp only [Set.mem_image, Set.mem_Icc, forall_exists_index, and_imp] <;>
      intro y _ _ _ <;> constructor <;> linarith
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
  simp_rw [← Function.comp_def,
    ← Set.iInter_union_of_antitone
      (Set.monotone_image.comp_antitone preCantorSet_antitone)
      (Set.monotone_image.comp_antitone preCantorSet_antitone),
    Function.comp_def, ← preCantorSet_succ]
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
