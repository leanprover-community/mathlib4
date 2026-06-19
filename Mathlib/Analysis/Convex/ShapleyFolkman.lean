/-
Copyright (c) 2026 Andrey Marennikov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrey Marennikov
-/

module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Shapley-Folkman lemma

This file proves the Shapley-Folkman lemma for finite sums of sets in finite-dimensional
real vector spaces.

The main result is `shapley_folkman`, which states that if a point belongs to a finite
sum of convex hulls, then it can be represented as a sum where all but at most
`finrank ℝ E` terms belong to the original sets.
-/

@[expose] public section

open scoped Pointwise BigOperators
open Set Finset
variable {ι : Type*}
variable {E : Type*}
section SetSums
variable [AddCommMonoid E]
example (A B : Set E) (x y : E) (hx : x ∈ A) (hy : y ∈ B) :
    x + y ∈ A + B := by
  exact ⟨x, hx, y, hy, rfl⟩
example (A B : Set E) (z : E) (hz : z ∈ A + B) :
    ∃ x ∈ A, ∃ y ∈ B, x + y = z := by
  simpa [Set.mem_add] using hz
lemma shapley_folkman_mem_of_choice
    {ι E : Type*}
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E]
    (S : ι → Set E)
    (x : E)
    (y : ι → E)
    (bad : Finset ι)
    (hy_conv : ∀ i ∈ bad, y i ∈ convexHull ℝ (S i))
    (hy_good : ∀ i ∈ (Finset.univ \ bad), y i ∈ S i)
    (hysum : ∑ i ∈ (Finset.univ : Finset ι), y i = x) :
    x ∈
      (∑ i ∈ bad, convexHull ℝ (S i)) +
      (∑ i ∈ (Finset.univ \ bad), S i) := by
  classical
  rw [Set.mem_add]
  refine ⟨
    ∑ i ∈ bad, y i,
    ?_,
    ∑ i ∈ (Finset.univ \ bad), y i,
    ?_,
    ?_
  ⟩
  · simpa using
      Set.finsetSum_mem_finsetSum
        bad
        (fun i => convexHull ℝ (S i))
        y
        hy_conv
  · simpa using
      Set.finsetSum_mem_finsetSum
        (Finset.univ \ bad)
        S
        y
        hy_good
  · have hbad_subset : bad ⊆ (Finset.univ : Finset ι) := by
      intro i hi
      simp
    have hsum_sdiff :
        ∑ i ∈ ((Finset.univ : Finset ι) \ bad), y i =
          (∑ i ∈ (Finset.univ : Finset ι), y i) - ∑ i ∈ bad, y i := by
      simp
    rw [hsum_sdiff]
    rw [hysum]
    simp [sub_eq_add_neg, add_left_comm]
lemma exists_caratheodory_finset
    {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (S : Set E)
    (x : E)
    (hx : x ∈ convexHull ℝ S) :
    ∃ T : Finset E,
      ↑T ⊆ S ∧
      x ∈ convexHull ℝ (T : Set E) ∧
      AffineIndependent ℝ (fun p : T => (p : E)) := by
  classical
  refine ⟨Caratheodory.minCardFinsetOfMemConvexHull hx, ?_, ?_, ?_⟩
  · exact Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  · exact Caratheodory.mem_minCardFinsetOfMemConvexHull hx
  · simpa using Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
lemma mem_of_convex_combo_univ_card_eq_one
    {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    {α : Type*} [Fintype α]
    {S : Set E} {y : E}
    {z : α → E} {w : α → ℝ}
    (hz_mem_S : ∀ a : α, z a ∈ S)
    (hcard : (Finset.univ : Finset α).card = 1)
    (hw_sum : ∑ a, w a = 1)
    (hw_eq : ∑ a, w a • z a = y) :
    y ∈ S := by
  classical
  rcases Finset.card_eq_one.mp hcard with ⟨a, ha⟩
  have huniv_eq : (Finset.univ : Finset α) = {a} := ha
  have hw_sum_single : w a = 1 := by
    simpa [huniv_eq] using hw_sum
  have hw_eq_single : w a • z a = y := by
    simpa [huniv_eq] using hw_eq
  have hy_eq : y = z a := by
    calc
      y = w a • z a := by
        exact hw_eq_single.symm
      _ = (1 : ℝ) • z a := by
        rw [hw_sum_single]
      _ = z a := by
        simp
  rw [hy_eq]
  exact hz_mem_S a
/-- A finite convex-combination representation used in the proof of the
Shapley-Folkman lemma.

For each index `i`, the point `y i` is represented as a positive convex
combination of points `z i a ∈ S i`, and the sum of all `y i` is `x`. -/
structure ShapleyFolkmanRep
    (ι E : Type*) [Fintype ι]
    [AddCommMonoid E] [Module ℝ E]
    (S : ι → Set E) (x : E) where
  /-- The finite index type for the convex combination at index `i`. -/
  α : ι → Type*
  /-- Finiteness of the index type `α i`. -/
  hα : ∀ i : ι, Fintype (α i)
  /-- The chosen summand at index `i`. -/
  y : ι → E
  /-- The points of `S i` used in the convex combination for `y i`. -/
  z : ∀ i : ι, α i → E
  /-- The positive weights of the convex combination for `y i`. -/
  w : ∀ i : ι, α i → ℝ
  /-- Each point `z i a` belongs to `S i`. -/
  hz_mem : ∀ i : ι, ∀ a : α i, z i a ∈ S i
  /-- All weights are positive. -/
  hw_pos : ∀ i : ι, ∀ a : α i, 0 < w i a
  /-- The weights at each index sum to one. -/
  hw_sum :
    ∀ i : ι,
      (@Finset.univ (α i) (hα i)).sum (fun a => w i a) = 1
  /-- The weighted sum at index `i` is `y i`. -/
  hw_eq :
    ∀ i : ι,
      (@Finset.univ (α i) (hα i)).sum (fun a => w i a • z i a) = y i
  /-- The sum of all chosen summands is the target point `x`. -/
  hsum :
    (∑ i ∈ (Finset.univ : Finset ι), y i) = x
/-- The total number of points used in all convex combinations of a
`ShapleyFolkmanRep`. -/
noncomputable def ShapleyFolkmanRep.complexity
    {ι E : Type*} [Fintype ι]
    [AddCommMonoid E] [Module ℝ E]
    {S : ι → Set E} {x : E}
    (R : ShapleyFolkmanRep ι E S x) : ℕ :=
  ∑ i ∈ (Finset.univ : Finset ι),
    (@Finset.univ (R.α i) (R.hα i)).card
/-- The set of indices where the convex combination in a
`ShapleyFolkmanRep` uses a number of points different from one. -/
noncomputable def ShapleyFolkmanRep.nonsingleton
    {ι E : Type*} [Fintype ι]
    [AddCommMonoid E] [Module ℝ E]
    {S : ι → Set E} {x : E}
    (R : ShapleyFolkmanRep ι E S x) : Finset ι := by
  classical
  exact Finset.univ.filter fun i =>
    (@Finset.univ (R.α i) (R.hα i)).card ≠ 1
universe uι uE uα
lemma exists_minimal_shapley_folkman_rep
    {ι : Type uι} {E : Type uE}
    [Fintype ι]
    [AddCommMonoid E] [Module ℝ E]
    {S : ι → Set E} {x : E}
    (hR : ∃ _ : ShapleyFolkmanRep.{uι, uE, uα} ι E S x, True) :
    ∃ Rmin : ShapleyFolkmanRep.{uι, uE, uα} ι E S x,
      ∀ R : ShapleyFolkmanRep.{uι, uE, uα} ι E S x,
        ShapleyFolkmanRep.complexity Rmin ≤
          ShapleyFolkmanRep.complexity R := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ R : ShapleyFolkmanRep.{uι, uE, uα} ι E S x,
      ShapleyFolkmanRep.complexity R = n
  have hP_exists : ∃ n : ℕ, P n := by
    rcases hR with ⟨R, _⟩
    exact ⟨ShapleyFolkmanRep.complexity R, R, rfl⟩
  let nmin : ℕ := Nat.find hP_exists
  have hnmin : P nmin := Nat.find_spec hP_exists
  rcases hnmin with ⟨Rmin, hRmin_complexity⟩
  refine ⟨Rmin, ?_⟩
  intro R
  have hP_R : P (ShapleyFolkmanRep.complexity R) := by
    exact ⟨R, rfl⟩
  have hn_le :
      nmin ≤ ShapleyFolkmanRep.complexity R :=
    Nat.find_min' hP_exists hP_R
  rw [hRmin_complexity]
  exact hn_le
lemma ShapleyFolkmanRep.nonsingleton_card_le_finrank_of_minimal
    {ι : Type uι} {E : Type uE}
    [Fintype ι]
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {S : ι → Set E} {x : E}
    (Rmin : ShapleyFolkmanRep.{uι, uE, uα} ι E S x)
    (hmin :
      ∀ R : ShapleyFolkmanRep.{uι, uE, uα} ι E S x,
        ShapleyFolkmanRep.complexity Rmin ≤
          ShapleyFolkmanRep.complexity R) :
    (ShapleyFolkmanRep.nonsingleton Rmin).card ≤ Module.finrank ℝ E := by
  classical
  let bad : Finset ι := ShapleyFolkmanRep.nonsingleton Rmin
  by_contra hnot
  have hbad_large : Module.finrank ℝ E < bad.card := by
    exact Nat.lt_of_not_ge hnot
  have hbad_pos : 0 < bad.card := by
    exact lt_of_le_of_lt (Nat.zero_le _) hbad_large
  have hbad_nonempty : bad.Nonempty := by
    exact Finset.card_pos.mp hbad_pos
  have hbad_card_ne_one :
      ∀ i ∈ bad,
        (@Finset.univ (Rmin.α i) (Rmin.hα i)).card ≠ 1 := by
    intro i hi
    have hi' :
        i ∈ ShapleyFolkmanRep.nonsingleton Rmin := by
      simpa [bad] using hi
    simpa [ShapleyFolkmanRep.nonsingleton] using hi'
  have hbad_card_pos :
      ∀ i ∈ bad,
        0 < (@Finset.univ (Rmin.α i) (Rmin.hα i)).card := by
    intro i hi
    classical
    by_contra hzero_not
    have hzero :
        (@Finset.univ (Rmin.α i) (Rmin.hα i)).card = 0 := by
      exact Nat.eq_zero_of_not_pos hzero_not
    have huniv_empty :
        (@Finset.univ (Rmin.α i) (Rmin.hα i)) = ∅ := by
      exact Finset.card_eq_zero.mp hzero
    have hsum_zero :
        (@Finset.univ (Rmin.α i) (Rmin.hα i)).sum (fun a => Rmin.w i a) = 0 := by
      simp [huniv_empty]
    have hzero_eq_one : (0 : ℝ) = 1 := by
      rw [← Rmin.hw_sum i]
      exact hsum_zero.symm
    norm_num at hzero_eq_one
  have hbad_card_two :
      ∀ i ∈ bad,
        2 ≤ (@Finset.univ (Rmin.α i) (Rmin.hα i)).card := by
    intro i hi
    have hpos := hbad_card_pos i hi
    have hne_one := hbad_card_ne_one i hi
    omega
  have hbad_two_points :
      ∀ i : bad, ∃ a b : Rmin.α i.1, a ≠ b := by
    intro i
    have hi_bad : i.1 ∈ bad := i.2
    have hcard_two :
        2 ≤ (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).card := by
      exact hbad_card_two i.1 hi_bad
    have hcard_gt_one :
        1 < (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).card := by
      exact Nat.lt_of_succ_le hcard_two
    rcases Finset.one_lt_card.mp hcard_gt_one with ⟨a, ha, b, hb, hab⟩
    exact ⟨a, b, hab⟩
  let aα : ∀ i : bad, Rmin.α i.1 := fun i =>
    Classical.choose (hbad_two_points i)
  let bα : ∀ i : bad, Rmin.α i.1 := fun i =>
    Classical.choose (Classical.choose_spec (hbad_two_points i))
  have habα : ∀ i : bad, aα i ≠ bα i := by
    intro i
    exact Classical.choose_spec (Classical.choose_spec (hbad_two_points i))
  let d : bad → E := fun i =>
    Rmin.z i.1 (aα i) - Rmin.z i.1 (bα i)
  have hnot_linearIndependent : ¬ LinearIndependent ℝ d := by
    intro hd_li
    have hcard_le_finrank :
        Fintype.card bad ≤ Module.finrank ℝ E := by
      exact LinearIndependent.fintype_card_le_finrank hd_li
    have hbad_card_eq : Fintype.card bad = bad.card := by
      simp
    have hbad_card_le_finrank :
        bad.card ≤ Module.finrank ℝ E := by
      simpa [hbad_card_eq] using hcard_le_finrank
    exact not_lt_of_ge hbad_card_le_finrank hbad_large
  have hdep_not_all_zero :
      ¬ ∀ c : bad → ℝ,
          (∑ i : bad, c i • d i = 0) → ∀ i : bad, c i = 0 := by
    intro h
    apply hnot_linearIndependent
    rw [Fintype.linearIndependent_iff]
    exact h
  push Not at hdep_not_all_zero
  rcases hdep_not_all_zero with ⟨c, hc_sum, i₀, hi₀_ne_zero⟩
  have hc_sum_expanded :
      ∑ i : bad,
        c i • (Rmin.z i.1 (aα i) - Rmin.z i.1 (bα i)) = 0 := by
    simpa [d] using hc_sum
  let p : ∀ i : bad, Rmin.α i.1 → ℝ := fun i a =>
    if a = aα i then c i
    else if a = bα i then -c i
    else 0
  have hp_a : ∀ i : bad, p i (aα i) = c i := by
    intro i
    simp [p]
  have hp_b : ∀ i : bad, p i (bα i) = -c i := by
    intro i
    have hb_ne_a : bα i ≠ aα i := by
      exact (habα i).symm
    simp [p, hb_ne_a]
  have hp_other :
      ∀ i : bad, ∀ q : Rmin.α i.1,
        q ≠ aα i → q ≠ bα i → p i q = 0 := by
    intro i q hqa hqb
    simp [p, hqa, hqb]
  have hp_sum_zero :
      ∀ i : bad,
        (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
          (fun q => p i q) = 0 := by
    intro i
    classical
    let U : Finset (Rmin.α i.1) :=
      @Finset.univ (Rmin.α i.1) (Rmin.hα i.1)
    let P : Finset (Rmin.α i.1) :=
      {aα i, bα i}
    have hsubset : P ⊆ U := by
      intro q hq
      simp [U]
    have hsum_univ_eq_pair :
        U.sum (fun q => p i q) =
          P.sum (fun q => p i q) := by
      symm
      apply Finset.sum_subset hsubset
      intro q hqU hq_not_pair
      have hqa : q ≠ aα i := by
        intro hq_eq
        apply hq_not_pair
        simp [P, hq_eq]
      have hqb : q ≠ bα i := by
        intro hq_eq
        apply hq_not_pair
        simp [P, hq_eq]
      exact hp_other i q hqa hqb
    change U.sum (fun q => p i q) = 0
    rw [hsum_univ_eq_pair]
    have ha_not_mem_singleton :
        aα i ∉ ({bα i} : Finset (Rmin.α i.1)) := by
      simp [habα i]
    have hP_eq :
        P = insert (aα i) ({bα i} : Finset (Rmin.α i.1)) := by
      simp [P]
    rw [hP_eq]
    rw [Finset.sum_insert ha_not_mem_singleton]
    rw [Finset.sum_singleton]
    rw [hp_a i, hp_b i]
    ring
  have hp_weighted_eq :
      ∀ i : bad,
        (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
          (fun q => p i q • Rmin.z i.1 q)
          =
        c i • (Rmin.z i.1 (aα i) - Rmin.z i.1 (bα i)) := by
    intro i
    classical
    let U : Finset (Rmin.α i.1) :=
      @Finset.univ (Rmin.α i.1) (Rmin.hα i.1)
    let P : Finset (Rmin.α i.1) :=
      {aα i, bα i}
    have hsubset : P ⊆ U := by
      intro q hq
      simp [U]
    have hsum_univ_eq_pair :
        U.sum (fun q => p i q • Rmin.z i.1 q) =
          P.sum (fun q => p i q • Rmin.z i.1 q) := by
      symm
      apply Finset.sum_subset hsubset
      intro q hqU hq_not_pair
      have hqa : q ≠ aα i := by
        intro hq_eq
        apply hq_not_pair
        simp [P, hq_eq]
      have hqb : q ≠ bα i := by
        intro hq_eq
        apply hq_not_pair
        simp [P, hq_eq]
      rw [hp_other i q hqa hqb]
      simp
    change U.sum (fun q => p i q • Rmin.z i.1 q) =
      c i • (Rmin.z i.1 (aα i) - Rmin.z i.1 (bα i))
    rw [hsum_univ_eq_pair]
    have ha_not_mem_singleton :
        aα i ∉ ({bα i} : Finset (Rmin.α i.1)) := by
      simp [habα i]
    have hP_eq :
        P = insert (aα i) ({bα i} : Finset (Rmin.α i.1)) := by
      simp [P]
    calc
      P.sum (fun q => p i q • Rmin.z i.1 q)
          =
          c i • Rmin.z i.1 (aα i) +
            (-c i) • Rmin.z i.1 (bα i) := by
            rw [hP_eq]
            rw [Finset.sum_insert ha_not_mem_singleton]
            rw [Finset.sum_singleton]
            rw [hp_a i, hp_b i]
      _ =
          c i • (Rmin.z i.1 (aα i) - Rmin.z i.1 (bα i)) := by
            rw [smul_sub]
            rw [sub_eq_add_neg]
            rw [neg_smul]
  have hp_weighted_sum_zero :
      ∑ i : bad,
        (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
          (fun q => p i q • Rmin.z i.1 q) = 0 := by
    calc
      ∑ i : bad,
        (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
          (fun q => p i q • Rmin.z i.1 q)
          =
        ∑ i : bad,
          c i • (Rmin.z i.1 (aα i) - Rmin.z i.1 (bα i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hp_weighted_eq i
      _ = 0 := by
            exact hc_sum_expanded
  let wε : ℝ → ∀ i : bad, Rmin.α i.1 → ℝ := fun ε i q =>
    Rmin.w i.1 q + ε * p i q
  have hwε_sum :
      ∀ ε : ℝ, ∀ i : bad,
        (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
          (fun q => wε ε i q) = 1 := by
    intro ε i
    let U : Finset (Rmin.α i.1) :=
      @Finset.univ (Rmin.α i.1) (Rmin.hα i.1)
    have hsum_p :
        U.sum (fun q => p i q) = 0 := by
      exact hp_sum_zero i
    have hsum_w :
        U.sum (fun q => Rmin.w i.1 q) = 1 := by
      exact Rmin.hw_sum i.1
    change U.sum (fun q => Rmin.w i.1 q + ε * p i q) = 1
    calc
      U.sum (fun q => Rmin.w i.1 q + ε * p i q)
          =
          U.sum (fun q => Rmin.w i.1 q) +
            U.sum (fun q => ε * p i q) := by
            rw [Finset.sum_add_distrib]
      _ =
          U.sum (fun q => Rmin.w i.1 q) +
            ε * U.sum (fun q => p i q) := by
            rw [Finset.mul_sum]
      _ = 1 := by
            rw [hsum_w, hsum_p]
            ring
  have hwε_weighted_eq :
      ∀ ε : ℝ, ∀ i : bad,
        (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
          (fun q => wε ε i q • Rmin.z i.1 q)
          =
        Rmin.y i.1 +
          ε •
            ((@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
              (fun q => p i q • Rmin.z i.1 q)) := by
    intro ε i
    let U : Finset (Rmin.α i.1) :=
      @Finset.univ (Rmin.α i.1) (Rmin.hα i.1)
    have hsum_w :
        U.sum (fun q => Rmin.w i.1 q • Rmin.z i.1 q) = Rmin.y i.1 := by
      exact Rmin.hw_eq i.1
    change
      U.sum
        (fun q =>
          (Rmin.w i.1 q + ε * p i q) • Rmin.z i.1 q)
        =
      Rmin.y i.1 +
        ε • U.sum (fun q => p i q • Rmin.z i.1 q)
    calc
      U.sum
        (fun q =>
          (Rmin.w i.1 q + ε * p i q) • Rmin.z i.1 q)
          =
        U.sum
          (fun q =>
            Rmin.w i.1 q • Rmin.z i.1 q +
              (ε * p i q) • Rmin.z i.1 q) := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [add_smul]
      _ =
        U.sum
          (fun q =>
            Rmin.w i.1 q • Rmin.z i.1 q +
              ε • (p i q • Rmin.z i.1 q)) := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [mul_smul]
      _ =
        U.sum (fun q => Rmin.w i.1 q • Rmin.z i.1 q) +
          U.sum (fun q => ε • (p i q • Rmin.z i.1 q)) := by
            rw [Finset.sum_add_distrib]
      _ =
        U.sum (fun q => Rmin.w i.1 q • Rmin.z i.1 q) +
          ε • U.sum (fun q => p i q • Rmin.z i.1 q) := by
            rw [Finset.smul_sum]
      _ =
        Rmin.y i.1 +
          ε • U.sum (fun q => p i q • Rmin.z i.1 q) := by
            rw [hsum_w]
  have hwε_bad_sum_eq :
      ∀ ε : ℝ,
        ∑ i : bad,
          (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
            (fun q => wε ε i q • Rmin.z i.1 q)
          =
        ∑ i : bad, Rmin.y i.1 := by
    intro ε
    calc
      ∑ i : bad,
        (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
          (fun q => wε ε i q • Rmin.z i.1 q)
          =
        ∑ i : bad,
          (Rmin.y i.1 +
            ε •
              ((@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
                (fun q => p i q • Rmin.z i.1 q))) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hwε_weighted_eq ε i
      _ =
        (∑ i : bad, Rmin.y i.1) +
          ∑ i : bad,
            ε •
              ((@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
                (fun q => p i q • Rmin.z i.1 q)) := by
            rw [Finset.sum_add_distrib]
      _ =
        (∑ i : bad, Rmin.y i.1) +
          ε •
            (∑ i : bad,
              (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
                (fun q => p i q • Rmin.z i.1 q)) := by
            rw [Finset.smul_sum]
      _ =
        ∑ i : bad, Rmin.y i.1 := by
            rw [hp_weighted_sum_zero]
            simp
  have hp_exists_neg :
      ∃ i : bad, ∃ q : Rmin.α i.1, p i q < 0 := by
    by_cases hc_pos : 0 < c i₀
    · refine ⟨i₀, bα i₀, ?_⟩
      rw [hp_b i₀]
      exact neg_lt_zero.mpr hc_pos
    · have hc_le_zero : c i₀ ≤ 0 := by
        exact le_of_not_gt hc_pos
      have hc_lt_zero : c i₀ < 0 := by
        exact lt_of_le_of_ne hc_le_zero hi₀_ne_zero
      refine ⟨i₀, aα i₀, ?_⟩
      rw [hp_a i₀]
      exact hc_lt_zero
  letI : ∀ i : bad, Fintype (Rmin.α i.1) := fun i =>
    Rmin.hα i.1
  let negPairs : Finset (Sigma fun i : bad => Rmin.α i.1) :=
    Finset.univ.filter fun iq =>
      p iq.1 iq.2 < 0
  have hnegPairs_nonempty : negPairs.Nonempty := by
    rcases hp_exists_neg with ⟨i, q, hq_neg⟩
    refine ⟨⟨i, q⟩, ?_⟩
    simp [negPairs, hq_neg]
  let ratio : (Sigma fun i : bad => Rmin.α i.1) → ℝ := fun iq =>
    Rmin.w iq.1.1 iq.2 / (-p iq.1 iq.2)
  have hratio_pos_on_negPairs :
      ∀ iq ∈ negPairs, 0 < ratio iq := by
    intro iq hiq
    have hp_neg : p iq.1 iq.2 < 0 := by
      simpa [negPairs] using hiq
    have hden_pos : 0 < -p iq.1 iq.2 := by
      exact neg_pos.mpr hp_neg
    have hw_pos : 0 < Rmin.w iq.1.1 iq.2 := by
      exact Rmin.hw_pos iq.1.1 iq.2
    unfold ratio
    exact div_pos hw_pos hden_pos
  have hmin_exists :
      ∃ iq ∈ negPairs, ∀ jq ∈ negPairs, ratio iq ≤ ratio jq := by
    exact Finset.exists_min_image negPairs ratio hnegPairs_nonempty
  rcases hmin_exists with ⟨epsPairMin, hepsPairMin_mem, hepsPairMin_min⟩
  let ε : ℝ := ratio epsPairMin
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact hratio_pos_on_negPairs epsPairMin hepsPairMin_mem
  have hp_eps_neg : p epsPairMin.1 epsPairMin.2 < 0 := by
    simpa [negPairs] using hepsPairMin_mem
  have hp_eps_ne_zero : p epsPairMin.1 epsPairMin.2 ≠ 0 := by
    exact ne_of_lt hp_eps_neg
  have hneg_p_eps_pos : 0 < -p epsPairMin.1 epsPairMin.2 := by
    exact neg_pos.mpr hp_eps_neg
  have hneg_p_eps_ne_zero : -p epsPairMin.1 epsPairMin.2 ≠ 0 := by
    exact ne_of_gt hneg_p_eps_pos
  have hwε_epsPairMin_zero :
      wε ε epsPairMin.1 epsPairMin.2 = 0 := by
    dsimp [wε, ε, ratio]
    field_simp [hneg_p_eps_ne_zero]
    ring
  have hwε_nonneg :
      ∀ i : bad, ∀ q : Rmin.α i.1, 0 ≤ wε ε i q := by
    intro i q
    by_cases hp_neg : p i q < 0
    · have hiq_mem : (Sigma.mk i q) ∈ negPairs := by
        simp [negPairs, hp_neg]
      have hε_le_ratio :
          ε ≤ ratio (Sigma.mk i q) := by
        dsimp [ε]
        exact hepsPairMin_min (Sigma.mk i q) hiq_mem
      have hp_pos_den : 0 < -p i q := by
        exact neg_pos.mpr hp_neg
      have hp_den_nonneg : 0 ≤ -p i q := by
        exact le_of_lt hp_pos_den
      have hw_pos : 0 < Rmin.w i.1 q := by
        exact Rmin.hw_pos i.1 q
      have hden_ne_zero : -p i q ≠ 0 := by
        exact ne_of_gt hp_pos_den
      dsimp [wε]
      have hmul_le :
          ε * (-p i q) ≤ Rmin.w i.1 q := by
        have hratio_eq :
            ratio (Sigma.mk i q) =
              Rmin.w i.1 q / (-p i q) := by
          rfl
        rw [hratio_eq] at hε_le_ratio
        have hmul_le' :
            ε * (-p i q) ≤
              (Rmin.w i.1 q / (-p i q)) * (-p i q) := by
          exact mul_le_mul_of_nonneg_right hε_le_ratio hp_den_nonneg
        have hdiv_mul :
            (Rmin.w i.1 q / (-p i q)) * (-p i q) =
              Rmin.w i.1 q := by
          exact div_mul_cancel₀ (Rmin.w i.1 q) hden_ne_zero
        rwa [hdiv_mul] at hmul_le'
      have htarget :
          0 ≤ Rmin.w i.1 q + ε * p i q := by
        have hrewrite :
            ε * p i q = -(ε * (-p i q)) := by
          ring
        rw [hrewrite]
        exact sub_nonneg.mpr hmul_le
      exact htarget
    · have hp_nonneg : 0 ≤ p i q := by
        exact le_of_not_gt hp_neg
      have hε_nonneg : 0 ≤ ε := by
        exact le_of_lt hε_pos
      have hw_pos : 0 < Rmin.w i.1 q := by
        exact Rmin.hw_pos i.1 q
      have hw_nonneg : 0 ≤ Rmin.w i.1 q := by
        exact le_of_lt hw_pos
      dsimp [wε]
      have hmul_nonneg : 0 ≤ ε * p i q := by
        exact mul_nonneg hε_nonneg hp_nonneg
      exact add_nonneg hw_nonneg hmul_nonneg
  have hwε_exists_pos :
      ∀ i : bad, ∃ q : Rmin.α i.1, 0 < wε ε i q := by
    intro i
    by_contra hnone
    have hall_nonpos :
        ∀ q : Rmin.α i.1, wε ε i q ≤ 0 := by
      intro q
      exact le_of_not_gt fun hpos => hnone ⟨q, hpos⟩
    have hall_zero :
        ∀ q : Rmin.α i.1, wε ε i q = 0 := by
      intro q
      have hnonneg : 0 ≤ wε ε i q := by
        exact hwε_nonneg i q
      have hnonpos : wε ε i q ≤ 0 := by
        exact hall_nonpos q
      exact le_antisymm hnonpos hnonneg
    have hsum_zero :
        (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
          (fun q => wε ε i q) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      exact hall_zero q
    have hsum_one :
        (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
          (fun q => wε ε i q) = 1 := by
      exact hwε_sum ε i
    have hzero_eq_one : (0 : ℝ) = 1 := by
      rw [← hsum_zero, hsum_one]
    norm_num at hzero_eq_one
  let αbadε : bad → Type uα := fun i =>
    { q : Rmin.α i.1 // 0 < wε ε i q }
  have hαbadε_fintype :
      ∀ i : bad, Fintype (αbadε i) := by
    intro i
    dsimp [αbadε]
    infer_instance
  have hαbadε_nonempty :
      ∀ i : bad, Nonempty (αbadε i) := by
    intro i
    rcases hwε_exists_pos i with ⟨q, hq_pos⟩
    exact ⟨⟨q, hq_pos⟩⟩
  have hepsPairMin_not_pos :
      ¬ 0 < wε ε epsPairMin.1 epsPairMin.2 := by
    rw [hwε_epsPairMin_zero]
    exact lt_irrefl 0
  have hcard_αbadε_lt :
      Fintype.card (αbadε epsPairMin.1) <
        Fintype.card (Rmin.α epsPairMin.1.1) := by
    classical
    let U : Finset (Rmin.α epsPairMin.1.1) :=
      @Finset.univ
        (Rmin.α epsPairMin.1.1)
        (Rmin.hα epsPairMin.1.1)
    let P : Finset (Rmin.α epsPairMin.1.1) :=
      U.filter fun q => 0 < wε ε epsPairMin.1 q
    have hP_subset_U : P ⊆ U := by
      intro q hq
      exact (Finset.mem_filter.mp hq).1
    have heps_mem_U : epsPairMin.2 ∈ U := by
      simp [U]
    have heps_not_mem_P : epsPairMin.2 ∉ P := by
      intro hmem
      have hpos : 0 < wε ε epsPairMin.1 epsPairMin.2 := by
        exact (Finset.mem_filter.mp hmem).2
      exact hepsPairMin_not_pos hpos
    have hP_ssubset_U : P ⊂ U := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hP_subset_U, ?_⟩
      intro hPU_eq
      have : epsPairMin.2 ∈ P := by
        rw [hPU_eq]
        exact heps_mem_U
      exact heps_not_mem_P this
    have hcard_P_lt_U : P.card < U.card := by
      exact Finset.card_lt_card hP_ssubset_U
    have hcard_subtype_eq_P :
        Fintype.card (αbadε epsPairMin.1) = P.card := by
      dsimp [αbadε, P, U]
      rw [Fintype.card_subtype]
    have hcard_old_eq_U :
        Fintype.card (Rmin.α epsPairMin.1.1) = U.card := by
      simp [U]
    rw [hcard_subtype_eq_P, hcard_old_eq_U]
    exact hcard_P_lt_U
  let αε : ι → Type uα := fun i =>
    { q : Rmin.α i //
      if hi : i ∈ bad then
        0 < wε ε ⟨i, hi⟩ q
      else
        True }
  have hαε_fintype :
      ∀ i : ι, Fintype (αε i) := by
    intro i
    dsimp [αε]
    letI : Fintype (Rmin.α i) := Rmin.hα i
    infer_instance
  let zε : ∀ i : ι, αε i → E := fun i a =>
    Rmin.z i a.1
  let wεFull : ∀ i : ι, αε i → ℝ := fun i a =>
    if hi : i ∈ bad then
      wε ε ⟨i, hi⟩ a.1
    else
      Rmin.w i a.1
  have hzε_mem :
      ∀ i : ι, ∀ a : αε i, zε i a ∈ S i := by
    intro i a
    change Rmin.z i a.1 ∈ S i
    exact Rmin.hz_mem i a.1
  have hwεFull_pos :
      ∀ i : ι, ∀ a : αε i, 0 < wεFull i a := by
    intro i a
    by_cases hi : i ∈ bad
    · have ha_pos :
          0 < wε ε ⟨i, hi⟩ a.1 := by
        have hsub := a.2
        simpa [αε, hi] using hsub
      simpa [wεFull, hi] using ha_pos
    · have ha_pos :
          0 < Rmin.w i a.1 := by
        exact Rmin.hw_pos i a.1
      simpa [wεFull, hi] using ha_pos
  have hwεFull_sum :
      ∀ i : ι,
        (@Finset.univ (αε i) (hαε_fintype i)).sum
          (fun a => wεFull i a) = 1 := by
    intro i
    by_cases hi : i ∈ bad
    · let ib : bad := ⟨i, hi⟩
      let U : Finset (Rmin.α i) :=
        @Finset.univ (Rmin.α i) (Rmin.hα i)
      let P : Finset (Rmin.α i) :=
        U.filter fun q => 0 < wε ε ib q
      have hsum_U :
          U.sum (fun q => wε ε ib q) = 1 := by
        exact hwε_sum ε ib
      have hsum_U_eq_P :
          U.sum (fun q => wε ε ib q) =
            P.sum (fun q => wε ε ib q) := by
        symm
        apply Finset.sum_subset
        · intro q hq
          exact (Finset.mem_filter.mp hq).1
        · intro q hqU hq_not_P
          have hnot_pos : ¬ 0 < wε ε ib q := by
            intro hpos
            apply hq_not_P
            simp [P, hqU, hpos]
          have hnonneg : 0 ≤ wε ε ib q := by
            exact hwε_nonneg ib q
          have hzero : wε ε ib q = 0 := by
            exact le_antisymm (le_of_not_gt hnot_pos) hnonneg
          rw [hzero]
      have hsubtype_eq_P :
          (@Finset.univ (αε i) (hαε_fintype i)).sum
            (fun a => wεFull i a)
          =
          P.sum (fun q => wε ε ib q) := by
        classical
        dsimp [P, U, ib]
        apply Finset.sum_bij
          (fun a _ => a.1)
        · intro a ha
          have ha_pos : 0 < wε ε ⟨i, hi⟩ a.1 := by
            simpa [αε, hi] using a.2
          simp [ha_pos]
        · intro a₁ ha₁ a₂ ha₂ hval
          exact Subtype.ext hval
        · intro q hq
          have hq_pos : 0 < wε ε ⟨i, hi⟩ q := by
            simpa [P, U, ib] using hq
          refine ⟨⟨q, ?_⟩, ?_, ?_⟩
          · simpa [αε, hi] using hq_pos
          · exact Finset.mem_univ _
          · rfl
        · intro a ha
          simp [wεFull, hi]
      calc
        (@Finset.univ (αε i) (hαε_fintype i)).sum
            (fun a => wεFull i a)
            =
          P.sum (fun q => wε ε ib q) := by
            exact hsubtype_eq_P
        _ =
          U.sum (fun q => wε ε ib q) := by
            exact hsum_U_eq_P.symm
        _ = 1 := by
            exact hsum_U
    · let U : Finset (Rmin.α i) :=
        @Finset.univ (Rmin.α i) (Rmin.hα i)
      have hsum_U :
          U.sum (fun q => Rmin.w i q) = 1 := by
        exact Rmin.hw_sum i
      have hsubtype_eq_U :
          (@Finset.univ (αε i) (hαε_fintype i)).sum
            (fun a => wεFull i a)
          =
          U.sum (fun q => Rmin.w i q) := by
        classical
        dsimp [U]
        apply Finset.sum_bij
          (fun a _ => a.1)
        · intro a ha
          simp
        · intro a₁ ha₁ a₂ ha₂ hval
          exact Subtype.ext hval
        · intro q hq
          refine ⟨⟨q, ?_⟩, ?_, ?_⟩
          · simp [hi]
          · exact Finset.mem_univ _
          · rfl
        · intro a ha
          simp [wεFull, hi]
      calc
        (@Finset.univ (αε i) (hαε_fintype i)).sum
            (fun a => wεFull i a)
            =
          U.sum (fun q => Rmin.w i q) := by
            exact hsubtype_eq_U
        _ = 1 := by
            exact hsum_U
  let yε : ι → E := fun i =>
    (@Finset.univ (αε i) (hαε_fintype i)).sum
      (fun a => wεFull i a • zε i a)
  have hwεFull_eq :
      ∀ i : ι,
        (@Finset.univ (αε i) (hαε_fintype i)).sum
          (fun a => wεFull i a • zε i a) = yε i := by
    intro i
    rfl
  have hyε_not_bad :
      ∀ i : ι, i ∉ bad → yε i = Rmin.y i := by
    intro i hi
    letI : Fintype (Rmin.α i) := Rmin.hα i
    dsimp [yε]
    have hmap :
        (Finset.univ : Finset (αε i)).map
          ⟨fun a : αε i => a.1, by
            intro a b h
            exact Subtype.ext h⟩
        =
        (Finset.univ : Finset (Rmin.α i)) := by
      ext q
      constructor
      · intro hq
        exact Finset.mem_univ q
      · intro hq
        simp only [Finset.mem_map, Finset.mem_univ, true_and]
        refine ⟨(⟨q, ?_⟩ : αε i), ?_⟩
        · simp [hi]
        · rfl
    calc
      (∑ a : αε i, wεFull i a • zε i a)
          =
        ∑ q : Rmin.α i, Rmin.w i q • Rmin.z i q := by
          rw [← hmap]
          simp [Finset.sum_map, zε, wεFull, hi]
      _ = Rmin.y i := by
          exact Rmin.hw_eq i
  have hyε_bad :
      ∀ i : bad,
        yε i.1 =
          (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
            (fun q => wε ε i q • Rmin.z i.1 q) := by
    intro i
    letI : Fintype (Rmin.α i.1) := Rmin.hα i.1
    dsimp [yε]
    have hmap :
        (Finset.univ : Finset (αε i.1)).map
          ⟨fun a : αε i.1 => a.1, by
            intro a b h
            exact Subtype.ext h⟩
        =
        (Finset.univ : Finset (Rmin.α i.1)).filter
          (fun q => 0 < wε ε i q) := by
      ext q
      constructor
      · intro hq
        simp only [Finset.mem_map, Finset.mem_univ, true_and] at hq
        rcases hq with ⟨a, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change 0 < wε ε i a.1
        simpa [αε, i.2] using a.2
      · intro hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        simp only [Finset.mem_map, Finset.mem_univ, true_and]
        refine ⟨(⟨q, ?_⟩ : αε i.1), ?_⟩
        · simpa [αε, i.2] using hq
        · rfl
    have hfilter_eq :
        ((Finset.univ : Finset (Rmin.α i.1)).filter
          (fun q => 0 < wε ε i q)).sum
            (fun q => wε ε i q • Rmin.z i.1 q)
        =
        (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
          (fun q => wε ε i q • Rmin.z i.1 q) := by
      rw [← Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Rmin.α i.1)))
        (p := fun q => 0 < wε ε i q)
        (f := fun q => wε ε i q • Rmin.z i.1 q)]
      have hnot_sum_zero :
          ((Finset.univ : Finset (Rmin.α i.1)).filter
            (fun q => ¬ 0 < wε ε i q)).sum
              (fun q => wε ε i q • Rmin.z i.1 q) = 0 := by
        apply Finset.sum_eq_zero
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        have hnonneg : 0 ≤ wε ε i q := hwε_nonneg i q
        have hle : wε ε i q ≤ 0 := le_of_not_gt hq
        have hw_zero : wε ε i q = 0 := le_antisymm hle hnonneg
        simp [hw_zero]
      rw [hnot_sum_zero, add_zero]
    calc
      (∑ a : αε i.1, wεFull i.1 a • zε i.1 a)
          =
        ((Finset.univ : Finset (Rmin.α i.1)).filter
          (fun q => 0 < wε ε i q)).sum
            (fun q => wε ε i q • Rmin.z i.1 q) := by
          rw [← hmap]
          simp [Finset.sum_map, zε, wεFull, i.2]
      _ =
        (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
          (fun q => wε ε i q • Rmin.z i.1 q) := by
          exact hfilter_eq
  have hsum_yε :
      (∑ i ∈ (Finset.univ : Finset ι), yε i) = x := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset ι))
      (p := fun i => i ∈ bad)
      (f := fun i => yε i)]
    have hbad_part :
        ((Finset.univ : Finset ι).filter fun i => i ∈ bad).sum yε
          =
        ∑ i : bad, yε i.1 := by
      have hfilter_bad :
          ((Finset.univ : Finset ι).filter fun i => i ∈ bad) = bad := by
        ext i
        simp
      rw [hfilter_bad]
      symm
      exact Finset.sum_attach bad (fun i : ι => yε i)
    have hgood_part :
        ((Finset.univ : Finset ι).filter fun i => ¬ i ∈ bad).sum yε
          =
        ((Finset.univ : Finset ι).filter fun i => ¬ i ∈ bad).sum Rmin.y := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hyε_not_bad i hi
    rw [hbad_part, hgood_part]
    have hbad_y :
        (∑ i : bad, yε i.1)
          =
        ∑ i : bad,
          (@Finset.univ (Rmin.α i.1) (Rmin.hα i.1)).sum
            (fun q => wε ε i q • Rmin.z i.1 q) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hyε_bad i
    rw [hbad_y]
    rw [hwε_bad_sum_eq ε]
    have hsplit_old :
        (∑ i : bad, Rmin.y i.1)
          +
        ((Finset.univ : Finset ι).filter fun i => ¬ i ∈ bad).sum Rmin.y
          =
        ∑ i, Rmin.y i := by
      rw [← Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset ι))
        (p := fun i => i ∈ bad)
        (f := fun i => Rmin.y i)]
      have hbad_old :
          ((Finset.univ : Finset ι).filter fun i => i ∈ bad).sum Rmin.y
            =
          ∑ i : bad, Rmin.y i.1 := by
        have hfilter_bad :
            ((Finset.univ : Finset ι).filter fun i => i ∈ bad) = bad := by
          ext i
          simp
        rw [hfilter_bad]
        symm
        exact Finset.sum_attach bad (fun i : ι => Rmin.y i)
      rw [hbad_old]
    exact hsplit_old.trans Rmin.hsum
  let Rε : ShapleyFolkmanRep.{uι, uE, uα} ι E S x := {
    α := αε
    hα := hαε_fintype
    y := yε
    z := zε
    w := wεFull
    hz_mem := hzε_mem
    hw_pos := hwεFull_pos
    hw_sum := hwεFull_sum
    hw_eq := hwεFull_eq
    hsum := hsum_yε
  }
  have hmin_Rε :
      ShapleyFolkmanRep.complexity Rmin ≤
        ShapleyFolkmanRep.complexity Rε := by
    exact hmin Rε
  have hcard_αε_le :
      ∀ i : ι,
        @Fintype.card (αε i) (hαε_fintype i) ≤
          @Fintype.card (Rmin.α i) (Rmin.hα i) := by
    intro i
    letI : Fintype (αε i) := hαε_fintype i
    letI : Fintype (Rmin.α i) := Rmin.hα i
    exact Fintype.card_le_of_injective
      (fun a : αε i => (a.1 : Rmin.α i))
      (by
        intro a b h
        exact Subtype.ext h)
  have hcard_αε_lt_at :
      @Fintype.card (αε epsPairMin.1.1)
          (hαε_fintype epsPairMin.1.1) <
        @Fintype.card (Rmin.α epsPairMin.1.1)
          (Rmin.hα epsPairMin.1.1) := by
    letI : Fintype (αε epsPairMin.1.1) :=
      hαε_fintype epsPairMin.1.1
    letI : Fintype (Rmin.α epsPairMin.1.1) :=
      Rmin.hα epsPairMin.1.1
    letI : Fintype (αbadε epsPairMin.1) :=
      hαbadε_fintype epsPairMin.1
    have hcard_eq :
        @Fintype.card (αε epsPairMin.1.1)
            (hαε_fintype epsPairMin.1.1)
          =
        @Fintype.card (αbadε epsPairMin.1)
            (hαbadε_fintype epsPairMin.1) := by
      let e :
          αε epsPairMin.1.1 ≃ αbadε epsPairMin.1 := {
        toFun := fun a => by
          refine ⟨a.1, ?_⟩
          have ha := a.2
          simpa [αε, epsPairMin.1.2] using ha
        invFun := fun a => by
          refine ⟨a.1, ?_⟩
          have ha := a.2
          simpa [αε, epsPairMin.1.2] using ha
        left_inv := by
          intro a
          exact Subtype.ext rfl
        right_inv := by
          intro a
          exact Subtype.ext rfl
      }
      exact Fintype.card_congr e
    rw [hcard_eq]
    exact hcard_αbadε_lt
  have hcomplexity_lt :
      ShapleyFolkmanRep.complexity Rε <
        ShapleyFolkmanRep.complexity Rmin := by
    dsimp [ShapleyFolkmanRep.complexity, Rε]
    apply Finset.sum_lt_sum
    · intro i hi
      exact hcard_αε_le i
    · refine ⟨epsPairMin.1.1, Finset.mem_univ epsPairMin.1.1, ?_⟩
      exact hcard_αε_lt_at
  exact not_lt_of_ge hmin_Rε hcomplexity_lt
lemma shapley_folkman_exists_choice_core
    {ι E : Type*}
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (S : ι → Set E)
    (x : E)
    (hx : x ∈ (∑ i ∈ (Finset.univ : Finset ι), convexHull ℝ (S i))) :
    ∃ y : ι → E,
    ∃ bad : Finset ι,
      bad.card ≤ Module.finrank ℝ E ∧
      (∀ i ∈ bad, y i ∈ convexHull ℝ (S i)) ∧
      (∀ i ∈ (Finset.univ \ bad), y i ∈ S i) ∧
      ∑ i ∈ (Finset.univ : Finset ι), y i = x := by
  classical
  rcases
      (Set.mem_finsetSum
        (Finset.univ : Finset ι)
        (fun i => convexHull ℝ (S i))
        x).mp hx with
    ⟨y₀, hy₀, hy₀sum⟩
  have hy₀_all : ∀ i : ι, y₀ i ∈ convexHull ℝ (S i) := by
    intro i
    exact hy₀ (Finset.mem_univ i)
  have hcar : ∀ i : ι,
      ∃ T : Finset E,
        ↑T ⊆ S i ∧
        y₀ i ∈ convexHull ℝ (T : Set E) ∧
        AffineIndependent ℝ (fun p : T => (p : E)) := by
    intro i
    exact exists_caratheodory_finset (S i) (y₀ i) (hy₀_all i)
  let T : ι → Finset E := fun i => Classical.choose (hcar i)
  have hT_subset : ∀ i : ι, ↑(T i) ⊆ S i := by
    intro i
    exact (Classical.choose_spec (hcar i)).1
  have hy₀_mem_T : ∀ i : ι, y₀ i ∈ convexHull ℝ (T i : Set E) := by
    intro i
    exact (Classical.choose_spec (hcar i)).2.1
  have hT_affineIndependent :
      ∀ i : ι, AffineIndependent ℝ (fun p : T i => (p : E)) := by
    intro i
    exact (Classical.choose_spec (hcar i)).2.2
  have hcombo_raw := fun i =>
    eq_pos_convex_span_of_mem_convexHull (hy₀_mem_T i)
  let α := fun i => Classical.choose (hcombo_raw i)
  have hcombo_spec := fun i =>
    Classical.choose_spec (hcombo_raw i)
  let hα : ∀ i : ι, Fintype (α i) := fun i =>
    Classical.choose (hcombo_spec i)
  let z : ∀ i : ι, α i → E := fun i =>
    Classical.choose (Classical.choose_spec (hcombo_spec i))
  let w : ∀ i : ι, α i → ℝ := fun i =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hcombo_spec i)))
  have hcombo_props :
      ∀ i : ι,
        Set.range (z i) ⊆ (T i : Set E) ∧
        AffineIndependent ℝ (z i) ∧
        (∀ a : α i, 0 < w i a) ∧
        ∑ a, w i a = 1 ∧
        ∑ a, w i a • z i a = y₀ i := by
    intro i
    dsimp [z, w]
    exact Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (hcombo_spec i)))
  have hz_mem_S : ∀ i : ι, ∀ a : α i, z i a ∈ S i := by
    intro i a
    have hz_mem_T : z i a ∈ (T i : Set E) := by
      exact (hcombo_props i).1 ⟨a, rfl⟩
    exact hT_subset i hz_mem_T
  let R₀ : ShapleyFolkmanRep ι E S x :=
    { α := α
      hα := hα
      y := y₀
      z := z
      w := w
      hz_mem := hz_mem_S
      hw_pos := by
        intro i a
        exact (hcombo_props i).2.2.1 a
      hw_sum := by
        intro i
        exact (hcombo_props i).2.2.2.1
      hw_eq := by
        intro i
        exact (hcombo_props i).2.2.2.2
      hsum := hy₀sum }
  have hR_exists :
      ∃ R : ShapleyFolkmanRep ι E S x, True := by
    exact ⟨R₀, trivial⟩
  rcases exists_minimal_shapley_folkman_rep hR_exists with
    ⟨Rmin, hRmin_minimal⟩
  let bad : Finset ι := ShapleyFolkmanRep.nonsingleton Rmin
  have hbad_iff :
      ∀ i : ι,
        i ∈ bad ↔
          (@Finset.univ (Rmin.α i) (Rmin.hα i)).card ≠ 1 := by
    intro i
    simp [bad, ShapleyFolkmanRep.nonsingleton]
  have hy_good :
      ∀ i ∈ (Finset.univ \ bad), Rmin.y i ∈ S i := by
    intro i hi
    classical
    letI := Rmin.hα i
    have hcard_univ :
        (Finset.univ : Finset (Rmin.α i)).card = 1 := by
      have hi_not_bad : i ∉ bad := (Finset.mem_sdiff.mp hi).2
      by_contra hcard
      exact hi_not_bad ((hbad_iff i).2 hcard)
    exact mem_of_convex_combo_univ_card_eq_one
      (S := S i)
      (y := Rmin.y i)
      (z := Rmin.z i)
      (w := Rmin.w i)
      (Rmin.hz_mem i)
      hcard_univ
      (Rmin.hw_sum i)
      (Rmin.hw_eq i)
  have hy_bad :
      ∀ i ∈ bad, Rmin.y i ∈ convexHull ℝ (S i) := by
    intro i hi
    have hz_subset : Set.range (Rmin.z i) ⊆ S i := by
      intro p hp
      rcases hp with ⟨a, rfl⟩
      exact Rmin.hz_mem i a
    have hy_mem_conv_range :
        Rmin.y i ∈ convexHull ℝ (Set.range (Rmin.z i)) := by
      rw [← Rmin.hw_eq i]
      exact Convex.sum_mem
        (convex_convexHull ℝ (Set.range (Rmin.z i)))
        (fun a _ => le_of_lt (Rmin.hw_pos i a))
        (Rmin.hw_sum i)
        (fun a _ => subset_convexHull ℝ (Set.range (Rmin.z i)) ⟨a, rfl⟩)
    exact convexHull_mono hz_subset hy_mem_conv_range
  have hbad_card : bad.card ≤ Module.finrank ℝ E := by
    simpa [bad] using
      ShapleyFolkmanRep.nonsingleton_card_le_finrank_of_minimal
        Rmin hRmin_minimal
  refine ⟨Rmin.y, bad, hbad_card, hy_bad, hy_good, ?_⟩
  exact Rmin.hsum
lemma shapley_folkman_exists_choice
    {ι E : Type*}
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (S : ι → Set E)
    (x : E)
    (hx : x ∈ (∑ i ∈ (Finset.univ : Finset ι), convexHull ℝ (S i))) :
    ∃ y : ι → E,
    ∃ bad : Finset ι,
      bad.card ≤ Module.finrank ℝ E ∧
      (∀ i ∈ bad, y i ∈ convexHull ℝ (S i)) ∧
      (∀ i ∈ (Finset.univ \ bad), y i ∈ S i) ∧
      ∑ i ∈ (Finset.univ : Finset ι), y i = x := by
  exact shapley_folkman_exists_choice_core S x hx
theorem shapley_folkman
    {ι E : Type*}
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (S : ι → Set E)
    (x : E)
    (hx : x ∈ (∑ i ∈ (Finset.univ : Finset ι), convexHull ℝ (S i))) :
    ∃ t : Finset ι,
      t.card ≤ Module.finrank ℝ E ∧
      x ∈
        (∑ i ∈ t, convexHull ℝ (S i)) +
        (∑ i ∈ (Finset.univ \ t), S i) := by
  classical
  rcases shapley_folkman_exists_choice S x hx with
    ⟨y, bad, hbad_card, hy_bad, hy_good, hysum⟩
  refine ⟨bad, hbad_card, ?_⟩
  exact shapley_folkman_mem_of_choice S x y bad hy_bad hy_good hysum
