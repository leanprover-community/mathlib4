/-
Copyright (c) 2025 Chi-Yun Hsu, Hanzhe Zhang, Tamanna Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chi-Yun Hsu, Hanzhe Zhang, Tamanna Agarwal
-/
module

public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Euler's Partition Theorem with Combinatorial Proof

This files proves Euler's Partition Theorem using combinatorial constructions.

Euler's Partition Theorem states that the number of integer partitions of `n` into `odd` parts
equals the number of partitions of `n` into `distinct` parts.

The combinatorial proof constructs explicit bijections between
the set of partitions of `n` into odd parts and the set of partitions of `n` into distinct parts.

Starting from an odd partition, we map each part `a` with multiplicity `m` to
the multiset consisting of `a * 2 ^ i`, where `2 ^ i` is in the binary expansion of `m`.

Conversely, starting from a distinct partition, we map each part `b` (with multiplicity 1) to
the multiset consisting of `hof b`, the highest odd factor of `b`, with multiplicity `b / hof(b)`.

## References
* <https://dspace.mit.edu/bitstream/handle/1721.1/123321/18-312-spring-2009/contents/readings-and-lecture-notes/MIT18_312S09_lec10_Patitio.pdf>

## Tags

integer partition, bijection
-/

@[expose] public section

open Nat Partition

/-- The multiset of `2 ^ i` in the binary expansion of a natural number `a` -/
def binary (a : ℕ) : Multiset ℕ := a.bitIndices.map (fun i ↦ 2 ^ i)

lemma binary_nodup (a : ℕ) : (binary a).Nodup := by
  apply Multiset.coe_nodup.mpr
  exact List.Nodup.map (Nat.pow_right_injective (le_refl 2)) bitIndices_nodup

/-- The highest odd factor of a natural number `b` -/
def hof (b : ℕ) : ℕ := ordCompl[2] b

lemma hof_eq_iff_zero_or_odd (b : ℕ) : hof b = b ↔ (b = 0 ∨ Odd b) := by
  rw [← not_even_iff_odd, even_iff_two_dvd]
  exact ordCompl_eq_self_iff_zero_or_not_dvd b prime_two

lemma hof_is_odd {b : ℕ} (b_ne_zero : b ≠ 0) : Odd (hof b) := by
  rw [← not_even_iff_odd, even_iff_two_dvd]
  exact not_dvd_ordCompl prime_two b_ne_zero

lemma hof_two_pow_mul (b i : ℕ) : hof (2 ^ i * b) = hof (b) :=
  ordCompl_self_pow_mul b i prime_two

/-- Given a part `a` of a partition `P`, construct the multiset consisting of `a * 2 ^ i`,
where `2 ^ i` is in the binary expansion of the multiplicity of `a`. -/
def FromOddPart {n : ℕ} (P : n.Partition) (a : ℕ) : Multiset ℕ :=
  (binary (Multiset.count a P.parts)).map (fun x ↦ x * a)

lemma FromOddPart_empty_of_notMem {n : ℕ} (P : n.Partition) (a : ℕ) :
    a ∉ P.parts → FromOddPart P a = 0 := by
  intro ha
  rw [FromOddPart]
  apply Multiset.count_eq_zero_of_notMem at ha
  simp [ha, binary]

lemma FromOddPart_pos {n : ℕ} (P : n.Partition) (a : ℕ) {b : ℕ} :
    b ∈ (FromOddPart P a) → b > 0 := by
  intro hb
  by_cases ha : a ∈ P.parts
  · apply Multiset.mem_map.mp at hb
    rcases hb with ⟨x, hx, hb⟩
    have x_pos : x > 0 := by
      rw [binary] at hx
      apply List.mem_map.mp at hx
      rcases hx with ⟨y, hy, hx⟩
      rw [← hx]
      exact Nat.pow_pos zero_lt_two
    have a_pos : a > 0 := P.parts_pos ha
    rw [← hb]
    exact Nat.mul_pos x_pos a_pos
  · rw [FromOddPart_empty_of_notMem P a ha] at hb
    contradiction

lemma FromOddPart_sum {n : ℕ} (P : n.Partition) (a : ℕ) :
    (FromOddPart P a).sum = (Multiset.count a P.parts) * a := by
  rw [FromOddPart, Multiset.sum_map_mul_right, Multiset.map_id']
  simp [binary]

lemma FromOddPart_nodup {n : ℕ} (P : n.Partition) (a : ℕ) : (FromOddPart P a).Nodup := by
  by_cases ha : a ∈ P.parts
  · apply Multiset.Nodup.map
    /- fun x ↦ x * a is injective -/
    · rintro x1 x2 heq
      dsimp at heq
      have a_ne_zero : a ≠ 0 := by
        apply Nat.pos_iff_ne_zero.mp
        exact P.parts_pos ha
      exact (Nat.mul_left_inj a_ne_zero).mp heq
    /- binary has no duplicates -/
    · exact binary_nodup _
  · rw [FromOddPart_empty_of_notMem P a ha]
    exact Multiset.nodup_zero

lemma FromOddPart_hof {n : ℕ} (P : n.Partition) (P_odd : P ∈ (odds n)) (a : ℕ) :
    ∀ b ∈ FromOddPart P a, hof b = a := by
  rintro b hb
  by_cases ha : a ∈ P.parts
  · apply Multiset.mem_map.mp at hb
    rcases hb with ⟨x, hx, hb⟩
    simp only [binary, Multiset.mem_coe, List.mem_map] at hx
    rcases hx with ⟨i, hi, hx⟩
    rw [← hb, ← hx, hof_two_pow_mul a i]
    apply (hof_eq_iff_zero_or_odd a).mpr
    right
    apply Nat.not_even_iff_odd.mp
    exact (Finset.mem_filter.mp P_odd).2 a ha
  · rw [FromOddPart_empty_of_notMem P a ha] at hb
    contradiction

lemma FromOddPart_disjoint {n : ℕ} (P : n.Partition) (P_odd : P ∈ (odds n)) (a a' : ℕ) :
    a ≠ a' → Disjoint (FromOddPart P a) (FromOddPart P a') := by
  rintro hneq
  apply Multiset.disjoint_iff_ne.mpr
  rintro x hx y hy heqxy
  have heq : a = a' := by
    calc
      a = hof x := (FromOddPart_hof P P_odd a x hx).symm
      _ = hof y := by rw [heqxy]
      _ = a' := FromOddPart_hof P P_odd a' y hy
  contradiction

/-- The multiset which is the union of `FromOddPart a` over distinct parts `a` of a partition `P`.
This is the map from odd partitions to distinct partitions on the `Multiset` level. -/
def FromOdd_parts {n : ℕ} (P : n.Partition) : Multiset ℕ :=
  Multiset.bind (P.parts.dedup) (FromOddPart P)

lemma Finsetsum_eq_Bind {n : ℕ} (P : n.Partition) :
    ∑ a ∈ P.parts.toFinset, (FromOddPart P a) = Multiset.bind (P.parts.dedup) (FromOddPart P) := by
  rfl

/-- Each part in the multiset `FromOdd_parts` is positive. -/
lemma FromOdd_parts_pos {n : ℕ} (P : n.Partition) {b : ℕ} : b ∈ (FromOdd_parts P) → b > 0 := by
  rintro hb
  rw [FromOdd_parts] at hb
  apply Multiset.mem_bind.mp at hb
  rcases hb with ⟨a, ha, hb⟩
  exact FromOddPart_pos P a hb

/-- The image of a partition of `n` under `FromOdd_parts` is still a partition of `n`. -/
lemma FromOdd_parts_sum {n : ℕ} (P : n.Partition) : (FromOdd_parts P).sum = n := by
  rw [FromOdd_parts, Multiset.sum_bind, (funext (FromOddPart_sum P))]
  simpa [P.parts_sum] using (Finset.sum_multiset_count P.parts).symm

/-- The map from odd partitions to distinct partitions on the `Partition` level. -/
def FromOdd {n : ℕ} (P : n.Partition) : n.Partition :=
  { parts := FromOdd_parts P,
    parts_pos := FromOdd_parts_pos P,
    parts_sum := FromOdd_parts_sum P }

/-- The image of an odd partition under `FromOdd` is a distinct partition. -/
theorem InDist {n : ℕ} (P : n.Partition) (P_odd : P ∈ (odds n)) :
    FromOdd P ∈ (distincts n) := by
  simp only [distincts, FromOdd, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [FromOdd_parts]
  apply Multiset.nodup_bind.mpr
  constructor
  /- Each FromOddPart P a has no duplicates. -/
  · intro a _
    exact FromOddPart_nodup P a
  /- Different FromOddPart P a are disjoint. -/
  · rw [Multiset.Pairwise]
    set PPartList := Multiset.sort P.parts.dedup with PPartList_def
    have PPartList_nodup : PPartList.Nodup := by
      apply Multiset.coe_nodup.mp
      rw [Multiset.sort_eq]
      apply Multiset.nodup_dedup
    use PPartList
    constructor
    · rw [Multiset.sort_eq]
    · apply (List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint
        (f := FromOddPart P) PPartList_nodup).mp
      rw [List.coe_toFinset]
      intro a ha a' ha' hneq
      simp only [Set.mem_setOf_eq] at ha ha'
      rw [PPartList_def, Multiset.mem_sort] at ha ha'
      dsimp [Function.onFun]
      exact FromOddPart_disjoint P P_odd a a' hneq

/-- The multiset consisting of `hof b` with multiplicity `b / hof(b)` of a natural number `b` -/
def FromDistPart (b : ℕ) : Multiset ℕ := Multiset.replicate (ordProj[2] b) (hof b)

lemma FromDistPart_pos {n : ℕ} (Q : n.Partition) (b : ℕ) (hb : b ∈ Q.parts) {a : ℕ} :
    a ∈ (FromDistPart b) → a > 0 := by
  rintro ha
  apply Multiset.mem_replicate.mp at ha
  rw [ha.2]
  apply Nat.pos_iff_ne_zero.mpr
  apply Nat.div_ne_zero_iff.mpr
  constructor
  · exact pow_ne_zero _ two_ne_zero
  · have b_pos : b > 0 := Q.parts_pos hb
    apply le_of_dvd b_pos (ordProj_dvd b 2)

lemma FromDistPart_sum (b : ℕ) : (FromDistPart b).sum = b := by
  simp only [FromDistPart, Multiset.sum_replicate, smul_eq_mul]
  exact ordProj_mul_ordCompl_eq_self b 2

/-- The multiset which is the union of `FromDistPart b` over distinct parts `b` of a partition `Q`.
This is the map from distinct partitions to odd partitions on the `Multiset` level. -/
def FromDist_parts {n : ℕ} (Q : n.Partition) : Multiset ℕ :=
  ∑ b ∈ Q.parts.toFinset, (FromDistPart b)

/-- Each part in the multiset `FromDist_parts` is positive. -/
lemma FromDist_parts_pos {n : ℕ} (Q : n.Partition) {a : ℕ} : a ∈ (FromDist_parts Q) → a > 0 := by
  rintro ha
  rw [FromDist_parts] at ha
  apply Multiset.mem_sum.mp at ha
  rcases ha with ⟨b, hb, ha⟩
  rw [Multiset.mem_toFinset] at hb
  exact FromDistPart_pos Q b hb ha

/-- The image of a partition of `n` under `FromDist_parts` is still a partition of `n`. -/
lemma FromDist_parts_sum {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) :
    (FromDist_parts Q).sum = n := by
  rw [FromDist_parts, Multiset.sum_sum, (funext FromDistPart_sum)]
  have : ∑ x ∈ Q.parts.toFinset, x = (Multiset.map (fun x ↦ x) (Q.parts.dedup)).sum := by rfl
  rw [this, Multiset.map_id']
  have Q_Nodup : Q.parts.Nodup := by simpa [distincts] using Q_dist
  rw [Multiset.dedup_eq_self.mpr Q_Nodup]
  exact Q.parts_sum

/-- The map from distinct partitions to odd partitions on the `Partition` level. -/
def FromDist {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) : n.Partition :=
  { parts := FromDist_parts Q
    parts_pos := FromDist_parts_pos Q
    parts_sum := FromDist_parts_sum Q Q_dist }

/-- The image of a distinct partition under `FromDist` is an odd partition. -/
theorem InOdd {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) :
    FromDist Q Q_dist ∈ odds n := by
  simp only [odds, restricted, not_even_iff_odd, Finset.mem_filter, Finset.mem_univ, true_and]
  intro a ha
  simp only [FromDist, FromDist_parts, Multiset.mem_sum, Multiset.mem_toFinset] at ha
  rcases ha with ⟨b, hb, ha⟩
  rw [FromDistPart] at ha
  apply Multiset.mem_replicate.mp at ha
  rw [ha.2]
  have b_ne_zero : b ≠ 0 := Nat.pos_iff_ne_zero.mp (Q.parts_pos hb)
  exact hof_is_odd b_ne_zero

lemma LeftInvPart_SameHof {n : ℕ} (P : n.Partition) (P_odd : P ∈ odds n) (a : ℕ) :
    ∑ b ∈ (FromOddPart P a).toFinset, ordProj[2] b = Multiset.count a P.parts := by
  by_cases a_zero : a = 0
  · have ha : a ∉ P.parts := by
      intro ha
      have : a ≠ 0 := Nat.pos_iff_ne_zero.mp (P.parts_pos ha)
      contradiction
    rw [FromOddPart_empty_of_notMem P a ha]
    rw [Multiset.count_eq_zero_of_notMem ha]
    simp
  · apply (Nat.mul_left_inj a_zero).mp
    rw [Finset.sum_mul]
    have ordProj_mul_hof_eq_self (b : ℕ) (hb : b ∈ (FromOddPart P a).toFinset) :
        ordProj[2] b * a = b := by
      rw [← FromOddPart_hof P P_odd a b (Multiset.mem_toFinset.mp hb)]
      exact ordProj_mul_ordCompl_eq_self b 2
    rw [Finset.sum_congr rfl ordProj_mul_hof_eq_self]
    rw [← FromOddPart_sum P a]
    rw [Finset.sum_multiset_count (FromOddPart P a)]
    apply Finset.sum_congr rfl
    rintro b hb
    have count_eq_one : Multiset.count b (FromOddPart P a) = 1 :=
      (Multiset.nodup_iff_count_eq_one.mp (FromOddPart_nodup P a) b)
      (Multiset.mem_toFinset.mp hb)
    simp [count_eq_one]

lemma LeftInvPart_diff_hof {n : ℕ} (P : n.Partition) (P_odd : P ∈ odds n) (a : ℕ) :
    ∀ b ∈ (FromOdd_parts P).toFinset,
    b ∉ (FromOddPart P a).toFinset → Multiset.count a (FromDistPart b) = 0 := by
  intro b hb b_notfrom_a
  rw [Multiset.mem_toFinset] at hb b_notfrom_a
  rw [Multiset.count_eq_zero_of_notMem]
  by_contra contra
  simp only [FromOdd_parts, Multiset.mem_bind, Multiset.mem_dedup] at hb
  rcases hb with ⟨a', ha', b_from_a'⟩
  rw [FromDistPart] at contra
  rw [Multiset.mem_replicate] at contra
  have hof_eq_a' : hof b = a' := FromOddPart_hof P P_odd a' b b_from_a'
  have a_eq_a' : a = a' := by rw [contra.2, hof_eq_a']
  rw [a_eq_a'] at b_notfrom_a
  contradiction

lemma Count_FromDistPart_eq_ordProj {n : ℕ} (P : n.Partition) (P_odd : P ∈ odds n) (a b : ℕ)
    (hb : b ∈ (FromOddPart P a).toFinset) :
    Multiset.count a (FromDistPart b) = ordProj[2] b := by
  rw [← FromOddPart_hof P P_odd a b (Multiset.mem_toFinset.mp hb)]
  simp [FromDistPart]

/-- `FromOdd` followed by `FromDist` is the identity on odd partitions.
Proof strategy : We compute the multiplicity of each integer `a` in `FromDist FromOdd P`.
`FromDist` is a sum over parts `b` in `FromOdd P`.
Only parts `b` in the subset `FromOddPart P a` of `FromOdd P` contribute to the multiplicity of `a`.
This is proven in `LeftInvPart_diff_hof`.
In `Count_FromDistPart_eq_ordProj`, we show that the multiplicity contribution from each such `b`
is the largest power of 2 dividing `b`.
Finally, we use `LeftInvPart_SameHof` to conclude that the total contribution is the
binary expansion of the original multiplicity of `a` in `P`.
-/
theorem LeftInv {n : ℕ} (P : n.Partition) (P_odd : P ∈ odds n) :
    FromDist (FromOdd P) (InDist P P_odd) = P := by
  ext a
  simp only [FromDist, FromDist_parts, Multiset.count_sum']
  have hsubset : (FromOddPart P a).toFinset ⊆ (FromOdd P).parts.toFinset := by
    apply Multiset.toFinset_subset.mpr
    simp only [FromOdd, FromOdd_parts]
    apply Multiset.subset_of_le
    by_cases ha : a ∈ P.parts
    · exact Multiset.le_bind P.parts.dedup (Multiset.mem_dedup.mpr ha)
    · simp [Multiset.count_eq_zero_of_notMem ha, FromOddPart, binary]
  rw [← Finset.sum_subset hsubset (LeftInvPart_diff_hof P P_odd a)]
  rw [Finset.sum_congr rfl (Count_FromDistPart_eq_ordProj P P_odd a)]
  exact LeftInvPart_SameHof P P_odd a

/-- The sub multiset of a partition `Q` consisting of parts with the same `hof` value as `b`.
We will use `SameHof` to define `FromDistPartSameHof`.
It is related to `FromDistPart` and is important in the proof of `RightInv`. -/
def SameHof {n : ℕ} (Q : n.Partition) (b : ℕ) :
  Multiset ℕ := Multiset.filter (fun b' ↦ (hof b' = hof b)) Q.parts

lemma SameHof_subset {n : ℕ} (Q : n.Partition) (b : ℕ) :
  SameHof Q b ⊆ Q.parts := Multiset.filter_subset _ _

/-- The multiset consisting of `hof b` with multiplicity equal to the sum of `b' / hof(b')`
over all parts `b'` in `Q` with the same `hof` value as `b`. -/
def FromDistPartSameHof {n : ℕ} (Q : n.Partition) (b : ℕ) : Multiset ℕ :=
  Multiset.replicate (Multiset.map (fun b' ↦ ordProj[2] b') (SameHof Q b)).sum (hof b)

lemma FromDistPartSameHof_eq_Finset_sum {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n)
    (b : ℕ) : FromDistPartSameHof Q b = ∑ b' ∈ (SameHof Q b).toFinset, FromDistPart b' := by
  unfold FromDistPartSameHof FromDistPart
  have : ∀ b' ∈ (SameHof Q b).toFinset,
      Multiset.replicate (2 ^ b'.factorization 2) (hof b') =
      Multiset.replicate (2 ^ b'.factorization 2) (hof b) := by
    intro b' hb'
    simp only [SameHof, Multiset.toFinset_filter, Finset.mem_filter, Multiset.mem_toFinset] at hb'
    rw [hb'.2]
  rw [Finset.sum_congr rfl this]
  symm
  rw [Multiset.eq_replicate]
  constructor
  · simp only [Multiset.card_sum, Multiset.card_replicate]
    have : ∑ x ∈ (SameHof Q b).toFinset, ordProj[2] x =
      (Multiset.map (fun x ↦ ordProj[2] x) ((SameHof Q b).dedup)).sum := by rfl
    rw [this]
    have Q_Nodup : Q.parts.Nodup := by simpa [distincts] using Q_dist
    rw [SameHof]
    rw [Multiset.dedup_eq_self.mpr (Multiset.Nodup.filter _ Q_Nodup)]
  · intro b' hb'
    simp only [Multiset.mem_sum, Multiset.mem_toFinset] at hb'
    rcases hb' with ⟨i, hi, hb'⟩
    rw [Multiset.mem_replicate] at hb'
    exact hb'.2

lemma Count_FromDist_parts_eq_FromDistPartSameHof {n : ℕ}
    (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
    Multiset.count (hof b) (FromDist_parts Q)
  = Multiset.count (hof b) (FromDistPartSameHof Q b) := by
  rw [FromDist_parts, FromDistPartSameHof_eq_Finset_sum Q Q_dist]
  repeat rw [Multiset.count_sum']
  symm
  apply Finset.sum_subset (Multiset.toFinset_subset.mpr (SameHof_subset Q b)) _
  intro b' hb' hb''
  rw [Multiset.mem_toFinset] at *
  rw [FromDistPart, Multiset.count_replicate]
  simp only [ite_eq_right_iff, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_and, imp_false]
  simp only [SameHof, Multiset.mem_filter, not_and] at hb''
  exact hb'' hb'

/-- The multiset of exponents of 2 for parts in `Q` with the same `hof` value as `b`. -/
def SameHof_bitIndices {n : ℕ} (Q : n.Partition) (b : ℕ) : Multiset ℕ :=
  Multiset.map (fun b' ↦ b'.factorization 2) (SameHof Q b)

/-- The finite set of exponents of 2 for parts in `Q` with the same `hof` value as `b`.
Non-duplication is implied by `Q` being a distinct partition. -/
def SameHof_bitIndices_finset {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
    Finset ℕ :=
  { val := SameHof_bitIndices Q b
    nodup := by
      apply Multiset.Nodup.map_on
      · intro x hx y hy heq
        rw [← ordProj_mul_ordCompl_eq_self x 2, ← ordProj_mul_ordCompl_eq_self y 2]
        simp only [SameHof, hof, Multiset.mem_filter] at hx hy
        rw [hx.2, hy.2, heq]
      · apply Multiset.Nodup.filter
        simpa [distincts] using Q_dist }

/-- The sorted list of exponents of 2 for parts in `Q` with the same `hof` value as `b`. -/
def SameHof_bitIndices_list {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) : List ℕ :=
  Finset.sort (SameHof_bitIndices_finset Q Q_dist b)

lemma SameHof_count_eq_bitIndices {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
    (Multiset.count (hof b) (FromDistPartSameHof Q b)).bitIndices =
    SameHof_bitIndices_list Q Q_dist b := by
  simp only [FromDistPartSameHof, Multiset.count_replicate_self]
  have : Multiset.map (fun b' ↦ ordProj[2] b') (SameHof Q b) =
      List.map (fun i ↦ 2 ^ i) (SameHof_bitIndices_list Q Q_dist b) := by
    rw [SameHof_bitIndices_list, ← Multiset.map_coe, Finset.sort_eq]
    simp [SameHof_bitIndices_finset, SameHof_bitIndices]
  rw [this, Multiset.sum_coe]
  have sort : List.SortedLT (SameHof_bitIndices_list Q Q_dist b) := Finset.sortedLT_sort _
  exact bitIndices_twoPowsum sort

/-- This is a key lemma to prove `RightInv`. Important Ingredients are
 `Count_FromDist_parts_eq_FromDistPartSameHof` and `SameHof_count_eq_bitIndices`.
-/
lemma RightInvPart_same_hof {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
    (FromOddPart (FromDist Q Q_dist) (hof b)) = SameHof Q b := by
  rw [FromOddPart, FromDist, Count_FromDist_parts_eq_FromDistPartSameHof Q Q_dist b]
  rw [binary, SameHof_count_eq_bitIndices Q Q_dist b]
  simp only [SameHof_bitIndices_list, SameHof_bitIndices_finset, SameHof_bitIndices]
  simp only [Finset.sort_mk, ← Multiset.map_coe, Multiset.sort_eq]
  nth_rewrite 2 [Multiset.map_map]
  rw [Multiset.map_map]
  have SameHof_eq_composedMap :
      ∀ b' ∈ SameHof Q b,
        ((fun x ↦ x * hof b) ∘ (fun i ↦ 2 ^ i) ∘ (fun b'' ↦ b''.factorization 2)) b' =
        (fun b'' ↦ b'') b' := by
    intro b' hb'
    simp only [SameHof, Multiset.mem_filter] at hb'
    simp only [hof, Function.comp_apply] at *
    rw [← hb'.2]
    exact ordProj_mul_ordCompl_eq_self b' 2
  rw [Multiset.map_congr rfl SameHof_eq_composedMap]
  simp

lemma RightInvPart_diff_hof {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) (b : ℕ) :
    ∀ a ∈ (FromDist Q Q_dist).parts.toFinset,
      a ∉ (FromDistPartSameHof Q b).toFinset →
      Multiset.count b (FromOddPart (FromDist Q Q_dist) a) = 0 := by
  intro a ha a_not_in_hofb
  /- Show a = hof b' for some b' in Q -/
  simp only [Multiset.mem_toFinset] at ha
  have a_odd : Odd a := by
    have FromDist_Q_odd : FromDist Q Q_dist ∈ odds n := InOdd Q Q_dist
    simp only [odds, restricted, not_even_iff_odd, Finset.mem_filter, Finset.mem_univ,
      true_and] at FromDist_Q_odd
    exact FromDist_Q_odd a ha
  simp only [FromDist, FromDist_parts, Multiset.mem_sum, Multiset.mem_toFinset] at ha
  rcases ha with ⟨b', b'_in_Q, ha⟩
  simp only [FromDistPart, Multiset.mem_replicate, ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero,
    false_and, not_false_eq_true, true_and] at ha
  /- Assume for the sake of contradiction that count b ≠ 0; then b = 2 ^ i * a for some i. -/
  rw [Multiset.count_eq_zero]
  intro contra
  simp only [FromOddPart, Multiset.mem_map] at contra
  rcases contra with ⟨x, hx, contra⟩
  simp only [binary, Multiset.mem_coe, List.mem_map] at hx
  rcases hx with ⟨i, hi, hx⟩
  rw [← hx] at contra
  have a_eq_hofb : a = hof b := by
    rw [← contra, hof_two_pow_mul a i, (hof_eq_iff_zero_or_odd a).mpr (Or.inr a_odd)]
  simp only [FromDistPartSameHof, Multiset.toFinset_replicate] at a_not_in_hofb
  /- Prove by cases depending on `SameHof Q b is empty or not` -/
  by_cases h : (Multiset.map (fun b' ↦ ordProj[2] b') (SameHof Q b)).sum = 0
  · simp [h] at a_not_in_hofb
    rw [a_eq_hofb] at ha
    have b'_in_SameHof : b' ∈ SameHof Q b := by simpa [SameHof] using ⟨b'_in_Q, ha.symm⟩
    have eq_zero : ordProj[2] b' = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← h]
      exact Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun b' ↦ ordProj[2] b') b'_in_SameHof)
    have ne_zero : ordProj[2] b' ≠ 0 := Nat.pos_iff_ne_zero.mp (ordProj_pos b' 2)
    contradiction
  · simp [h] at a_not_in_hofb
    contradiction

/-- `FromDist` followed by `FromOdd` is the identity on distinct partitions.
Proof strategy : We compute the multiplicity of each integer `b` in `FromOdd FromDist Q`.
`FromDist` is a sum over parts `b` in `FromOdd P`.
Only parts `a` in the subset `FromDistPartSameHof Q b` of `FromOdd P` contribute to
the multiplicity of `b`.
This is proven in `RightInvPart_diff_hof`.
Such `a` has to be `hof b`, so instead of `FromOdd` we can consider only `FromOddPart hof b`.
The reduced case is then handled by `RightInvPart_same_hof`.
-/
theorem RightInv {n : ℕ} (Q : n.Partition) (Q_dist : Q ∈ distincts n) :
    FromOdd (FromDist Q Q_dist) = Q := by
  ext b
  simp only [FromOdd, FromOdd_parts]
  rw [← Finsetsum_eq_Bind]
  simp only [Multiset.count_sum']
  have hsubset : (FromDistPartSameHof Q b).toFinset ⊆ (FromDist Q Q_dist).parts.toFinset := by
    apply Multiset.toFinset_subset.mpr
    simp only [FromDist, FromDist_parts]
    apply Multiset.subset_of_le
    rw [FromDistPartSameHof_eq_Finset_sum Q Q_dist]
    apply Finset.sum_le_sum_of_subset
    exact Multiset.toFinset_subset.mpr (SameHof_subset Q b)
  rw [← Finset.sum_subset hsubset (RightInvPart_diff_hof Q Q_dist b)]
  /- Prove by cases depending on `SameHof Q b is empty or not` -/
  by_cases h : (Multiset.map (fun b' ↦ ordProj[2] b') (SameHof Q b)).sum = 0
  · simp only [FromDistPartSameHof, h, Multiset.replicate_zero, Multiset.toFinset_zero,
    Finset.sum_empty]
    rw [Multiset.count_eq_zero.mpr]
    intro b_in_Q
    have b_in_SameHof : b ∈ SameHof Q b := by simpa [SameHof] using b_in_Q
    have eq_zero : ordProj[2] b = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← h]
      exact Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun b' ↦ ordProj[2] b') b_in_SameHof)
    have ne_zero : ordProj[2] b ≠ 0 := Nat.pos_iff_ne_zero.mp (ordProj_pos b 2)
    contradiction
  · simp only [FromDistPartSameHof, Multiset.toFinset_replicate, h, ↓reduceIte,
    Finset.sum_singleton]
    rw [RightInvPart_same_hof Q Q_dist b]
    simp [SameHof]

/-- Euler's identity: The number of odd partitions of `n` equals
the number of distinct partitions of `n`. -/
theorem EulerIdentity (n : ℕ) : (odds n).card = (distincts n).card :=
  Finset.card_bij' (fun P _ ↦ FromOdd P) FromDist InDist InOdd LeftInv RightInv
