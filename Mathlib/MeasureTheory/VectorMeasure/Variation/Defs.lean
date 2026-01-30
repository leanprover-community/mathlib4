/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.Order.Partition.Finpartition

/-!
# Total variation for vector-valued measures

This file contains the definition of variation for any `VectorMeasure` in an `ENormedAddCommMonoid`,
in particular, any `NormedAddCommGroup`.

Given a vector-valued measure `μ` we consider the problem of finding a countably additive function
`f` such that, for any set `E`, `‖μ(E)‖ ≤ f(E)`. This suggests defining `f(E)` as the supremum over
partitions `{Eᵢ}` of `E`, of the quantity `∑ᵢ, ‖μ(Eᵢ)‖`. Indeed any solution of the problem must be
not less than this function. It turns out that this function is a measure.

## Main definition

* `VectorMeasure.variation` is the definition of the total variation measure.

## Implementation notes

Variation is defined as an `ℝ≥0∞`-valued `VectorMeasure` rather than as a `Measure`, this is
somewhat natural since we start with `VectorMeasure`. This quantity is called
`VectorMeasure.ennrealVariation` and the corresponding `Measure`, given by
`VectorMeasure.ennrealToMeasure`, is called `VectorMeasure.ennrealVariation`.

Variation is defined for signed measures in `MeasureTheory.SignedMeasure.totalVariation`. This
definition uses the Hahn–Jordan decomposition of a signed measure. However this construction doesn't
generalize to other vector-valued measures, in particular doesn't apply to the case of complex
measures.

The notion of defining a set function as the supremum over all choices of partition of the sum gives
a measure for any subadditive set function which assigns zero measure to the empty set. Consequently
the construction is first developed for any subadditive set function before specializing to the case
of `s ↦ ‖μ s‖ₑ`.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section

/-!
### To be moved to Order/Partition/Finpartition
-/

namespace Finpartition

/-- Extend a partition of `a` to a partition of `b` when `a ≤ b`, by adding `b \ a` as a `part`. -/
def extendOfLE {α : Type*} [GeneralizedBooleanAlgebra α]
    [DecidableEq α] {a b : α} (P : Finpartition a) (hab : a ≤ b) : Finpartition b :=
  if hr : b \ a = ⊥ then (le_antisymm (sdiff_eq_bot_iff.mp hr) hab) ▸ P
    else P.extend hr disjoint_sdiff_self_right (sup_sdiff_cancel_right hab)

-- We don't need the following here but perhaps it is good to add this with the new def?
lemma parts_extendOfLE_of_eq {α : Type*} [GeneralizedBooleanAlgebra α]
    [DecidableEq α] {a : α} (P : Finpartition a) :
    (P.extendOfLE (a := a) (b := a) (by rfl)).parts = P.parts := by simp [extendOfLE]

-- We don't need the following here but perhaps it is good to add this with the new def?
lemma parts_extendOfLE_of_lt {α : Type*} [GeneralizedBooleanAlgebra α]
    [DecidableEq α] {a b : α} (P : Finpartition a) (hab : a < b) :
    (P.extendOfLE (le_of_lt hab)).parts = insert (b \ a) P.parts := by
  simp [extendOfLE, Std.not_le_of_gt hab]

lemma parts_subset_extendOfLE {α : Type*} [GeneralizedBooleanAlgebra α]
    [DecidableEq α] {a b : α} (P : Finpartition a) (hab : a ≤ b) :
    P.parts ⊆ (P.extendOfLE hab).parts := by
  simp only [Finpartition.extendOfLE]
  split_ifs with hr
  · cases le_antisymm (sdiff_eq_bot_iff.mp hr) hab; rfl
  · exact Finset.subset_insert _ _

-- Added this definition since it seemed the useful thing but currently this is not used here
/-- Construct a `Finpartition` of `T.sup id` from a finset `T` of pairwise disjoint elements.
Any `⊥` elements in `T` are erased. -/
@[simps]
def ofPairwiseDisjoint {α : Type*} [DistribLattice α] [OrderBot α] [DecidableEq α] (T : Finset α)
    (hT : (T : Set α).PairwiseDisjoint id) : Finpartition (T.sup id) where
  parts := T.erase ⊥
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr fun _ ha _ hb hab =>
    hT (Finset.erase_subset _ _ ha) (Finset.erase_subset _ _ hb) hab
  sup_parts := Finset.sup_erase_bot T
  bot_notMem := Finset.notMem_erase _ _

-- Despite being similar to `Finpartition.bind` this is much more convenient. Better name?
/-- Merge a family of partitions of pairwise disjoint elements into a partition of their sup.
Similar to `Finpartition.bind`, but combines partitions of different elements rather than
refining a single partition. -/
def biUnion {ι α : Type*} [DistribLattice α] [OrderBot α] [DecidableEq α]
    {I : Finset ι} {a : ι → α} (P : ∀ i, Finpartition (a i))
    (ha : Set.PairwiseDisjoint (I : Set ι) a) : Finpartition (I.sup a) where
  parts := I.biUnion fun i => (P i).parts
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr fun x hx y hy hxy => by
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at hx hy
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨j, hj, hyj⟩ := hy
    by_cases hij : i = j
    · subst hij; exact (P i).disjoint hxi hyj fun h => hxy (h ▸ rfl)
    · exact (ha hi hj hij).mono ((P i).le hxi) ((P j).le hyj)
  sup_parts := by
    rw [Finset.sup_biUnion]
    exact Finset.sup_congr rfl fun i _ => (P i).sup_parts
  bot_notMem := by
    rw [Finset.mem_biUnion]; push_neg; exact fun i _ => (P i).bot_notMem

/-- The sum over a merged partition equals the sum of sums over component partitions. -/
lemma sum_biUnion {ι α : Type*} [DistribLattice α] [OrderBot α] [DecidableEq α]
    {I : Finset ι} {a : ι → α} (P : ∀ i, Finpartition (a i))
    (ha : Set.PairwiseDisjoint (I : Set ι) a) {M : Type*} [AddCommMonoid M] (f : α → M) :
    ∑ p ∈ (Finpartition.biUnion P ha).parts, f p = ∑ i ∈ I, ∑ p ∈ (P i).parts, f p := by
  change ∑ p ∈ I.biUnion (fun i => (P i).parts), f p = _
  refine Finset.sum_biUnion fun i hi j hj hij => ?_
  rw [Function.onFun, Finset.disjoint_left]
  intro p hpi hpj
  have hp_disj : Disjoint p p := (ha hi hj hij).mono ((P i).le hpi) ((P j).le hpj)
  exact (P i).ne_bot hpi (disjoint_self.mp hp_disj)

/-- Restrict a partition of `a` to a sub-element `b ≤ a` by intersecting each part with `b`. -/
def restrict {α : Type*} [DistribLattice α] [OrderBot α] [DecidableEq α]
    {a : α} (P : Finpartition a) (b : α) (hb : b ≤ a) : Finpartition b where
  parts := (P.parts.image (· ⊓ b)).erase ⊥
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr fun x hx y hy hxy => by
    simp only [Finset.coe_erase, Finset.coe_image, Set.mem_diff, Set.mem_image,
      Set.mem_singleton_iff] at hx hy
    obtain ⟨⟨px, hpx, rfl⟩, _⟩ := hx
    obtain ⟨⟨py, hpy, rfl⟩, _⟩ := hy
    simpa [Function.onFun, id_eq]
      using (P.disjoint hpx hpy fun h => hxy (h ▸ rfl)).mono inf_le_left inf_le_left
  sup_parts := by
    simp only [Finset.sup_erase_bot, Finset.sup_image, Function.id_comp,
      (Finset.sup_inf_distrib_right ..).symm]
    have : P.parts.sup (fun x => x) = a := P.sup_parts
    rw [this, inf_eq_right.mpr hb]
  bot_notMem := Finset.notMem_erase _ _

/-- The sum over restricted partition parts equals the sum over original parts with `f (· ⊓ b)`,
provided `f ⊥ = 0` (so bottom terms don't contribute). -/
lemma sum_restrict {α : Type*} [DistribLattice α] [OrderBot α] [DecidableEq α]
    {a : α} (P : Finpartition a) {b : α} (hb : b ≤ a) {M : Type*} [AddCommMonoid M]
    (f : α → M) (hf : f ⊥ = 0) :
    ∑ p ∈ (P.restrict b hb).parts, f p = ∑ q ∈ P.parts, f (q ⊓ b) := by
  have hinj : ∀ x ∈ P.parts.filter (· ⊓ b ≠ ⊥), ∀ y ∈ P.parts.filter (· ⊓ b ≠ ⊥),
      x ⊓ b = y ⊓ b → x = y := fun x hx y hy hxy => by
    simp only [Finset.mem_filter] at hx hy
    by_contra hne
    have hdisj : Disjoint (x ⊓ b) (y ⊓ b) := (P.disjoint hx.1 hy.1 hne).mono inf_le_left inf_le_left
    rw [hxy] at hdisj
    exact hy.2 (disjoint_self.mp hdisj)
  have heq : (P.parts.image (· ⊓ b)).erase ⊥ = (P.parts.filter (· ⊓ b ≠ ⊥)).image (· ⊓ b) := by
    ext p; simp only [Finset.mem_erase, ne_eq, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨hp, q, hq, rfl⟩; exact ⟨q, ⟨hq, hp⟩, rfl⟩
    · rintro ⟨q, ⟨hq, hp⟩, rfl⟩; exact ⟨hp, q, hq, rfl⟩
  have hz : ∑ x ∈ P.parts.filter (¬ · ⊓ b ≠ ⊥), f (x ⊓ b) = 0 := Finset.sum_eq_zero fun x hx => by
    simp only [ne_eq, Decidable.not_not, Finset.mem_filter] at hx
    rw [hx.2, hf]
  simp only [restrict, heq, ← Finset.sum_filter_add_sum_filter_not P.parts (· ⊓ b ≠ ⊥), hz,
    Finset.sum_image hinj, add_zero]

end Finpartition

variable {X : Type*} [MeasurableSpace X]

open MeasureTheory BigOperators ENNReal Function

namespace MeasureTheory

/-!
## Variation of a subadditive `ℝ≥0∞`-valued function

Given a set function `f : Set X → ℝ≥0∞` we can define another set function by taking the supremum
over all partitions `E i` of the sum of `∑ i, f (E i)`. If `f` is sub-additive then the function
defined is an `ℝ≥0∞`-valued measure.
-/

section

variable (f : Set X → ℝ≥0∞)

open Classical in
/-- If `s` is measurable then `preVariation s f` is the supremum over partitions `P` of `s` of the
quantity `∑ p ∈ P.parts, f p`. If `s` is not measurable then it is set to `0`. -/
noncomputable def preVariation (s : Set X) : ℝ≥0∞ :=
  if h : MeasurableSet s then
    ⨆ (P : Finpartition (⟨s, h⟩ : Subtype MeasurableSet)), ∑ p ∈ P.parts, f p
    else 0

end

namespace VectorMeasure.preVariation

variable (f : Set X → ℝ≥0∞)

/-- `preVariation` of the empty set is equal to zero. -/
lemma empty : preVariation f ∅ = 0 := by simp [preVariation]

lemma sum_le {s : Set X} (hs : MeasurableSet s)
    (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) :
    ∑ p ∈ P.parts, f p ≤ preVariation f s := by
  simpa [preVariation, hs, le_iSup_iff] using fun _ a ↦ a P

open Classical in
/-- If `P` is a partition of `s₁` and `s₁ ⊆ s₂` then `∑ p ∈ P.parts, f p ≤ preVariation f s₂`. -/
lemma sum_le_preVariation_of_subset {s₁ s₂ : Set X} (hs₁ : MeasurableSet s₁)
    (hs₂ : MeasurableSet s₂) (h : s₁ ⊆ s₂) (P : Finpartition (⟨s₁, hs₁⟩ : Subtype MeasurableSet)) :
    ∑ p ∈ P.parts, f p ≤ preVariation f s₂ := by
  by_cases heq : s₁ = s₂
  · rw [← heq]; exact sum_le f hs₁ P
  · let b : Subtype MeasurableSet := ⟨s₂ \ s₁, hs₂.diff hs₁⟩
    have hb : b ≠ ⊥ := fun hc => heq (h.antisymm (Set.diff_eq_empty.mp (congrArg (·.1) hc)))
    have hab : Disjoint (⟨s₁, hs₁⟩ : Subtype MeasurableSet) b := by
      simp only [b, disjoint_iff, Subtype.ext_iff]
      exact Set.inter_diff_self s₁ s₂
    have hc : (⟨s₁, hs₁⟩ : Subtype MeasurableSet) ⊔ b = ⟨s₂, hs₂⟩ :=
      Subtype.ext (Set.union_diff_cancel h)
    calc ∑ p ∈ P.parts, f p
      _ ≤ ∑ p ∈ (P.extend hb hab hc).parts, f p :=
          Finset.sum_le_sum_of_subset fun _ hx => Finset.mem_insert_of_mem hx
      _ ≤ preVariation f s₂ := sum_le f hs₂ _

/-- `preVariation` is monotone in terms of the (measurable) set. -/
lemma mono {s₁ s₂ : Set X} (hs₂ : MeasurableSet s₂) (h : s₁ ⊆ s₂) :
    preVariation f s₁ ≤ preVariation f s₂ := by
  by_cases hs₁ : MeasurableSet s₁
  · have := sum_le_preVariation_of_subset f hs₁ hs₂ h
    simp_all [preVariation]
  · simp [preVariation, hs₁]

lemma exists_Finpartition_sum_gt {s : Set X} (hs : MeasurableSet s) {a : ℝ≥0∞}
    (ha : a < preVariation f s) : ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
    a < ∑ p ∈ P.parts, f p := by
  simp_all [preVariation, lt_iSup_iff]

lemma exists_Finpartition_sum_ge {s : Set X} (hs : MeasurableSet s) {ε : NNReal} (hε : 0 < ε)
    (h : preVariation f s ≠ ⊤) :
    ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
    preVariation f s ≤ ∑ p ∈ P.parts, f p + ε := by
  let ε' := min ε (preVariation f s).toNNReal
  have hε' : ε' ≤ preVariation f s := by simp_all [ε']
  have : ε' ≤ ε := by simp_all [ε']
  obtain hw | hw : preVariation f s ≠ 0 ∨ preVariation f s = 0 := ne_or_eq _ _
  · have : 0 < ε' := by
      simp only [lt_inf_iff, ε']
      exact ⟨hε, toNNReal_pos hw h⟩
    let a := preVariation f s - ε'
    have ha : a < preVariation f s := ENNReal.sub_lt_self h hw (by positivity)
    obtain ⟨P, hP⟩ := exists_Finpartition_sum_gt f hs ha
    use P
    calc preVariation f s
      _ = a + ε' := (tsub_add_cancel_of_le hε').symm
      _ ≤ ∑ p ∈ P.parts, f p + ε' := by
        exact (ENNReal.add_le_add_iff_right coe_ne_top).mpr (le_of_lt hP)
      _ ≤ ∑ p ∈ P.parts, f p + ε := by gcongr
  · simp [*]

-- Perhaps goes in MeasurableSpace.Basic? Or just a private helper here?
open Classical in
/-- The sup of measurable set subtypes over a finset equals the biUnion of the underlying sets. -/
lemma Finset.sup_measurableSetSubtype_eq_biUnion {ι : Type*}
    (s : ι → Subtype (@MeasurableSet X _)) (I : Finset ι) :
    ((I.sup s : Subtype MeasurableSet) : Set X) = ⋃ i ∈ I, (s i).val := by
  refine I.induction_on (by simp) ?_
  intro _ _ _ h
  simp [← h]

open Classical in
lemma sum_le_preVariation_iUnion' {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s))
    (P : ∀ (i : ℕ), Finpartition (⟨s i, hs i⟩ : Subtype MeasurableSet)) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p ≤ preVariation f (⋃ i, s i) := by
  let s' (i : ℕ) : Subtype MeasurableSet := ⟨s i, hs i⟩
  have hs_disj : Set.PairwiseDisjoint (Finset.range n : Set ℕ) s' := fun i _ j _ hij => by
    simp only [Function.onFun, disjoint_iff, Subtype.ext_iff]
    exact Set.disjoint_iff_inter_eq_empty.mp (hs' hij)
  let Q := Finpartition.biUnion P hs_disj
  have hQ_le : (Finset.range n).sup s' ≤ ⟨⋃ i, s i, MeasurableSet.iUnion hs⟩ := by
    rw [← Subtype.coe_le_coe, Finset.sup_measurableSetSubtype_eq_biUnion s']
    exact Set.iUnion₂_subset fun i _ => Set.subset_iUnion s i
  let R := Q.extendOfLE hQ_le
  calc ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p
    _ = ∑ p ∈ Q.parts, f p := (Finpartition.sum_biUnion P hs_disj (fun p => f p)).symm
    _ ≤ ∑ p ∈ R.parts, f p := Finset.sum_le_sum_of_subset (Q.parts_subset_extendOfLE hQ_le)
    _ ≤ preVariation f (⋃ i, s i) := sum_le f (MeasurableSet.iUnion hs) R

lemma sum_le_preVariation_iUnion {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) :
    ∑' i, preVariation f (s i) ≤ preVariation f (⋃ i, s i) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  wlog hn : n ≠ 0
  · simp [show n = 0 by omega]
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' hsnetop ↦ ?_
  let ε := ε' / n
  have hε : 0 < ε := by positivity
  have hs'' i : preVariation f (s i) ≠ ⊤ := lt_top_iff_ne_top.mp <|
    (mono f (MeasurableSet.iUnion hs) (Set.subset_iUnion s i)).trans_lt hsnetop
  -- For each set `s i` we choose a Finpartition `P i` such that, for each `i`,
  -- `preVariation f (s i) ≤ ∑ p ∈ (P i), f p + ε`.
  choose P hP using fun i ↦ exists_Finpartition_sum_ge f (hs i) (hε) (hs'' i)
  calc ∑ i ∈ Finset.range n, preVariation f (s i)
    _ ≤ ∑ i ∈ Finset.range n, (∑ p ∈ (P i).parts, f p + ε) := Finset.sum_le_sum fun i _ => hP i
    _ = ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p + ε' := by
      rw [Finset.sum_add_distrib]; norm_cast
      simp [show n * ε = ε' by rw [mul_div_cancel₀ _ (by positivity)]]
    _ ≤ preVariation f (⋃ i, s i) + ε' := by gcongr; exact sum_le_preVariation_iUnion' f hs hs' P n

-- Perhaps this should be called `IsCountablySubadditiveOnDisjoint`?
-- Or is this a common notion that belongs somewhere else?
-- Mathlib has `AddContent.IsSigmaSubadditive` but we don't have an `AddContent` here with `‖μ ·‖ₑ`.
/-- A set function is subadditive if the value assigned to the union of disjoint sets is bounded
above by the sum of the values assigned to the individual sets. -/
def IsSubadditive (f : Set X → ℝ≥0∞) : Prop := ∀ (s : ℕ → Set X), (∀ i, MeasurableSet (s i)) →
  Pairwise (Disjoint on s) → f (⋃ (i : ℕ), s i) ≤ ∑' (i : ℕ), f (s i)

-- This is strictly weaker than `iUnion` and so shouldn't be public or could be inlined in `iUnion`
open Classical in
lemma iUnion_le {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) (hf : IsSubadditive f) (hf' : f ∅ = 0) :
    preVariation f (⋃ i, s i) ≤ ∑' i, preVariation f (s i) := by
  refine ENNReal.le_tsum_of_forall_lt_exists_sum fun b hb ↦ ?_
  simp only [preVariation, MeasurableSet.iUnion hs, reduceDIte, lt_iSup_iff] at hb
  obtain ⟨Q, hQ⟩ := hb
  let s' (i : ℕ) : Subtype MeasurableSet := ⟨s i, hs i⟩
  let P (i : ℕ) := Q.restrict (s' i) (Set.subset_iUnion s i)
  have splitting : ∑ q ∈ Q.parts, f q ≤ ∑' i, ∑ p ∈ (P i).parts, f p := by
    calc ∑ q ∈ Q.parts, f q
      _ ≤ ∑ q ∈ Q.parts, ∑' i, f (q ⊓ s' i) := by
          apply Finset.sum_le_sum fun q hq => ?_
          have hq_eq : q.val = ⋃ i, q.val ∩ s i := by
            rw [← Set.inter_iUnion]; exact (Set.inter_eq_left.mpr (Q.le hq)).symm
          have hq_disj : Pairwise (Disjoint on fun i => q.val ∩ s i) :=
            fun i j hij => (hs' hij).mono Set.inter_subset_right Set.inter_subset_right
          calc f q
            _ = f (⋃ i, q.val ∩ s i) := congrArg f hq_eq
            _ ≤ ∑' i, f (q.val ∩ s i) := hf _ (q.2.inter <| hs ·) hq_disj
            _ = ∑' i, f (q ⊓ s' i) := rfl
      _ = ∑' i, ∑ q ∈ Q.parts, f (q ⊓ s' i) :=
          (Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)).symm
      _ = ∑' i, ∑ p ∈ (P i).parts, f p := by
          congr 1; funext i
          exact (Q.sum_restrict _ (fun p => f p) hf').symm
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp <| ENNReal.tsum_eq_iSup_nat ▸ lt_of_lt_of_le hQ splitting
  have bound (i : ℕ) : ∑ p ∈ (P i).parts, f p ≤ preVariation f (s i) := sum_le f (hs i) (P i)
  exact ⟨Finset.range n, lt_of_lt_of_le hn (Finset.sum_le_sum fun i _ => bound i)⟩

/-- Additivity of `preVariation` for disjoint measurable sets. -/
lemma iUnion (hf : IsSubadditive f) (hf' : f ∅ = 0) (s : ℕ → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) :
    HasSum (fun i ↦ preVariation f (s i)) (preVariation f (⋃ i, s i)) := by
  refine ENNReal.summable.hasSum_iff.mpr (eq_of_le_of_ge ?_ ?_)
  · exact sum_le_preVariation_iUnion f hs hs'
  · exact iUnion_le f hs hs' hf hf'

end VectorMeasure.preVariation

/-!
## Definition of variation
-/

namespace VectorMeasure

open MeasureTheory.VectorMeasure preVariation

variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

lemma isSubadditive_enorm_vectorMeasure (μ : VectorMeasure X V) : IsSubadditive (‖μ ·‖ₑ) := by
  intro _ hs hs'
  simpa [VectorMeasure.of_disjoint_iUnion hs hs'] using enorm_tsum_le_tsum_enorm

/-- The variation of a `VectorMeasure` as an `ℝ≥0∞`-valued `VectorMeasure`. -/
noncomputable def ennrealVariation (μ : VectorMeasure X V) : VectorMeasure X ℝ≥0∞ where
  measureOf' := preVariation (‖μ ·‖ₑ)
  empty' := preVariation.empty (‖μ ·‖ₑ)
  not_measurable' _ h := by simp [preVariation, h]
  m_iUnion' := iUnion (‖μ ·‖ₑ) (isSubadditive_enorm_vectorMeasure μ) (by simp)

/-- The variation of a `VectorMeasure` as a `Measure`. -/
noncomputable def variation (μ : VectorMeasure X V) : Measure X
  := (ennrealVariation μ).ennrealToMeasure

end VectorMeasure

end MeasureTheory
