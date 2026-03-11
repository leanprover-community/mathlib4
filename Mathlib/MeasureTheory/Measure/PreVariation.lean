/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.Order.Partition.Finpartition

/-!
# Pre-variation of a subadditive set function

Given a σ-subadditive `ℝ≥0∞`-valued set function `f`, we define the pre-variation as the supremum
over finite measurable partitions of the sum of `f` on the parts. This construction yields a
measure.

## Main definitions

* `IsSigmaSubadditiveSetFun f` — `f` is σ-subadditive on measurable sets
* `ennrealPreVariation f` — the `VectorMeasure X ℝ≥0∞` built from a σ-subadditive function
* `preVariation f` — the `Measure X` built from a σ-subadditive function

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section

variable {X : Type*} [MeasurableSpace X]

open MeasureTheory BigOperators NNReal ENNReal Function

namespace MeasureTheory

/-!
## Pre-variation of a subadditive `ℝ≥0∞`-valued function

Given a set function `f : Set X → ℝ≥0∞` we can define another set function by taking the supremum
over all finite partitions of measurable sets `E i` of the sum of `∑ i, f (E i)`. If `f` is
σ-subadditive then the function defined is an `ℝ≥0∞`-valued measure.
-/

section

variable (f : Set X → ℝ≥0∞)

open Classical in
/-- If `s` is measurable then `preVariationFun f s` is the supremum over partitions `P` of `s` of
the quantity `∑ p ∈ P.parts, f p`. If `s` is not measurable then it is set to `0`. -/
noncomputable def preVariationFun (s : Set X) : ℝ≥0∞ :=
  if h : MeasurableSet s then
    ⨆ (P : Finpartition (⟨s, h⟩ : Subtype MeasurableSet)), ∑ p ∈ P.parts, f p
  else 0

end

namespace preVariation

variable (f : Set X → ℝ≥0∞)

/-- `preVariationFun` of the empty set is equal to zero. -/
lemma empty : preVariationFun f ∅ = 0 := by simp [preVariationFun]

@[simp]
lemma zero : preVariationFun (0 : Set X → ℝ≥0∞) = 0 := by ext; simp [preVariationFun]

lemma sum_le {s : Set X} (hs : MeasurableSet s)
    (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) :
    ∑ p ∈ P.parts, f p ≤ preVariationFun f s := by
  simpa [preVariationFun, hs, le_iSup_iff] using fun _ a ↦ a P

/-- A `Finpartition` constructor in the subtype of `MeasurableSet` from a `P : Finpartition s` with
explicit measurability assumptions. -/
noncomputable def _root_.Finpartition.toMeasurableSet {s : Set X} (P : Finpartition s)
    (hs : MeasurableSet s) (hP : ∀ p ∈ P.parts, MeasurableSet p) :
    Finpartition (⟨s, hs⟩ : Subtype MeasurableSet) :=
  letI : Fintype (Subtype (P.parts : Set (Set X))) := Fintype.subtype P.parts (by intro; rfl)
  { parts := Finset.image
      (fun p : (Subtype (P.parts : Set (Set X))) =>
        (⟨p.val, hP p.val p.property⟩ : Subtype MeasurableSet))
      Finset.univ
    supIndep := by
      have hPd := P.supIndep
      simp_all only [Finset.supIndep_iff_pairwiseDisjoint]
      intro u hu v hv h
      simp_all only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
        Subtype.exists, ne_eq]
      obtain ⟨a, hap, ha⟩ := hu
      obtain ⟨b, hbp, hb⟩ := hv
      have hab := hPd hap hbp (by simpa [← ha, ← hb, Subtype.mk.injEq] using h)
      simp only [disjoint_iff, ← ha, ← hb]
      simp_rw [disjoint_iff] at hab
      exact Subtype.ext hab
    sup_parts := by
      apply Subtype.ext
      ext x
      rw [Finset.sup_coe]
      · exact ⟨by intro h; simpa [← P.sup_parts] using h, by intro h; simpa [← P.sup_parts] using h⟩
      exact fun _ _ hx hy ↦ MeasurableSet.union hx hy
    bot_notMem := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      intro ⟨p, hp⟩
      apply P.bot_notMem
      rw [Subtype.mk_eq_bot_iff (by simp)] at hp
      rw [← hp]
      exact Finset.coe_mem p }

section

/-- If `pr` remains true for intersection and union, `Subtype Pr` carries the lattice structure. -/
abbrev instSubtypeLattice {X : Type*} (pr : Set X → Prop)
  (printer : ∀ s t, pr s → pr t → pr (s ⊓ t)) (prunion : ∀ s t, pr s → pr t → pr (s ⊔ t)) :
    Lattice (Subtype pr) where
  sup := fun ⟨s, hs⟩ ⟨t, ht⟩ => ⟨s ⊔ t, prunion s t hs ht⟩
  inf := fun ⟨s, hs⟩ ⟨t, ht⟩ => ⟨s ⊓ t, printer s t hs ht⟩
  le_sup_left := by simp
  le_sup_right := by simp
  sup_le a b c hac hbc := by
    intro x hx
    rcases hx with (hx | hx)
    · exact Set.mem_of_subset_of_mem hac hx
    · exact Set.mem_of_subset_of_mem hbc hx
  inf_le_left := by simp
  inf_le_right := by simp
  le_inf a b c hac hbc := by
    intro x hx
    exact ⟨hac hx, hbc hx⟩

/-- If `pr` remains true for intersection and union, `Subtype Pr` carries the distributive lattice
structure. -/
abbrev instSubtypeDistribLattice {X : Type*} (pr : Set X → Prop)
  (printer : ∀ s t, pr s → pr t → pr (s ⊓ t)) (prunion : ∀ s t, pr s → pr t → pr (s ⊔ t)) :
    DistribLattice (Subtype pr) :=
  { toLattice := instSubtypeLattice pr printer prunion
    le_sup_inf := by
      intro a b c x hx
      simp_all only
      rw [Subtype.coe_sup prunion]
      rw [Subtype.coe_inf printer] at hx
      simp only [Set.inf_eq_inter, Set.mem_inter_iff] at hx
      rcases hx.1 with hxa | hxb
      · left; exact hxa
      · rcases hx.2 with hxab | hxac
        · left; exact hxab
        · right
          rw [Subtype.coe_inf printer b c]
          simpa using ⟨hxb, hxac⟩ }

/-- A `Finpartition` constructor in `Subtype pr` for `pr : Set X → Prop` such that `pr` is closed
under intersection and union and `pr ⊥` holds from a `P : Finpartition s` with explicit assumptions
that `pr s` and `pr p` for each part `p`.
-/
noncomputable def _root_.Finpartition.toSubtype
  {X : Type*} {s : Set X} (P : Finpartition s)
  (pr : Set X → Prop) (printer : ∀ s t, pr s → pr t → pr (s ⊓ t))
  (prunion : ∀ s t, pr s → pr t → pr (s ⊔ t))
  (hbot : pr (⊥ : Set X))
  (hs : pr s) (hP : ∀ p ∈ P.parts, pr p) :
  @Finpartition (Subtype pr) (instSubtypeLattice pr printer prunion)
    (Subtype.orderBot hbot) ⟨s, hs⟩ :=
  letI : Fintype (Subtype (P.parts : Set (Set X))) := Fintype.subtype P.parts (by intro; rfl)
  letI : DistribLattice (Subtype pr) := instSubtypeDistribLattice pr printer prunion
  letI : OrderBot (Subtype pr) := Subtype.orderBot hbot
  { parts := Finset.image
      (fun p : (Subtype (P.parts : Set (Set X))) =>
        (⟨p.val, hP p.val p.property⟩ : Subtype pr))
      Finset.univ
    supIndep := by
      apply Finset.SupIndep.image
      simp only [CompTriple.comp_eq]
      have hPd := P.supIndep
      rw [Finset.supIndep_iff_pairwiseDisjoint]
      rw [Finset.supIndep_iff_pairwiseDisjoint] at hPd
      simp_all only [Finset.coe_univ]
      intro x hx y hy h
      refine disjoint_iff.mpr ?_
      simp only
      have hPd' := @Set.PairwiseDisjoint.eq_or_disjoint _ _ _ _ _ _ hPd x y (by simp) (by simp)
      have hxy : x.val ≠ y.val := by exact Subtype.coe_ne_coe.mpr h
      rcases hPd' with (hxy' | hxy')
      · exfalso; exact (iff_false_intro hxy).mp hxy'
      · apply disjoint_iff.mp
        intro a hax hay z hz
        simp_all only [Set.mem_univ, ne_eq, id_eq]
        exact Set.mem_of_subset_of_mem (hxy' hax hay) hz
    sup_parts := by
      apply Subtype.ext
      ext x
      rw [Finset.sup_coe]
      · exact ⟨by intro h; simpa [← P.sup_parts] using h, by intro h; simpa [← P.sup_parts] using h⟩
      exact fun s t hs ht ↦ prunion s t hs ht
    bot_notMem := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      intro ⟨p, hp⟩
      apply P.bot_notMem
      rw [Subtype.mk_eq_bot_iff hbot] at hp
      rw [← hp]
      exact Finset.coe_mem p }

end

lemma sum_eq_sum_finpartition_subtype {s : Set X} (hs : MeasurableSet s) (P : Finpartition s)
    (hP : ∀ p ∈ P.parts, MeasurableSet p) :
    ∑ p ∈ P.parts, f p = ∑ p ∈ (Finpartition.toMeasurableSet P hs hP).parts, f p := by
  apply Finset.sum_bij (fun p hpP => ⟨p, hP p hpP⟩)
  · intro _ ht; simpa [Finpartition.toMeasurableSet] using ht
  · intro _ _ _ _ h; simpa [Subtype.mk.injEq] using h
  · intro _ hp; simpa [Finpartition.toMeasurableSet] using hp
  · intro _ _; exact EReal.coe_ennreal_eq_coe_ennreal_iff.mp rfl

lemma sum_le' {s : Set X} (hs : MeasurableSet s)
    (P : Finpartition s) (hP : ∀ p ∈ P.parts, MeasurableSet p) :
    ∑ p ∈ P.parts, f p ≤ preVariationFun f s := by
  simp only [preVariationFun, hs, ↓reduceDIte]
  calc
    ∑ p ∈ P.parts, f p = ∑ p ∈ (Finpartition.toMeasurableSet P hs hP).parts, f p :=
        sum_eq_sum_finpartition_subtype f hs P hP
    _ ≤ ⨆ (Q : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)), ∑ p ∈ Q.parts, f p :=
        le_iSup (fun (Q : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) => ∑ p ∈ Q.parts, f p)
        (Finpartition.toMeasurableSet P hs hP)

/-- If `P` is a partition of `s₁` and `s₁ ⊆ s₂` then
`∑ p ∈ P.parts, f p ≤ preVariationFun f s₂`. -/
lemma sum_le_preVariationFun_of_subset {s₁ s₂ : Set X} (hs₁ : MeasurableSet s₁)
    (hs₂ : MeasurableSet s₂) (h : s₁ ⊆ s₂) (P : Finpartition (⟨s₁, hs₁⟩ : Subtype MeasurableSet)) :
    ∑ p ∈ P.parts, f p ≤ preVariationFun f s₂ := by
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
      _ ≤ preVariationFun f s₂ := sum_le f hs₂ _

/-- `preVariationFun` is monotone in terms of the (measurable) set. -/
lemma mono {s₁ s₂ : Set X} (hs₂ : MeasurableSet s₂) (h : s₁ ⊆ s₂) :
    preVariationFun f s₁ ≤ preVariationFun f s₂ := by
  by_cases hs₁ : MeasurableSet s₁
  · have := sum_le_preVariationFun_of_subset f hs₁ hs₂ h
    simp_all [preVariationFun]
  · simp [preVariationFun, hs₁]

lemma exists_Finpartition_sum_gt {s : Set X} (hs : MeasurableSet s) {a : ℝ≥0∞}
    (ha : a < preVariationFun f s) : ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
    a < ∑ p ∈ P.parts, f p := by
  simp_all [preVariationFun, lt_iSup_iff]

set_option backward.isDefEq.respectTransparency false in
lemma exists_Finpartition_sum_ge {s : Set X} (hs : MeasurableSet s) {ε : ℝ≥0} (hε : 0 < ε)
    (h : preVariationFun f s ≠ ⊤) :
    ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
    preVariationFun f s ≤ ∑ p ∈ P.parts, f p + ε := by
  let ε' := min ε (preVariationFun f s).toNNReal
  have hε' : ε' ≤ preVariationFun f s := by simp_all [ε']
  have : ε' ≤ ε := by simp_all [ε']
  obtain hw | hw : preVariationFun f s ≠ 0 ∨ preVariationFun f s = 0 := ne_or_eq _ _
  · have : 0 < ε' := by
      simp only [lt_inf_iff, ε']
      exact ⟨hε, toNNReal_pos hw h⟩
    let a := preVariationFun f s - ε'
    have ha : a < preVariationFun f s := ENNReal.sub_lt_self h hw (by positivity)
    obtain ⟨P, hP⟩ := exists_Finpartition_sum_gt f hs ha
    use P
    calc preVariationFun f s
      _ = a + ε' := (tsub_add_cancel_of_le hε').symm
      _ ≤ ∑ p ∈ P.parts, f p + ε' := by
        exact (ENNReal.add_le_add_iff_right coe_ne_top).mpr (le_of_lt hP)
      _ ≤ ∑ p ∈ P.parts, f p + ε := by gcongr
  · simp [*]

set_option backward.isDefEq.respectTransparency false in
/-- The sup of measurable set subtypes over a finset equals the biUnion of the underlying sets. -/
lemma Finset.sup_measurableSetSubtype_eq_biUnion {ι : Type*}
    (s : ι → Subtype (@MeasurableSet X _)) (I : Finset ι) :
    ((I.sup s : Subtype MeasurableSet) : Set X) = ⋃ i ∈ I, (s i).val := by
  classical
  refine I.induction_on (by simp) ?_
  intro _ _ _ h
  simp [← h]

lemma sum_le_preVariationFun_iUnion' {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s))
    (P : ∀ (i : ℕ), Finpartition (⟨s i, hs i⟩ : Subtype MeasurableSet)) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p ≤ preVariationFun f (⋃ i, s i) := by
  let s' (i : ℕ) : Subtype MeasurableSet := ⟨s i, hs i⟩
  have hs_disj : Set.PairwiseDisjoint (Finset.range n : Set ℕ) s' := fun i _ j _ hij => by
    simp only [Function.onFun, disjoint_iff, Subtype.ext_iff]
    exact Set.disjoint_iff_inter_eq_empty.mp (hs' hij)
  let Q := Finpartition.combine P hs_disj.supIndep
  have hQ_le : (Finset.range n).sup s' ≤ ⟨⋃ i, s i, MeasurableSet.iUnion hs⟩ := by
    rw [← Subtype.coe_le_coe, Finset.sup_measurableSetSubtype_eq_biUnion s']
    exact Set.iUnion₂_subset fun i _ => Set.subset_iUnion s i
  let R := Q.extendOfLE hQ_le
  calc ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p
    _ = ∑ p ∈ Q.parts, f p := (Finpartition.sum_combine P hs_disj.supIndep (fun p => f p)).symm
    _ ≤ ∑ p ∈ R.parts, f p := Finset.sum_le_sum_of_subset (Q.parts_subset_extendOfLE hQ_le)
    _ ≤ preVariationFun f (⋃ i, s i) := sum_le f (MeasurableSet.iUnion hs) R

lemma sum_le_preVariationFun_iUnion {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) :
    ∑' i, preVariationFun f (s i) ≤ preVariationFun f (⋃ i, s i) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  by_cases hn : n = 0
  · simp [hn]
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' hsnetop ↦ ?_
  let ε := ε' / n
  have hε : 0 < ε := by positivity
  have hs'' i : preVariationFun f (s i) ≠ ⊤ := lt_top_iff_ne_top.mp <|
    (mono f (MeasurableSet.iUnion hs) (Set.subset_iUnion s i)).trans_lt hsnetop
  -- For each set `s i` we choose a Finpartition `P i` such that, for each `i`,
  -- `preVariationFun f (s i) ≤ ∑ p ∈ (P i), f p + ε`.
  choose P hP using fun i ↦ exists_Finpartition_sum_ge f (hs i) (hε) (hs'' i)
  calc ∑ i ∈ Finset.range n, preVariationFun f (s i)
    _ ≤ ∑ i ∈ Finset.range n, (∑ p ∈ (P i).parts, f p + ε) := Finset.sum_le_sum fun i _ => hP i
    _ = ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p + ε' := by
      rw [Finset.sum_add_distrib]; norm_cast
      simp [show n * ε = ε' by simpa using mul_div_cancel₀ ε' (Nat.cast_ne_zero.mpr hn)]
    _ ≤ preVariationFun f (⋃ i, s i) + ε' := by
      gcongr; exact sum_le_preVariationFun_iUnion' f hs hs' P n

end preVariation

/-- A set function is σ-subadditive on measurable sets if the value assigned to the union of a
countable disjoint family of measurable sets is bounded above by the sum of values on the family. -/
def IsSigmaSubadditiveSetFun (f : Set X → ℝ≥0∞) : Prop :=
  ∀ (s : ℕ → {t : Set X // MeasurableSet t}), Pairwise (Disjoint on (Subtype.val ∘ s)) →
    f (⋃ i, (s i).val) ≤ ∑' i, f (s i)

lemma isSigmaSubadditiveSetFun_zero : IsSigmaSubadditiveSetFun (0 : Set X → ℝ≥0∞) := by intro; simp

namespace preVariation

variable {f : Set X → ℝ≥0∞}

/-- Additivity of `preVariationFun` for disjoint measurable sets. -/
lemma iUnion (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : ℕ → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) :
    HasSum (fun i ↦ preVariationFun f (s i)) (preVariationFun f (⋃ i, s i)) := by
  refine ENNReal.summable.hasSum_iff.mpr (le_antisymm (sum_le_preVariationFun_iUnion f hs hs') ?_)
  refine ENNReal.le_tsum_of_forall_lt_exists_sum fun b hb ↦ ?_
  simp only [preVariationFun, MeasurableSet.iUnion hs, reduceDIte, lt_iSup_iff] at hb
  obtain ⟨Q, hQ⟩ := hb
  let s' (i : ℕ) : Subtype MeasurableSet := ⟨s i, hs i⟩
  let P (i : ℕ) := Q.restrict (b := s' i) (Set.subset_iUnion s i)
  have splitting : ∑ q ∈ Q.parts, f q ≤ ∑' i, ∑ p ∈ (P i).parts, f p := by
    calc ∑ q ∈ Q.parts, f q
      _ ≤ ∑ q ∈ Q.parts, ∑' i, f (q ⊓ s' i) := by
          apply Finset.sum_le_sum fun q hq => ?_
          have hq_eq : q.val = ⋃ i, q.val ∩ s i := by
            rw [← Set.inter_iUnion]; exact (Set.inter_eq_left.mpr (Q.le hq)).symm
          let t (i : ℕ) : Subtype MeasurableSet := ⟨q.val ∩ s i, q.2.inter (hs i)⟩
          have ht_disj : Pairwise (Disjoint on (Subtype.val ∘ t)) :=
            fun i j hij => (hs' hij).mono Set.inter_subset_right Set.inter_subset_right
          calc f q
            _ = f (⋃ i, q.val ∩ s i) := congrArg f hq_eq
            _ = f (⋃ i, (t i).val) := rfl
            _ ≤ ∑' i, f (t i) := hf t ht_disj
            _ = ∑' i, f (q ⊓ s' i) := rfl
      _ = ∑' i, ∑ q ∈ Q.parts, f (q ⊓ s' i) :=
          (Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)).symm
      _ = ∑' i, ∑ p ∈ (P i).parts, f p := by
          congr 1; funext i
          exact (Q.sum_restrict _ (fun p => f p) hf').symm
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp <| ENNReal.tsum_eq_iSup_nat ▸ lt_of_lt_of_le hQ splitting
  have bound (i : ℕ) : ∑ p ∈ (P i).parts, f p ≤ preVariationFun f (s i) := sum_le f (hs i) (P i)
  exact ⟨Finset.range n, lt_of_lt_of_le hn (Finset.sum_le_sum fun i _ => bound i)⟩

end preVariation

/-!
## Construction of measures from σ-subadditive functions
-/

variable (f : Set X → ℝ≥0∞)

/-- The `VectorMeasure X ℝ≥0∞` built from a σ-subadditive function. -/
noncomputable def ennrealPreVariation (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) :
    VectorMeasure X ℝ≥0∞ where
  measureOf' := preVariationFun f
  empty' := preVariation.empty f
  not_measurable' _ h := by simp [preVariationFun, h]
  m_iUnion' := preVariation.iUnion hf hf'

lemma ennrealPreVariation_apply (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : Set X) :
  ennrealPreVariation f hf hf' s = preVariationFun f s := rfl

@[simp]
lemma ennrealPreVariation_zero :
    ennrealPreVariation (0 : Set X → ℝ≥0∞) (isSigmaSubadditiveSetFun_zero) (by simp) = 0 := by
  ext; simp [ennrealPreVariation_apply]

/-- The `Measure X` built from a σ-subadditive function. -/
noncomputable def preVariation (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) : Measure X :=
  (ennrealPreVariation f hf hf').ennrealToMeasure

lemma preVariation_apply (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : Set X) :
    preVariation f hf hf' s = (ennrealPreVariation f hf hf').ennrealToMeasure s := rfl

@[simp]
theorem VectorMeasure.ennrealToMeasure_zero {α : Type*} {m : MeasurableSpace α} :
    MeasureTheory.VectorMeasure.ennrealToMeasure (0 : VectorMeasure α ℝ≥0∞) = 0 := by
  ext s; simp [VectorMeasure.ennrealToMeasure]

@[simp]
lemma preVariation_zero_eq_zero :
    preVariation (0 : Set X → ℝ≥0∞) (isSigmaSubadditiveSetFun_zero) (by simp) = 0 := by
  ext s; simp [preVariation_apply]

end MeasureTheory
