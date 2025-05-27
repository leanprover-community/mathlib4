import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Complex

-- set_option linter.flexible true

/-!
# Riesz–Markov–Kakutani representation theorem for complex linear functionals


## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

## To do

Availability of other theorems used in the proof:
- 3.14: compactly supported continuous functions are dense in `L^p`
(depends on 3.13 `MeasureTheory.Lp.simpleFunc.isDenseEmbedding`, this is written only for
`NormalSpace α` and approximation given by bounded functions)
- 6.12: polar decomposition of a complex measure
(the Jordan decomposition `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition` is
available for `SignedMeasure`. need to write it as a `rnDeriv`, and make it also for
`ComplexMeasure`)
- 6.13: total variation (`MeasureTheory.SignedMeasure.totalVariation`) is equal to integral (short
proof which depends on 6.12)
- 6.16: Duality of `L^1` and `L^∞` (not in Mathlib [https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Lp.20duality/near/495207025])
-/

section CompleteLinearOrder

variable {α : Type*}{ι : Type*} [CompleteLinearOrder α] {s : Set α} {a b : α}

theorem lt_biSup_iff {s : Set ι} {f : ι → α} : a < ⨆ i ∈ s, f i ↔ ∃ i ∈ s, a < f i := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := lt_iSup_iff.mp h
    obtain ⟨his, ha⟩ := lt_iSup_iff.mp hi
    exact ⟨i, ⟨his, ha⟩⟩
  · intro h
    obtain ⟨i, hi⟩ := h
    apply lt_iSup_iff.mpr
    use i
    apply lt_iSup_iff.mpr
    simpa [exists_prop]

end CompleteLinearOrder


-- ## Alternative 1: define variation as a VectorMeasure

section TotalVariation

open MeasureTheory BigOperators ENNReal

variable {X : Type*} [MeasurableSpace X]
  {V 𝕜 : Type*} [SeminormedAddCommGroup V]  (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 V]
  (μ : VectorMeasure X V)

-- In mathlib, the notion `Measure` requires that it is defined on all sets and countable
-- subbadditivity holds.
-- In contrast, `VectorMeasure` requires that countable additivity holds only
-- for `MeasurableSet`s. This is closer to the textbook notion of measure (including Rudin).
-- We should probably proceed as follows:
-- 1. Define `ℝ≥0∞`-valued `VectorMeasure` using sup as in Rudin. This requires essentially only
--    countable additivity.
-- 2. Define, by combining `MeasureTheory.inducedOuterMeasure` and `MeasureTheory.OuterMeasure.trim`
--    a function that takes an `ℝ≥0∞`-valued `VectorMeasure` to a `Measure`. Then, by
--    `MeasureTheory.inducedOuterMeasure_eq`, `inducedOuterMeasure` coincide on measurable sets.
-- This seems better because many other parts of the project depends on `Measure` (concerning the
--  L^p spaces).

lemma ENNReal.hasSum_iff (f : ℕ → ℝ≥0∞) (a : ℝ≥0∞) : HasSum f a ↔
    (∀ (n : ℕ), ∑ i ∈ Finset.range n, f i ≤ a) ∧
    (∀ b < a, ∃ (n : ℕ), b < ∑ i ∈ Finset.range n, f i) := by
  obtain ha | ha | ha := a.trichotomy
  · -- The case `a = 0`.
    suffices h : (∀ x, f x = 0) ↔ ∀ n i, i < n → f i = 0 by simpa [ha, hasSum_zero_iff]
    exact ⟨fun h _ i _ ↦ h i, fun h i ↦  h (i + 1) i (by omega)⟩
  · -- The case `a = ∞`.
    suffices h: (∀ i, ¬i = ∞ → ∃ a, ∀ (b : ℕ), a ≤ b → i < ∑ i ∈ Finset.range b, f i) ↔
        ∀ b < ⊤, ∃ n, b < ∑ i ∈ Finset.range n, f i by
      simpa [ha, hasSum_iff_tendsto_nat, nhds_top]
    refine ⟨fun h b hb ↦ ?_, fun h b hb ↦ ?_⟩
    · obtain ⟨n, hn⟩ := h b (LT.lt.ne_top hb)
      exact ⟨n, hn n n.le_refl⟩
    · obtain ⟨n, hn⟩ := h b (Ne.lt_top' <| Ne.symm hb)
      exact ⟨n, fun m _ ↦ gt_of_ge_of_gt (Finset.sum_le_sum_of_subset (by simpa)) hn⟩
  · -- The case `0 < a ∧ a < ∞`.
    obtain ⟨ha'', ha'⟩ := (a.toReal_pos_iff).mp ha
    rw [ENNReal.hasSum_iff_tendsto_nat]
    constructor
    · intro h
      refine ⟨fun n ↦ ?_, fun b hb ↦ ?_⟩
      · rw [tendsto_atTop_nhds] at h
        by_contra! hc
        have hn : ∀ m, n ≤ m → ∑ i ∈ Finset.range n, f i ≤  ∑ i ∈ Finset.range m, f i :=
          fun _ _ ↦ Finset.sum_le_sum_of_subset (by simpa)
        let s := Set.Ico 0 (∑ i ∈ Finset.range n, f i)
        obtain ⟨ℓ, hℓ⟩ := h s ⟨by simp, hc⟩ isOpen_Ico_zero
        exact (lt_self_iff_false _).mp <|
          lt_of_lt_of_le ((hℓ (max n ℓ) (by omega)).2) (hn (max n ℓ) (by omega))
      · rw [tendsto_atTop_nhds] at h
        let s := Set.Ioo b (a + 1)
        have hs : a ∈ s := by simpa [s, hb] using lt_add_right (LT.lt.ne_top ha') one_ne_zero
        obtain ⟨n, hn⟩ := h s hs isOpen_Ioo
        exact ⟨n, (hn n (Nat.le_refl _)).1⟩
    · rw [and_imp]
      intro hf hf'
      rw [ENNReal.tendsto_nhds ha'.ne_top]
      intro ε hε
      simp only [Set.mem_Icc, tsub_le_iff_right, Filter.eventually_atTop, ge_iff_le]
      have hε' := (ENNReal.sub_lt_self_iff (LT.lt.ne_top ha')).mpr ⟨ha'', hε⟩
      obtain ⟨n, hn⟩ := hf' (a - ε) hε'
      refine ⟨n, fun m hm ↦ ?_⟩
      constructor
      · calc a
        _ ≤ a - ε + ε := by exact le_tsub_add
        _ ≤ ∑ i ∈ Finset.range n, f i + ε := add_le_add_right (le_of_lt hn) ε
        _ ≤ ∑ i ∈ Finset.range m, f i + ε := by gcongr
      · exact le_add_right (hf m)

lemma ENNReal.exist_iSup_le_add_of_pos {ι : Type*} {ε : ℝ≥0∞} {f : ι → ℝ≥0∞} (hε : 0 < ε)
    (h : iSup f < ⊤) : ∃ (i : ι), iSup f ≤ f i + ε := by
  sorry

lemma ENNReal.exist_biSup_le_add_of_pos {ι : Type*} {ε : ℝ≥0∞} {f : ι → ℝ≥0∞} {s : Set ι}
    (hε : 0 < ε) (h : ⨆ j ∈ s, f j < ⊤) : ∃ (i : ι), ⨆ j ∈ s, f j ≤ f i + ε := by
  obtain ⟨i, hi⟩ := ENNReal.exist_iSup_le_add_of_pos hε h
  rw [← OrderedSub.tsub_le_iff_right, le_iSup_iff] at hi
  have := hi (f i)
  use i
  simpa

noncomputable def vectorTotalVariation : VectorMeasure X ℝ≥0∞ where
  measureOf' (s : Set X) := by
    classical
    exact if (MeasurableSet s)
      then ⨆ E ∈ {E' : ℕ → Set X | (∀ n, MeasurableSet (E' n)) ∧
                  Pairwise (Function.onFun Disjoint E') ∧ ⋃ n, E' n = s},
            ∑' n, ENNReal.ofReal ‖μ (E n)‖
      else 0
  empty' := by
    simp only [MeasurableSet.empty, ↓reduceIte, Set.iUnion_eq_empty, Set.mem_setOf_eq,
      iSup_eq_zero, ENNReal.tsum_eq_zero, and_imp]
    intro E Emeasurable Edisjoint Eempty n
    rw [Eempty n]
    simp
  not_measurable' s h := if_neg h
  m_iUnion' E Emeasurable Edisjoint := by
    simp_rw [Emeasurable, MeasurableSet.iUnion Emeasurable]
    simp only [↓reduceIte, Set.mem_setOf_eq]
    rw [ENNReal.hasSum_iff]
    -- countable additivity, follow Rudin
    constructor
    · intro m
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε hlttop
      -- use `ε / m` instead of `ε`
      set F : ℕ → Set X := Classical.choose
        (ENNReal.exist_biSup_le_add_of_pos (ENNReal.coe_lt_coe.mpr hε) hlttop) with hF
      set specF := Classical.choose_spec
        (ENNReal.exist_biSup_le_add_of_pos (ENNReal.coe_lt_coe.mpr hε) hlttop)
      simp only [iSup_le_iff] at specF




      sorry
    · intro b hb
      obtain ⟨F, hF⟩ := lt_biSup_iff.mp hb
      rw [Set.mem_def, ENNReal.tsum_eq_iSup_nat] at hF
      obtain ⟨n, hn⟩ := lt_iSup_iff.mp hF.2
      use n
      -- take intersection of `F` and `E i` to get a refined partition,
      -- have : ∀ i, ∃ (A : ℕ → Set X), (∀ n, MeasurableSet A n) ∧ Pairwise (Function.onFun Disjoint A)
      --     ∧ ⋃ n, A n = E i ∧ ∑' n, ENNReal.ofReal ‖μ (A n)‖
      sorry

-- ## Alternative 1: define variation as a VectorMeasure

namespace variation

open MeasureTheory BigOperators ENNReal Function

variable {X V 𝕜 : Type*} [MeasurableSpace X] [SeminormedAddCommGroup V] (𝕜 : Type*) [NormedField 𝕜]
  [NormedSpace 𝕜 V] [T2Space V] [SeminormedGroup V]
 (μ : VectorMeasure X V)

-- Section : Partitions
-- NOTE: instead of working with partitions of `s`, work with sets of disjoints sets
-- contained within `s` since the same value will be achieved in the supremum.
-- Perhaps better described as "inner partitions".
-- NOTE: forbid the empty set so that partitions of disjoint sets are disjoint sets of sets.

def partitions (s : Set X) : Set (Finset (Set X)) :=
    {P | (∀ t ∈ P, t ⊆ s) ∧ (∀ t ∈ P, MeasurableSet t) ∧ (P.toSet.PairwiseDisjoint id) ∧
    (∀ p ∈ P, p ≠ ∅)}

lemma partitions_empty : partitions (∅ : Set X) = {∅} := by
  dsimp [partitions]
  ext P
  simp only [Set.subset_empty_iff, Finset.forall_mem_not_eq', Set.mem_setOf_eq,
    Set.mem_singleton_iff]
  constructor
  · intro ⟨hP', a, b, hP''⟩
    by_contra! hP
    obtain ⟨p, hp⟩ := Finset.Nonempty.exists_mem (Finset.nonempty_iff_ne_empty.mpr hP)
    simp_all [hP' p hp, ne_eq]
  · intro hp
    simp [hp]

open Classical in
/-- If each `P i` is a partition of `s i` then the union is a partition of `⋃ i, s i`. -/
lemma partition_union {s : ℕ → Set X} (hs : Pairwise (Disjoint on s))
    {P : ℕ → Finset (Set X)} (hP : ∀ i, P i ∈ partitions (s i)) (n : ℕ):
    Finset.biUnion (Finset.range n) P ∈ partitions (⋃ i, s i) := by
  simp only [partitions, ne_eq, Finset.forall_mem_not_eq', Set.mem_setOf_eq, Finset.mem_biUnion,
    Finset.mem_range, forall_exists_index, and_imp, not_exists, not_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p i _ hp
    exact Set.subset_iUnion_of_subset i ((hP i).1 p hp)
  · intro p i _ hp
    exact (hP i).2.1 p hp
  · intro p hp q hq hpq r hrp hrq
    simp only [Set.bot_eq_empty, Set.le_eq_subset, Set.subset_empty_iff]
    simp only [id_eq, Set.le_eq_subset] at hrp hrq
    simp only [Finset.coe_biUnion, Finset.coe_range, Set.mem_Iio, Set.mem_iUnion, Finset.mem_coe,
      exists_prop] at hp hq
    obtain ⟨i, hi, hp⟩ := hp
    obtain ⟨j, hj, hq⟩ := hq
    obtain hc | hc : i = j ∨ i ≠ j := by omega
    · rw [hc] at hp
      exact Set.subset_eq_empty ((hP j).2.2.1 hp hq hpq hrp hrq) rfl
    · have hp' := (hP i).1 p hp
      have hq' := (hP j).1 q hq
      exact Set.subset_eq_empty (hs hc (subset_trans hrp hp') (subset_trans hrq hq')) rfl
  · intro i _ h
    exact (hP i).2.2.2 ∅ h rfl

/-- If P, Q are partitions of two disjoint sets then P and Q are disjoint. -/
lemma partitions_disjoint {s t : Set X} (hst : Disjoint s t) {P Q : Finset (Set X)}
    (hP : P ∈ partitions s) (hQ : Q ∈ partitions t) : Disjoint P Q := by
  intro R hRP hRQ
  simp only [Finset.bot_eq_empty, Finset.le_eq_subset, Finset.subset_empty]
  by_contra! hc
  obtain ⟨r, hr⟩ := Finset.Nonempty.exists_mem <| Finset.nonempty_iff_ne_empty.mpr hc
  have := hst (hP.1 r <| hRP hr) (hQ.1 r <| hRQ hr)
  have := hP.2.2.2 r (hRP hr)
  simp_all

open Classical in
/-- If `P` is a partition then the restriction of `P` to a set `s` is a partition of `s`. -/
lemma partition_restrict {s t : Set X} {P : Finset (Set X)} (hs : P ∈ partitions s)
    (ht : MeasurableSet t) : (P.image (fun p ↦ p ∩ t)).filter (· ≠ ∅) ∈ partitions t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ h
    obtain ⟨_, _, hp⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
    simp [← hp]
  · intro r hr
    have := Finset.mem_filter.mp hr
    obtain ⟨p, hp, hp'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    rw [← hp']
    exact MeasurableSet.inter (hs.2.1 p hp) ht
  · intro _ hr _ hr'
    obtain ⟨p, hp, hp'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr').1
    rw [← hp', ← hq']
    intro hpqt
    have hpq : p ≠ q := fun h ↦ hpqt (congrFun (congrArg Inter.inter h) t)
    intro a ha ha'
    have hap : a ≤ p := by
      simp only [id_eq, Set.le_eq_subset, Set.subset_inter_iff] at ha
      exact ha.1
    have haq : a ≤ q := by
      simp only [id_eq, Set.le_eq_subset, Set.subset_inter_iff] at ha'
      exact ha'.1
    exact hs.2.2.1 hp hq hpq hap haq
  · intro _ hp
    exact (Finset.mem_filter.mp hp).2

-- Section : definition of variation

/-- Given a partition `E` of a set `s`, this returns the sum of the norm of the measure of the
elements of that partition. -/
private noncomputable def varOfPart (P : Finset (Set X)) := ∑ p ∈ P, ‖μ p‖ₑ

open Classical in
noncomputable def variationAux (s : Set X) :=
    if (MeasurableSet s) then ⨆ P ∈ partitions s, varOfPart μ P else 0

/-- `variationAux` of the empty set is equal to zero. -/
lemma variation_empty' : variationAux μ ∅ = 0 := by
  simp [variationAux, varOfPart, partitions_empty]

lemma variationAux_le {s : Set X} (hs : MeasurableSet s) {a : ℝ≥0∞} (ha : a < variationAux μ s) :
    ∃ P ∈ partitions s, a < varOfPart μ P := by
  simp only [variationAux, hs, reduceIte] at ha
  exact lt_biSup_iff.mp ha

-- lemma variationAux_le' {s : Set X} (hs : MeasurableSet s) {ε : NNReal} (hε: 0 < ε) :
--     ∃ P ∈ partitions s, variationAux μ s ≤ varOfPart μ P + ε := by
--   -- This holds since `variationAux μ s` is defined as a supremum over all `P ∈ partitions s`.
--   simp only [variationAux, hs, reduceIte]
--   suffices h : ∃ P ∈ partitions s, variationAux μ s - ε ≤ varOfPart μ P by
--     dsimp [variationAux] at h
--     simp_all
--   simp only [variationAux, hs, reduceIte]
--   by_contra! hc
--   replace hc : ⨆ P ∈ variation.partitions s, variation.varOfPart μ P ≤
--       (⨆ P ∈ variation.partitions s, variation.varOfPart μ P) -  ε := by
--     refine iSup₂_le_iff.mpr ?_
--     exact fun i j ↦ le_of_lt (hc i j)
--   have := calc ⨆ P ∈ variation.partitions s, variation.varOfPart μ P
--     _ < ⨆ P ∈ variation.partitions s, variation.varOfPart μ P + ε := by
--       sorry
--     _ ≤ ⨆ P ∈ variation.partitions s, variation.varOfPart μ P := by
--       refine (toNNReal_le_toNNReal ?_ ?_).mp ?_
--       · sorry
--       · sorry
--       · sorry
--   exact (lt_self_iff_false _).mp this

lemma le_variationAux {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP : P ∈ partitions s) : varOfPart μ P ≤ variationAux μ s := by
  simp only [variationAux, hs, reduceIte]
  exact le_biSup (varOfPart μ) hP


-- Similar to `norm_tsum_le_tsum_norm` and `nnnorm_tsum_le` in `Analysis/Normed/Group/InfiniteSum`.
variable {ι E : Type*} [SeminormedAddCommGroup E]
/-- `‖∑' i, f i‖ₑ ≤ (∑' i, ‖f i‖ₑ)`, automatically `∑' i, ‖f i‖ₑ` is summable. -/
theorem enorm_tsum_le_tsum_enorm {f : ι → E} : ‖∑' i, f i‖ₑ ≤ ∑' i, ‖f i‖ₑ := by
  sorry

open Classical in
/-- Given a partition `Q`, `varOfPart μ Q` is bounded by the sum of the `varOfPart μ (P i)` where
the `P i` are the partitions formed by restricting to a disjoint set of sets `s i`. -/
lemma varOfPart_le_tsum {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) {Q : Finset (Set X)} (hQ : Q ∈ partitions (⋃ i, s i)) :
    varOfPart μ Q ≤ ∑' i, varOfPart μ ({x ∈ Finset.image (fun q ↦ q ∩ s i) Q | x ≠ ∅}) := by
  let P (i : ℕ) := (Q.image (fun q ↦ q ∩ (s i))).filter (· ≠ ∅)
  calc
    _ = ∑ q ∈ Q, ‖μ q‖ₑ := by simp [varOfPart]
    _ = ∑ q ∈ Q, ‖μ (⋃ i, q ∩ s i)‖ₑ := ?_
    _ ≤ ∑ q ∈ Q, ∑' i, ‖μ (q ∩ s i)‖ₑ := ?_
    _ = ∑' i, ∑ q ∈ Q, ‖μ (q ∩ s i)‖ₑ := ?_
    _ ≤ ∑' i, ∑ p ∈ (P i), ‖μ p‖ₑ := ?_
    _ = ∑' i, (varOfPart μ (P i)) := by simp [varOfPart]
  · -- Each `q` is equal to the union of `q ∩ s i`.
    suffices h : ∀ q ∈ Q, q = ⋃ i, q ∩ s i by
      refine Finset.sum_congr rfl (fun q hq ↦ ?_)
      simp_rw [← h q hq]
    intro q hq
    ext x
    constructor
    · intro hx
      obtain ⟨_, hs⟩ := (hQ.1 q hq) hx
      obtain ⟨i, _⟩ := Set.mem_range.mp hs.1
      simp_all [Set.mem_iUnion_of_mem i]
    · intro _
      simp_all
  · -- Additivity of the measure since the `s i` are pairwise disjoint.
    gcongr with p hp
    have : μ (⋃ i, p ∩ s i) = ∑' i, μ (p ∩ s i) := by
      have hps : ∀ i, MeasurableSet (p ∩ s i) := by
        intro i
        refine MeasurableSet.inter (hQ.2.1 p hp) (hs i)
      have hps' : Pairwise (Disjoint on fun i ↦ p ∩ s i) := by
        refine (Symmetric.pairwise_on (fun ⦃x y⦄ a ↦ Disjoint.symm a) fun i ↦ p ∩ s i).mpr ?_
        intro _ _ _
        refine Disjoint.inter_left' p (Disjoint.inter_right' p ?_)
        exact hs' (by omega)
      exact VectorMeasure.of_disjoint_iUnion hps hps'
    rw [this]
    exact enorm_tsum_le_tsum_enorm
  · -- Swapping the order of the sum.
    refine Eq.symm (Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable))
  · -- By defintion of the restricted partition
    refine ENNReal.tsum_le_tsum ?_
    intro i
    calc ∑ q ∈ Q, ‖μ (q ∩ s i)‖ₑ
      _ = ∑ p ∈ (Finset.image (fun q ↦ q ∩ s i) Q), ‖μ p‖ₑ := by
        refine Eq.symm (Finset.sum_image_of_disjoint ?_ ?_)
        · simp only [Set.bot_eq_empty, VectorMeasure.empty]
          -- Remains to show that `‖0‖ₑ = 0` by `enorm_zero` doesn't work.
          have : ‖(0 : V)‖ₑ = 0 := by sorry
          exact this
        · intro p hp q hq hpq
          refine Disjoint.inter_left (s i) (Disjoint.inter_right (s i) ?_)
          exact hQ.2.2.1 hp hq hpq
      _ ≤  ∑ p ∈ P i, ‖μ p‖ₑ := by
        refine Finset.sum_le_sum_of_ne_zero ?_
        intro p hp hp'
        dsimp [P]
        obtain hc | hc : p = ∅ ∨ ¬p = ∅ := eq_or_ne p ∅
        · -- Remains to show that `‖0‖ₑ = 0` but `enorm_zero` doesn't work.
          have : ‖(0 : V)‖ₑ = 0 := by
            have : ‖(0 : V)‖ = 0 := by exact norm_zero
            have := ofReal_norm_eq_enorm' (0 : V)
            sorry
          simp [hc, this] at hp'
        · rw [Finset.mem_filter, Finset.mem_image]
          refine ⟨?_, hc⟩
          obtain ⟨q, _, _⟩ := Finset.mem_image.mp hp
          use q

/-- Aditivity of `variationAux` for disjoint measurable sets. -/
lemma variation_m_iUnion' (s : ℕ → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) :
    HasSum (fun i ↦ variationAux μ (s i)) (variationAux μ (⋃ i, s i)) := by
  rw [ENNReal.hasSum_iff]
  constructor
  · -- The sum of `variationAux μ (s i)` is le `variationAux μ (⋃ i, s i)`.
    intro n
    wlog hn : n ≠ 0
    · simp [show n = 0 by omega]
    apply ENNReal.le_of_forall_pos_le_add
    intro ε' hε' _
    let ε := ε' / n
    have hε : 0 < ε := by positivity
    -- For each set `s i` we choose a partition `P i` such that, for each `i`,
    -- `variationAux μ (s i) ≤ varOfPart μ (P i) + ε`.
    choose P hP using fun i ↦ variationAux_le μ (hs i) (hε)
    calc ∑ i ∈ Finset.range n, variationAux μ (s i)
      _ ≤ ∑ i ∈ Finset.range n, (varOfPart μ (P i) + ε) := by
        gcongr with i hi
        exact (hP i).2
      _ = ∑ i ∈ Finset.range n, varOfPart μ (P i) + ε' := by
        rw [Finset.sum_add_distrib]
        norm_cast
        simp [show n * ε = ε' by rw [mul_div_cancel₀ _ (by positivity)]]
      _ ≤ variationAux μ (⋃ i, s i) + ε' := by
        -- Since the union of the partitions `P i` is a partition of `⋃ i, s i`, we know that
        -- `∑' i, varOfPart μ (E i) ≤ variationAux μ (⋃ i, s i)`.
        suffices h : ∑ i ∈ Finset.range n, varOfPart μ (P i) ≤ variationAux μ (⋃ i, s i) by gcongr
        classical
        let Q := Finset.biUnion (Finset.range n) P
        have hQ : Q ∈ partitions (⋃ i, s i) := partition_union hs' (fun i ↦ (hP i).1) n
        calc
          _ = ∑ i ∈ Finset.range n, ∑ p ∈ P i, ENNReal.ofReal ‖μ p‖ := by simp [varOfPart]
          _ = ∑ q ∈ Q, ENNReal.ofReal ‖μ q‖ := by
            refine Eq.symm (Finset.sum_biUnion ?_)
            intro l _ m _ hlm
            exact partitions_disjoint (hs' hlm) (hP l).1 (hP m).1
          _ ≤ variationAux μ (⋃ i, s i) := by
            have := le_variationAux μ (MeasurableSet.iUnion hs) hQ
            simpa
  · -- Variation of the union, `variationAux μ (⋃ i, s i)` is le the sum of `variationAux μ (s i)`.
    intro b hb
    simp only [variationAux, hs, reduceIte]
    simp only [variationAux, MeasurableSet.iUnion hs, reduceIte] at hb
    obtain ⟨Q, hQ, hbQ⟩ := lt_biSup_iff.mp hb
    -- Take the partitions defined as intersection of `Q` and `s i`.
    classical
    let P (i : ℕ) := (Q.image (fun q ↦ q ∩ (s i))).filter (· ≠ ∅)
    have hP (i : ℕ) : P i ∈ partitions (s i) := partition_restrict hQ (hs i)
    have : varOfPart μ Q ≤ ∑' (i : ℕ), varOfPart μ (P i) := varOfPart_le_tsum μ hQ
    -- Choose `ε`.
    obtain ⟨ε, hε, hε'⟩ : ∃ (ε : ℝ≥0∞), 0 < ε ∧ b + ε < varOfPart μ Q := by
      have := hbQ
      obtain ⟨c, hc, hc'⟩ := exists_between hbQ
      exact ⟨c - b, tsub_pos_of_lt hc, by simpa [add_tsub_cancel_of_le (le_of_lt hc)]⟩
    -- Choose `n` large so that considering a finite set of `s i` suffices.
    obtain ⟨n, hn⟩ : ∃ n, ∑' i, varOfPart μ (P i) ≤
        ∑ i ∈ Finset.range n, varOfPart μ (P i) + ε := by

      sorry
    use n
    suffices h : b + ε < (∑ x ∈ Finset.range n, ⨆ P ∈ partitions (s x), varOfPart μ P) + ε by
      exact lt_of_add_lt_add_right h
    calc b + ε
      _ < varOfPart μ Q := hε'
      _ ≤ ∑' (i : ℕ), variation.varOfPart μ (P i) := varOfPart_le_tsum μ hQ
      _ ≤ ∑ i ∈ Finset.range n, varOfPart μ (P i) + ε := hn
      _ ≤ (∑ x ∈ Finset.range n, ⨆ P ∈ partitions (s x), varOfPart μ P) + ε := by
        gcongr with i hi
        exact le_biSup (varOfPart μ) (hP i)

/-- The variation of a vector-valued measure as a `VectorMeasure`. -/
noncomputable def variation : VectorMeasure X ℝ≥0∞ where
  measureOf'          := variationAux μ
  empty'              := variation_empty' μ
  not_measurable' _ h := if_neg h
  m_iUnion'           := variation_m_iUnion' μ

-- Section : properties of variation

theorem norm_measure_le_variation (μ : VectorMeasure X V) (E : Set X) :
    ‖μ E‖ₑ ≤ (variation μ E) := by
  dsimp [variation, variationAux]
  wlog hE' : E ≠ ∅
  · push_neg at hE'
    simp [hE']

  by_cases hE : ¬MeasurableSet E
  · simp [hE, μ.not_measurable' hE]
  · push_neg at hE
    simp only [hE, reduceIte, varOfPart]
    let P' : Finset (Set X) := {E}
    have hP' : P' ∈ partitions E := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [P']
      · simpa [P']
      · simp [P']
      · simpa [P']
    have hEP' : ENNReal.ofReal ‖μ E‖ = varOfPart μ P' := by
      simp [varOfPart, P']
    rw [hEP']
    dsimp [varOfPart]
    refine le_iSup₂_of_le P' hP' fun a ha ↦ ?_
    -- have : 0 ≤ ∑ p ∈ P', ‖μ p‖ := by
    --   sorry
    -- have : ∀ p ∈ P', 0 ≤ ‖μ p‖ := by
    --   sorry
    use ∑ p ∈ P', ⟨‖μ p‖, by positivity⟩
    constructor
    · simp only [ofReal_norm, WithTop.coe_sum, some_eq_coe']
      congr
    · refine NNReal.coe_le_coe.mp ?_
      sorry

-- TO DO : the total variation is a norm on the space of vector-valued measures.

-- TO DO : if `μ` is a `ℝ≥0∞`-valued `VectorMeasure` then `variation μ = μ`.

-- TO DO : variation corresponds to the Hahn–Jordan decomposition for a signed measure.

end variation


-- ## Alternative 2: define variation as a measure
namespace Variation2
open TopologicalSpace NNReal Function

-- Implementation note: instead of working with partitions of `K`, work with sets of disjoints sets
-- contained within `K` since the same value will be achieved in the supremum.
private def partitions (K : Set X) : Set (ℕ → Set X) :=
    {E : ℕ → Set X | (∀ n, (E n) ⊆ K) ∧ (∀ n, MeasurableSet (E n)) ∧ Pairwise (Disjoint on E)}

/-- By construction partitions behave in a monotone way. -/
lemma partitions_mono {s₁ s₂ : Set X} (hs : s₁ ⊆ s₂) : partitions s₁ ⊆ partitions s₂ :=
  fun _ hE ↦ ⟨fun n ↦ subset_trans (hE.1 n) hs, hE.2⟩

/-- Given a partition of a set `K`, this returns the sum of the norm of the measure of the elements
of that partition. If elements of the partition are non-measurable then the measure of that will be
0 and hence not contribute to the sum. -/
private noncomputable def varOfPart (μ : VectorMeasure X V) (E : ℕ → Set X) : ℝ≥0∞ :=
    ∑' n, ENNReal.ofReal ‖μ (E n)‖

/-- The value of variation defined as a supremum. -/
noncomputable def variationAux (μ : VectorMeasure X V) (K : Set X) : ℝ≥0∞ :=
    ⨆ E ∈ partitions K, varOfPart μ E

/-- `variationAux` of the empty set is equal to zero. -/
lemma variation_empty (μ : VectorMeasure X V) : variationAux μ ∅ = 0 := by
  simp only [variationAux, partitions, Set.subset_empty_iff, Set.mem_setOf_eq, varOfPart,
    ENNReal.iSup_eq_zero, ofReal_eq_zero, and_imp]
  intro _ _ _
  simp_all

/-- `s ↦ variationAux μ s` is monotone. -/
lemma variation_mono (μ : VectorMeasure X V) (s₁ s₂ : Set X) (hs : s₁ ⊆ s₂) :
    variationAux μ s₁ ≤ variationAux μ s₂ := by
  exact iSup_le_iSup_of_subset (partitions_mono hs)

/-- `variationAux` is subadditive for countable disjoint unions. -/
lemma variation_iUnion_nat [T2Space V] (μ : VectorMeasure X V) (s : ℕ → Set X)
    (hs : Pairwise (Function.onFun Disjoint s)) :
    variationAux μ (⋃ i, s i) ≤ ∑' (i : ℕ), variationAux μ (s i) := by
  -- Sufficies to prove that for any `E ∈ partitions (⋃ i, s i)`,
  -- `varOfPart μ E` is bounded above by
  -- `∑' (i : ℕ), ⨆ E ∈ partitions (s i), varOfPart μ E`.
  suffices h : ∀ E ∈ partitions (⋃ i, s i), varOfPart μ E ≤
      ∑' (i : ℕ), variationAux μ (s i) by
    exact iSup₂_le_iff.mpr h
  intro E hE
  -- In order to proceed, for each `i` we define the partition `F i` by intersecting `E` with `s i`.
  let F i j := s i ∩ E j
  -- The partitions created by intersection with the sets `s i` are still partitions.
  have F_partition : ∀ i, (fun j ↦ F i j) ∈ partitions (s i) := by
    intro i
    refine ⟨?_, ?_, ?_⟩
    · simp [F]
    · intro j
      simp only [F]
      -- PROBLEM: need to show `MeasurableSet (s i ∩ E j)` but only know `MeasurableSet (E j)`.
      sorry
    · intro _ _ hij
      simp only [Disjoint, Set.le_eq_subset, Set.subset_inter_iff, Set.bot_eq_empty,
        Set.subset_empty_iff, and_imp, F]
      intro _ _ hx _ hx'
      exact Set.subset_eq_empty (hE.2.2 hij hx hx') rfl
  have sum_F_le (i : ℕ) : varOfPart μ (fun j ↦ F i j) ≤ variationAux μ (s i) :=
    le_biSup (varOfPart μ) (F_partition i)
  calc varOfPart μ E
    _ = ∑' n, ENNReal.ofReal ‖μ (E n)‖ := rfl
    _ = ∑' i, ENNReal.ofReal ‖μ (⋃ j, F j i)‖ := by
      have (i : ℕ) : E i = ⋃ j, F j i := by
        -- The proof of this `have` can be more efficient.
        ext x
        constructor
        · simp only [F]
          intro hx
          simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_and_right, F]
          constructor
          · apply Set.mem_iUnion.mp
            exact (hE.1 i) hx
          · exact hx
        · simp [F]
      simp_rw [this]
    _ ≤ ∑' i, ∑' j, ENNReal.ofReal ‖μ (F i j)‖ := by
      -- Since the sets `F i j` are all disjoint.
      have (i : ℕ) : μ (⋃ j, F i j) = ∑' j, μ (F i j) := by
        apply VectorMeasure.of_disjoint_iUnion -- Requires `[T2Space V]`
        · intro j
          exact (F_partition i).2.1 j
        · exact (F_partition i).2.2
      gcongr with i

      sorry
    _ = ∑' i, varOfPart μ (fun j ↦ F i j) := by
      -- By defintion of `varOfPart`.
      sorry
    _ ≤ ∑' i, variationAux μ (s i) := by
      -- As proved above in `sum_F_le`.
      sorry

/-- The variation outer measure of a vector-valued measure. -/
noncomputable def variation [T2Space V] (μ : VectorMeasure X V) : OuterMeasure X where
  measureOf  := variationAux μ
  empty      := variation_empty μ
  mono       := variation_mono μ _ _
  iUnion_nat := variation_iUnion_nat μ

/-- Countable additivity of measurable sets. -/
lemma variation_m_iUnion [T2Space V] (μ : VectorMeasure X V) ⦃f : ℕ → Set X⦄
    (hf : ∀ i, MeasurableSet (f i)) (hf' : Pairwise (Disjoint on f)) :
    (variation μ).trim (⋃ i, f i) = ∑' i, (variation μ).trim (f i) := by
  sorry

-- NOTE: perhaps we can avoid using `trim` since `variationAux` already works for all sets.
/-- The variation measure of a vector-valued measure. -/
noncomputable def variation' [T2Space V] (μ : VectorMeasure X V) : Measure X :=
  {
    (variation μ).trim with
      m_iUnion := sorry
      trim_le  := le_of_eq (OuterMeasure.trim_trim (variation μ))
  -- where
  --   measureOf := variationAux μ
  --   empty := variation_empty μ
  --   mono := variation_mono μ _ _
  --   iUnion_nat := variation_iUnion_nat μ
  --   m_iUnion := sorry
  --   trim_le := sorry
  }


end Variation2

-- ## Alternative 3: define variation by first defining a content and hence a measure

namespace Variation3
open TopologicalSpace NNReal Function
variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
open TopologicalSpace NNReal

-- Implementation note: instead of working with partitions of `K`, work with sets of disjoints sets
-- contained within `K` since the same value will be achieved in the supremum.
private def partitions (K : Set X) : Set (ℕ → Set X) :=
    {E : ℕ → Set X | (∀ n, (E n) ⊆ K) ∧ Pairwise (Function.onFun Disjoint E)}

/-- Given a partition of a set `K`, this returns the sum of the norm of the measure of the elements
of that partition. If elements of the partition are non-measurable then the measure of that will be
0 and hence not contribute to the sum. -/
private noncomputable def varOfPart (μ : VectorMeasure X V) (E : ℕ → Set X) : ℝ≥0 :=
    ⟨∑' n,  ‖μ (E n)‖, tsum_nonneg (fun n ↦ norm_nonneg (μ (E n)))⟩

noncomputable def variationContentAux (μ : VectorMeasure X V) (K : Compacts X) : ℝ≥0 :=
    ⨆ E ∈ partitions K, varOfPart μ E

lemma partitionsMono {E₁ E₂ : Set X} (h : E₁ ⊆ E₂) : partitions E₁ ⊆ partitions E₂ := by
  intro E hE
  refine ⟨?_,?_⟩
  · exact fun n _ hx ↦ h ((hE.1 n) hx)
  · exact hE.2

theorem variationContentAux_mono (μ : VectorMeasure X V) (K₁ K₂ : Compacts X)
    (h : (K₁ : Set X) ⊆ K₂) : variationContentAux μ K₁ ≤ variationContentAux μ K₂ := by
  dsimp [variationContentAux]
  -- follows from the fact that the partitions are monotone
  have := partitionsMono h
  -- apply iSup_le_iSup_of_subset
  sorry

theorem variationContentAux_sup_le (μ : VectorMeasure X V) (K₁ K₂ : Compacts X) :
    variationContentAux μ (K₁ ⊔ K₂) ≤ variationContentAux μ K₁ + variationContentAux μ K₂ := by
  -- From any partition of `K₁ ⊔ K₂` we obtain a partition of `K₁` and of `K₂`.
  -- The elements of these partititions are subsets of the elements of the original partition.
  -- The conclusion follows from the fact that `μ` is monotone.
  sorry

theorem variationContentAux_sup_disjoint (μ : VectorMeasure X V) (K₁ K₂ : Compacts X)
    (h: Disjoint (K₁ : Set X) K₂) (h' : IsClosed (K₁ : Set X)) (h'' : IsClosed (K₂ : Set X)) :
    variationContentAux μ (K₁ ⊔ K₂) = variationContentAux μ K₁ + variationContentAux μ K₂ := by
  refine le_antisymm (variationContentAux_sup_le μ K₁ K₂) ?_
  -- we need only prove `≤`
  -- Given a partition of `K₁` and a partition of `K₂` we obtain a partition of `K₁ ⊔ K₂` by
  -- combining them.
  sorry

/-- The variation content of a vector-valued measure. -/
noncomputable def variationContent (μ : VectorMeasure X V) : Content X where
  toFun := variationContentAux μ
  mono' := variationContentAux_mono μ
  sup_disjoint' := variationContentAux_sup_disjoint μ
  sup_le' := variationContentAux_sup_le μ

lemma contentRegular_variationContent (μ : VectorMeasure X V) :
    (variationContent μ).ContentRegular := by
  sorry

/-- The variation measure of a vector-valued measure. -/
noncomputable def variation (μ : VectorMeasure X V) := (variationContent μ).measure

theorem abs_measure_le_variation (μ : VectorMeasure X V) (E : Set X) :
    ‖μ E‖ ≤ (variation μ E).toReal := by
  sorry

-- TO DO : show that total variation is a norm on the space of vector-valued measures.

end Variation3



/-- **Theorem**
Let `Φ` be a linear functional on `C_0(X, ℂ)`. Suppsoe that `μ`, `μ'` are complex Borel measures
such that, `∀ f : C_0(X, ℂ)`, `Φ f = ∫ x, f x ∂μ` and `Φ f = ∫ x, f x ∂μ'`. Then `μ = μ'`. -/
theorem uniqueness : True := sorry

-- **Proof** [Rudin 87, Theorem 6.19]
-- Suppose `μ` is a regular complex Borel measure on `X`
-- and that `∫ f dμ = 0` for all `f \in C_0(X)`.
-- *Theorem 6.12* gives a Borel function `h`, such that `|h| = 1` and `dμ = h d|μ|`.
-- For any sequence `{f_n}` in `C_0(X)` we then have
-- `|μ|(X) = \int_X (\bar{h} - f_n) h`, `d|μ| ≤ \int_X |\bar{h} - f_n| \, d|μ|`.
-- Since `C_c(X)` is dense in `L^1(|μ|)` (*Theorem 3.14*), `\{f_n\}` can be
-- so chosen that the last expression in the above tends to 0 as `n → \infty`.
-- Thus `|μ|(X) = 0`, and `μ = 0`.
-- It is easy to see that the difference of two regular complex Borel measures on `X` is regular.


section ComplexRMK

open NNReal
open ZeroAtInfty MeasureTheory CompactlySupported CompactlySupportedContinuousMap

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
variable (Φ : C₀(X, ℂ) →L[ℂ] ℂ)

-- TO DO: define `norm` as a `ContinuousMap` and use `norm ∘ f` in the following instead of the
-- `absOfFunc X f` hack.
def absOfFunc₀ (f : C₀(X, ℂ)) : C₀(X, ℝ) := sorry
def absOfFunc_c (f : C_c(X, ℂ)) : C_c(X, ℝ) := sorry

-- TO DO: figure out using this coercial directly in the argument.
def toZeroAtInftyContinuousMap : C_c(X, ℂ) → C₀(X, ℂ) := fun f ↦ (f : C₀(X, ℂ))
def toZeroAtInftyContinuousMap' : C_c(X, ℝ) → C₀(X, ℝ) := fun f ↦ (f : C₀(X, ℝ))

noncomputable def identity : C_c(X, ℝ≥0) → C_c(X, ℝ) := CompactlySupportedContinuousMap.toReal

-- TO DO: define the identity between the ℝ and ℂ spaces of continuous functions,
-- similar to `CompactlySupportedContinuousMap.toReal`.
def toComplex : C_c(X, ℝ) → C_c(X, ℂ) := by sorry


/-- Let `Φ` be a bounded linear functional on `C₀(X, ℂ)`. There exists a positive linear functional
`Λ` on `C₀(X, ℝ)` such that, `∀ f : C₀(X, ℂ)`, `|Φ f| ≤ Λ |f|` and `Λ |f| ≤ ‖f‖` (`‖⬝‖` denotes
the supremum norm). [Rudin 87, part of proof of Theorem 6.19] -/
theorem exists_pos_lin_func : ∃ (Λ : C₀(X, ℝ) →L[ℝ] ℝ), ∀ (f : C₀(X, ℂ)),
    ‖Φ f‖ ≤ Λ (absOfFunc₀ f) ∧ Λ (absOfFunc₀ f) ≤ ‖f‖ := by

  -- If `f ∈` [class of all nonnegative real members of `C_c(X, ℝ)`],
  -- define `Λ f = \sup { |Φ(h)| : h ∈ C_c(X, ℂ), |h| ≤ f }`.
  let U (f : C_c(X, ℝ≥0)) := toZeroAtInftyContinuousMap '' {h : C_c(X, ℂ) | ∀ x : X, ‖h x‖ ≤ f x}
  let Λ' (f : C_c(X, ℝ≥0)) := sSup (norm '' (Φ '' U f))

  -- Then `Λ f ≥ 0`, `Λ` satisfies the two required inequalities,
  have (f : C_c(X, ℝ≥0)) : 0 ≤ Λ' f := by
    -- because it is the sup of nonnegative quantities
    sorry
  have (f : C_c(X, ℝ≥0)) : ‖Φ (toComplex (f.toReal))‖ ≤ Λ' f := by
    sorry
  have (f : C_c(X, ℝ≥0)) : Λ' f ≤ ‖toZeroAtInftyContinuousMap' f.toReal‖ := by
    sorry

  -- `0 ≤ f_1 ≤ f_2` implies `Λ f_1 ≤ Λ f_2`, and `Λ (cf) = c Λ f` if `c` is a positive constant.

  -- We have to show that
  -- (10) `Λ(f + g) = Λ f + Λ g` whenever `f, g ∈ C_c^+(X)`,
  -- and we then have to extend `Λ` to a linear functional on `C_c(X, ℝ)`.
  -- Fix `f` and `g \in C_c^+(X)`.
  -- If `ε > 0`, there exist `h_1, h_2 \in C_c(X, ℝ)` such that `|h_1| ≤ f`, `|h_2| ≤ g`,
  -- `Λ f ≤ |Φ(h_1)| + ε`, `Λ g ≤ |Φ(h_2)| + ε`.
  -- There are complex numbers `α_i`, `|α_i| = 1`, so that `α_i Φ(h_i) = |Φ(h_i)|`, `i = 1, 2`.
  -- Then
  -- `Λ f + Λ g ≤ |Φ(h_1)| + |Φ(h_2)| + 2ε`
  -- `_ = Φ(α_1 h_1 + α_2 h_2) + 2ε`
  -- `_ ≤ Λ(|h_1| + |h_2|) + 2ε`
  -- `_ ≤ Λ(f + g) + 2ε`
  -- so that the inequality `≥` holds in (10).
  -- Next, choose `h ∈ C_c(X)`, subject only to the condition `|h| ≤ f + g`,
  -- let `V = { x : f(x) + g(x) > 0 }`, and define
  -- `h_1(x) = \frac{f(x) h(x)}{f(x) + g(x)}`,
  -- `h_2(x) = \frac{g(x) h(x)}{f(x) + g(x)}` when `x ∈ V`,
  -- `h_1(x) = h_2(x) = 0` when `x ∉ V`.
  -- It is clear that `h_1` is continuous at every point of `V`.
  -- If `x_0 ∉ V`, then `h(x_0) = 0`;
  -- since `h` is continuous and since `|h_1(x)| ≤ |h(x)|` for all `x ∈ X`,
  -- it follows that `x_0` is a point of continuity of `h_1`.
  -- Thus `h_1 \in C_c(X)`, and the same holds for `h_2`.
  -- Since `h_1 + h_2 = h` and `|h_1| ≤ f`, `|h_2| ≤ g`, we have
  -- `|Φ(h)| = |Φ(h_1) + Φ(h_2)| ≤ |Φ(h_1)| + |Φ(h_2)| ≤ Λ f + Λ g`.
  -- Hence `Λ(f + g) ≤ Λ f + Λ g`, and we have proved (10).
  -- If `f` is now a real function, `f \in C_c(X)`, then `2f^+ = |f| + f`,
  -- so that `f^+ \in C_c^+(X)`;
  -- likewise, `f^- \in C_c^+(X)`; and since `f = f^+ - f^-`, it is natural to define
  -- `Λ f = Λ f^+ - Λ f^- ` for `f \in C_c(X)`, `f` real
  -- and
  -- `Λ(u + iv) = Λ u + i Λ v`.
  -- Simple algebraic manipulations, just like those which occur in the proof of
  -- Theorem 1.32, show now that our extended functional `Λ` is linear on `C_c(X)`.

  sorry


variable [MeasurableSpace X] [BorelSpace X]

/-- **Theorem**
Let `Φ` be a bounded linear functional on `C₀(X, ℂ)`. Then (1) there exists a complex Borel measure
`μ` such that, `∀ f : C₀(X, ℂ)`, `Φ f = ∫ x, f x ∂μ`, (2) `‖Φ‖ = |μ|(X)`. -/
theorem Complex.integral_rieszMeasure : True := by
  -- ∃ (μ : ComplexMeasure X), ∀ (f : C₀(X, ℂ)),
  --  Φ f = ∫ x, f x ∂μ
  --  ∧ ‖Φ‖ = ComplexMeasureMeasure.totalVariation μ X
  -- TO DO: define `ComplexMeasureMeasure.totalVariation`
  -- TO DO: define `ComplexMeasure.integral`, maybe in general `VectorMeasure.integral`

  -- **Proof** [Rudin 87, Theorem 6.19]
  -- Assume `‖Φ‖ = 1`, without loss of generality.
  -- *Part 1:*
  -- Using `exists_pos_lin_func` we obtain a *positive* linear functional `Λ` on `C_c(X)`, such that
  -- (4) `|Φ(f)| ≤ Λ(|f|) ≤ ‖f‖` for all `f \in C_c(X))`.
  -- Once we have this `Λ`, we associate with it a positive Borel measure `λ`, given by
  -- have := RealRMK.integral_rieszMeasure
  -- `RealRMK.rieszMeasure hΛ` and which is a representation by `RealRMK.integral_rieszMeasure`.
  -- It also implies that `λ` is regular if `λ(X) < \infty`.
  -- Since `Λ(X) = \sup {Λ f : 0 ≤ f ≤ 1, f \in C_c(X)}`
  -- and since `|Λ f| ≤ 1` if `‖f‖ ≤ 1`, we see that actually `λ(X) ≤ 1`.
  -- We also deduce from (4) that
  -- `|Φ(f)| ≤ Λ(|f|) = ∫_X |f| dλ = ‖f‖_1`, `f \in C_c(X))`.
  -- The last norm refers to the space `L^1(λ)`.
  -- Thus `Φ` is a linear functional on `C_c(X)` of norm at most 1, with respect to the `L^1(λ)`-norm
  -- on `C_c(X)`.
  -- There is a norm-preserving extension of `Φ` to a linear functional on `L^1(λ)`, and therefore
  -- *Theorem 6.16* (the case `p = 1`) gives a Borel function `g`, with `|g| ≤ 1`, such that
  -- (6) `Φ(f) = ∫_X fg dλ`, `f \in C_c(X)`.
  -- Each side of (6) is a continuous functional on `C_0(X)`, and `C_c(X)` is dense in `C_0(X)`.
  -- Hence (6) holds for all `f \in C_0(X)`, and we obtain the representation with `dμ = g dλ`.
  -- *Part 2:*
  -- Since `\|Φ\| = 1`, (6) shows that
  -- `∫_X |g| dλ ≥ \sup { |Φ(f)| : f \in C_0(X), ‖f‖ ≤ 1 } = 1`.
  -- We also know that `λ(X) ≤ 1` and `|g| ≤ 1`.
  -- These facts are compatible only if `λ(X) = 1` and `|g| = 1` a.e. `[λ]`.
  -- Thus `d|μ| = |g| dλ = dλ`, by *Theorem 6.13*,
  -- and `|μ|(X) = λ(X) = 1 = ‖Φ‖`,
  sorry


end ComplexRMK
