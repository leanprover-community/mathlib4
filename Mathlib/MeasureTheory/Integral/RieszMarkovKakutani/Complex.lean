import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Complex

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

lemma ENNReal.hasSum_iff_XXX (f : ℕ → ℝ≥0∞) (a : ℝ≥0∞): HasSum f a ↔
    (∀ (n : ℕ), ∑ i ∈ Finset.range n, f i ≤ a) ∧
    (∀ b < a, ∃ (n : ℕ), b < ∑ i ∈ Finset.range n, f i) := by
  rw [ENNReal.hasSum_iff_tendsto_nat]
  constructor
  · intro h
    constructor
    · sorry
    · sorry
  · intro h O hO
    simp only [Filter.mem_map, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage]
    sorry

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
    rw [ENNReal.hasSum_iff_XXX]
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

-- obsolete
noncomputable def supOuterMeasure : OuterMeasure X where
  measureOf (s : Set X) :=
    ⨅ t ∈ {t' : Set X | MeasurableSet t' ∧ s ⊆ t'},
      ⨆ E ∈ {E' : ℕ → Set X | (∀ n, MeasurableSet (E' n)) ∧ Pairwise (Function.onFun Disjoint E')
        ∧ ⋃ n, E' n = t},
      ∑' n, ENNReal.ofReal ‖μ (E n)‖
  empty := by
    simp only [Set.empty_subset, and_true, Set.mem_setOf_eq]
    apply le_antisymm
    · apply le_trans (biInf_le _ MeasurableSet.empty)
      simp only [Set.iUnion_eq_empty, nonpos_iff_eq_zero, iSup_eq_zero, ENNReal.tsum_eq_zero,
        and_imp]
      intro _ _ _ hEempty n
      simp [hEempty n]
    · simp
  mono {s₁ s₂} h := by
    simp only [Set.mem_setOf_eq, le_iInf_iff, and_imp]
    intro t ht hst
    have ht' : t ∈ {t' : Set X | MeasurableSet t' ∧ s₁ ⊆ t'} := by
      rw [Set.setOf_and]
      exact ⟨ht, (Set.Subset.trans h hst)⟩
    apply le_trans (biInf_le _ ht')
    exact le_of_eq rfl
  iUnion_nat := by
    sorry

-- noncomputable def supTotalVariation : Measure X :=
--   { (supOuterMeasure μ).trim with
--     m_iUnion := sorry
--     -- countable additivity for measurable sets, follow Rudin
--     -- use `OuterMeasure.trim_eq` for measurable sets
--     trim_le := le_of_eq (OuterMeasure.trim_trim (supOuterMeasure μ)) }



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
private noncomputable def sumOfNormOfMeasure (μ : VectorMeasure X V) (E : ℕ → Set X) : ℝ≥0∞ :=
    ∑' n, ENNReal.ofReal ‖μ (E n)‖

/-- The value of variation defined as a supremum. -/
noncomputable def variationAux (μ : VectorMeasure X V) (K : Set X) : ℝ≥0∞ :=
    ⨆ E ∈ partitions K, sumOfNormOfMeasure μ E

/-- `variationAux` of the empty set is equal to zero. -/
lemma variation_empty (μ : VectorMeasure X V) : variationAux μ ∅ = 0 := by
  simp only [variationAux, partitions, Set.subset_empty_iff, Set.mem_setOf_eq, sumOfNormOfMeasure,
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
  -- `sumOfNormOfMeasure μ E` is bounded above by
  -- `∑' (i : ℕ), ⨆ E ∈ partitions (s i), sumOfNormOfMeasure μ E`.
  suffices h : ∀ E ∈ partitions (⋃ i, s i), sumOfNormOfMeasure μ E ≤
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
  have sum_F_le (i : ℕ) : sumOfNormOfMeasure μ (fun j ↦ F i j) ≤ variationAux μ (s i) :=
    le_biSup (sumOfNormOfMeasure μ) (F_partition i)
  calc sumOfNormOfMeasure μ E
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
    _ = ∑' i, sumOfNormOfMeasure μ (fun j ↦ F i j) := by
      -- By defintion of `sumOfNormOfMeasure`.
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
private noncomputable def sumOfNormOfMeasure (μ : VectorMeasure X V) (E : ℕ → Set X) : ℝ≥0 :=
    ⟨∑' n,  ‖μ (E n)‖, tsum_nonneg (fun n ↦ norm_nonneg (μ (E n)))⟩

noncomputable def variationContentAux (μ : VectorMeasure X V) (K : Compacts X) : ℝ≥0 :=
    ⨆ E ∈ partitions K, sumOfNormOfMeasure μ E

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
