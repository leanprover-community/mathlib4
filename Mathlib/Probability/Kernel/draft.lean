import Mathlib.Probability.Kernel.Disintegration
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Kernel.BuildKernel

open MeasureTheory Set Filter

open scoped ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α Ω : Type*} {mα : MeasurableSpace α}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

lemma measurableSet_tendsto_nhds {β γ ι : Type*} [MeasurableSpace β]
    [TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ]
    [hγ : OpensMeasurableSpace γ] [Countable ι] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → β → γ} (hf : ∀ i, Measurable (f i)) (c : γ) :
    MeasurableSet { x | Tendsto (fun n ↦ f n x) l (𝓝 c) } := sorry

lemma measurableSet_tendsto_fun {β γ ι : Type*} [MeasurableSpace β]
    [TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ]
    [hγ : OpensMeasurableSpace γ] [Countable ι] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → β → γ} (hf : ∀ i, Measurable (f i)) {g : β → γ}
    (hg : Measurable g) :
    MeasurableSet { x | Tendsto (fun n ↦ f n x) l (𝓝 (g x)) } := by
  letI := upgradePolishSpace γ
  have : { x | Tendsto (fun n ↦ f n x) l (𝓝 (g x)) }
      = { x | Tendsto (fun n ↦ dist (f n x) (g x)) l (𝓝 0) } := by
    ext x
    simp only [mem_setOf_eq]
    rw [tendsto_iff_dist_tendsto_zero]
  rw [this]
  exact measurableSet_tendsto_nhds (fun n ↦ (hf n).dist hg) 0

section Real

section dissection_system

def I (n : ℕ) (k : ℤ) : Set ℝ := Set.Ico (k * (2⁻¹ : ℝ) ^ n) ((k + 1) * ((2 : ℝ) ^ n)⁻¹)

lemma measurableSet_I (n : ℕ) (k : ℤ) : MeasurableSet (I n k) := measurableSet_Ico

lemma pairwise_disjoint_I (n : ℕ) : Pairwise (Disjoint on fun k ↦ I n k) := by
  sorry

lemma I_succ_union (n : ℕ) (k : ℤ) : I (n+1) (2 * k) ∪ I (n+1) (2 * k + 1) = I n k := by
  ext x
  cases lt_or_le x ((2 * k + 1) * ((2 : ℝ) ^ (n+1))⁻¹) with
  | inl h=>
    simp only [I, inv_pow, mem_Ico, Int.cast_mul, Int.int_cast_ofNat, Int.cast_add,
      Int.cast_one, mem_union, h, and_true, not_le.mpr h, false_and, or_false]
    sorry
  | inr h =>
    simp only [I, inv_pow, mem_Ico, Int.cast_mul, Int.int_cast_ofNat, Int.cast_add,
      Int.cast_one, mem_union, not_lt.mpr h, and_false, h, true_and, false_or]
    sorry

-- todo : `Filtration` should be renamed to `filtration`
def ℱ : Filtration ℕ (borel ℝ) where
  seq := fun n ↦ MeasurableSpace.generateFrom {s | ∃ k, s = I n k}
  mono' := by
    refine monotone_nat_of_le_succ ?_
    intro n
    refine MeasurableSpace.generateFrom_le fun s ⟨k, hs⟩ ↦ ?_
    rw [hs, ← I_succ_union n k]
    refine MeasurableSet.union ?_ ?_
    · exact MeasurableSpace.measurableSet_generateFrom ⟨2 * k, rfl⟩
    · exact MeasurableSpace.measurableSet_generateFrom ⟨2 * k + 1, rfl⟩
  le' := fun n ↦ by
    refine MeasurableSpace.generateFrom_le fun s ⟨k, hs⟩ ↦ ?_
    rw [hs]
    exact measurableSet_I n k

lemma measurableSet_ℱ_I (n : ℕ) (k : ℤ) : MeasurableSet[ℱ n] (I n k) :=
  MeasurableSpace.measurableSet_generateFrom ⟨k, rfl⟩

noncomputable def indexI (n : ℕ) (t : ℝ) : ℤ := Int.floor (t * 2^n)

lemma mem_I_indexI (n : ℕ) (t : ℝ) : t ∈ I n (indexI n t) := by
  rw [indexI, I]
  simp only [inv_pow, mem_Ico]
  constructor
  · rw [← div_eq_mul_inv, div_le_iff]
    · exact Int.floor_le (t * 2 ^ n)
    · positivity
  · rw [← div_eq_mul_inv, lt_div_iff]
    · exact Int.lt_floor_add_one (t * 2 ^ n)
    · positivity

lemma indexI_of_mem (n : ℕ) (k : ℤ) (t : ℝ) (ht : t ∈ I n k) : indexI n t = k := by
  rw [indexI]
  simp only [I, inv_pow, mem_Ico, ← div_eq_mul_inv] at ht
  rw [div_le_iff, lt_div_iff] at ht
  · rw [Int.floor_eq_iff]
    exact ht
  · positivity
  · positivity

lemma mem_I_iff_indexI (n : ℕ) (k : ℤ) (t : ℝ) : t ∈ I n k ↔ indexI n t = k :=
  ⟨fun h ↦ indexI_of_mem n k t h, fun h ↦ h ▸ mem_I_indexI n t⟩

lemma measurable_indexI (n : ℕ) : Measurable[ℱ n] (indexI n) := by
  unfold indexI
  refine @measurable_to_countable' ℤ ℝ _ _ (ℱ n) _ (fun k ↦ ?_)
  have : (fun t ↦ ⌊t * (2 : ℝ) ^ n⌋) ⁻¹' {k} = I n k := by
    ext t
    simp only [mem_preimage, mem_singleton_iff, I, inv_pow, mem_Ico]
    rw [Int.floor_eq_iff]
    refine ⟨fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩, fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩⟩
    · rw [mul_inv_le_iff, mul_comm]
      · exact h1
      · positivity
    · rw [← div_eq_mul_inv, lt_div_iff]
      · exact h2
      · positivity
    · rw [mul_inv_le_iff, mul_comm] at h1
      · exact h1
      · positivity
    · rw [← div_eq_mul_inv, lt_div_iff] at h2
      · exact h2
      · positivity
  rw [this]
  exact measurableSet_ℱ_I n k

lemma iUnion_I (n : ℕ) : ⋃ k, I n k = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨indexI n x, mem_I_indexI n x⟩

lemma indexI_le_indexI_iff (n : ℕ) (t x : ℝ) :
    indexI n t ≤ indexI n x ↔ ⌊t * 2 ^ n⌋ * (2 ^ n)⁻¹ ≤ x := by
  simp only [indexI._eq_1]
  rw [← div_eq_mul_inv, div_le_iff, Int.le_floor]
  positivity

lemma iUnion_ge_I (n : ℕ) (t : ℝ) :
    ⋃ (k) (_ : indexI n t ≤ k), I n k = Ici (⌊t * 2 ^ n⌋ * (2 ^ n)⁻¹ : ℝ) := by
  ext x
  simp [mem_I_iff_indexI, indexI_le_indexI_iff]

lemma iInter_biUnion_I (x : ℝ) : ⋂ n, ⋃ (k) (_ : indexI n x ≤ k), I n k = Ici x := by
  ext t
  simp [iUnion_ge_I]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · sorry
  · intro n
    refine le_trans ?_ h
    rw [← div_eq_mul_inv, div_le_iff]
    · exact Int.floor_le (x * 2 ^ n)
    · positivity

lemma iSup_ℱ : ⨆ n, ℱ n = borel ℝ := by
  refine le_antisymm ?_ ?_
  · rw [iSup_le_iff]
    exact ℱ.le
  · conv_lhs => rw [borel_eq_generateFrom_Ici ℝ]
    refine MeasurableSpace.generateFrom_le (fun s ⟨x, hx⟩ ↦ ?_)
    rw [← hx, ← iInter_biUnion_I x]
    refine MeasurableSet.iInter (fun n ↦ ?_)
    refine MeasurableSet.biUnion ?_ (fun k hk ↦ ?_)
    · sorry
    · sorry

end dissection_system

variable {β : Type*} [MeasurableSpace β]

-- issue with the following: joint measurability
--noncomputable
--def M' (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
--  (((κ a).restrict (univ ×ˢ s)).fst.trim (ℱ.le n)).rnDeriv (((kernel.fst κ a)).trim (ℱ.le n)) t

noncomputable
def M (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (n : ℕ) (t : ℝ) : ℝ :=
  (κ a (I n (indexI n t) ×ˢ s) / kernel.fst κ a (I n (indexI n t))).toReal

lemma m_def (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (n : ℕ) :
    M κ a s n = fun t ↦ (κ a (I n (indexI n t) ×ˢ s) / kernel.fst κ a (I n (indexI n t))).toReal :=
  rfl

lemma measurable_m_aux (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) (n : ℕ) :
    Measurable (fun (p : α × ℝ) ↦
      κ p.1 (I n (indexI n p.2) ×ˢ s) / kernel.fst κ p.1 (I n (indexI n p.2))) := by
  change Measurable ((fun (p : α × ℤ) ↦
    κ p.1 (I n p.2 ×ˢ s) / kernel.fst κ p.1 (I n p.2)) ∘ (fun (p : α × ℝ) ↦ (p.1, indexI n p.2)))
  have h1 : Measurable (fun (p : α × ℤ) ↦ κ p.1 (I n p.2 ×ˢ s) / kernel.fst κ p.1 (I n p.2)) := by
    refine Measurable.div ?_ ?_
    · have h_swap : Measurable fun (p : ℤ × α) ↦ κ p.2 (I n p.1 ×ˢ s) := by
        refine measurable_uncurry_of_continuous_of_measurable
          (u := fun k a ↦ κ a (I n k ×ˢ s)) ?_ ?_
        · exact fun _ ↦ continuous_bot
        · exact fun _ ↦ kernel.measurable_coe _ ((measurableSet_I _ _).prod hs)
      change Measurable ((fun (p : ℤ × α) ↦ κ p.2 (I n p.1 ×ˢ s)) ∘ Prod.swap)
      exact h_swap.comp measurable_swap
    · have h_swap : Measurable fun (p : ℤ × α) ↦ kernel.fst κ p.2 (I n p.1) := by
        refine measurable_uncurry_of_continuous_of_measurable
          (u := fun k a ↦ kernel.fst κ a (I n k)) ?_ ?_
        · exact fun _ ↦ continuous_bot
        · exact fun _ ↦ kernel.measurable_coe _ (measurableSet_I _ _)
      change Measurable ((fun (p : ℤ × α) ↦ kernel.fst κ p.2 (I n p.1)) ∘ Prod.swap)
      exact h_swap.comp measurable_swap
  refine h1.comp (measurable_fst.prod_mk ?_)
  exact (Measurable.mono (measurable_indexI n) (ℱ.le n) le_rfl).comp measurable_snd

lemma measurable_m (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) (n : ℕ) :
    Measurable (fun (p : α × ℝ) ↦ M κ p.1 s n p.2) :=
  (measurable_m_aux κ hs n).ennreal_toReal

lemma measurable_m_left (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) (n : ℕ) (t : ℝ) :
    Measurable (fun a ↦ M κ a s n t) :=
  (measurable_m κ hs n).comp (measurable_id.prod_mk measurable_const)

lemma measurable_m_right (κ : kernel α (ℝ × β)) {s : Set β} (a : α) (hs : MeasurableSet s) (n : ℕ) :
    Measurable (M κ a s n) :=
  (measurable_m κ hs n).comp (measurable_const.prod_mk measurable_id)

lemma adapted_m (κ : kernel α (ℝ × β)) (a : α) (s : Set β) : Adapted ℱ (M κ a s) := by
  intro n
  rw [m_def]
  refine Measurable.stronglyMeasurable ?_
  refine @Measurable.ennreal_toReal _ (ℱ n) _ ?_
  refine Measurable.div ?_ ?_
  · change Measurable[ℱ n] ((fun k ↦ κ a (I n k ×ˢ s)) ∘ (indexI n))
    refine Measurable.comp ?_ (measurable_indexI n)
    exact measurable_of_countable _
  · change Measurable[ℱ n] ((fun k ↦ (kernel.fst κ) a (I n k)) ∘ (indexI n))
    refine Measurable.comp ?_ (measurable_indexI n)
    exact measurable_of_countable _

lemma m_nonneg (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (n : ℕ) (t : ℝ) :
    0 ≤ M κ a s n t :=
  ENNReal.toReal_nonneg

lemma m_le_one (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (n : ℕ) (t : ℝ) :
    M κ a s n t ≤ 1 := by
  rw [M]
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul, kernel.fst_apply' _ _ (measurableSet_I _ _)]
  refine measure_mono (fun x ↦ ?_)
  simp only [mem_prod, mem_setOf_eq, and_imp]
  exact fun h _ ↦ h

lemma snorm_m_le_one (κ : kernel α (ℝ × β)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) (s : Set β) (n : ℕ) :
    snorm (M κ a s n) 1 (kernel.fst κ a) ≤ 1 := by
  refine (snorm_mono_real (g := fun _ ↦ 1) ?_).trans ?_
  · intro x
    simp only [Real.norm_eq_abs, abs_le]
    constructor
    · have h := m_nonneg κ a s n x
      linarith
    · exact m_le_one _ _ _ _ _
  · by_cases h0 : kernel.fst κ a = 0
    · simp [h0]
    · rw [snorm_const _ one_ne_zero h0]
      simp

lemma integrable_m (κ : kernel α (ℝ × β)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) {s : Set β} (hs : MeasurableSet s) (n : ℕ) :
    Integrable (M κ a s n) (kernel.fst κ a) := by
  rw [← memℒp_one_iff_integrable]
  refine ⟨Measurable.aestronglyMeasurable ?_, ?_⟩
  · exact measurable_m_right κ a hs n
  · exact (snorm_m_le_one κ a s n).trans_lt ENNReal.one_lt_top

lemma set_integral_m_I (κ : kernel α (ℝ × β)) [IsFiniteKernel (kernel.fst κ)]
    (a : α) {s : Set β} (hs : MeasurableSet s) (n : ℕ) (k : ℤ) :
    ∫ t in I n k, M κ a s n t ∂(kernel.fst κ a) = (κ a (I n k ×ˢ s)).toReal := by
  simp_rw [M]
  rw [integral_toReal]
  rotate_left
  · refine Measurable.aemeasurable ?_
    have h := measurable_m_aux κ hs n
    sorry
  · sorry
  congr
  have : ∫⁻ t in I n k, κ a (I n (indexI n t) ×ˢ s)
                        / kernel.fst κ a (I n (indexI n t)) ∂(kernel.fst κ) a
      = ∫⁻ t in I n k, κ a (I n k ×ˢ s) / kernel.fst κ a (I n k) ∂(kernel.fst κ) a := by
    refine set_lintegral_congr_fun (measurableSet_I _ _) (ae_of_all _ (fun t ht ↦ ?_))
    rw [indexI_of_mem _ _ _ ht]
  rw [this]
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
  by_cases h0 : kernel.fst κ a (I n k) = 0
  · simp only [h0, mul_zero]
    rw [kernel.fst_apply' _ _ (measurableSet_I _ _)] at h0
    refine (measure_mono_null ?_ h0).symm
    intro p
    simp only [mem_prod, mem_setOf_eq, and_imp]
    exact fun h _ ↦ h
  rw [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel h0, mul_one]
  exact measure_ne_top _ _

lemma integral_m (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) (n : ℕ) :
    ∫ t, M κ a s n t ∂(kernel.fst κ a) = (κ a (univ ×ˢ s)).toReal := by
  rw [← integral_univ, ← iUnion_I n, iUnion_prod_const, measure_iUnion]
  rotate_left
  · intro i j hij
    simp only [Set.disjoint_prod, disjoint_self, bot_eq_empty]
    exact Or.inl (pairwise_disjoint_I n hij)
  · exact fun k ↦ (measurableSet_I n k).prod hs
  rw [integral_iUnion (measurableSet_I n) (pairwise_disjoint_I n)
    (integrable_m κ a hs n).integrableOn]
  rw [ENNReal.tsum_toReal_eq (fun _ ↦ measure_ne_top _ _)]
  congr with k
  rw [set_integral_m_I _ _ hs]

lemma set_integral_m (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) (n : ℕ) {A : Set ℝ} (hA : MeasurableSet[ℱ n] A) :
    ∫ t in A, M κ a s n t ∂(kernel.fst κ a) = (κ a (A ×ˢ s)).toReal := by
  suffices MeasurableSet A ∧ ∫ t in A, M κ a s n t ∂(kernel.fst κ a) = (κ a (A ×ˢ s)).toReal by
    exact this.2
  refine MeasurableSpace.generateFrom_induction
    (p := fun A' ↦ MeasurableSet A'
      ∧ ∫ t in A', M κ a s n t ∂(kernel.fst κ) a = ENNReal.toReal (κ a (A' ×ˢ s)))
    (C := {s | ∃ k, s = I n k}) ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨k, rfl⟩
    rw [set_integral_m_I _ _ hs]
    exact ⟨measurableSet_I _ _, rfl⟩
  · simp only [MeasurableSet.empty, Measure.restrict_empty, integral_zero_measure, empty_prod,
      OuterMeasure.empty', ENNReal.zero_toReal, and_self]
  · intro A ⟨hA, hA_eq⟩
    have h := integral_add_compl hA (integrable_m κ a hs n)
    refine ⟨hA.compl, ?_⟩
    rw [hA_eq, integral_m κ a hs] at h
    have : Aᶜ ×ˢ s = univ ×ˢ s \ A ×ˢ s := by
      rw [prod_diff_prod, compl_eq_univ_diff]
      simp
    rw [this, measure_diff (by intro x; simp) (hA.prod hs) (measure_ne_top (κ a) _),
      ENNReal.toReal_sub_of_le (measure_mono (by intro x; simp)) (measure_ne_top _ _)]
    rw [eq_tsub_iff_add_eq_of_le, add_comm]
    · exact h
    · rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
      exact measure_mono (by intro x; simp)
  · intro f hf
    simp only at hf
    -- todo: introduce disjointed sets, etc.
    sorry

lemma condexp_m (κ : kernel α (ℝ × β)) [IsMarkovKernel (kernel.fst κ)] (a : α) (s : Set β)
    {i j : ℕ} (hij : i ≤ j) :
    (kernel.fst κ a)[M κ a s j | ℱ i] =ᵐ[kernel.fst κ a] M κ a s i := by
  sorry

lemma martingale_m (κ : kernel α (ℝ × β)) [IsMarkovKernel (kernel.fst κ)] (a : α) (s : Set β) :
    Martingale (M κ a s) ℱ (kernel.fst κ a) :=
  ⟨adapted_m κ a s, fun _ _ ↦ condexp_m κ a s⟩

lemma m_mono_set (κ : kernel α (ℝ × β)) (a : α) {s s' : Set β} (h : s ⊆ s') (n : ℕ) (t : ℝ) :
    M κ a s n t ≤ M κ a s' n t := by
  rw [M, M, ENNReal.toReal_le_toReal]
  · gcongr
    rw [prod_subset_prod_iff]
    simp [subset_rfl, h]
  · rw [ne_eq, ENNReal.div_eq_top]
    push_neg
    constructor
    · sorry
    · sorry
  · rw [ne_eq, ENNReal.div_eq_top]
    push_neg
    constructor
    · sorry
    · sorry

lemma m_univ (κ : kernel α (ℝ × β)) [IsFiniteKernel κ] (a : α) (n : ℕ) (t : ℝ) :
    M κ a univ n t = if kernel.fst κ a (I n (indexI n t)) = 0 then 0 else 1 := by
  rw [M]
  by_cases h : kernel.fst κ a (I n (indexI n t)) = 0
  · simp [h]
    by_cases h' : κ a (I n (indexI n t) ×ˢ univ) = 0
    · simp [h']
    · rw [ENNReal.div_zero h']
      simp
  · simp only [h, ite_false]
    rw [kernel.fst_apply' _ _ (measurableSet_I _ _)]
    have : I n (indexI n t) ×ˢ univ = {p : ℝ × β | p.1 ∈ I n (indexI n t)} := by
      ext x
      simp
    rw [this, ENNReal.div_self]
    · simp
    · rwa [kernel.fst_apply' _ _ (measurableSet_I _ _)] at h
    · exact measure_ne_top _ _

lemma m_empty (κ : kernel α (ℝ × β)) [IsFiniteKernel κ] (a : α) (n : ℕ) (t : ℝ) :
    M κ a ∅ n t = 0 := by
  rw [M]
  simp

lemma m_univ_ae (κ : kernel α (ℝ × β)) [IsFiniteKernel κ] (a : α) (n : ℕ) :
    ∀ᵐ t ∂(kernel.fst κ a), M κ a univ n t = 1 := by
  rw [ae_iff]
  have : {t | ¬M κ a univ n t = 1} ⊆ {t | kernel.fst κ a (I n (indexI n t)) = 0} := by
    intro t ht
    simp only [mem_setOf_eq] at ht ⊢
    rw [m_univ] at ht
    simpa using ht
  refine measure_mono_null this ?_
  have : {t | kernel.fst κ a (I n (indexI n t)) = 0}
      ⊆ ⋃ (k) (_ : kernel.fst κ a (I n k) = 0), I n k := by
    intro t
    simp only [mem_setOf_eq, mem_iUnion, exists_prop]
    intro ht
    exact ⟨indexI n t, ht, mem_I_indexI _ _⟩
  refine measure_mono_null this ?_
  rw [measure_iUnion_null]
  intro i
  simp

lemma tendsto_m_atTop_univ_of_monotone (κ : kernel α (ℝ × β)) [IsFiniteKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Monotone s) (hs_iUnion : ⋃ i, s i = univ) (n : ℕ) (t : ℝ) :
    Tendsto (fun m ↦ M κ a (s m) n t) atTop (𝓝 (M κ a univ n t)) := by
  simp_rw [M]
  refine (ENNReal.tendsto_toReal ?_).comp ?_
  · rw [ne_eq, ENNReal.div_eq_top]
    push_neg
    sorry
  by_cases h0 : kernel.fst κ a (I n (indexI n t)) = 0
  · simp only [h0]
    sorry
  refine ENNReal.Tendsto.div_const ?_ ?_
  · have h := tendsto_measure_iUnion (μ := κ a) (s := fun m ↦ I n (indexI n t) ×ˢ s m) ?_
    swap
    · intro m m' hmm'
      simp only [le_eq_subset, prod_subset_prod_iff, subset_rfl, true_and]
      exact Or.inl <| hs hmm'
    convert h
    rw [← prod_iUnion, hs_iUnion]
  · exact Or.inr h0

lemma tendsto_m_atTop_ae_of_monotone (κ : kernel α (ℝ × β)) [IsFiniteKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Monotone s) (hs_iUnion : ⋃ i, s i = univ) (n : ℕ) :
    ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun m ↦ M κ a (s m) n t) atTop (𝓝 1) := by
  filter_upwards [m_univ_ae κ a n] with t ht
  rw [← ht]
  exact tendsto_m_atTop_univ_of_monotone κ a s hs hs_iUnion n t

lemma tendsto_m_atTop_empty_of_antitone (κ : kernel α (ℝ × β)) [IsFiniteKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Antitone s) (hs_iInter : ⋂ i, s i = ∅)
    (hs_meas : ∀ n, MeasurableSet (s n)) (n : ℕ) (t : ℝ) :
    Tendsto (fun m ↦ M κ a (s m) n t) atTop (𝓝 (M κ a ∅ n t)) := by
  simp_rw [M]
  refine (ENNReal.tendsto_toReal ?_).comp ?_
  · rw [ne_eq, ENNReal.div_eq_top]
    push_neg
    sorry
  by_cases h0 : kernel.fst κ a (I n (indexI n t)) = 0
  · simp only [h0, prod_empty, OuterMeasure.empty', ENNReal.zero_div]
    sorry
  refine ENNReal.Tendsto.div_const ?_ ?_
  · have h := tendsto_measure_iInter (μ := κ a) (s := fun m ↦ I n (indexI n t) ×ˢ s m) ?_ ?_ ?_
    · convert h
      rw [← prod_iInter, hs_iInter]
    · exact fun n ↦ MeasurableSet.prod (measurableSet_I _ _) (hs_meas n)
    · intro m m' hmm'
      simp only [le_eq_subset, prod_subset_prod_iff, subset_rfl, true_and]
      exact Or.inl <| hs hmm'
    · exact ⟨0, measure_ne_top _ _⟩
  · simp only [prod_empty, OuterMeasure.empty', ne_eq, not_true_eq_false, false_or, h0,
      not_false_iff]

lemma tendsto_m_atTop_of_antitone (κ : kernel α (ℝ × β)) [IsFiniteKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Antitone s) (hs_iInter : ⋂ i, s i = ∅)
    (hs_meas : ∀ n, MeasurableSet (s n)) (n : ℕ) (t : ℝ) :
    Tendsto (fun m ↦ M κ a (s m) n t) atTop (𝓝 0) := by
  rw [← m_empty κ a n t]
  exact tendsto_m_atTop_empty_of_antitone κ a s hs hs_iInter hs_meas n t

lemma tendsto_m_limitProcess (κ : kernel α (ℝ × β)) (a : α) [IsMarkovKernel (kernel.fst κ)]
    (s : Set β) :
    ∀ᵐ t ∂(kernel.fst κ a),
      Tendsto (fun n ↦ M κ a s n t) atTop (𝓝 (ℱ.limitProcess (M κ a s) (kernel.fst κ a) t)) := by
  refine Submartingale.ae_tendsto_limitProcess (martingale_m κ a s).submartingale (R := 1) ?_
  intro n
  rw [ENNReal.coe_one]
  exact snorm_m_le_one κ a s n

lemma limitProcess_mem_L1 (κ : kernel α (ℝ × β)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) (s : Set β) :
    Memℒp (ℱ.limitProcess (M κ a s) (kernel.fst κ a)) 1 (kernel.fst κ a) := by
  refine Submartingale.memℒp_limitProcess (martingale_m κ a s).submartingale (R := 1) ?_
  intro n
  rw [ENNReal.coe_one]
  exact snorm_m_le_one κ a s n

noncomputable
def MLimsup (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (t : ℝ) : ℝ :=
  limsup (fun n ↦ M κ a s n t) atTop

lemma mLimsup_ae_eq_mLim (κ : kernel α (ℝ × β)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) (s : Set β) :
    MLimsup κ a s =ᵐ[kernel.fst κ a] ℱ.limitProcess (M κ a s) (kernel.fst κ a) := by
  filter_upwards [tendsto_m_limitProcess κ a s] with t ht using ht.limsup_eq

lemma tendsto_m_mLimsup (κ : kernel α (ℝ × β)) (a : α) [IsMarkovKernel (kernel.fst κ)] (s : Set β) :
    ∀ᵐ t ∂(kernel.fst κ a),
      Tendsto (fun n ↦ M κ a s n t) atTop (𝓝 (MLimsup κ a s t)) := by
  filter_upwards [tendsto_m_limitProcess κ a s, mLimsup_ae_eq_mLim κ a s] with t h1 h2
  rw [h2]
  exact h1

lemma measurable_mLimsup (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) :
    Measurable (fun (p : α × ℝ) ↦ MLimsup κ p.1 s p.2) :=
  measurable_limsup (fun n ↦ measurable_m κ hs n)

lemma measurable_mLimsup_left (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) (t : ℝ) :
    Measurable (fun a ↦ MLimsup κ a s t) := by
  sorry

lemma measurable_mLimsup_right (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) (a : α) :
    Measurable (MLimsup κ a s) := by
  sorry

lemma mLimsup_mono_set (κ : kernel α (ℝ × β)) (a : α) {s s' : Set β} (h : s ⊆ s') (t : ℝ) :
    MLimsup κ a s t ≤ MLimsup κ a s' t := by
  rw [MLimsup, MLimsup]
  refine limsup_le_limsup ?_ ?_ ?_
  · exact Filter.eventually_of_forall (fun n ↦ m_mono_set κ a h n t)
  · sorry
  · sorry

lemma mLimsup_nonneg (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (t : ℝ) :
    0 ≤ MLimsup κ a s t := by
  refine le_limsup_of_frequently_le ?_ ?_
  · exact Filter.frequently_of_forall (fun n ↦ m_nonneg _ _ _ _ _)
  · sorry

lemma mLimsup_le_one (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (t : ℝ) :
    MLimsup κ a s t ≤ 1 := by
  refine limsup_le_of_le ?_ ?_
  · sorry
  · exact Filter.eventually_of_forall (fun n ↦ m_le_one _ _ _ _ _)

lemma mLimsup_univ (κ : kernel α (ℝ × β)) [IsFiniteKernel κ] (a : α) :
    ∀ᵐ t ∂(kernel.fst κ a), MLimsup κ a Set.univ t = 1 := by
  have h := m_univ_ae κ a
  rw [← ae_all_iff] at h
  filter_upwards [h] with t ht
  rw [MLimsup]
  simp_rw [ht]
  rw [limsup_const] -- should be simp

lemma tendsto_mLimsup_atTop_ae_of_monotone (κ : kernel α (ℝ × β)) [IsFiniteKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Monotone s) (hs_iUnion : ⋃ i, s i = univ) (n : ℕ) :
    ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun m ↦ MLimsup κ a (s m) t) atTop (𝓝 1) := by
  sorry

lemma tendsto_mLimsup_atTop_of_antitone (κ : kernel α (ℝ × β)) [IsFiniteKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Antitone s) (hs_iInter : ⋂ i, s i = ∅)
    (hs_meas : ∀ n, MeasurableSet (s n)) (n : ℕ) (t : ℝ) :
    Tendsto (fun m ↦ MLimsup κ a (s m) t) atTop (𝓝 0) := by
  sorry

section Iic_Q

noncomputable
def todo1' (κ : kernel α (ℝ × ℝ)) (a : α) (t : ℝ) (q : ℚ) : ℝ := MLimsup κ a (Set.Iic q) t

lemma measurable_todo1' (κ : kernel α (ℝ × ℝ)) (q : ℚ) :
    Measurable (fun p : α × ℝ ↦ todo1' κ p.1 p.2 q) := by
  sorry

lemma monotone_todo1' (κ : kernel α (ℝ × ℝ)) (a : α) (t : ℝ) : Monotone (todo1' κ a t) := by
  intro q r hqr
  rw [todo1', todo1']
  refine mLimsup_mono_set κ a ?_ t
  refine Iic_subset_Iic.mpr ?_
  exact_mod_cast hqr

lemma todo1'_nonneg (κ : kernel α (ℝ × ℝ)) (a : α) (t : ℝ) (q : ℚ) : 0 ≤ todo1' κ a t q :=
  mLimsup_nonneg κ a _ t

lemma todo1'_le_one (κ : kernel α (ℝ × ℝ)) (a : α) (t : ℝ) (q : ℚ) : todo1' κ a t q ≤ 1 :=
  mLimsup_le_one κ a _ t

lemma tendsto_atTop_todo1' (κ : kernel α (ℝ × ℝ)) (a : α) :
    ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun q ↦ todo1' κ a t q) atTop (𝓝 1) := by
  sorry

lemma tendsto_atBot_todo1' (κ : kernel α (ℝ × ℝ)) (a : α) (t : ℝ) :
    Tendsto (fun q ↦ todo1' κ a t q) atBot (𝓝 0) := by
  sorry

lemma iInf_rat_gt_todo1'_eq (κ : kernel α (ℝ × ℝ)) (a : α) (t : ℝ) (q : ℚ) :
    ⨅ r : Ioi q, todo1' κ a t r = todo1' κ a t q := by
  sorry

end Iic_Q

section Rat

lemma measurableSet_tendstoAtTopSet (κ : kernel α (ℝ × ℝ)) :
    MeasurableSet {p : α × ℝ | Tendsto (fun q ↦ todo1' κ p.1 p.2 q) atTop (𝓝 1)} :=
  measurableSet_tendsto_nhds (fun q ↦ measurable_todo1' κ q) 1

open Classical in
noncomputable
def todo2' (κ : kernel α (ℝ × ℝ)) (p : α × ℝ) : ℚ → ℝ :=
  if Tendsto (fun q ↦ todo1' κ p.1 p.2 q) atTop (𝓝 1)
    then fun q ↦ todo1' κ p.1 p.2 q
    else fun q ↦ if q < 0 then 0 else 1

lemma measurable_todo2' (κ : kernel α (ℝ × ℝ)) (q : ℚ) :
    Measurable (fun p ↦ todo2' κ p q) := by
  classical
  simp only [todo2', ite_apply]
  exact Measurable.ite (measurableSet_tendstoAtTopSet κ) (measurable_todo1' κ q) measurable_const

lemma monotone_todo2' (κ : kernel α (ℝ × ℝ)) (p : α × ℝ) :
    Monotone (todo2' κ p) := by
  unfold todo2'
  split_ifs with h
  · exact monotone_todo1' κ p.1 p.2
  · intro x y hxy
    dsimp only
    split_ifs with h_1 h_2 h_2
    exacts [le_rfl, zero_le_one, absurd (hxy.trans_lt h_2) h_1, le_rfl]

lemma todo2'_nonneg (κ : kernel α (ℝ × ℝ)) (p : α × ℝ) :
    0 ≤ todo2' κ p := by
  unfold todo2'
  split_ifs with h
  · exact todo1'_nonneg κ p.1 p.2
  · intro q
    simp only [Pi.one_apply]
    split_ifs <;> simp

lemma todo2'_le_one (κ : kernel α (ℝ × ℝ)) (p : α × ℝ) :
    todo2' κ p ≤ 1 := by
  unfold todo2'
  split_ifs with h
  · exact todo1'_le_one κ p.1 p.2
  · intro q
    simp only [Pi.one_apply]
    split_ifs <;> simp

lemma tendsto_atTop_todo2' (κ : kernel α (ℝ × ℝ)) (p : α × ℝ) :
    Tendsto (todo2' κ p) atTop (𝓝 1) := by
  unfold todo2'
  split_ifs with h
  · exact h
  · refine' (tendsto_congr' _).mp tendsto_const_nhds
    rw [EventuallyEq, eventually_atTop]
    exact ⟨0, fun q hq ↦ (if_neg (not_lt.mpr hq)).symm⟩

lemma tendsto_atBot_todo2' (κ : kernel α (ℝ × ℝ)) (p : α × ℝ) :
    Tendsto (todo2' κ p) atBot (𝓝 0) := by
  unfold todo2'
  split_ifs with h
  · exact tendsto_atBot_todo1' κ p.1 p.2
  · refine' (tendsto_congr' _).mp tendsto_const_nhds
    rw [EventuallyEq, eventually_atBot]
    refine' ⟨-1, fun q hq ↦ (if_pos (hq.trans_lt _)).symm⟩
    linarith

theorem inf_gt_todo2' (κ : kernel α (ℝ × ℝ)) (p : α × ℝ) (t : ℚ) :
    ⨅ r : Ioi t, todo2' κ p r = todo2' κ p t := by
  rw [todo2']
  split_ifs with hp
  · simp_rw [iInf_rat_gt_todo1'_eq]
  · simp only
    have h_bdd : BddBelow (range fun r : ↥(Ioi t) ↦ ite ((r : ℚ) < 0) (0 : ℝ) 1) := by
      refine' ⟨0, fun x hx ↦ _⟩
      obtain ⟨y, rfl⟩ := mem_range.mpr hx
      dsimp only
      split_ifs
      exacts [le_rfl, zero_le_one]
    split_ifs with h
    · refine' le_antisymm _ (le_ciInf fun x ↦ _)
      · obtain ⟨q, htq, hq_neg⟩ : ∃ q, t < q ∧ q < 0 := by
          refine' ⟨t / 2, _, _⟩
          · linarith
          · linarith
        refine' (ciInf_le h_bdd ⟨q, htq⟩).trans _
        rw [if_pos]
        rwa [Subtype.coe_mk]
      · split_ifs
        exacts [le_rfl, zero_le_one]
    · refine' le_antisymm _ _
      · refine' (ciInf_le h_bdd ⟨t + 1, lt_add_one t⟩).trans _
        split_ifs
        exacts [zero_le_one, le_rfl]
      · refine' le_ciInf fun x ↦ _
        rw [if_neg]
        rw [not_lt] at h ⊢
        exact h.trans (mem_Ioi.mp x.prop).le

lemma isCDFLike_todo2' (κ : kernel α (ℝ × ℝ)) : IsCDFLike (todo2' κ) where
  mono := monotone_todo2' κ
  nonneg := todo2'_nonneg κ
  le_one := todo2'_le_one κ
  tendsto_atTop_one := tendsto_atTop_todo2' κ
  tendsto_atBot_zero := tendsto_atBot_todo2' κ
  iInf_rat_gt_eq := inf_gt_todo2' κ
  measurable := measurable_todo2' κ

end Rat

noncomputable
def kernel.condexpReal (κ : kernel α (ℝ × ℝ)) : kernel (α × ℝ) ℝ :=
  (isCDFLike_todo2' κ).kernel

end Real

variable {Ω' : Type*} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']

def kernel.condexp (κ : kernel α (Ω × Ω')) [IsMarkovKernel (kernel.fst κ)] :
    kernel (α × Ω) Ω' :=
  sorry

theorem kernel.eq_compProd (κ : kernel α (Ω × Ω')) [IsMarkovKernel κ] :
    κ = kernel.fst κ ⊗ₖ (kernel.condexp κ) := by
  sorry

end ProbabilityTheory
