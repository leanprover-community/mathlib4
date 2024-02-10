import Mathlib.Probability.Kernel.Disintegration
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Kernel.BuildKernel

open MeasureTheory Set Filter

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α Ω : Type*} {mα : MeasurableSpace α}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section Real

section dissection_system

def I (n : ℕ) (k : ℤ) : Set ℝ := Set.Ico (k * (2⁻¹ : ℝ) ^ n) ((k + 1) * ((2 : ℝ) ^ n)⁻¹)

lemma measurableSet_I (n : ℕ) (k : ℤ) : MeasurableSet (I n k) := measurableSet_Ico

lemma Measure.iInf_Iic_gt_prod {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ]
    {s : Set α} (hs : MeasurableSet s) (t : ℚ) :
    ⨅ r : { r' : ℚ // t < r' }, ρ (s ×ˢ Iic (r : ℝ)) = ρ (s ×ˢ Iic (t : ℝ)) := by
  have h := Measure.iInf_IicSnd_gt ρ t hs
  simp_rw [Measure.IicSnd_apply ρ _ hs] at h
  rw [← h]

lemma pairwise_disjoint_I (n : ℕ) : Pairwise (Disjoint on fun k ↦ I n k) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_iff]
  intro x
  simp only [I, inv_pow, mem_inter_iff, mem_Ico, mem_empty_iff_false, and_imp, imp_false, not_lt]
  intro h1 h2 h3
  sorry

lemma I_succ_union (n : ℕ) (k : ℤ) : I (n+1) (2 * k) ∪ I (n+1) (2 * k + 1) = I n k := by
  ext x
  cases lt_or_le x ((2 * k + 1) * ((2 : ℝ) ^ (n+1))⁻¹) with
  | inl h =>
    simp only [I, inv_pow, mem_Ico, Int.cast_mul, Int.int_cast_ofNat, Int.cast_add,
      Int.cast_one, mem_union, h, and_true, not_le.mpr h, false_and, or_false]
    have : x < (k + 1) * (2 ^ n)⁻¹ := by
      refine h.trans_le ?_
      rw [pow_add, pow_one, mul_inv, mul_comm _ 2⁻¹, ← mul_assoc]
      gcongr
      rw [add_mul, one_mul, mul_comm, ← mul_assoc, inv_mul_cancel two_ne_zero, one_mul]
      gcongr
      norm_num
    simp only [this, and_true]
    rw [pow_add, pow_one, mul_inv, mul_comm _ 2⁻¹, ← mul_assoc, mul_comm _ 2⁻¹, ← mul_assoc,
      inv_mul_cancel two_ne_zero, one_mul]
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
    refine MeasurableSet.biUnion ?_ (fun k _ ↦ ?_)
    · exact to_countable _
    · exact le_iSup ℱ n _ (measurableSet_ℱ_I n k)

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

lemma measurable_ℱ_m (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (n : ℕ) :
    Measurable[ℱ n] (M κ a s n) := by
  rw [m_def]
  refine @Measurable.ennreal_toReal _ (ℱ n) _ ?_
  refine Measurable.div ?_ ?_
  · change Measurable[ℱ n] ((fun k ↦ κ a (I n k ×ˢ s)) ∘ (indexI n))
    refine Measurable.comp ?_ (measurable_indexI n)
    exact measurable_of_countable _
  · change Measurable[ℱ n] ((fun k ↦ (kernel.fst κ) a (I n k)) ∘ (indexI n))
    refine Measurable.comp ?_ (measurable_indexI n)
    exact measurable_of_countable _

lemma stronglyMeasurable_ℱ_m (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (n : ℕ) :
    StronglyMeasurable[ℱ n] (M κ a s n) :=
  (measurable_ℱ_m κ a s n).stronglyMeasurable

lemma adapted_m (κ : kernel α (ℝ × β)) (a : α) (s : Set β) : Adapted ℱ (M κ a s) :=
  stronglyMeasurable_ℱ_m κ a s

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
  refine (snorm_le_of_ae_bound (C := 1) (ae_of_all _ (fun x ↦ ?_))).trans ?_
  · simp only [Real.norm_eq_abs, abs_of_nonneg (m_nonneg κ a s n x), m_le_one κ a s n x]
  · simp

lemma integrable_m (κ : kernel α (ℝ × β)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) {s : Set β} (hs : MeasurableSet s) (n : ℕ) :
    Integrable (M κ a s n) (kernel.fst κ a) := by
  rw [← memℒp_one_iff_integrable]
  refine ⟨Measurable.aestronglyMeasurable ?_, ?_⟩
  · exact measurable_m_right κ a hs n
  · exact (snorm_m_le_one κ a s n).trans_lt ENNReal.one_lt_top

lemma set_integral_m_I (κ : kernel α (ℝ × β)) [IsFiniteKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) (n : ℕ) (k : ℤ) :
    ∫ t in I n k, M κ a s n t ∂(kernel.fst κ a) = (κ a (I n k ×ˢ s)).toReal := by
  simp_rw [M]
  rw [integral_toReal]
  rotate_left
  · refine Measurable.aemeasurable ?_
    have h := measurable_m_aux κ hs n
    change Measurable
      ((fun (p : α × ℝ) ↦ κ p.1 (I n (indexI n p.2) ×ˢ s) / kernel.fst κ p.1 (I n (indexI n p.2)))
        ∘ (fun t ↦ (a, t)))
    exact h.comp measurable_prod_mk_left
  · refine ae_of_all _ (fun t ↦ ?_)
    by_cases h0 : kernel.fst κ a (I n (indexI n t)) = 0
    · suffices κ a (I n (indexI n t) ×ˢ s) = 0 by simp [h0, this]
      rw [kernel.fst_apply' _ _ (measurableSet_I _ _)] at h0
      refine measure_mono_null (fun x ↦ ?_) h0
      simp only [mem_prod, mem_setOf_eq, and_imp]
      exact fun h _ ↦ h
    · refine ENNReal.div_lt_top ?_ h0
      exact measure_ne_top _ _
  congr
  have : ∫⁻ t in I n k, κ a (I n (indexI n t) ×ˢ s)
                        / kernel.fst κ a (I n (indexI n t)) ∂(kernel.fst κ) a
      = ∫⁻ _ in I n k, κ a (I n k ×ˢ s) / kernel.fst κ a (I n k) ∂(kernel.fst κ) a := by
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
  refine MeasurableSpace.induction_on_inter (m := ℱ n) (s := {s | ∃ k, s = I n k})
    (C := fun A ↦ ∫ t in A, M κ a s n t ∂(kernel.fst κ a) = (κ a (A ×ˢ s)).toReal) rfl
    ?_ ?_ ?_ ?_ ?_ hA
  · rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩ hst
    refine ⟨i, ?_⟩
    suffices i = j by rw [this, inter_self]
    by_contra h_ne
    have h_disj := pairwise_disjoint_I n h_ne
    rw [nonempty_iff_ne_empty] at hst
    refine hst ?_
    rwa [Function.onFun, disjoint_iff_inter_eq_empty] at h_disj
  · simp
  · rintro _ ⟨k, rfl⟩
    rw [set_integral_m_I _ _ hs]
  · intro A hA hA_eq
    have hA' : MeasurableSet A := ℱ.le _ _ hA
    have h := integral_add_compl hA' (integrable_m κ a hs n)
    rw [hA_eq, integral_m κ a hs] at h
    have : Aᶜ ×ˢ s = univ ×ˢ s \ A ×ˢ s := by
      rw [prod_diff_prod, compl_eq_univ_diff]
      simp
    rw [this, measure_diff (by intro x; simp) (hA'.prod hs) (measure_ne_top (κ a) _),
      ENNReal.toReal_sub_of_le (measure_mono (by intro x; simp)) (measure_ne_top _ _)]
    rw [eq_tsub_iff_add_eq_of_le, add_comm]
    · exact h
    · rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
      exact measure_mono (by intro x; simp)
  · intro f hf_disj hf h_eq
    rw [integral_iUnion (fun i ↦ ℱ.le n _ (hf i)) hf_disj (integrable_m κ _ hs _).integrableOn]
    simp_rw [h_eq]
    rw [iUnion_prod_const, measure_iUnion _ (fun i ↦ (ℱ.le n _ (hf i)).prod hs)]
    · rw [ENNReal.tsum_toReal_eq]
      exact fun _ ↦ measure_ne_top _ _
    · intro i j hij
      rw [Function.onFun, Set.disjoint_prod]
      exact Or.inl (hf_disj hij)

lemma set_integral_m_of_le (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) {n m : ℕ} (hnm : n ≤ m)
    {A : Set ℝ} (hA : MeasurableSet[ℱ n] A) :
    ∫ t in A, M κ a s m t ∂(kernel.fst κ a) = (κ a (A ×ˢ s)).toReal :=
  set_integral_m κ a hs m (ℱ.mono hnm A hA)

lemma condexp_m (κ : kernel α (ℝ × β)) [IsMarkovKernel κ] (a : α) {s : Set β}
    (hs : MeasurableSet s) {i j : ℕ} (hij : i ≤ j) :
    (kernel.fst κ a)[M κ a s j | ℱ i] =ᵐ[kernel.fst κ a] M κ a s i := by
  symm
  refine ae_eq_condexp_of_forall_set_integral_eq ?_ ?_ ?_ ?_ ?_
  · exact integrable_m κ a hs j
  · refine fun t _ _ ↦ Integrable.integrableOn ?_
    exact integrable_m κ _ hs _
  · intro t ht _
    rw [set_integral_m κ a hs i ht, set_integral_m_of_le κ a hs hij ht]
  · exact StronglyMeasurable.aeStronglyMeasurable' (stronglyMeasurable_ℱ_m κ a s i)

lemma martingale_m (κ : kernel α (ℝ × β)) [IsMarkovKernel κ] (a : α) {s : Set β}
    (hs : MeasurableSet s) :
    Martingale (M κ a s) ℱ (kernel.fst κ a) :=
  ⟨adapted_m κ a s, fun _ _ ↦ condexp_m κ a hs⟩

lemma m_mono_set (κ : kernel α (ℝ × β)) (a : α) {s s' : Set β} (h : s ⊆ s') (n : ℕ) (t : ℝ) :
    M κ a s n t ≤ M κ a s' n t := by
  have h_ne_top : ∀ s, κ a (I n (indexI n t) ×ˢ s) / kernel.fst κ a (I n (indexI n t)) ≠ ⊤ := by
    intro s
    rw [ne_eq, ENNReal.div_eq_top]
    push_neg
    simp_rw [kernel.fst_apply' _ _ (measurableSet_I _ _)]
    constructor
    · refine fun h h0 ↦ h (measure_mono_null (fun x ↦ ?_) h0)
      simp only [mem_prod, mem_setOf_eq, and_imp]
      exact fun h _ ↦ h
    · refine fun h_top ↦ eq_top_mono (measure_mono (fun x ↦ ?_)) h_top
      simp only [mem_prod, mem_setOf_eq, and_imp]
      exact fun h _ ↦ h
  rw [M, M, ENNReal.toReal_le_toReal]
  · gcongr
    rw [prod_subset_prod_iff]
    simp [subset_rfl, h]
  · exact h_ne_top s
  · exact h_ne_top s'

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

lemma m_empty (κ : kernel α (ℝ × β)) (a : α) (n : ℕ) (t : ℝ) :
    M κ a ∅ n t = 0 := by
  rw [M]
  simp

lemma m_univ_ae (κ : kernel α (ℝ × β)) [IsFiniteKernel κ] (a : α) (n : ℕ) :
    ∀ᵐ t ∂(kernel.fst κ a), M κ a univ n t = 1 := by
  rw [ae_iff]
  have : {t | ¬ M κ a univ n t = 1} ⊆ {t | kernel.fst κ a (I n (indexI n t)) = 0} := by
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

lemma tendsto_m_atTop_univ_of_monotone (κ : kernel α (ℝ × β))
    (a : α) (s : ℕ → Set β) (hs : Monotone s) (hs_iUnion : ⋃ i, s i = univ) (n : ℕ) (t : ℝ) :
    Tendsto (fun m ↦ M κ a (s m) n t) atTop (𝓝 (M κ a univ n t)) := by
  simp_rw [M]
  refine (ENNReal.tendsto_toReal ?_).comp ?_
  · rw [ne_eq, ENNReal.div_eq_top]
    push_neg
    simp_rw [kernel.fst_apply' _ _ (measurableSet_I _ _)]
    constructor
    · refine fun h h0 ↦ h (measure_mono_null (fun x ↦ ?_) h0)
      simp only [mem_prod, mem_setOf_eq, and_imp]
      exact fun h _ ↦ h
    · refine fun h_top ↦ eq_top_mono (measure_mono (fun x ↦ ?_)) h_top
      simp only [mem_prod, mem_setOf_eq, and_imp]
      exact fun h _ ↦ h
  by_cases h0 : kernel.fst κ a (I n (indexI n t)) = 0
  · rw [kernel.fst_apply' _ _ (measurableSet_I _ _)] at h0 ⊢
    suffices ∀ m, κ a (I n (indexI n t) ×ˢ s m) = 0 by
      simp only [this, h0, ENNReal.zero_div, tendsto_const_nhds_iff]
      suffices κ a (I n (indexI n t) ×ˢ univ) = 0 by simp only [this, ENNReal.zero_div]
      convert h0
      ext x
      simp only [mem_prod, mem_univ, and_true, mem_setOf_eq]
    refine fun m ↦ measure_mono_null (fun x ↦ ?_) h0
    simp only [mem_prod, mem_setOf_eq, and_imp]
    exact fun h _ ↦ h
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
    simp
  by_cases h0 : kernel.fst κ a (I n (indexI n t)) = 0
  · simp only [h0, prod_empty, OuterMeasure.empty', ENNReal.zero_div]
    have : ∀ m, (κ a) (I n (indexI n t) ×ˢ s m) = 0 := by
      intro m
      rw [kernel.fst_apply' _ _ (measurableSet_I _ _)] at h0
      refine measure_mono_null ?_ h0
      intro x hx
      rw [mem_prod] at hx
      exact hx.1
    simp [this]
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

lemma tendsto_m_limitProcess (κ : kernel α (ℝ × β)) (a : α) [IsMarkovKernel κ]
    {s : Set β} (hs : MeasurableSet s) :
    ∀ᵐ t ∂(kernel.fst κ a),
      Tendsto (fun n ↦ M κ a s n t) atTop (𝓝 (ℱ.limitProcess (M κ a s) (kernel.fst κ a) t)) := by
  refine Submartingale.ae_tendsto_limitProcess (martingale_m κ a hs).submartingale (R := 1) ?_
  intro n
  rw [ENNReal.coe_one]
  exact snorm_m_le_one κ a s n

lemma limitProcess_mem_L1 (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) :
    Memℒp (ℱ.limitProcess (M κ a s) (kernel.fst κ a)) 1 (kernel.fst κ a) := by
  refine Submartingale.memℒp_limitProcess (martingale_m κ a hs).submartingale (R := 1) ?_
  intro n
  rw [ENNReal.coe_one]
  exact snorm_m_le_one κ a s n

lemma tendsto_snorm_one_m_limitProcess (κ : kernel α (ℝ × β)) (a : α) [IsMarkovKernel κ]
    {s : Set β} (hs : MeasurableSet s) :
    Tendsto
      (fun n ↦ snorm (M κ a s n - ℱ.limitProcess (M κ a s) (kernel.fst κ a)) 1 (kernel.fst κ a))
      atTop (𝓝 0) := by
  refine Submartingale.tendsto_snorm_one_limitProcess ?_ ?_
  · exact (martingale_m κ a hs).submartingale
  · refine uniformIntegrable_of le_rfl ENNReal.one_ne_top ?_ ?_
    · exact fun n ↦ (measurable_m_right κ a hs n).aestronglyMeasurable
    · intro ε _
      refine ⟨2, fun n ↦ ?_⟩
      refine le_of_eq_of_le ?_ (?_ : 0 ≤ ENNReal.ofReal ε)
      · have : {x | 2 ≤ ‖M κ a s n x‖₊} = ∅ := by
          ext x
          simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
          refine (?_ : _ ≤ (1 : ℝ≥0)).trans_lt one_lt_two
          rw [Real.nnnorm_of_nonneg (m_nonneg _ _ _ _ _)]
          exact mod_cast (m_le_one _ _ _ _ _)
        rw [this]
        simp
      · simp

lemma snorm_restrict_le [NormedAddCommGroup β] {p : ℝ≥0∞} {f : α → β} {μ : Measure α} (s : Set α) :
    snorm f p (μ.restrict s) ≤ snorm f p μ :=
  snorm_mono_measure f Measure.restrict_le_self

lemma tendsto_snorm_restrict_zero {α β ι : Type*} {mα : MeasurableSpace α} [NormedAddCommGroup β]
    {p : ℝ≥0∞} {f : ι → α → β} {μ : Measure α} {l : Filter ι}
    (h : Tendsto (fun n ↦ snorm (f n) p μ) l (𝓝 0)) (s : Set α) :
    Tendsto (fun n ↦ snorm (f n) p (μ.restrict s)) l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h ?_ ?_
  · exact fun _ ↦ zero_le _
  · exact fun _ ↦ snorm_restrict_le _

lemma tendsto_snorm_one_restrict_m_limitProcess (κ : kernel α (ℝ × β)) (a : α) [IsMarkovKernel κ]
    {s : Set β} (hs : MeasurableSet s) (A : Set ℝ) :
    Tendsto (fun n ↦ snorm (M κ a s n - ℱ.limitProcess (M κ a s) (kernel.fst κ a)) 1
        ((kernel.fst κ a).restrict A))
      atTop (𝓝 0) :=
  tendsto_snorm_restrict_zero (tendsto_snorm_one_m_limitProcess κ a hs) A

noncomputable
def MLimsup (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (t : ℝ) : ℝ :=
  limsup (fun n ↦ M κ a s n t) atTop

lemma mLimsup_ae_eq_limitProcess (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) :
    MLimsup κ a s =ᵐ[kernel.fst κ a] ℱ.limitProcess (M κ a s) (kernel.fst κ a) := by
  filter_upwards [tendsto_m_limitProcess κ a hs] with t ht using ht.limsup_eq

lemma tendsto_m_mLimsup (κ : kernel α (ℝ × β)) (a : α) [IsMarkovKernel κ]
    {s : Set β} (hs : MeasurableSet s) :
    ∀ᵐ t ∂(kernel.fst κ a),
      Tendsto (fun n ↦ M κ a s n t) atTop (𝓝 (MLimsup κ a s t)) := by
  filter_upwards [tendsto_m_limitProcess κ a hs, mLimsup_ae_eq_limitProcess κ a hs] with t h1 h2
  rw [h2]
  exact h1

lemma measurable_mLimsup (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) :
    Measurable (fun (p : α × ℝ) ↦ MLimsup κ p.1 s p.2) :=
  measurable_limsup (fun n ↦ measurable_m κ hs n)

lemma measurable_mLimsup_left (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) (t : ℝ) :
    Measurable (fun a ↦ MLimsup κ a s t) := by
  change Measurable ((fun (p : α × ℝ) ↦ MLimsup κ p.1 s p.2) ∘ (fun a ↦ (a, t)))
  exact (measurable_mLimsup κ hs).comp (measurable_id.prod_mk measurable_const)

lemma measurable_mLimsup_right (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) (a : α) :
    Measurable (MLimsup κ a s) := by
  change Measurable ((fun (p : α × ℝ) ↦ MLimsup κ p.1 s p.2) ∘ (fun t ↦ (a, t)))
  exact (measurable_mLimsup κ hs).comp (measurable_const.prod_mk measurable_id)

lemma mLimsup_mono_set (κ : kernel α (ℝ × β)) (a : α) {s s' : Set β} (h : s ⊆ s') (t : ℝ) :
    MLimsup κ a s t ≤ MLimsup κ a s' t := by
  rw [MLimsup, MLimsup]
  refine limsup_le_limsup ?_ ?_ ?_
  · exact eventually_of_forall (fun n ↦ m_mono_set κ a h n t)
  · -- todo: extract lemma (of find it)
    refine ⟨0, ?_⟩
    simp only [eventually_map, eventually_atTop, ge_iff_le, forall_exists_index]
    intro x n h
    specialize h n le_rfl
    exact (m_nonneg _ _ _ _ _).trans h
  · -- todo: extract lemma (of find it)
    refine ⟨1, ?_⟩
    simp only [eventually_map, eventually_atTop, ge_iff_le]
    exact ⟨0, fun n _ ↦ m_le_one _ _ _ _ _⟩

lemma mLimsup_nonneg (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (t : ℝ) :
    0 ≤ MLimsup κ a s t := by
  refine le_limsup_of_frequently_le ?_ ?_
  · exact frequently_of_forall (fun n ↦ m_nonneg _ _ _ _ _)
  · -- todo: extract lemma (of find it)
    refine ⟨1, ?_⟩
    simp only [eventually_map, eventually_atTop, ge_iff_le]
    exact ⟨0, fun n _ ↦ m_le_one _ _ _ _ _⟩

lemma mLimsup_le_one (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (t : ℝ) :
    MLimsup κ a s t ≤ 1 := by
  refine limsup_le_of_le ?_ ?_
  · -- todo: extract lemma (of find it)
    refine ⟨0, ?_⟩
    simp only [eventually_map, eventually_atTop, ge_iff_le, forall_exists_index]
    intro x n h
    specialize h n le_rfl
    exact (m_nonneg _ _ _ _ _).trans h
  · exact eventually_of_forall (fun n ↦ m_le_one _ _ _ _ _)

lemma mLimsup_univ (κ : kernel α (ℝ × β)) [IsFiniteKernel κ] (a : α) :
    ∀ᵐ t ∂(kernel.fst κ a), MLimsup κ a Set.univ t = 1 := by
  have h := m_univ_ae κ a
  rw [← ae_all_iff] at h
  filter_upwards [h] with t ht
  rw [MLimsup]
  simp_rw [ht]
  rw [limsup_const] -- should be simp

lemma snorm_mLimsup_le_one (κ : kernel α (ℝ × β)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) (s : Set β) :
    snorm (fun t ↦ MLimsup κ a s t) 1 (kernel.fst κ a) ≤ 1 := by
  refine (snorm_le_of_ae_bound (C := 1) (ae_of_all _ (fun t ↦ ?_))).trans ?_
  · simp only [Real.norm_eq_abs, abs_of_nonneg (mLimsup_nonneg κ a s t),
      mLimsup_le_one κ a s t]
  · simp

lemma integrable_mLimsup (κ : kernel α (ℝ × β)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun t ↦ MLimsup κ a s t) (kernel.fst κ a) := by
  rw [← memℒp_one_iff_integrable]
  refine ⟨Measurable.aestronglyMeasurable ?_, ?_⟩
  · exact measurable_mLimsup_right κ hs a
  · exact (snorm_mLimsup_le_one κ a s).trans_lt ENNReal.one_lt_top

lemma tendsto_integral_of_L1' {ι G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure α}
    (f : α → G) (hfi : Integrable f μ)
    {F : ι → α → G} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ)
    (hF : Tendsto (fun i ↦ snorm (F i - f) 1 μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, F i x ∂μ) l (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [snorm_one_eq_lintegral_nnnorm, Pi.sub_apply] at hF
  exact hF

lemma tendsto_set_integral_of_L1 {ι G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure α}
    (f : α → G) (hfi : Integrable f μ)
    {F : ι → α → G} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ)
    (hF : Tendsto (fun i ↦ ∫⁻ x, ‖F i x - f x‖₊ ∂μ) l (𝓝 0)) (s : Set α) :
    Tendsto (fun i ↦ ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  refine tendsto_integral_of_L1 f hfi.restrict ?_ ?_
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← snorm_one_eq_lintegral_nnnorm] at hF ⊢
    exact tendsto_snorm_restrict_zero hF s

lemma tendsto_set_integral_of_L1' {ι G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure α}
    (f : α → G) (hfi : Integrable f μ)
    {F : ι → α → G} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ)
    (hF : Tendsto (fun i ↦ snorm (F i - f) 1 μ) l (𝓝 0)) (s : Set α) :
    Tendsto (fun i ↦ ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  refine tendsto_set_integral_of_L1 f hfi hFi ?_ s
  simp_rw [snorm_one_eq_lintegral_nnnorm, Pi.sub_apply] at hF
  exact hF

lemma tendsto_set_integral_m (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) (A : Set ℝ) :
    Tendsto (fun i ↦ ∫ x in A, M κ a s i x ∂(kernel.fst κ) a) atTop
      (𝓝 (∫ x in A, MLimsup κ a s x ∂(kernel.fst κ) a)) := by
  refine tendsto_set_integral_of_L1' (μ := kernel.fst κ a) (MLimsup κ a s)
    (integrable_mLimsup κ a hs) (F := fun i t ↦ M κ a s i t) (l := atTop)
    (eventually_of_forall (fun n ↦ integrable_m _ _ hs _)) ?_ A
  refine (tendsto_congr fun n ↦ ?_).mp (tendsto_snorm_one_m_limitProcess κ a hs)
  refine snorm_congr_ae ?_
  refine EventuallyEq.sub EventuallyEq.rfl ?_
  exact (mLimsup_ae_eq_limitProcess κ a hs).symm

lemma set_integral_mLimsup_of_measurableSet (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) (n : ℕ)
    {A : Set ℝ} (hA : MeasurableSet[ℱ n] A) :
    ∫ t in A, MLimsup κ a s t ∂(kernel.fst κ a) = (κ a (A ×ˢ s)).toReal := by
  suffices ∫ t in A, MLimsup κ a s t ∂(kernel.fst κ a) = ∫ t in A, M κ a s n t ∂(kernel.fst κ a) by
    rw [this]
    exact set_integral_m _ _ hs _ hA
  suffices ∫ t in A, MLimsup κ a s t ∂(kernel.fst κ a)
      = limsup (fun i ↦ ∫ t in A, M κ a s i t ∂(kernel.fst κ a)) atTop by
    rw [this, ← limsup_const (α := ℕ) (f := atTop) (∫ t in A, M κ a s n t ∂(kernel.fst κ a)),
      limsup_congr]
    simp only [eventually_atTop, ge_iff_le]
    refine ⟨n, fun m hnm ↦ ?_⟩
    rw [set_integral_m_of_le _ _ hs hnm hA, set_integral_m _ _ hs _ hA]
  -- use L1 convergence
  have h := tendsto_set_integral_m κ a hs A
  rw [h.limsup_eq]

lemma integral_mLimsup (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) :
    ∫ t, MLimsup κ a s t ∂(kernel.fst κ a) = (κ a (univ ×ˢ s)).toReal := by
  rw [← integral_univ, set_integral_mLimsup_of_measurableSet κ a hs 0 MeasurableSet.univ]

lemma set_integral_mLimsup (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) {A : Set ℝ} (hA : MeasurableSet A) :
    ∫ t in A, MLimsup κ a s t ∂(kernel.fst κ a) = (κ a (A ×ˢ s)).toReal := by
  have hA' : MeasurableSet[⨆ n, ℱ n] A := by rwa [iSup_ℱ]
  refine MeasurableSpace.induction_on_inter (m := ⨆ n, ℱ n)
    (C := fun A ↦ ∫ t in A, MLimsup κ a s t ∂(kernel.fst κ a) = (κ a (A ×ˢ s)).toReal)
    (MeasurableSpace.measurableSpace_iSup_eq ℱ) ?_ ?_ ?_ ?_ ?_ hA'
  · rintro s ⟨n, hs⟩ t ⟨m, ht⟩ _
    exact ⟨max n m, (ℱ.mono (le_max_left n m) _ hs).inter (ℱ.mono (le_max_right n m) _ ht)⟩
  · simp
  · intro A ⟨n, hA⟩
    exact set_integral_mLimsup_of_measurableSet κ a hs n hA
  · intro A hA hA_eq
    rw [iSup_ℱ] at hA
    have h := integral_add_compl hA (integrable_mLimsup κ a hs)
    rw [hA_eq, integral_mLimsup κ a hs] at h
    have : Aᶜ ×ˢ s = univ ×ˢ s \ A ×ˢ s := by
      rw [prod_diff_prod, compl_eq_univ_diff]
      simp
    rw [this, measure_diff (by intro x; simp) (hA.prod hs) (measure_ne_top (κ a) _),
      ENNReal.toReal_sub_of_le (measure_mono (by intro x; simp)) (measure_ne_top _ _)]
    rw [eq_tsub_iff_add_eq_of_le, add_comm]
    · exact h
    · rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
      exact measure_mono (by intro x; simp)
  · intro f hf_disj hf h_eq
    rw [integral_iUnion _ hf_disj (integrable_mLimsup _ _ hs).integrableOn]
    · simp_rw [h_eq]
      rw [← ENNReal.tsum_toReal_eq (fun _ ↦ measure_ne_top _ _)]
      congr
      rw [iUnion_prod_const, measure_iUnion]
      · intro i j hij
        rw [Function.onFun, Set.disjoint_prod]
        exact Or.inl (hf_disj hij)
      · rw [iSup_ℱ] at hf
        exact fun i ↦ (hf i).prod hs
    · rwa [iSup_ℱ] at hf

lemma tendsto_mLimsup_atTop_ae_of_monotone (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Monotone s) (hs_iUnion : ⋃ i, s i = univ)
    (hs_meas : ∀ n, MeasurableSet (s n)) :
    ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun m ↦ MLimsup κ a (s m) t) atTop (𝓝 1) := by
  have h1 := tendsto_m_atTop_ae_of_monotone κ a s hs hs_iUnion
  have h2 := fun (n : ℕ) ↦ tendsto_m_mLimsup κ a (hs_meas n)
  rw [← ae_all_iff] at h1 h2
  filter_upwards [h1, h2] with t h_tendsto_set h_tendsto_nat
  sorry

lemma tendsto_mLimsup_atTop_ae_of_antitone (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Antitone s) (hs_iInter : ⋂ i, s i = ∅)
    (hs_meas : ∀ n, MeasurableSet (s n)) :
    ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun m ↦ MLimsup κ a (s m) t) atTop (𝓝 0) := by
  have h1 := tendsto_m_atTop_of_antitone κ a s hs hs_iInter hs_meas
  have h2 := fun (n : ℕ) ↦ tendsto_m_mLimsup κ a (hs_meas n)
  rw [← ae_all_iff] at h2
  filter_upwards [h2] with t h_tendsto_nat
  sorry

section Iic_Q

noncomputable
def mLimsupIic (κ : kernel α (ℝ × ℝ)) (a : α) (t : ℝ) (q : ℚ) : ℝ := MLimsup κ a (Set.Iic q) t

lemma measurable_mLimsupIic (κ : kernel α (ℝ × ℝ)) (q : ℚ) :
    Measurable (fun p : α × ℝ ↦ mLimsupIic κ p.1 p.2 q) :=
  measurable_mLimsup κ measurableSet_Iic

lemma measurable_mLimsupIic_right (κ : kernel α (ℝ × ℝ)) (a : α) (q : ℚ) :
    Measurable (fun t ↦ mLimsupIic κ a t q) :=
  measurable_mLimsup_right _ measurableSet_Iic _

lemma monotone_mLimsupIic (κ : kernel α (ℝ × ℝ)) (a : α) (t : ℝ) : Monotone (mLimsupIic κ a t) := by
  intro q r hqr
  rw [mLimsupIic, mLimsupIic]
  refine mLimsup_mono_set κ a ?_ t
  refine Iic_subset_Iic.mpr ?_
  exact_mod_cast hqr

lemma mLimsupIic_nonneg (κ : kernel α (ℝ × ℝ)) (a : α) (t : ℝ) (q : ℚ) : 0 ≤ mLimsupIic κ a t q :=
  mLimsup_nonneg κ a _ t

lemma mLimsupIic_le_one (κ : kernel α (ℝ × ℝ)) (a : α) (t : ℝ) (q : ℚ) : mLimsupIic κ a t q ≤ 1 :=
  mLimsup_le_one κ a _ t

lemma tendsto_atTop_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) :
    ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun q ↦ mLimsupIic κ a t q) atTop (𝓝 1) := by
  suffices ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun (n : ℕ) ↦ mLimsupIic κ a t n) atTop (𝓝 1) by
    sorry
  let s : ℕ → Set ℝ := fun n ↦ Iic n
  have hs : Monotone s := fun i j hij ↦ Iic_subset_Iic.mpr (by exact mod_cast hij)
  have hs_iUnion : ⋃ i, s i = univ := by
    ext x
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact ⟨Nat.ceil x, Nat.le_ceil x⟩
  have hs_meas : ∀ n, MeasurableSet (s n) := fun _ ↦ measurableSet_Iic
  filter_upwards [tendsto_mLimsup_atTop_ae_of_monotone κ a s hs hs_iUnion hs_meas]
    with x hx using hx

lemma tendsto_atBot_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) :
    ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun q ↦ mLimsupIic κ a t q) atBot (𝓝 0) := by
  suffices ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun q ↦ mLimsupIic κ a t (-q)) atTop (𝓝 0) by
    filter_upwards [this] with t ht
    have h_eq_neg : (fun q ↦ mLimsupIic κ a t q) = fun q ↦ mLimsupIic κ a t (- -q) := by
      simp_rw [neg_neg]
    rw [h_eq_neg]
    exact ht.comp tendsto_neg_atBot_atTop
  suffices ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun (n : ℕ) ↦ mLimsupIic κ a t (-n)) atTop (𝓝 0) by
    sorry
  let s : ℕ → Set ℝ := fun n ↦ Iic (-n)
  have hs : Antitone s := fun i j hij ↦ Iic_subset_Iic.mpr (neg_le_neg (by exact mod_cast hij))
  have hs_iInter : ⋂ i, s i = ∅ := by
    ext x
    simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le, neg_lt]
    exact exists_nat_gt (-x)
  have hs_meas : ∀ n, MeasurableSet (s n) := fun _ ↦ measurableSet_Iic
  convert tendsto_mLimsup_atTop_ae_of_antitone κ a s hs hs_iInter hs_meas with x n
  rw [mLimsupIic]
  simp

lemma set_integral_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ]
    (a : α) (q : ℚ) {A : Set ℝ} (hA : MeasurableSet A) :
    ∫ t in A, mLimsupIic κ a t q ∂(kernel.fst κ a) = (κ a (A ×ˢ Iic (q : ℝ))).toReal :=
  set_integral_mLimsup κ a measurableSet_Iic hA

lemma integrable_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) (q : ℚ) :
    Integrable (fun t ↦ mLimsupIic κ a t q) (kernel.fst κ a) :=
  integrable_mLimsup _ _ measurableSet_Iic

lemma bddBelow_range_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) (t : ℝ) (q : ℚ) :
    BddBelow (range fun (r : Ioi q) ↦ mLimsupIic κ a t r) := by
  refine ⟨0, ?_⟩
  rw [mem_lowerBounds]
  rintro x ⟨y, rfl⟩
  exact mLimsupIic_nonneg _ _ _ _

lemma integrable_iInf_rat_gt_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) (q : ℚ) :
    Integrable (fun t ↦ ⨅ r : Ioi q, mLimsupIic κ a t r) (kernel.fst κ a) := by
  rw [← memℒp_one_iff_integrable]
  refine ⟨Measurable.aestronglyMeasurable ?_, ?_⟩
  · exact measurable_iInf fun i ↦ measurable_mLimsupIic_right κ a i
  refine (?_ : _ ≤ (1 : ℝ≥0∞)).trans_lt ENNReal.one_lt_top
  refine (snorm_le_of_ae_bound (C := 1) (ae_of_all _ (fun t ↦ ?_))).trans ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg]
    · refine ciInf_le_of_le ?_ ?_ ?_
      · exact bddBelow_range_mLimsupIic κ a t _
      · exact ⟨q + 1, by simp⟩
      · exact mLimsupIic_le_one _ _ _ _
    · exact le_ciInf fun r ↦ mLimsupIic_nonneg κ a t r
  · simp

lemma set_integral_iInf_rat_gt_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ]
    (a : α) (q : ℚ) {A : Set ℝ} (hA : MeasurableSet A) :
    ∫ t in A, ⨅ r : Ioi q, mLimsupIic κ a t r ∂(kernel.fst κ a)
      = (κ a (A ×ˢ Iic (q : ℝ))).toReal := by
  refine le_antisymm ?_ ?_
  · have h : ∀ r : Ioi q, ∫ t in A, ⨅ r' : Ioi q, mLimsupIic κ a t r' ∂(kernel.fst κ a)
        ≤ (κ a (A ×ˢ Iic (r : ℝ))).toReal := by
      intro r
      rw [← set_integral_mLimsupIic κ a r hA]
      refine set_integral_mono ?_ ?_ ?_
      · exact (integrable_iInf_rat_gt_mLimsupIic _ _ _).integrableOn
      · exact (integrable_mLimsupIic _ _ _).integrableOn
      · exact fun t ↦ ciInf_le (bddBelow_range_mLimsupIic _ _ _ _) r
    calc ∫ t in A, ⨅ r : Ioi q, mLimsupIic κ a t r ∂(kernel.fst κ a)
      ≤ ⨅ r : Ioi q, (κ a (A ×ˢ Iic (r : ℝ))).toReal := le_ciInf h
    _ = (κ a (A ×ˢ Iic (q : ℝ))).toReal := by
        rw [← Measure.iInf_Iic_gt_prod hA q]
        exact (ENNReal.toReal_iInf (fun r ↦ measure_ne_top _ _)).symm
  · rw [← set_integral_mLimsupIic κ a q hA]
    refine set_integral_mono ?_ ?_ ?_
    · exact (integrable_mLimsupIic _ _ _).integrableOn
    · exact (integrable_iInf_rat_gt_mLimsupIic _ _ _).integrableOn
    · exact fun t ↦ le_ciInf (fun r ↦ monotone_mLimsupIic _ _ _ (le_of_lt r.prop))

lemma iInf_rat_gt_mLimsupIic_eq (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) :
    ∀ᵐ t ∂(kernel.fst κ a), ∀ q : ℚ, ⨅ r : Ioi q, mLimsupIic κ a t r = mLimsupIic κ a t q := by
  rw [ae_all_iff]
  refine fun q ↦ ae_eq_of_forall_set_integral_eq_of_sigmaFinite (μ := kernel.fst κ a) ?_ ?_ ?_
  · intro s _ _
    refine Integrable.integrableOn ?_
    exact integrable_iInf_rat_gt_mLimsupIic κ _ _
  · exact fun s _ _ ↦ (integrable_mLimsupIic κ a q).integrableOn
  · intro s hs _
    rw [set_integral_mLimsupIic _ _ _ hs, set_integral_iInf_rat_gt_mLimsupIic _ _ _ hs]

end Iic_Q

section Rat

lemma isRatStieltjesPoint_mLimsupIic_ae (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) :
    ∀ᵐ t ∂(kernel.fst κ a), IsRatStieltjesPoint (fun p q ↦ mLimsupIic κ p.1 p.2 q) (a, t) := by
  filter_upwards [tendsto_atTop_mLimsupIic κ a, tendsto_atBot_mLimsupIic κ a,
    iInf_rat_gt_mLimsupIic_eq κ a] with t ht_top ht_bot ht_iInf
  constructor
  · exact monotone_mLimsupIic κ a t
  · exact mLimsupIic_nonneg κ a t
  · exact mLimsupIic_le_one κ a t
  · exact ht_top
  · exact ht_bot
  · exact ht_iInf

lemma todo3_mLimsupIic_ae_eq (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) (q : ℚ) :
    (fun t ↦ todo3 _ (measurable_mLimsupIic κ) (a, t) q)
      =ᵐ[kernel.fst κ a] fun t ↦ mLimsupIic κ a t q := by
  filter_upwards [isRatStieltjesPoint_mLimsupIic_ae κ a] with a ha
  rw [todo3_eq, toCDFLike_of_isRatStieltjesPoint ha]

end Rat

-- todo: name?
noncomputable
def kernel.condexpReal (κ : kernel α (ℝ × ℝ)) : kernel (α × ℝ) ℝ :=
  cdfKernel (measurable_mLimsupIic κ)

instance (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] : IsMarkovKernel (kernel.condexpReal κ) := by
  unfold kernel.condexpReal; infer_instance

lemma condexpReal_Iic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) (t x : ℝ) :
    kernel.condexpReal κ (a, t) (Iic x)
      = ENNReal.ofReal (todo3 _ (measurable_mLimsupIic κ) (a, t) x) :=
  cdfKernel_Iic _ _

lemma set_lintegral_condexpReal_Iic_rat (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) (q : ℚ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ∫⁻ t in s, kernel.condexpReal κ (a, t) (Iic q) ∂(kernel.fst κ a) = κ a (s ×ˢ Iic (q : ℝ)) := by
  simp_rw [condexpReal_Iic]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [set_integral_congr_ae (g := fun t ↦ mLimsupIic κ a t q) hs,
      set_integral_mLimsupIic κ _ _ hs, ENNReal.ofReal_toReal]
    · exact measure_ne_top _ _
    · filter_upwards [todo3_mLimsupIic_ae_eq κ a q] with t ht
      exact fun _ ↦ ht
  · refine Integrable.restrict ?_
    rw [integrable_congr (todo3_mLimsupIic_ae_eq κ a q)]
    exact integrable_mLimsupIic _ _ _
  · exact ae_of_all _ (fun x ↦ todo3_nonneg _ _ _)

lemma set_lintegral_condexpReal_Iic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) (x : ℝ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ∫⁻ t in s, kernel.condexpReal κ (a, t) (Iic x) ∂(kernel.fst κ a) = κ a (s ×ˢ Iic x) := by
  -- We have the result for `x : ℚ` thanks to `set_lintegral_condexpReal_Iic_rat`.
  -- We use the equality `condCDF ρ a x = ⨅ r : {r' : ℚ // x < r'}, condCDF ρ a r` and a monotone
  -- convergence argument to extend it to the reals.
  by_cases hρ_zero : (kernel.fst κ a).restrict s = 0
  · rw [hρ_zero, lintegral_zero_measure]
    refine le_antisymm (zero_le _) ?_
    calc κ a (s ×ˢ Iic x)
      ≤ κ a (Prod.fst ⁻¹' s) := measure_mono (prod_subset_preimage_fst s (Iic x))
    _ = kernel.fst κ a s := by rw [kernel.fst_apply' _ _ hs]; rfl
    _ = (kernel.fst κ a).restrict s univ := by rw [Measure.restrict_apply_univ]
    _ = 0 := by simp only [hρ_zero, Measure.coe_zero, Pi.zero_apply]
  have h : ∫⁻ t in s, kernel.condexpReal κ (a, t) (Iic x) ∂(kernel.fst κ a)
      = ∫⁻ t in s, ⨅ r : { r' : ℚ // x < r' },
        kernel.condexpReal κ (a, t) (Iic r) ∂(kernel.fst κ a) := by
    congr with t : 1
    rw [← measure_iInter_eq_iInf]
    · congr with y : 1
      simp only [mem_Iic, mem_iInter, Subtype.forall]
      refine ⟨fun h a ha ↦ h.trans ?_, fun h ↦ ?_⟩
      · exact mod_cast ha.le
      · refine le_of_forall_lt_rat_imp_le fun q hq ↦ h q ?_
        exact mod_cast hq
    · exact fun _ ↦ measurableSet_Iic
    · refine Monotone.directed_ge fun r r' hrr' ↦ ?_
      refine Iic_subset_Iic.mpr ?_
      exact mod_cast hrr'
    · obtain ⟨q, hq⟩ := exists_rat_gt x
      exact ⟨⟨q, hq⟩, measure_ne_top _ _⟩
  have h_nonempty : Nonempty { r' : ℚ // x < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt x
    exact ⟨⟨r, hrx⟩⟩
  rw [h, lintegral_iInf_directed_of_measurable hρ_zero fun q : { r' : ℚ // x < ↑r' } ↦ ?_]
  rotate_left
  · intro b
    rw [set_lintegral_condexpReal_Iic_rat _ _ _ hs]
    exact measure_ne_top _ _
  · refine Monotone.directed_ge fun i j hij t ↦ measure_mono (Iic_subset_Iic.mpr ?_)
    exact mod_cast hij
  · exact (kernel.measurable_coe _ measurableSet_Iic).comp measurable_prod_mk_left
  simp_rw [set_lintegral_condexpReal_Iic_rat κ _ _ hs]
  rw [← measure_iInter_eq_iInf]
  · rw [← prod_iInter]
    congr with y
    simp only [mem_iInter, mem_Iic, Subtype.forall, Subtype.coe_mk]
    exact ⟨le_of_forall_lt_rat_imp_le, fun hyx q hq ↦ hyx.trans hq.le⟩
  · exact fun i ↦ hs.prod measurableSet_Iic
  · refine Monotone.directed_ge fun i j hij ↦ ?_
    refine prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, Iic_subset_Iic.mpr ?_⟩)
    exact mod_cast hij
  · exact ⟨h_nonempty.some, measure_ne_top _ _⟩

lemma set_lintegral_condexpReal_univ (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ∫⁻ t in s, kernel.condexpReal κ (a, t) univ ∂(kernel.fst κ a) = κ a (s ×ˢ univ) := by
  simp only [measure_univ, lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    one_mul, kernel.fst_apply' _ _ hs]
  congr with x
  simp only [mem_prod, mem_univ, and_true, mem_setOf_eq]

lemma lintegral_condexpReal_univ (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) :
    ∫⁻ t, kernel.condexpReal κ (a, t) univ ∂(kernel.fst κ a) = κ a univ := by
  rw [← set_lintegral_univ, set_lintegral_condexpReal_univ κ a MeasurableSet.univ,
    univ_prod_univ]

lemma set_lintegral_condexpReal_prod (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α)
    {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫⁻ x in s, kernel.condexpReal κ (a, x) t ∂(kernel.fst κ a) = κ a (s ×ˢ t) := by
  -- `set_lintegral_condKernelReal_Iic` gives the result for `t = Iic x`. These sets form a
  -- π-system that generates the Borel σ-algebra, hence we can get the same equality for any
  -- measurable set `t`.
  apply MeasurableSpace.induction_on_inter (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic _ _ _ _ ht
  · simp only [measure_empty, lintegral_const, zero_mul, prod_empty]
  · rintro t ⟨q, rfl⟩
    exact set_lintegral_condexpReal_Iic κ a _ hs
  · intro t ht ht_lintegral
    calc ∫⁻ x in s, kernel.condexpReal κ (a, x) tᶜ ∂(kernel.fst κ a)
      = ∫⁻ x in s, kernel.condexpReal κ (a, x) univ - kernel.condexpReal κ (a, x) t ∂(kernel.fst κ a) := by
          congr with x; rw [measure_compl ht (measure_ne_top (kernel.condexpReal κ (a, x)) _)]
    _ = ∫⁻ x in s, kernel.condexpReal κ (a, x) univ ∂(kernel.fst κ a)
          - ∫⁻ x in s, kernel.condexpReal κ (a, x) t ∂(kernel.fst κ a) := by
        rw [lintegral_sub]
        · exact (kernel.measurable_coe (kernel.condexpReal κ) ht).comp measurable_prod_mk_left
        · rw [ht_lintegral]
          exact measure_ne_top _ _
        · exact eventually_of_forall fun a ↦ measure_mono (subset_univ _)
    _ = κ a (s ×ˢ univ) - κ a (s ×ˢ t) := by
        rw [set_lintegral_condexpReal_univ κ a hs, ht_lintegral]
    _ = κ a (s ×ˢ tᶜ) := by
        rw [← measure_diff _ (hs.prod ht) (measure_ne_top _ _)]
        · rw [prod_diff_prod, compl_eq_univ_diff]
          simp only [diff_self, empty_prod, union_empty]
        · rw [prod_subset_prod_iff]
          exact Or.inl ⟨subset_rfl, subset_univ t⟩
  · intro f hf_disj hf_meas hf_eq
    simp_rw [measure_iUnion hf_disj hf_meas]
    rw [lintegral_tsum, prod_iUnion, measure_iUnion]
    · simp_rw [hf_eq]
    · intro i j hij
      rw [Function.onFun, Set.disjoint_prod]
      exact Or.inr (hf_disj hij)
    · exact fun i ↦ MeasurableSet.prod hs (hf_meas i)
    · exact fun i ↦
        ((kernel.measurable_coe _ (hf_meas i)).comp measurable_prod_mk_left).aemeasurable.restrict

lemma lintegral_condexpReal_mem (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    ∫⁻ x, kernel.condexpReal κ (a, x) {y | (x, y) ∈ s} ∂(kernel.fst κ a) = κ a s := by
  -- `set_lintegral_condKernelReal_prod` gives the result for sets of the form `t₁ × t₂`. These
  -- sets form a π-system that generates the product σ-algebra, hence we can get the same equality
  -- for any measurable set `s`.
  apply MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod _ _ _ _ hs
  · simp only [mem_empty_iff_false, setOf_false, measure_empty, lintegral_const,
      zero_mul]
  · rintro _ ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    simp only [mem_setOf_eq] at ht₁ ht₂
    have h_prod_eq_snd : ∀ a ∈ t₁, {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} = t₂ := by
      intro a ha
      simp only [ha, prod_mk_mem_set_prod_eq, true_and_iff, setOf_mem_eq]
    rw [← lintegral_add_compl _ ht₁]
    have h_eq1 : ∫⁻ x in t₁, kernel.condexpReal κ (a, x) {y : ℝ | (x, y) ∈ t₁ ×ˢ t₂} ∂(kernel.fst κ a)
        = ∫⁻ x in t₁, kernel.condexpReal κ (a, x) t₂ ∂(kernel.fst κ a) := by
      refine' set_lintegral_congr_fun ht₁ (eventually_of_forall fun a ha ↦ _)
      rw [h_prod_eq_snd a ha]
    have h_eq2 : ∫⁻ x in t₁ᶜ, kernel.condexpReal κ (a, x) {y : ℝ | (x, y) ∈ t₁ ×ˢ t₂} ∂(kernel.fst κ a) = 0 := by
      suffices h_eq_zero : ∀ x ∈ t₁ᶜ, kernel.condexpReal κ (a, x) {y : ℝ | (x, y) ∈ t₁ ×ˢ t₂} = 0
      · rw [set_lintegral_congr_fun ht₁.compl (eventually_of_forall h_eq_zero)]
        simp only [lintegral_const, zero_mul]
      intro a hat₁
      rw [mem_compl_iff] at hat₁
      simp only [hat₁, prod_mk_mem_set_prod_eq, false_and_iff, setOf_false, measure_empty]
    rw [h_eq1, h_eq2, add_zero]
    exact set_lintegral_condexpReal_prod κ a ht₁ ht₂
  · intro t ht ht_eq
    calc ∫⁻ x, kernel.condexpReal κ (a, x) {y : ℝ | (x, y) ∈ tᶜ} ∂(kernel.fst κ a)
      = ∫⁻ x, kernel.condexpReal κ (a, x) {y : ℝ | (x, y) ∈ t}ᶜ ∂(kernel.fst κ a) := rfl
    _ = ∫⁻ x, kernel.condexpReal κ (a, x) univ
          - kernel.condexpReal κ (a, x) {y : ℝ | (x, y) ∈ t} ∂(kernel.fst κ a) := by
        congr with x : 1
        exact measure_compl (measurable_prod_mk_left ht)
          (measure_ne_top (kernel.condexpReal κ (a, x)) _)
    _ = ∫⁻ x, kernel.condexpReal κ (a, x) univ ∂(kernel.fst κ a) -
          ∫⁻ x, kernel.condexpReal κ (a, x) {y : ℝ | (x, y) ∈ t} ∂(kernel.fst κ a) := by
        have h_le : (fun x ↦ kernel.condexpReal κ (a, x) {y : ℝ | (x, y) ∈ t})
              ≤ᵐ[kernel.fst κ a] fun x ↦ kernel.condexpReal κ (a, x) univ :=
          eventually_of_forall fun _ ↦ measure_mono (subset_univ _)
        rw [lintegral_sub _ _ h_le]
        · exact kernel.measurable_kernel_prod_mk_left' ht a
        refine ((lintegral_mono_ae h_le).trans_lt ?_).ne
        rw [lintegral_condexpReal_univ]
        exact measure_lt_top _ univ
    _ = κ a univ - κ a t := by rw [ht_eq, lintegral_condexpReal_univ]
    _ = κ a tᶜ := (measure_compl ht (measure_ne_top _ _)).symm
  · intro f hf_disj hf_meas hf_eq
    have h_eq : ∀ a, {x | (a, x) ∈ ⋃ i, f i} = ⋃ i, {x | (a, x) ∈ f i} := by
      intro a; ext x; simp only [mem_iUnion, mem_setOf_eq]
    simp_rw [h_eq]
    have h_disj : ∀ a, Pairwise (Disjoint on fun i ↦ {x | (a, x) ∈ f i}) := by
      intro a i j hij
      have h_disj := hf_disj hij
      rw [Function.onFun, disjoint_iff_inter_eq_empty] at h_disj ⊢
      ext1 x
      simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false_iff]
      intro h_mem_both
      suffices (a, x) ∈ ∅ by rwa [mem_empty_iff_false] at this
      rwa [← h_disj, mem_inter_iff]
    calc ∫⁻ x, kernel.condexpReal κ (a, x) (⋃ i, {y | (x, y) ∈ f i}) ∂(kernel.fst κ a)
      = ∫⁻ x, ∑' i, kernel.condexpReal κ (a, x) {y | (x, y) ∈ f i} ∂(kernel.fst κ a) := by
          congr with x : 1
          rw [measure_iUnion (h_disj x) fun i ↦ measurable_prod_mk_left (hf_meas i)]
    _ = ∑' i, ∫⁻ x, kernel.condexpReal κ (a, x) {y | (x, y) ∈ f i} ∂(kernel.fst κ a) :=
          lintegral_tsum fun i ↦ (kernel.measurable_kernel_prod_mk_left' (hf_meas i) a).aemeasurable
    _ = ∑' i, κ a (f i) := by simp_rw [hf_eq]
    _ = κ a (iUnion f) := (measure_iUnion hf_disj hf_meas).symm

lemma kernel.eq_compProd_condexpReal (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] :
    κ = kernel.fst κ ⊗ₖ kernel.condexpReal κ := by
  ext a s hs
  rw [kernel.compProd_apply _ _ _ hs, lintegral_condexpReal_mem κ a hs]

end Real

variable {Ω' : Type*} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']

def kernel.condexp (κ : kernel α (Ω × Ω')) [IsMarkovKernel (kernel.fst κ)] :
    kernel (α × Ω) Ω' :=
  sorry

theorem kernel.eq_compProd (κ : kernel α (Ω × Ω')) [IsMarkovKernel κ] :
    κ = kernel.fst κ ⊗ₖ kernel.condexp κ := by
  sorry

end ProbabilityTheory
