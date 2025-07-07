import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.Real.StarOrdered
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

section BirkhoffMax

variable {α : Type*}

/-- The maximum of `birkhoffSum f φ i` for `i` ranging from `1` to `n + 1`. -/
def birkhoffMax (f : α → α) (φ : α → ℝ) : ℕ →o (α → ℝ) :=
  partialSups (birkhoffSum f φ ∘ .succ)

lemma birkhoffMax_succ {f : α → α} {φ n x} :
    birkhoffMax f φ n.succ x = φ x + 0 ⊔ birkhoffMax f φ n (f x) := by
  have : birkhoffSum f φ ∘ .succ = fun k ↦ φ + birkhoffSum f φ k ∘ f := by
    funext k x; dsimp
    rw [add_comm k 1, birkhoffSum_add f φ 1, birkhoffSum_one];
    rfl
  nth_rw 1 [birkhoffMax, this, partialSups_const_add]
  rw [Pi.add_apply, add_right_inj]
  rw [show n.succ = Order.succ n by rfl, partialSups_succ', Pi.sup_apply]
  simp_rw [Pi.partialSups_apply, Function.comp_apply, ← Pi.partialSups_apply]
  rfl

abbrev birkhoffMaxDiff (f : α → α) (φ : α → ℝ) (n : ℕ) (x : α) :=
  birkhoffMax f φ (n + 1) x - birkhoffMax f φ n (f x)

theorem birkhoffMaxDiff_aux {f : α → α} {φ n x} :
    birkhoffMaxDiff f φ n x = φ x - (0 ⊓ birkhoffMax f φ n (f x)) := by
  rw [sub_eq_sub_iff_add_eq_add, birkhoffMax_succ, add_assoc, add_right_inj, max_add_min, zero_add]

lemma birkhoffMaxDiff_antitone  {f : α → α} {φ} : Antitone (birkhoffMaxDiff f φ) := by
  intro m n h x
  rw [birkhoffMaxDiff_aux, birkhoffMaxDiff_aux]
  apply add_le_add_left
  simp only [neg_le_neg_iff, le_inf_iff, inf_le_left, inf_le_iff, true_and]
  right
  exact (birkhoffMax f φ).monotone' h _

@[measurability]
lemma birkhoffSum_measurable [MeasurableSpace α]
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) {n} :
    Measurable (birkhoffSum f φ n) := by
  apply Finset.measurable_sum
  measurability

@[measurability]
lemma birkhoffMax_measurable [MeasurableSpace α]
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) {n} :
    Measurable (birkhoffMax f φ n) := by
  induction n <;> unfold birkhoffMax <;> measurability

end BirkhoffMax

noncomputable section BirkhoffThm

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α : Type*} [msα : MeasurableSpace α] (μ : Measure α := by volume_tac)

/-- The supremum of `birkhoffSum f φ (n + 1) x` over `n : ℕ`. -/
def birkhoffSup (f : α → α) (φ : α → ℝ) (x : α) : EReal := iSup fun n ↦ ↑(birkhoffSum f φ (n + 1) x)

lemma birkhoffSup_measurable
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    Measurable (birkhoffSup f φ) := Measurable.iSup
  (fun _ ↦ Measurable.coe_real_ereal (birkhoffSum_measurable hf hφ))

/-- The set of points `x` for which `birkhoffSup f φ x = ⊤`. -/
def divergentSet (f : α → α) (φ : α → ℝ) : Set α := (birkhoffSup f φ)⁻¹' {⊤}

lemma divergentSet_invariant  {f : α → α} {x φ}:
    f x ∈ divergentSet f φ ↔ x ∈ divergentSet f φ := by
  constructor
  all_goals
    intro hx
    simp only [divergentSet, Set.mem_preimage, birkhoffSup, Set.mem_singleton_iff, iSup_eq_top] at *
    intro M hM
    cases' M using EReal.rec with a
    · use 0; apply EReal.bot_lt_coe
    case top => contradiction
  case mp =>
    cases' hx ↑(- φ x + a) (EReal.coe_lt_top _) with N hN
    norm_cast at *
    rw [neg_add_lt_iff_lt_add, ← birkhoffSum_succ'] at hN
    use N + 1
  case mpr =>
    cases' hx ↑(φ x + a) (EReal.coe_lt_top _) with N hN
    norm_cast at *
    conv =>
      congr
      intro i
      rw [← add_lt_add_iff_left (φ x), ← birkhoffSum_succ']
    cases' N with N
    · /- ugly case! :( -/
      cases' hx ↑(birkhoffSum f φ 1 x) (EReal.coe_lt_top _) with N hNN
      cases' N with N
      · exfalso; exact (lt_self_iff_false _).mp hNN
      · use N
        norm_cast at hNN
        exact lt_trans hN hNN
    · use N

lemma divergentSet_measurable
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    MeasurableSet (divergentSet f φ) :=
      measurableSet_preimage (birkhoffSup_measurable hf hφ) (measurableSet_singleton _)

lemma divergentSet_mem_invalg
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    MeasurableSet[invariants f] (divergentSet f φ) :=
  /- should be `Set.ext divergentSet_invariant` but it is VERY slow -/
  ⟨divergentSet_measurable hf hφ, funext (fun _ ↦ propext divergentSet_invariant)⟩

lemma birkhoffMax_tendsto_top_mem_divergentSet {f : α → α} {x φ} (hx : x ∈ divergentSet f φ) :
    Tendsto (birkhoffMax f φ · x) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  simp only [divergentSet, Set.mem_preimage, birkhoffSup, Set.mem_singleton_iff, iSup_eq_top] at hx
  cases' hx b (EReal.coe_lt_top _) with N hN
  norm_cast at hN
  use N
  exact fun n hn ↦ le_trans (le_of_lt hN) (le_partialSups_of_le (birkhoffSum f φ ∘ .succ) hn x )

lemma birkhoffMaxDiff_tendsto_of_mem_divergentSet {f : α → α} {x φ} (hx : x ∈ divergentSet f φ) :
    Tendsto (birkhoffMaxDiff f φ · x) atTop (𝓝 (φ x)) := by
  have hx' : f x ∈ divergentSet f φ := divergentSet_invariant.mpr hx
  simp_rw [birkhoffMaxDiff_aux]
  nth_rw 2 [← sub_zero (φ x)]
  apply Tendsto.sub tendsto_const_nhds
  cases' tendsto_atTop_atTop.mp (birkhoffMax_tendsto_top_mem_divergentSet hx') 0 with N hN
  exact tendsto_atTop_of_eventually_const (i₀ := N) fun i hi ↦ inf_of_le_left (hN i hi)

abbrev nonneg : Filter ℝ := ⨅ ε > 0, 𝓟 (Set.Iio ε)

lemma birkhoffAverage_tendsto_nonpos_of_not_mem_divergentSet {f : α → α} {x φ}
    (hx : x ∉ divergentSet f φ) :
    Tendsto (birkhoffAverage ℝ f φ · x) atTop nonneg := by
  /- it suffices to show there are upper bounds ≤ ε for all ε > 0 -/
  simp only [tendsto_iInf, gt_iff_lt, tendsto_principal, Set.mem_Iio, eventually_atTop, ge_iff_le]
  intro ε hε

  /- from `hx` hypothesis, the birkhoff sums are bounded above -/
  simp only [divergentSet, Set.mem_preimage, birkhoffSup, Set.mem_singleton_iff, iSup_eq_top,
    not_forall, not_exists, not_lt, exists_prop] at hx
  rcases hx with ⟨M', M_lt_top, M_is_bound⟩

  /- the upper bound is, in fact, a real number -/
  cases' M' using EReal.rec with M
  case bot => exfalso; exact (EReal.bot_lt_coe _).not_ge (M_is_bound 0)
  case top => contradiction
  norm_cast at M_is_bound

  /- use archimedian property of reals -/
  obtain ⟨N, hN⟩ := Archimedean.arch M hε
  have upperBound (n : ℕ) (hn : N ≤ n) : birkhoffAverage ℝ f φ (n + 1) x < ε := by
    have : M < (n + 1) • ε := by
      exact hN.trans_lt $ smul_lt_smul_of_pos_right (Nat.lt_succ_of_le hn) hε
    rw [nsmul_eq_mul] at this
    exact (inv_smul_lt_iff_of_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ n))).mpr
        ((M_is_bound n).trans_lt this)

  /- conclusion -/
  use N + 1
  intro n hn
  specialize upperBound n.pred (Nat.le_pred_of_lt hn)
  rwa [← Nat.succ_pred_eq_of_pos (Nat.zero_lt_of_lt hn)]

/- From now on, assume f is measure-preserving and φ is integrable. -/
variable {f : α → α} (hf : MeasurePreserving f μ μ)
         {φ : α → ℝ} (hφ : Integrable φ μ) (hφ' : Measurable φ) /- seems necessary? -/

lemma iterates_integrable {i : ℕ} (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) :
    Integrable (φ ∘ f^[i]) μ := by
  apply (integrable_map_measure _ _).mp
  · rwa [(hf.iterate i).map_eq]
  · rw [(hf.iterate i).map_eq]
    exact hφ.aestronglyMeasurable
  exact (hf.iterate i).measurable.aemeasurable

lemma birkhoffSum_integrable (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) {n} :
    Integrable (birkhoffSum f φ n) μ :=
  integrable_finset_sum _ fun _ _ ↦ iterates_integrable μ hf hφ

lemma birkhoffMax_integrable (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) {n} :
    Integrable (birkhoffMax f φ n) μ := by
  unfold birkhoffMax
  induction' n with n hn
  · simpa
  · simpa using Integrable.sup hn (birkhoffSum_integrable μ hf hφ)

lemma birkhoffMaxDiff_integrable (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) {n} :
    Integrable (birkhoffMaxDiff f φ n) μ := by
  apply Integrable.sub (birkhoffMax_integrable μ hf hφ)
  apply (integrable_map_measure _ hf.measurable.aemeasurable).mp <;> rw [hf.map_eq]
  · exact birkhoffMax_integrable μ hf hφ
  · exact (birkhoffMax_integrable μ hf hφ).aestronglyMeasurable

lemma int_birkhoffMaxDiff_in_divergentSet_tendsto (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hφ' : Measurable φ) :
    Tendsto (fun n ↦ ∫ x in divergentSet f φ, birkhoffMaxDiff f φ n x ∂μ) atTop
            (𝓝 $ ∫ x in divergentSet f φ, φ x ∂ μ) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence (abs φ ⊔ abs (birkhoffMaxDiff f φ 0))
  · exact fun _ ↦ (birkhoffMaxDiff_integrable μ hf hφ).aestronglyMeasurable.restrict
  · apply Integrable.sup <;> apply Integrable.abs
    · exact hφ.restrict
    · exact (birkhoffMaxDiff_integrable μ hf hφ).restrict
  · intro n
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs (by simp [birkhoffMaxDiff_aux]) (birkhoffMaxDiff_antitone (zero_le n) _)
  · exact (ae_restrict_iff' (divergentSet_measurable hf.measurable hφ')).mpr
      (ae_of_all _ fun _ hx ↦ birkhoffMaxDiff_tendsto_of_mem_divergentSet hx)

lemma int_birkhoffMaxDiff_in_divergentSet_nonneg (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hφ' : Measurable φ) {n} :
    0 ≤ ∫ x in divergentSet f φ, birkhoffMaxDiff f φ n x ∂μ := by
  unfold birkhoffMaxDiff
  have : (μ.restrict (divergentSet f φ)).map f = μ.restrict (divergentSet f φ) := by
    nth_rw 1 [
      ← (divergentSet_mem_invalg hf.measurable hφ').2,
      ← μ.restrict_map hf.measurable (divergentSet_measurable hf.measurable hφ'),
      hf.map_eq
    ]
  have mi {n : ℕ} := birkhoffMax_integrable μ hf hφ (n := n)
  have mm {n : ℕ} := birkhoffMax_measurable hf.measurable hφ' (n := n)
  rw [integral_sub, sub_nonneg]
  · rw [← integral_map (hf.aemeasurable.restrict) mm.aestronglyMeasurable, this]
    exact integral_mono mi.restrict mi.restrict ((birkhoffMax f φ).monotone (Nat.le_succ _))
  · exact mi.restrict
  · apply (integrable_map_measure mm.aestronglyMeasurable hf.aemeasurable.restrict).mp
    rw [this]
    exact mi.restrict

lemma int_in_divergentSet_nonneg (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hφ' : Measurable φ) : 0 ≤ ∫ x in divergentSet f φ, φ x ∂μ :=
  le_of_tendsto_of_tendsto' tendsto_const_nhds
    (int_birkhoffMaxDiff_in_divergentSet_tendsto μ hf hφ hφ')
    (fun _ ↦ int_birkhoffMaxDiff_in_divergentSet_nonneg μ hf hφ hφ')

/- these seem to be missing? -/
lemma nullMeasurableSpace_le {μ : Measure α} :
    msα ≤ NullMeasurableSpace.instMeasurableSpace (α := α) (μ := μ) :=
  fun s hs ↦ ⟨s, hs, ae_eq_refl s⟩

variable [hμ : IsProbabilityMeasure μ]

lemma divergentSet_zero_meas_of_condexp_neg
    (h : ∀ᵐ x ∂μ, (μ[φ|invariants f]) x < 0) (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hφ' : Measurable φ) :
    μ (divergentSet f φ) = 0 := by
  have pos : ∀ᵐ x ∂μ.restrict (divergentSet f φ), 0 < -(μ[φ|invariants f]) x := by
    exact ae_restrict_of_ae (h.mono fun _ hx ↦ neg_pos.mpr hx)
  have ds_meas := divergentSet_mem_invalg hf.measurable hφ'
  by_contra hm; simp_rw [← pos_iff_ne_zero] at hm
  have : ∫ x in divergentSet f φ, φ x ∂μ < 0 := by
    rw [← setIntegral_condExp (invariants_le f) hφ ds_meas,
      ← Left.neg_pos_iff, ← integral_neg, integral_pos_iff_support_of_nonneg_ae]
    · unfold Function.support
      rw [(ae_iff_measure_eq _).mp]
      · rwa [Measure.restrict_apply_univ _]
      · conv in _ ≠ _ => rw [ne_comm]
        exact Eventually.ne_of_lt pos
      · apply measurableSet_support _
        apply (stronglyMeasurable_condExp).measurable.neg.le _
        exact (le_trans (invariants_le f) nullMeasurableSpace_le)
    · exact ae_le_of_ae_lt pos
    · exact integrable_condExp.restrict.neg
  exact this.not_ge (int_in_divergentSet_nonneg μ hf hφ hφ')

lemma limsup_birkhoffAverage_nonpos_of_condexp_neg (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hφ' : Measurable φ) (h : ∀ᵐ x ∂μ, (μ[φ|invariants f]) x < 0) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f φ · x) atTop nonneg := by
  apply Eventually.mono _ fun _ ↦ birkhoffAverage_tendsto_nonpos_of_not_mem_divergentSet
  apply ae_iff.mpr
  simp only [not_not, Set.setOf_mem_eq]
  exact divergentSet_zero_meas_of_condexp_neg μ h hf hφ hφ'

def invCondexp (μ : Measure α := by volume_tac) [IsProbabilityMeasure μ]
    (f : α → α) (φ : α → ℝ) : α → ℝ := μ[φ|invariants f]

theorem birkhoffErgodicTheorem_aux {ε : ℝ} (hε : 0 < ε) (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hφ' : Measurable φ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f φ · x - (invCondexp μ f φ x + ε)) atTop nonneg := by
  let ψ := φ - (invCondexp μ f φ + fun _ ↦ ε)
  have ψ_integrable : Integrable ψ μ := hφ.sub (integrable_condExp.add (integrable_const _))
  have ψ_measurable : Measurable ψ := by
    suffices Measurable (invCondexp μ f φ) by measurability
    exact stronglyMeasurable_condExp.measurable.le (invariants_le f)

  have condexpψ_const : invCondexp μ f ψ =ᵐ[μ] - fun _ ↦ ε := calc
    μ[ψ|invariants f]
    _ =ᵐ[μ] _ - _ := condExp_sub hφ (integrable_condExp.add (integrable_const _)) _
    _ =ᵐ[μ] _ - (_ + _) := (condExp_add integrable_condExp (integrable_const _) _).neg.add_left
    _ =ᵐ[μ] _ - (_ + _) := (condExp_condExp_of_le (le_of_eq rfl)
                            (invariants_le f)).add_right.neg.add_left
    _ = - μ[fun _ ↦ ε|invariants f] := by simp
    _ = - fun _ ↦ ε := by rw [condExp_const (invariants_le f)]

  have limsup_nonpos : ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f ψ · x) atTop nonneg := by
    suffices ∀ᵐ x ∂μ, invCondexp μ f ψ x < 0 from
      limsup_birkhoffAverage_nonpos_of_condexp_neg μ hf ψ_integrable ψ_measurable this
    exact condexpψ_const.mono fun x hx ↦ by simp [hx, hε]

  refine limsup_nonpos.mono fun x hx => ?_

  suffices ∀ (n : ℕ), 0 < n → birkhoffAverage ℝ f ψ n x = birkhoffAverage ℝ f φ n x - (invCondexp μ f φ x + ε) by
    simp only [tendsto_iInf, gt_iff_lt, tendsto_principal, Set.mem_Iio, eventually_atTop,
      ge_iff_le] at hx ⊢
    intro r hr
    cases' hx r hr with n hn
    use n + 1
    intro k hk
    rw [← this k (Nat.zero_lt_of_lt hk)]
    exact hn k (Nat.le_of_succ_le hk)

  have condexpφ_invariant : invCondexp μ f φ ∘ f = invCondexp μ f φ :=
    invariant_of_measurable_invariants stronglyMeasurable_condExp.measurable

  intro n hn
  simp [ψ, birkhoffAverage_sub, birkhoffAverage_add, birkhoffAverage_of_invariant ℝ
    (show _ = fun _ ↦ ε from rfl) hn, birkhoffAverage_of_invariant ℝ condexpφ_invariant hn]

/-- This is the main result but assuming `Measurable φ`. -/
theorem birkhoffErgodicTheorem (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) (hφ' : Measurable φ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f φ · x) atTop (𝓝 (invCondexp μ f φ x)) := by
  have : ∀ᵐ x ∂μ, ∀ (k : {k : ℕ // k > 0}),
      ∀ᶠ n in atTop, |birkhoffAverage ℝ f φ n x - (invCondexp μ f φ x)| < (k : ℝ)⁻¹ := by
    apply ae_all_iff.mpr
    rintro ⟨k, hk⟩
    let δ := (k : ℝ)⁻¹/2
    have hδ : δ > 0 := by simpa [δ]
    have p₁ := birkhoffErgodicTheorem_aux μ hδ hf hφ hφ'
    have p₂ := birkhoffErgodicTheorem_aux μ hδ hf hφ.neg hφ'.neg
    have : invCondexp μ f (-φ) =ᵐ[μ] -invCondexp μ f φ := condExp_neg _ _
    refine ((p₁.and p₂).and this).mono fun x ⟨⟨hx₁, hx₂⟩, hx₃⟩ => ?_
    simp only [tendsto_iInf, gt_iff_lt, tendsto_principal, Set.mem_Iio, eventually_atTop,
      ge_iff_le] at hx₁ hx₂ ⊢
    cases' hx₁ δ hδ with n₁ hn₁
    cases' hx₂ δ hδ with n₂ hn₂
    simp_rw [δ] at hn₁ hn₂ ⊢
    use (max n₁ n₂)
    intro m hm
    apply abs_lt.mpr
    constructor
    · specialize hn₂ m (le_of_max_le_right hm)
      rw [hx₃, birkhoffAverage_neg] at hn₂
      norm_num at hn₂
      linarith
    · specialize hn₁ m (le_of_max_le_left hm)
      linarith

  refine this.mono fun x hx => Metric.tendsto_atTop.mpr fun ε hε => ?_
  cases' Archimedean.arch 1 hε with k hk
  have hk' : 1 < (k + 1) • ε :=
    hk.trans_lt $ smul_lt_smul_of_pos_right (lt_add_one k) hε
  simp only [eventually_atTop, ge_iff_le, Subtype.forall, gt_iff_lt] at hx
  cases' hx k.succ (Nat.zero_lt_succ k) with N hN
  use N
  intro n hn
  apply (hN n hn).trans
  rw [inv_lt_iff_one_lt_mul₀ (Nat.cast_pos.mpr k.succ_pos)]
  norm_num at hk' ⊢
  linarith

/-- Here we drop the assumption that the observable is `Measurable`. -/
theorem birkhoffErgodicTheorem' {Φ : α → ℝ} (hf : MeasurePreserving f μ μ) (hΦ : Integrable Φ μ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f Φ · x) atTop (𝓝 (invCondexp μ f Φ x)) := by
  -- Take `φ` as the measurable approximation to the ae measurable `Φ`.
  let φ := hΦ.left.mk
  have hφ' : Measurable φ := hΦ.left.measurable_mk
  have hΦ' : Φ =ᵐ[μ] φ := hΦ.left.ae_eq_mk
  have hφ : Integrable φ μ := (integrable_congr hΦ.left.ae_eq_mk).mp hΦ
  -- Obtain a full measure set such that the three relevant results hold.
  obtain ⟨s, hs, hs'⟩ : ∃ s ∈ ae μ, Set.EqOn (invCondexp μ f Φ) (invCondexp μ f φ) s :=
    eventuallyEq_iff_exists_mem.mp <| condExp_congr_ae hΦ'
  obtain ⟨t, ht, ht'⟩ := eventually_iff_exists_mem.mp <| birkhoffErgodicTheorem μ hf hφ hφ'
  have := ae_all_iff.mpr <| birkhoffAverage_ae_eq_of_ae_eq ℝ hf.quasiMeasurePreserving hΦ'
  obtain ⟨u, hu, hu'⟩ := eventually_iff_exists_mem.mp this
  -- Apply the three results on the chosen set.
  refine eventually_iff_exists_mem.mpr ⟨s ∩ t ∩ u, inter_mem (inter_mem hs ht) hu, fun y hy ↦ ?_⟩
  simp [hs' hy.1.1, ht' y hy.1.2, hu' y hy.2]
