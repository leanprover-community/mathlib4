/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis, Oliver Butterley
-/
import Mathlib.Algebra.Order.AddGroup.PartialSups
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.SuccOrder.PartialSups
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.Real.StarOrdered
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.MeasurePreserving.Lemmas
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Pointwise Ergodic Theorem

The Pointwise Ergodic Theorem, also known as Birkhoff's Ergodic Theorem, establishes the convergence
of time averages for dynamical systems.

Let `(α, μ)` be a probability space and `f: α → α` be a measure-preserving transformation. The
result states that, for any integrable function `φ  ∈ L¹(μ)`, the time averages
`(1/n)∑_{k=0}^{n-1} φ(f^k x)` converge almost everywhere as `n → ∞` to a limit function `φ*`.
Moreover the limit function `φ*` is essentially `f`-invariant and integrable with `∫φ* dμ = ∫φ dμ`.
If the system is ergodic, then `φ*` equals the constant `∫f dμ` almost everywhere.

The limit function `φ*` is equal to the conditional expectation of `φ` with respect to the σ-algebra
of `f`-invariant sets. This is used explicitly during this proof and also in the main statement.

## Main statements

* `ae_tendsTo_birkhoffAverage_condExp`: time average coincides with conditional expectation

-/

section BirkhoffMax

variable {α : Type*}

/-- The maximum of `birkhoffSum f φ i` for `i` ranging from `1` to `n + 1`. -/
def birkhoffMax (f : α → α) (φ : α → ℝ) : ℕ →o (α → ℝ) :=
  partialSups (birkhoffSum f φ ∘ .succ)

lemma birkhoffMax_succ {f : α → α} {φ n x} :
    birkhoffMax f φ n.succ x = φ x + 0 ⊔ birkhoffMax f φ n (f x) := by
  change
    (partialSups (birkhoffSum f φ ∘ Nat.succ)) n.succ x = φ x + max 0 ((birkhoffMax f φ) n (f x))
  have h : birkhoffSum f φ ∘ Nat.succ = fun k ↦ φ + birkhoffSum f φ k ∘ f := by
    funext k _
    simp [add_comm k 1, birkhoffSum_add f φ 1, birkhoffSum_one]
  rw [h, partialSups_const_add, Pi.add_apply, add_right_inj, show n.succ = Order.succ n by rfl,
    partialSups_succ', Pi.sup_apply, Pi.partialSups_apply]
  simp [Function.comp_apply, ← Pi.partialSups_apply]
  rfl

/-- The difference between the maximum of `birkhoffSum f φ i` for `i` ranging from `1` to `n + 1`
and the maximum of the same quantity for `i` ranging from `2` to `n + 2`. -/
abbrev birkhoffMaxDiff (f : α → α) (φ : α → ℝ) (n : ℕ) (x : α) :=
  birkhoffMax f φ (n + 1) x - birkhoffMax f φ n (f x)

theorem birkhoffMaxDiff_aux {f : α → α} {φ n x} :
    birkhoffMaxDiff f φ n x = φ x - (0 ⊓ birkhoffMax f φ n (f x)) := by
  rw [sub_eq_sub_iff_add_eq_add, birkhoffMax_succ, add_assoc, add_right_inj, max_add_min, zero_add]

lemma birkhoffMaxDiff_antitone {f : α → α} {φ} : Antitone (birkhoffMaxDiff f φ) := by
  intro m n h x
  rw [birkhoffMaxDiff_aux, birkhoffMaxDiff_aux]
  apply add_le_add_left
  simp only [neg_le_neg_iff, le_inf_iff, inf_le_left, inf_le_iff, true_and]
  right
  exact (birkhoffMax f φ).monotone' h _

@[measurability]
lemma birkhoffSum_measurable [MeasurableSpace α] {f : α → α} (hf : Measurable f) {φ : α → ℝ}
    (hφ : Measurable φ) {n} : Measurable (birkhoffSum f φ n) := by
  apply Finset.measurable_sum
  measurability

@[measurability]
lemma birkhoffMax_measurable [MeasurableSpace α] {f : α → α} (hf : Measurable f) {φ : α → ℝ}
    (hφ : Measurable φ) {n} : Measurable (birkhoffMax f φ n) := by
  induction n <;> unfold birkhoffMax <;> measurability

end BirkhoffMax

section DivergentSet

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α : Type*}

/-- The supremum of `birkhoffSum f φ (n + 1) x` over `n : ℕ`. -/
noncomputable def birkhoffSup (f : α → α) (φ : α → ℝ) (x : α) : EReal :=
  iSup fun n ↦ ↑(birkhoffSum f φ (n + 1) x)

lemma birkhoffSup_measurable [MeasurableSpace α] {f : α → α} (hf : Measurable f) {φ : α → ℝ}
    (hφ : Measurable φ) : Measurable (birkhoffSup f φ) :=
  Measurable.iSup (fun _ ↦ Measurable.coe_real_ereal (birkhoffSum_measurable hf hφ))

/-- The set of points `x` for which `birkhoffSup f φ x = ⊤`. -/
def divergentSet (f : α → α) (φ : α → ℝ) : Set α := (birkhoffSup f φ)⁻¹' {⊤}

lemma divergentSet_invariant {f : α → α} {x φ} : f x ∈ divergentSet f φ ↔ x ∈ divergentSet f φ := by
  constructor
  all_goals
    intro hx
    simp only [divergentSet, Set.mem_preimage, birkhoffSup, Set.mem_singleton_iff, iSup_eq_top] at *
    intro M hM
    induction M using EReal.rec with
    | bot => exact ⟨0, EReal.bot_lt_coe _⟩
    | top => contradiction
    | coe a => ?_
  case mp =>
    obtain ⟨N, hN⟩ := hx (- φ x + a) (EReal.coe_lt_top _)
    use N + 1
    norm_cast at *
    rwa [neg_add_lt_iff_lt_add, ← birkhoffSum_succ'] at hN
  case mpr =>
    suffices ∃ i, φ x + a < birkhoffSum f φ (i + 1 + 1) x by
      norm_cast at *
      obtain ⟨i, hi⟩ := this
      exact ⟨i, by rwa [← add_lt_add_iff_left (φ x), ← birkhoffSum_succ']⟩
    obtain ⟨N, hN⟩ := hx (φ x + a) (EReal.coe_lt_top _)
    match N with
    | 0 =>
      obtain ⟨M, hM⟩ := hx ↑(birkhoffSum f φ 1 x) (EReal.coe_lt_top _)
      match M with
      | 0 => simp_all
      | N + 1 => exact ⟨N, lt_trans (EReal.coe_lt_coe_iff.mp hN) <| EReal.coe_lt_coe_iff.mp hM⟩
    | N + 1 => exact ⟨N, EReal.coe_lt_coe_iff.mp hN⟩

lemma divergentSet_measurable {f : α → α} [MeasurableSpace α] (hf : Measurable f) {φ : α → ℝ}
    (hφ : Measurable φ) : MeasurableSet (divergentSet f φ) :=
  measurableSet_preimage (birkhoffSup_measurable hf hφ) (measurableSet_singleton _)

lemma divergentSet_mem_invalg [MeasurableSpace α] {f : α → α} (hf : Measurable f) {φ : α → ℝ}
    (hφ : Measurable φ) : MeasurableSet[invariants f] (divergentSet f φ) :=
  ⟨divergentSet_measurable hf hφ, funext (fun _ ↦ propext divergentSet_invariant)⟩

lemma birkhoffMax_tendsto_top_mem_divergentSet {f : α → α} {x φ} (hx : x ∈ divergentSet f φ) :
    Tendsto (birkhoffMax f φ · x) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  simp only [divergentSet, Set.mem_preimage, birkhoffSup, Set.mem_singleton_iff, iSup_eq_top] at hx
  obtain ⟨N, hN⟩ := hx b (EReal.coe_lt_top _)
  norm_cast at hN
  use N
  exact fun n hn ↦ le_trans (le_of_lt hN) (le_partialSups_of_le (birkhoffSum f φ ∘ .succ) hn x )

lemma birkhoffMaxDiff_tendsto_of_mem_divergentSet {f : α → α} {x φ} (hx : x ∈ divergentSet f φ) :
    Tendsto (birkhoffMaxDiff f φ · x) atTop (𝓝 (φ x)) := by
  have hx' : f x ∈ divergentSet f φ := divergentSet_invariant.mpr hx
  simp_rw [birkhoffMaxDiff_aux]
  nth_rw 2 [← sub_zero (φ x)]
  apply Tendsto.sub tendsto_const_nhds
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp (birkhoffMax_tendsto_top_mem_divergentSet hx') 0
  exact tendsto_atTop_of_eventually_const (i₀ := N) fun i hi ↦ inf_of_le_left (hN i hi)

/-- The filter of non-negative real numbers. -/
abbrev nonneg : Filter ℝ := ⨅ ε > 0, 𝓟 (Set.Iio ε)

lemma birkhoffAverage_tendsto_nonpos_of_not_mem_divergentSet {f : α → α} {x φ}
    (hx : x ∉ divergentSet f φ) : Tendsto (birkhoffAverage ℝ f φ · x) atTop nonneg := by
  /- it suffices to show there are upper bounds ≤ ε for all ε > 0 -/
  simp only [tendsto_iInf, gt_iff_lt, tendsto_principal, Set.mem_Iio, eventually_atTop, ge_iff_le]
  intro ε hε
  /- from `hx` hypothesis, the birkhoff sums are bounded above -/
  simp only [divergentSet, Set.mem_preimage, birkhoffSup, Set.mem_singleton_iff, iSup_eq_top,
    not_forall, not_exists, not_lt, exists_prop] at hx
  rcases hx with ⟨M', M_lt_top, M_is_bound⟩
  /- the upper bound is, in fact, a real number -/
  obtain ⟨M, hM⟩ : ∃ (M : ℝ), ∀ (n : ℕ), birkhoffSum f φ (n + 1) x ≤ M := by
    induction M' using EReal.rec with
    | bot => exfalso; exact (EReal.bot_lt_coe _).not_ge (M_is_bound 0)
    | top => contradiction
    | coe M => exact ⟨M, by norm_cast at M_is_bound⟩
  /- use archimedian property of reals -/
  obtain ⟨N, hN⟩ := Archimedean.arch M hε
  have upperBound (n : ℕ) (hn : N ≤ n) : birkhoffAverage ℝ f φ (n + 1) x < ε := by
    have : M < (n + 1) • ε := by
      exact hN.trans_lt <| smul_lt_smul_of_pos_right (Nat.lt_succ_of_le hn) hε
    rw [nsmul_eq_mul] at this
    exact (inv_smul_lt_iff_of_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ n))).mpr
        ((hM n).trans_lt this)
  /- conclusion -/
  use N + 1
  intro n hn
  specialize upperBound n.pred (Nat.le_pred_of_lt hn)
  rwa [← Nat.succ_pred_eq_of_pos (Nat.zero_lt_of_lt hn)]

variable {f : α → α} [MeasurableSpace α] (μ : Measure α := by volume_tac) {φ : α → ℝ}

lemma birkhoffSum_integrable (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) {n} :
    Integrable (birkhoffSum f φ n) μ :=
  integrable_finset_sum _ fun _ _ ↦ MeasurePreserving.comp_iterate_integrable hf hφ

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
            (𝓝 <| ∫ x in divergentSet f φ, φ x ∂ μ) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (abs φ ⊔ abs (birkhoffMaxDiff f φ 0))
  · exact fun _ ↦ (birkhoffMaxDiff_integrable μ hf hφ).aestronglyMeasurable.restrict
  · apply Integrable.sup <;> apply Integrable.abs
    · exact hφ.restrict
    · exact (birkhoffMaxDiff_integrable μ hf hφ).restrict
  · intro n
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs (by simp [birkhoffMaxDiff_aux])
      (birkhoffMaxDiff_antitone (zero_le n) _)
  · exact (ae_restrict_iff' (divergentSet_measurable hf.measurable hφ')).mpr
      (ae_of_all _ fun _ hx ↦ birkhoffMaxDiff_tendsto_of_mem_divergentSet hx)

lemma int_birkhoffMaxDiff_in_divergentSet_nonneg (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hφ' : Measurable φ) {n} :
    0 ≤ ∫ x in divergentSet f φ, birkhoffMaxDiff f φ n x ∂μ := by
  unfold birkhoffMaxDiff
  have : (μ.restrict (divergentSet f φ)).map f = μ.restrict (divergentSet f φ) := by
    nth_rw 1 [← (divergentSet_mem_invalg hf.measurable hφ').2,
      ← μ.restrict_map hf.measurable (divergentSet_measurable hf.measurable hφ'),
      hf.map_eq]
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

omit [MeasurableSpace α] in
lemma nullMeasurableSpace_le [msα : MeasurableSpace α] {μ : Measure α} :
    msα ≤ NullMeasurableSpace.instMeasurableSpace (α := α) (μ := μ) :=
  fun s hs ↦ ⟨s, hs, ae_eq_refl s⟩

lemma divergentSet_zero_meas_of_condexp_neg [hμ : IsProbabilityMeasure μ]
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
        refine (le_trans (invariants_le f) nullMeasurableSpace_le)
    · exact ae_le_of_ae_lt pos
    · exact integrable_condExp.restrict.neg
  exact this.not_ge (int_in_divergentSet_nonneg μ hf hφ hφ')

lemma ae_tendsTo_birkhoffAverage_of_condExp_neg [hμ : IsProbabilityMeasure μ]
    (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) (hφ' : Measurable φ)
    (h : ∀ᵐ x ∂μ, (μ[φ|invariants f]) x < 0) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f φ · x) atTop nonneg := by
  apply Eventually.mono _ fun _ ↦ birkhoffAverage_tendsto_nonpos_of_not_mem_divergentSet
  apply ae_iff.mpr
  simp only [not_not, Set.setOf_mem_eq]
  exact divergentSet_zero_meas_of_condexp_neg μ h hf hφ hφ'

end DivergentSet

section PointwiseErgodicTheorem

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α : Type*} {f : α → α} [MeasurableSpace α] (μ : Measure α := by volume_tac)
    {φ : α → ℝ} [hμ : IsProbabilityMeasure μ]

/-- The time average is a.e., eventually not much less than the conditional expectation. -/
lemma ae_tendsTo_birkhoffAverage_sub_condExp_nonneg {ε : ℝ} (hε : 0 < ε)
    (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) (hφ' : Measurable φ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f φ · x - (μ[φ|invariants f] x + ε)) atTop nonneg := by
  -- Let `ψ` denote the difference between `φ` and the conditional expectation of `φ` plus `ε`.
  let ψ := φ - (μ[φ|invariants f] + fun _ ↦ ε)
  have ψ_integrable : Integrable ψ μ := hφ.sub (integrable_condExp.add (integrable_const _))
  have ψ_measurable : Measurable ψ := by
    suffices Measurable (μ[φ|invariants f]) by measurability
    exact stronglyMeasurable_condExp.measurable.le (invariants_le f)
  -- It follows from the definition of `ψ` that it is a.e. equal to `-ε`.
  have condexpψ_const : μ[ψ|invariants f] =ᵐ[μ] - fun _ ↦ ε := calc
    _ =ᵐ[μ] μ[φ|invariants f] - μ[μ[φ|invariants f] + fun _ ↦ ε|invariants f] :=
      condExp_sub hφ (integrable_condExp.add (integrable_const _)) _
    _ =ᵐ[μ] μ[φ|invariants f] - (μ[μ[φ|invariants f]|invariants f] + μ[fun _ ↦ ε|invariants f]) :=
      (condExp_add integrable_condExp (integrable_const _) _).neg.add_left
    _ =ᵐ[μ] μ[φ|invariants f] - (μ[φ|invariants f] + μ[fun _ ↦ ε|invariants f]) :=
      (condExp_condExp_of_le (le_of_eq rfl) (invariants_le f)).add_right.neg.add_left
    _ = - μ[fun _ ↦ ε|invariants f] := by simp
    _ = - fun _ ↦ ε := by rw [condExp_const <| invariants_le f]
  -- For typical points the time average of `ψ` is eventually non-negative.
  have limsup_nonpos : ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f ψ · x) atTop nonneg := by
    suffices ∀ᵐ x ∂μ, μ[ψ|invariants f] x < 0 from
      ae_tendsTo_birkhoffAverage_of_condExp_neg μ hf ψ_integrable ψ_measurable this
    exact condexpψ_const.mono fun x hx ↦ by simp [hx, hε]
  -- Transfer the result on `ψ` to the required result on `φ`.
  refine limsup_nonpos.mono fun x hx => ?_
  suffices ∀ (n : ℕ), 0 < n →
      birkhoffAverage ℝ f ψ n x = birkhoffAverage ℝ f φ n x - (μ[φ|invariants f] x + ε) by
    simp only [tendsto_iInf, gt_iff_lt, tendsto_principal, Set.mem_Iio, eventually_atTop,
      ge_iff_le] at hx ⊢
    intro r hr
    obtain ⟨n, hn⟩ := hx r hr
    refine ⟨n + 1, fun k hk ↦ ?_⟩
    rw [← this k (Nat.zero_lt_of_lt hk)]
    exact hn k (Nat.le_of_succ_le hk)
  intro n hn
  have : μ[φ|invariants f] ∘ f = μ[φ|invariants f] :=
    comp_eq_of_measurable_invariants stronglyMeasurable_condExp.measurable
  simp [ψ, birkhoffAverage_sub, birkhoffAverage_add, birkhoffAverage_of_invariant ℝ
    (show _ = fun _ ↦ ε from rfl) hn, birkhoffAverage_of_invariant ℝ this hn]

/-- Same as the main result `ae_tendsTo_birkhoffAverage_condExp` but assuming `Measurable φ`. -/
private lemma ae_tendsTo_birkhoffAverage_condExp_aux
    (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) (hφ' : Measurable φ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f φ · x) atTop (𝓝 (μ[φ|invariants f] x)) := by
  have : ∀ᵐ x ∂μ, ∀ (k : {k : ℕ // k > 0}),
      ∀ᶠ n in atTop, |birkhoffAverage ℝ f φ n x - (μ[φ|invariants f] x)| < (k : ℝ)⁻¹ := by
    apply ae_all_iff.mpr
    rintro ⟨k, hk⟩
    let δ := (k : ℝ)⁻¹ / 2
    have hδ : δ > 0 := by simpa [δ]
    have p₁ := ae_tendsTo_birkhoffAverage_sub_condExp_nonneg μ hδ hf hφ hφ'
    have p₂ := ae_tendsTo_birkhoffAverage_sub_condExp_nonneg μ hδ hf hφ.neg hφ'.neg
    have : μ[-φ|invariants f] =ᵐ[μ] - μ[φ|invariants f] := condExp_neg _ _
    refine ((p₁.and p₂).and this).mono fun x ⟨⟨hx₁, hx₂⟩, hx₃⟩ => ?_
    simp only [tendsto_iInf, gt_iff_lt, tendsto_principal, Set.mem_Iio, eventually_atTop,
      ge_iff_le] at hx₁ hx₂ ⊢
    obtain ⟨n₁, hn₁⟩ := hx₁ δ hδ
    obtain ⟨n₂, hn₂⟩ := hx₂ δ hδ
    simp_rw [δ] at hn₁ hn₂ ⊢
    refine ⟨max n₁ n₂, fun m hm ↦ abs_lt.mpr ⟨?_, ?_⟩⟩
    · specialize hn₂ m (le_of_max_le_right hm)
      rw [hx₃, birkhoffAverage_neg] at hn₂
      norm_num at hn₂
      linarith
    · specialize hn₁ m (le_of_max_le_left hm)
      linarith
  refine this.mono fun x hx ↦ Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := Archimedean.arch 1 hε
  have hk' : 1 < (k + 1) • ε :=
    hk.trans_lt <| smul_lt_smul_of_pos_right (lt_add_one k) hε
  simp only [eventually_atTop, ge_iff_le, Subtype.forall, gt_iff_lt] at hx
  obtain ⟨N, hN⟩ := hx k.succ (Nat.zero_lt_succ k)
  refine ⟨N, fun n hn ↦ ?_⟩
  apply (hN n hn).trans
  rw [inv_lt_iff_one_lt_mul₀ (Nat.cast_pos.mpr k.succ_pos)]
  norm_num at hk' ⊢
  linarith

/-- **Pointwise Ergodic Theorem** a.k.a. **Birkhoff's Ergodic Theorem**

Time average coincides with conditional expectation for typical points. -/
theorem ae_tendsTo_birkhoffAverage_condExp {Φ : α → ℝ} (hf : MeasurePreserving f μ μ)
    (hΦ : Integrable Φ μ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f Φ · x) atTop (𝓝 (μ[Φ|invariants f] x)) := by
  let φ := hΦ.left.mk
  have hΦ' : Φ =ᵐ[μ] φ := hΦ.left.ae_eq_mk
  have hφ : Integrable φ μ := (integrable_congr hΦ.left.ae_eq_mk).mp hΦ
  have h1 := condExp_congr_ae (m := invariants f) hΦ'
  have h2 := ae_tendsTo_birkhoffAverage_condExp_aux μ hf hφ hΦ.left.measurable_mk
  have h3 := ae_all_iff.mpr <| birkhoffAverage_ae_eq_of_ae_eq ℝ hf.quasiMeasurePreserving hΦ'
  filter_upwards [h1, h2, h3] with _ h1' h2' h3'
  simp [h1', h2', h3']

end PointwiseErgodicTheorem
