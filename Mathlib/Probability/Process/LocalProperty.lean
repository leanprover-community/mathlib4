/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.Data.Set.Dissipate

/-! # Local properties of processes

This file defines local and stable properties of stochastic processes with respect to a filtration.
This is notably useful in local martingales.

## Main definitions

* `ProbabilityTheory.IsPreLocalizingSequence`: A pre-localizing sequence is a sequence of stopping
  times which tends almost surely to infinity.
* `ProbabilityTheory.IsLocalizingSequence`: A localizing sequence is a pre-localizing sequence
  which is almost surely increasing.
* `ProbabilityTheory.Locally`: A stochastic process `X` is said to satisfy a property `p` locally
  with respect to a filtration `𝓕` if there exists a localizing sequence `(τ n)` such that for all
  `n`, the stopped process `X^{τ n} I_{τ n > ⊥}` satisfies `p`.
* `ProbabilityTheory.IsStable`: A property of stochastic processes is said to be stable if it is
  preserved under taking the stopped process `X^{τ} I_{τ > ⊥}` by a stopping time `τ`.

## Main results

* `ProbabilityTheory.IsStable.isStable_locally`: If a property `p` is stable, then the property
  "satisfies `p` locally" is also stable.
* `ProbabilityTheory.isLocalizingSequence_of_isPreLocalizingSequence`: Given a
  pre-localizing sequence `(τ n)`, the sequence `⊓ j ≥ n, τ j` is a localizing sequence.
* `ProbabilityTheory.locally_of_isPreLocalizingSequence`: If a property `p` is stable, then it is
  locally satisfied by `X` if the definition of local holds replacing localizing sequence by
  pre-localizing sequence.
* `ProbabilityTheory.locally_locally`: For stable properties, locally is idempotent.
* `ProbabilityTheory.locally_induction`: If `q` is a stable property, and `p` implies locally `q`,
  then locally `p` implies locally `q`.

### Tags

localizing sequence, local property, stable property
-/

@[expose] public section

open MeasureTheory Filter Filtration
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A pre-localizing sequence is a sequence of stopping times that tends almost surely to
infinity. -/
structure IsPreLocalizingSequence [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → WithTop ι) (P : Measure Ω := by volume_tac) :
    Prop where
  isStoppingTime : ∀ n, IsStoppingTime 𝓕 (τ n)
  tendsto_top : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤)

/-- A localizing sequence is a sequence of stopping times that is almost surely increasing and
tends almost surely to infinity. -/
structure IsLocalizingSequence [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → WithTop ι)
    (P : Measure Ω := by volume_tac) extends IsPreLocalizingSequence 𝓕 τ P where
  mono : ∀ᵐ ω ∂P, Monotone (τ · ω)

lemma isLocalizingSequence_const_top [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) : IsLocalizingSequence 𝓕 (fun _ _ ↦ ⊤) P where
  isStoppingTime n := by simp [IsStoppingTime]
  mono := ae_of_all _ fun _ _ _ _ ↦ by simp
  tendsto_top := by filter_upwards [] with ω using tendsto_const_nhds

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

lemma IsLocalizingSequence.min [TopologicalSpace ι] [OrderTopology ι] {τ σ : ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : IsLocalizingSequence 𝓕 σ P) :
    IsLocalizingSequence 𝓕 (min τ σ) P where
  isStoppingTime n := (hτ.isStoppingTime n).min (hσ.isStoppingTime n)
  mono := by filter_upwards [hτ.mono, hσ.mono] with ω hτω hσω; exact hτω.min hσω
  tendsto_top := by
    filter_upwards [hτ.tendsto_top, hσ.tendsto_top] with ω hτω hσω using hτω.min hσω

variable [OrderBot ι]

/-- A stochastic process `X` is said to satisfy a property `p` locally with respect to a
filtration `𝓕` if there exists a localizing sequence `(τ_n)` such that for all `n`, the stopped
process of `fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)` satisfies `p`. -/
def Locally [TopologicalSpace ι] [OrderTopology ι] [Zero E]
    (p : (ι → Ω → E) → Prop) (𝓕 : Filtration ι mΩ)
    (X : ι → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∃ τ : ℕ → Ω → WithTop ι, IsLocalizingSequence 𝓕 τ P ∧
    ∀ n, p (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))

namespace Locally

variable [TopologicalSpace ι] [OrderTopology ι]

/-- A localizing sequence, witness of the local property of the stochastic process. -/
noncomputable
def localSeq [Zero E] (hX : Locally p 𝓕 X P) :
    ℕ → Ω → WithTop ι :=
  hX.choose

lemma IsLocalizingSequence [Zero E] (hX : Locally p 𝓕 X P) :
    IsLocalizingSequence 𝓕 (hX.localSeq) P :=
  hX.choose_spec.1

lemma stoppedProcess [Zero E] (hX : Locally p 𝓕 X P) (n : ℕ) :
    p (stoppedProcess (fun i ↦ {ω | ⊥ < hX.localSeq n ω}.indicator (X i)) (hX.localSeq n)) :=
  hX.choose_spec.2 n

lemma of_prop [Zero E] (hp : p X) : Locally p 𝓕 X P :=
  ⟨fun n _ ↦ (⊤ : WithTop ι), isLocalizingSequence_const_top _ _, by simpa⟩

lemma mono [Zero E] (hpq : ∀ X, p X → q X) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  ⟨hpX.localSeq, hpX.IsLocalizingSequence, fun n ↦ hpq _ <| hpX.stoppedProcess n⟩

lemma of_and [Zero E] (hX : Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P) :
    Locally p 𝓕 X P ∧ Locally q 𝓕 X P :=
  ⟨hX.mono <| fun _ ↦ And.left, hX.mono <| fun _ ↦ And.right⟩

lemma left [Zero E] (hX : Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P) :
    Locally p 𝓕 X P :=
  hX.of_and.left

lemma right [Zero E] (hX : Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P) :
    Locally q 𝓕 X P :=
  hX.of_and.right

end Locally

variable [Zero E]

/-- A property of stochastic processes is said to be stable if it is preserved under taking
the stopped process by a stopping time. -/
def IsStable
    (𝓕 : Filtration ι mΩ) (p : (ι → Ω → E) → Prop) : Prop :=
    ∀ X : ι → Ω → E, p X → ∀ τ : Ω → WithTop ι, IsStoppingTime 𝓕 τ →
      p (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ)

lemma IsStable.and (p q : (ι → Ω → E) → Prop)
    (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q) :
    IsStable 𝓕 (fun X ↦ p X ∧ q X) :=
  fun _ hX τ hτ ↦ ⟨hp _ hX.left τ hτ, hq _ hX.right τ hτ⟩

variable [TopologicalSpace ι] [OrderTopology ι]

lemma IsStable.isStable_locally (hp : IsStable 𝓕 p) :
    IsStable 𝓕 (fun Y ↦ Locally p 𝓕 Y P) := by
  intro X hX τ hτ
  refine ⟨hX.localSeq, hX.IsLocalizingSequence, fun n ↦ ?_⟩
  simp_rw [← stoppedProcess_indicator_comm', Set.indicator_indicator, Set.inter_comm,
    ← Set.indicator_indicator, stoppedProcess_stoppedProcess, inf_comm]
  rw [stoppedProcess_indicator_comm', ← stoppedProcess_stoppedProcess]
  exact hp _ (hX.stoppedProcess n) τ hτ

lemma locally_and (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q) :
    Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P ↔ Locally p 𝓕 X P ∧ Locally q 𝓕 X P := by
  refine ⟨Locally.of_and, fun ⟨hpX, hqX⟩ ↦
    ⟨_, hpX.IsLocalizingSequence.min hqX.IsLocalizingSequence, fun n ↦ ⟨?_, ?_⟩⟩⟩
  · convert hp _ (hpX.stoppedProcess n) _ <| hqX.IsLocalizingSequence.isStoppingTime n using 1
    ext i ω
    rw [stoppedProcess_indicator_comm]
    simp_rw [Pi.inf_apply, lt_inf_iff, inf_comm (hpX.localSeq n)]
    rw [← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_comm,
      (_ : {ω | ⊥ < hpX.localSeq n ω ∧ ⊥ < hqX.localSeq n ω}
        = {ω | ⊥ < hpX.localSeq n ω} ∩ {ω | ⊥ < hqX.localSeq n ω}), Set.inter_comm]
    · simp_rw [← Set.indicator_indicator]
      rfl
    · rfl
  · convert hq _ (hqX.stoppedProcess n) _ <| hpX.IsLocalizingSequence.isStoppingTime n using 1
    ext i ω
    rw [stoppedProcess_indicator_comm]
    simp_rw [Pi.inf_apply, lt_inf_iff]
    rw [← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_comm,
      (_ : {ω | ⊥ < hpX.localSeq n ω ∧ ⊥ < hqX.localSeq n ω}
        = {ω | ⊥ < hpX.localSeq n ω} ∩ {ω | ⊥ < hqX.localSeq n ω})]
    · simp_rw [← Set.indicator_indicator]
      rfl
    · rfl

end LinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

lemma measure_iInter_of_ae_antitone {ι : Type*}
    [Countable ι] [Preorder ι] [IsDirected ι fun (x1 x2 : ι) ↦ x1 ≤ x2]
    {s : ι → Set Ω} (hs : ∀ᵐ ω ∂P, Antitone (s · ω))
    (hsm : ∀ (i : ι), MeasureTheory.NullMeasurableSet (s i) P) (hfin : ∃ (i : ι), P (s i) ≠ ⊤) :
    P (⋂ (i : ι), s i) = ⨅ (i : ι), P (s i) := by
  set t : ι → Set Ω := fun i ↦ ⋂ j ≤ i, s j with ht
  have hst (i : ι) : s i =ᵐ[P] t i := by
    filter_upwards [hs] with ω hω
    suffices ω ∈ s i ↔ ω ∈ t i by
      exact propext this
    simp only [ht, Set.mem_iInter]
    refine ⟨fun (h : s i ω) j hj ↦ ?_, fun h ↦ h i le_rfl⟩
    change s j ω
    specialize hω hj
    simp only [le_Prop_eq] at hω
    exact hω h
  rw [measure_congr <| Filter.EventuallyEq.countable_iInter hst, Antitone.measure_iInter]
  · exact iInf_congr <| fun i ↦ measure_congr <| (hst i).symm
  · exact Set.antitone_dissipate
  · exact fun _ ↦ NullMeasurableSet.iInter <| fun j ↦ NullMeasurableSet.iInter <| fun _ ↦ hsm j
  · obtain ⟨i, hi⟩ := hfin
    refine ⟨i, (lt_of_le_of_lt ?_ <| lt_top_iff_ne_top.2 hi).ne⟩
    rw [measure_congr (hst i)]

lemma isLocalizingSequence_of_isPreLocalizingSequence
    [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
    {τ : ℕ → Ω → WithTop ι} [IsRightContinuous 𝓕] (hτ : IsPreLocalizingSequence 𝓕 τ P) :
    IsLocalizingSequence 𝓕 (fun i ω ↦ ⨅ j ≥ i, τ j ω) P where
  isStoppingTime (n : ℕ) := IsStoppingTime.biInf (Set.to_countable {j | j ≥ n})
    (fun j _ ↦ hτ.isStoppingTime j)
  mono :=  ae_of_all _ <| fun ω n m hnm ↦ iInf_le_iInf_of_subset <| fun k hk ↦ hnm.trans hk
  tendsto_top := by
    filter_upwards [hτ.tendsto_top] with ω hω
    replace hω := hω.liminf_eq
    rw [liminf_eq_iSup_iInf_of_nat] at hω
    rw [← hω]
    refine tendsto_atTop_iSup ?_
    intro n m hnm
    simp only [ge_iff_le, le_iInf_iff, iInf_le_iff]
    intro k hk i hi
    grind

/-- A stable property satisfies `p` locally for `X` if there exists a pre-localizing sequence `τ`
for which the stopped process of `fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)` satisfies `p`. -/
lemma locally_of_isPreLocalizingSequence
    [Zero E] [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι] {τ : ℕ → Ω → WithTop ι}
    (hp : IsStable 𝓕 p) [IsRightContinuous 𝓕] (hτ : IsPreLocalizingSequence 𝓕 τ P)
    (hpτ : ∀ n, p (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))) :
    Locally p 𝓕 X P := by
  refine ⟨_, isLocalizingSequence_of_isPreLocalizingSequence hτ, fun n ↦ ?_⟩
  rw [stoppedProcess_indicator_comm', ← stoppedProcess_stoppedProcess_of_le_right
    (τ := fun ω ↦ τ n ω) (fun _ ↦ (iInf_le _ n).trans <| iInf_le _ le_rfl),
    ← stoppedProcess_indicator_comm']
  convert hp _ (hpτ n) (fun ω ↦ ⨅ j ≥ n, τ j ω) <|
    (isLocalizingSequence_of_isPreLocalizingSequence hτ).isStoppingTime n using 2
  ext i ω
  rw [stoppedProcess_indicator_comm', Set.indicator_indicator]
  congr 1
  ext ω'
  simp only [ge_iff_le, Set.mem_setOf_eq, Set.mem_inter_iff]
  exact ⟨fun h ↦ ⟨h, lt_of_lt_of_le h <| (iInf_le _ n).trans (iInf_le _ le_rfl)⟩, fun h ↦ h.1⟩

section

variable [SecondCountableTopology ι] [IsFiniteMeasure P]

private lemma isPreLocalizingSequence_of_isLocalizingSequence_aux'
    {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ T : ℕ → ι, Tendsto T atTop atTop
      ∧ ∀ n, ∃ k, P {ω | σ n k ω < min (τ n ω) (T n)} ≤ (1 / 2) ^ n := by
  obtain ⟨T, -, hT⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop ι
  refine ⟨T, hT, fun n ↦ ?_⟩
  by_contra hn; push_neg at hn
  suffices (1 / 2) ^ n ≤ P (⋂ k : ℕ, {ω | σ n k ω < min (τ n ω) (T n)}) by
    refine (by simp : ¬ (1 / 2 : ℝ≥0∞) ^ n ≤ 0) <| this.trans <| nonpos_iff_eq_zero.2 ?_
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [(hσ n).tendsto_top] with ω hTop hmem
    simp_rw [WithTop.tendsto_nhds_top_iff, eventually_atTop] at hTop
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hmem
    obtain ⟨N, hN⟩ := hTop (T n)
    specialize hN N le_rfl
    specialize hmem N
    grind
  rw [measure_iInter_of_ae_antitone, le_iInf_iff]
  · exact fun k ↦ (hn k).le
  · filter_upwards [(hσ n).mono] with ω hω
    intros i j hij
    specialize hω hij
    simp only [lt_inf_iff, le_Prop_eq] at *
    change σ n j ω < τ n ω ∧ σ n j ω < T n → σ n i ω < τ n ω ∧ σ n i ω < T n
    grind
  · intro i
    refine MeasurableSet.nullMeasurableSet ?_
    simp_rw [lt_inf_iff]
    rw [(_ : {ω | σ n i ω < τ n ω ∧ σ n i ω < T n} = {ω | σ n i ω < τ n ω} ∩ {ω | σ n i ω < T n})]
    · exact MeasurableSet.inter
        (measurableSet_lt ((hσ n).isStoppingTime i).measurable' (hτ.isStoppingTime n).measurable')
        <| measurableSet_lt ((hσ n).isStoppingTime i).measurable' measurable_const
    · rfl
  · exact ⟨0, measure_ne_top P _⟩

/-- Auxiliary definition for `isPreLocalizingSequence_of_isLocalizingSequence` which constructs a
strictly increasing sequence from a given sequence. -/
def mkStrictMonoAux (x : ℕ → ℕ) : ℕ → ℕ
| 0 => x 0
| n + 1 => max (x (n + 1)) (mkStrictMonoAux x n) + 1

lemma mkStrictMonoAux_strictMono (x : ℕ → ℕ) : StrictMono (mkStrictMonoAux x) := by
  refine strictMono_nat_of_lt_succ <| fun n ↦ ?_
  simp only [mkStrictMonoAux]
  exact lt_of_le_of_lt (le_max_right (x (n + 1)) _) (lt_add_one (max (x (n + 1)) _))

lemma le_mkStrictMonoAux (x : ℕ → ℕ) : ∀ n, x n ≤ mkStrictMonoAux x n
| 0 => by simp [mkStrictMonoAux]
| n + 1 => by
    simp only [mkStrictMonoAux]
    exact (le_max_left (x (n + 1)) (mkStrictMonoAux x n)).trans <|
       Nat.le_add_right (max (x (n + 1)) (mkStrictMonoAux x n)) 1

lemma isPreLocalizingSequence_of_isLocalizingSequence_aux
    {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, StrictMono nk ∧ ∃ T : ℕ → ι, Tendsto T atTop atTop
      ∧ ∀ n, P {ω | σ n (nk n) ω < min (τ n ω) (T n)} ≤ (1 / 2) ^ n := by
  obtain ⟨T, hT, h⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux' hτ hσ
  choose nk hnk using h
  refine ⟨mkStrictMonoAux nk, mkStrictMonoAux_strictMono nk, T, hT, fun n ↦
    le_trans (EventuallyLE.measure_le ?_) (hnk n)⟩
  filter_upwards [(hσ n).mono] with ω hω
  specialize hω (le_mkStrictMonoAux nk n)
  simp only [lt_inf_iff, le_Prop_eq]
  change σ n (mkStrictMonoAux nk n) ω < τ n ω ∧ σ n (mkStrictMonoAux nk n) ω < T n →
    σ n (nk n) ω < τ n ω ∧ σ n (nk n) ω < T n
  grind

lemma isPreLocalizingSequence_of_isLocalizingSequence
    [NoMaxOrder ι] {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, StrictMono nk
      ∧ IsPreLocalizingSequence 𝓕 (fun i ω ↦ (τ i ω) ⊓ (σ i (nk i) ω)) P := by
  obtain ⟨nk, hnk, T, hT, hP⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux hτ hσ
  refine ⟨nk, hnk, fun n ↦ (hτ.isStoppingTime n).min ((hσ _).isStoppingTime _), ?_⟩
  have : ∑' n, P {ω | σ n (nk n) ω < min (τ n ω) (T n)} < ∞ :=
    lt_of_le_of_lt (ENNReal.summable.tsum_mono ENNReal.summable hP)
      (tsum_geometric_lt_top.2 <| by norm_num)
  have hτTop := hτ.tendsto_top
  filter_upwards [ae_eventually_notMem this.ne, hτTop] with ω hω hωτ
  replace hT := hωτ.min <| WithTop.tendsto_coe_atTop.comp hT
  simp_rw [eventually_atTop, not_lt, ← eventually_atTop] at hω
  rw [min_self] at hT
  rw [← min_self ⊤]
  refine hωτ.min <| tendsto_of_tendsto_of_tendsto_of_le_of_le' hT tendsto_const_nhds hω ?_
  simp only [le_top, eventually_atTop, ge_iff_le, implies_true, exists_const]

variable [DenselyOrdered ι] [NoMaxOrder ι] [Zero E]

/-- A stable property holding locally is idempotent. -/
lemma locally_locally
    [IsRightContinuous 𝓕] (hp : IsStable 𝓕 p) :
    Locally (fun Y ↦ Locally p 𝓕 Y P) 𝓕 X P ↔ Locally p 𝓕 X P := by
  refine ⟨fun hL ↦ ?_, fun hL ↦ ?_⟩
  · have hLL := hL.stoppedProcess
    choose τ hτ₁ hτ₂ using hLL
    obtain ⟨nk, hnk, hpre⟩ := isPreLocalizingSequence_of_isLocalizingSequence
      hL.IsLocalizingSequence hτ₁
    refine locally_of_isPreLocalizingSequence hp hpre <| fun n ↦ ?_
    specialize hτ₂ n (nk n)
    convert hτ₂ using 1
    ext i ω
    rw [stoppedProcess_indicator_comm', stoppedProcess_indicator_comm',
      stoppedProcess_stoppedProcess, stoppedProcess_indicator_comm']
    simp only [lt_inf_iff, Set.indicator_indicator]
    congr 1
    · ext ω'; simp only [And.comm, Set.mem_setOf_eq, Set.mem_inter_iff]
    · simp_rw [inf_comm]
      rfl
  · exact ⟨hL.localSeq, hL.IsLocalizingSequence, fun n ↦ Locally.of_prop <| hL.stoppedProcess n⟩

/-- If `p` implies `q` locally, then `p` locally implies `q` locally. -/
lemma locally_induction [IsRightContinuous 𝓕]
    (hpq : ∀ Y, p Y → Locally q 𝓕 Y P) (hq : IsStable 𝓕 q) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  (locally_locally hq).1 <| hpX.mono hpq

lemma locally_induction₂ {r : (ι → Ω → E) → Prop} [IsRightContinuous 𝓕]
    (hrpq : ∀ Y, r Y → p Y → Locally q 𝓕 Y P)
    (hr : IsStable 𝓕 r) (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q)
    (hrX : Locally r 𝓕 X P) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  locally_induction (p := fun Y ↦ r Y ∧ p Y) (and_imp.2 <| hrpq ·) hq
    <| (locally_and hr hp).2 ⟨hrX, hpX⟩

end

end ConditionallyCompleteLinearOrderBot

end ProbabilityTheory
