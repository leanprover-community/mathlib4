/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Independence.BoundedContinuousFunction
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Independence.ZeroOne
public import Mathlib.Probability.Independence.Integration

/-!
# Brownian motion

-/

@[expose] public section

open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

section Aux

open ProbabilityTheory

lemma eventually_nhdsGT {α : Type*} [TopologicalSpace α] [LinearOrder α] [ClosedIciTopology α]
    {a b : α} (hab : a < b) {p : α → Prop} (h : ∀ x ∈ Set.Ioc a b, p x) :
    ∀ᶠ x in 𝓝[>] a, p x :=
  sets_of_superset (x := Set.Ioo a b) _ (Ioo_mem_nhdsGT hab) (by grind)

lemma MeasurableSpace.comap_le_comap
    {Ω 𝓧 𝓨 : Type*} [m𝓧 : MeasurableSpace 𝓧] [m𝓨 : MeasurableSpace 𝓨]
    {X : Ω → 𝓧} {Y : Ω → 𝓨} (f : 𝓧 → 𝓨) (hf : Measurable f) (h : Y = f ∘ X) :
    m𝓨.comap Y ≤ m𝓧.comap X := by
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hf.comap_le

lemma MeasureTheory.Filtration.natural_eq_comap {Ω ι : Type*} {m : MeasurableSpace Ω}
    {β : ι → Type*} [(i : ι) → TopologicalSpace (β i)]
    [∀ (i : ι), TopologicalSpace.MetrizableSpace (β i)]
    [mβ : (i : ι) → MeasurableSpace (β i)] [∀ (i : ι), BorelSpace (β i)] [Preorder ι]
    (u : (i : ι) → Ω → β i)
    (hum : ∀ (i : ι), StronglyMeasurable (u i)) (i : ι) :
    Filtration.natural u hum i = .comap (fun ω (j : Set.Iic i) ↦ u j ω) inferInstance := by
  simp_rw [Filtration.natural, comap_process, iSup_subtype']
  rfl

lemma ProbabilityTheory.measure_eq_zero_or_one_of_indep_self {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsZeroOrProbabilityMeasure P]
    (hm1 : m ≤ mΩ) (hm2 : Indep m m P) {A : Set Ω} (hA : MeasurableSet[m] A) :
    P A = 0 ∨ P A = 1 := by
  rw [Indep_iff_IndepSets, indepSets_iff_singleton_indepSets] at hm2
  replace hm2 := indepSets_iff_singleton_indepSets.1 (hm2 A hA).symm A hA
  exact measure_eq_zero_or_one_of_indepSet_self <|
    (indepSet_iff_indepSets_singleton (hm1 A hA) (hm1 A hA) P).2 hm2

lemma MeasurableSpace.generateFrom_singleton_eq_comap_indicator_one {Ω : Type*} {A : Set Ω} :
    MeasurableSpace.generateFrom {A} =
      MeasurableSpace.comap (A.indicator (1 : Ω → ℝ)) inferInstance := by
  refine le_antisymm (MeasurableSpace.generateFrom_le fun s hs ↦ ?_)
    (Measurable.comap_le ?_)
  · simp only [Set.mem_singleton_iff] at hs
    rw [hs, ← measurable_indicator_const_iff (1 : ℝ)]
    exact comap_measurable _
  · apply (measurable_indicator_const_iff 1).2 ?_
    exact MeasurableSpace.measurableSet_generateFrom (by simp)

lemma ProbabilityTheory.singleton_indepSets_comap_iff {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsZeroOrProbabilityMeasure P] {𝓧 : Type*}
    {m𝓧 : MeasurableSpace 𝓧} {A : Set Ω} {X : Ω → 𝓧} (hX : Measurable X) (hA : MeasurableSet A) :
    IndepSets {A} {s | MeasurableSet[m𝓧.comap X] s} P ↔
      (A.indicator (1 : Ω → ℝ)) ⟂ᵢ[P] X := by
  rw [IndepFun_iff_Indep, ← generateFrom_singleton_eq_comap_indicator_one]
  constructor
  · exact IndepSets.indep (generateFrom_le (by simpa)) hX.comap_le (by simp [IsPiSystem])
      (@MeasurableSpace.isPiSystem_measurableSet _ (m𝓧.comap X)) rfl (by simp)
  · refine fun h ↦ Indep.indepSets ?_
    convert h
    simp

lemma IndepSets.setIntegral_eq_mul {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧} [IsZeroOrProbabilityMeasure μ]
    {f : 𝓧 → ℝ} {A : Set Ω} (hA1 : IndepSets {A} {s | MeasurableSet[m𝓧.comap X] s} μ)
    (hX : Measurable X) (hA2 : MeasurableSet A)
    (hf : AEStronglyMeasurable f (μ.map X)) :
    ∫ ω in A, f (X ω) ∂μ = μ.real A * ∫ ω, f (X ω) ∂μ :=
  calc ∫ ω in A, f (X ω) ∂μ
    = ∫ ω, (A.indicator 1 ω) * f (X ω) ∂μ := by
        rw [← integral_indicator hA2]
        congr with ω
        by_cases hω : ω ∈ A <;> simp [hω]
  _ = ∫ ω, id (A.indicator 1 ω) * f (X ω) ∂μ := by simp
  _ = μ.real A * ∫ ω, f (X ω) ∂μ := by
    rw [IndepFun.integral_fun_comp_mul_comp]
    · simp [integral_indicator_one hA2]
    · exact (singleton_indepSets_comap_iff hX hA2).1 hA1
    · exact (aemeasurable_indicator_const_iff 1).2 hA2.nullMeasurableSet
    · exact hX.aemeasurable
    · fun_prop
    · exact hf

lemma Indep.singleton_indepSets {Ω : Type*} {m1 m2 mΩ : MeasurableSpace Ω}
    {P : Measure Ω} (h : Indep m1 m2 P) {A : Set Ω}
    (hA : MeasurableSet[m1] A) : IndepSets {A} {s | MeasurableSet[m2] s} P := by
  have := (Indep_iff_IndepSets m1 m2 P).1 h
  apply indepSets_of_indepSets_of_le_left this
  simpa

lemma measurableSpace_le_iff {Ω : Type*} {m1 m2 : MeasurableSpace Ω} :
    m1 ≤ m2 ↔ ∀ s, MeasurableSet[m1] s → MeasurableSet[m2] s := by aesop

open Finset

/-- Telescopic sum when summing over `Fin`. -/
lemma Fin.sum_Iic_sub {E : Type*} [AddCommGroup E] {n : ℕ} (a : Fin n) (f : Fin (n + 1) → E) :
    ∑ i ∈ Iic a, (f i.succ - f i.castSucc) = f a.succ - f 0 := by
  let g : Fin n → E := fun i ↦ if i ∈ Iic a then f i.succ - f i.castSucc else 0
  let h : ℕ → E := fun i ↦ if hi : i < n then g ⟨i, hi⟩ else 0
  calc
  _ = ∑ i, g i := by
    rw [Finset.sum_ite_mem, univ_inter]
  _ = ∑ i : Fin n, h i := by
    congr with i
    simp_rw [h, dif_pos i.2]
  _ = ∑ i ∈ range a.succ, h i := by
    rw [Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr_of_eq_on_inter ?_ (by grind) (by grind)
    simp only [mem_range, Fin.val_succ, not_lt]
    intro i hi1 hi2
    simp_rw [h, dif_pos hi1, g]
    rw [if_neg (by simpa)]
  _ = ∑ i ∈ range a.succ, (f (Fin.ofNat (n + 1) (i + 1)) - f (Fin.ofNat (n + 1) i)) := by
    apply Finset.sum_congr rfl
    simp only [Fin.val_succ, mem_range, mem_Iic, Fin.succ_mk, Fin.castSucc_mk, Fin.ofNat_eq_cast, h,
      g]
    intro i hi
    rw [dif_pos (by omega), if_pos]
    · congr
      · rw [Nat.mod_eq_of_lt]
        grind
      · rw [Nat.mod_eq_of_lt]
        grind
    rw [Fin.le_def]
    grind
  _ = f a.succ - f 0 := by
    rw [Finset.sum_range_sub (fun i ↦ f (Fin.ofNat (n + 1) i))]
    congr
    ext
    simp

end Aux

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

namespace Finset

/-! ### Indexing the elements of a finset in order -/

variable [LinearOrder T] (I : Finset T)

/-- Given a finite set `I : Finset T` of cardinality `n`, `ofFin : Fin #I → T`
is the map `(t₁, ..., tₙ)`, where `t₁ < ... < tₙ` are the elements of `I`. -/
noncomputable def ofFin (i : Fin #I) : T := (I.sort (· ≤ ·)).get
  (Fin.cast (I.length_sort (· ≤ ·)).symm i)

lemma monotone_ofFin : Monotone I.ofFin :=
  fun i j hij ↦ (I.pairwise_sort (· ≤ ·)).rel_get_of_le (by simpa)

lemma ofFin_mem (i : Fin #I) : I.ofFin i ∈ I := I.mem_sort (· ≤ ·) |>.1 <| List.get_mem _ _

/-- Given a finite set `I : Finset T`, and `t : I`,
`I.toFin t` returns the position of `t` in `I`. -/
noncomputable def toFin (i : I) : Fin #I :=
  haveI : NeZero #I := ⟨Nonempty.card_ne_zero ⟨i.1, i.2⟩⟩
  Fin.ofNat #I ((I.sort (· ≤ ·)).idxOf i.1)

@[simp]
lemma ofFin_toFin (i : I) : I.ofFin (I.toFin i) = i.1 := by
  rw [toFin, ofFin]
  nth_rw 2 [← (I.sort (· ≤ ·)).idxOf_get (a := i.1)]
  · congr
    ext
    simp only [Fin.ofNat_eq_cast, Fin.val_cast, Fin.val_natCast]
    rw [Nat.mod_eq_of_lt]
    rw [← I.length_sort (· ≤ ·)]
    exact List.idxOf_lt_length_of_mem <| I.mem_sort (· ≤ ·) |>.2 i.2
  exact List.idxOf_lt_length_of_mem <| I.mem_sort (· ≤ ·) |>.2 i.2

@[simp]
lemma toFin_ofFin (i : Fin #I) : I.toFin ⟨I.ofFin i, ofFin_mem I i⟩ = i := by
  simp_rw [toFin, ofFin]
  rw [List.get_idxOf (sort_nodup ..)]
  simp

section Bot

variable [Bot T]

/-- Given a finite set `I : Finset T` of cardinality `n`, `ofFin' : Fin (#I + 1) → T`
is the map `(⊥, t₁, ..., tₙ)`, where `t₁ < ... < tₙ` are the elements of `I`. -/
noncomputable def ofFin' (i : Fin (#I + 1)) : T :=
  if h : i = 0
    then ⊥
    else I.ofFin (i.pred h)

@[simp]
lemma ofFin'_zero : I.ofFin' 0 = ⊥ := rfl

lemma ofFin'_of_ne_zero (i : Fin (#I + 1)) (hi : i ≠ 0) :
    I.ofFin' i = I.ofFin (i.pred hi) := by rw [ofFin', dif_neg hi]

@[simp]
lemma ofFin'_succ (i : Fin #I) :
    I.ofFin' i.succ = I.ofFin i := by
  rw [ofFin'_of_ne_zero, Fin.pred_succ]
  simp

lemma ofFin'_mem (i : Fin (#I + 1)) (hi : i ≠ 0) : I.ofFin' i ∈ I := by
  rw [ofFin'_of_ne_zero _ _ hi]
  exact ofFin_mem I _

end Bot

lemma monotone_ofFin' [OrderBot T] : Monotone (I.ofFin') := by
  intro i j hij
  obtain rfl | hi := eq_or_ne i 0
  · simp
  rw [ofFin'_of_ne_zero I i hi, ofFin'_of_ne_zero I j (by aesop)]
  apply monotone_ofFin
  simpa

end Finset

namespace ProbabilityTheory

section Increments

/-! ### Independent increments -/

/-- A process `X : T → Ω → E` has independent increments if for any `n ≥ 1` and `t₁ ≤ ... ≤ tₙ`,
the random variables `X t₂ - X t₁, ..., X tₙ - X tₙ₋₁` are independent. -/
def HasIndepIncrements [Preorder T] [Sub E] [MeasurableSpace E] (X : T → Ω → E)
    (P : Measure Ω := by volume_tac) :
    Prop :=
  ∀ n, ∀ t : Fin (n + 1) → T, Monotone t →
    iIndepFun (fun (i : Fin n) ω ↦ X (t i.succ) ω - X (t i.castSucc) ω) P

lemma HasIndepIncrements.increments_nat {T E : Type*} [Preorder T] [Sub E] [MeasurableSpace E]
    {P : Measure Ω} {X : T → Ω → E} (h : HasIndepIncrements X P) :
    ∀ t : ℕ → T, Monotone t → iIndepFun (fun i ω ↦ X (t (i + 1)) ω - X (t i) ω) P := by
  intro t ht
  rw [ProbabilityTheory.iIndepFun_iff_finset]
  intro s
  by_cases! hs : s.Nonempty
  · rcases s.max_of_nonempty hs with ⟨n, hn⟩
    let g : (s → Fin n.succ) :=
      fun x ↦ ⟨x, by simpa [hn] using s.le_max x.mem⟩
    apply iIndepFun.precomp (g := g) _ <| h n.succ (fun m ↦ t m) _
    · simp [g, Function.Injective]
    · exact ht.comp Fin.val_strictMono.monotone
  · have := (h 0 (fun _ ↦ t 0) (fun _ ↦ by aesop)).isProbabilityMeasure
    rw [hs]; aesop

lemma HasIndepIncrements.of_increments_nat {T E : Type*} [Preorder T] [Sub E] [MeasurableSpace E]
    {P : Measure Ω} {X : T → Ω → E}
    (h : ∀ t : ℕ → T, Monotone t ∧ EventuallyConst t atTop →
    iIndepFun (fun i ω ↦ X (t (i + 1)) ω - X (t i) ω) P) :
    HasIndepIncrements X P := by
  intro n t ht
  let t' := fun x ↦ t ⟨min n x, by aesop⟩
  convert iIndepFun.precomp Fin.val_injective <| h t' _
  · simp
  · aesop
  · refine ⟨fun _ _ _ ↦ by apply ht; aesop,?_⟩
    rw [eventuallyConst_atTop]
    use n; aesop

/-- `incrementsToRestrict I` is a continuous linear map `f` such that
`f (xₜ₁, xₜ₂ - xₜ₁, ..., xₜₙ - xₜₙ₋₁) = (xₜ₁, ..., xₜₙ)`. -/
noncomputable def incrementsToRestrict [LinearOrder T] (R : Type*) [Semiring R] [AddCommMonoid E]
    [Module R E] [TopologicalSpace E] [ContinuousAdd E] (I : Finset T) :
    (Fin #I → E) →L[R] (I → E) :=
  { toFun x i := ∑ j ≤ I.toFin i, x j
    map_add' x y := by ext; simp [sum_add_distrib]
    map_smul' m x := by ext; simp [smul_sum]
    cont := by fun_prop }

lemma incrementsToRestrict_increments_ofFin'_ae_eq_restrict [LinearOrder T] (R : Type*) [OrderBot T]
    [Semiring R] [AddCommGroup E] [Module R E] [TopologicalSpace E] [ContinuousAdd E]
    {X : T → Ω → E} (h : ∀ᵐ ω ∂P, X ⊥ ω = 0) (I : Finset T) :
    (fun ω ↦ I.restrict (X · ω)) =ᵐ[P]
      (incrementsToRestrict R I) ∘
        (fun ω i ↦ X (I.ofFin' i.succ) ω - X (I.ofFin' i.castSucc) ω) := by
  filter_upwards [h] with ω hω
  ext t
  simp only [restrict, incrementsToRestrict, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply]
  rw [Fin.sum_Iic_sub (I.toFin t) (fun j ↦ X (I.ofFin' j) ω)]
  simp [hω]

lemma HasIndepIncrements.indepFun_sub_sub [Preorder T] [MeasurableSpace E] [AddGroup E]
    {X : T → Ω → E} (h : HasIndepIncrements X P) {r s t : T} (hrs : r ≤ s) (hst : s ≤ t) :
    IndepFun (X s - X r) (X t - X s) P := by
  let τ' : ℕ → T
    | 0 => r
    | 1 => s
    | _ => t
  exact h.increments_nat τ' (fun _ ↦ by grind)|>.indepFun (by norm_num : 0 ≠ 1)

lemma HasIndepIncrements.indepFun_eval_sub [Preorder T] [MeasurableSpace E] [AddGroup E]
    {X : T → Ω → E} (h : HasIndepIncrements X P) {r s t : T} (hrs : r ≤ s) (hst : s ≤ t)
    (hX : ∀ᵐ ω ∂P, X r ω = 0) :
    IndepFun (X s) (X t - X s) P := by
  have := h.indepFun_sub_sub hrs hst
  refine this.congr ?_ .rfl
  filter_upwards [hX] with ω hω using by simp [hω]

/-- A stochastic process `X` with independent increments and such that `X t` is gaussian for
all `t` is a Gaussian process. -/
lemma HasIndepIncrements.isGaussianProcess [LinearOrder T] [OrderBot T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    {X : T → Ω → E} (law : ∀ t, HasGaussianLaw (X t) P) (h_bot : ∀ᵐ ω ∂P, X ⊥ ω = 0)
    (incr : HasIndepIncrements X P) :
    IsGaussianProcess X P where
  hasGaussianLaw I := by
    have := (law ⊥).isProbabilityMeasure
    obtain rfl | hI := I.eq_empty_or_nonempty
    · constructor
      have : P.map (fun ω ↦ Finset.restrict ∅ fun x ↦ X x ω) = .dirac Classical.ofNonempty := by
        ext s -
        apply Subsingleton.set_cases (p := fun s ↦ Measure.map _ _ s = _)
        · simp
        simp only [measure_univ]
        exact @measure_univ _ _ _
          (Measure.isProbabilityMeasure_map (aemeasurable_pi_lambda _ fun _ ↦ (law _).aemeasurable))
      rw [this]
      infer_instance
    have := incrementsToRestrict_increments_ofFin'_ae_eq_restrict ℝ h_bot I
    refine @HasGaussianLaw.congr _ _ _ _ _ _ _ _ _ _ ?_ this.symm
    refine HasGaussianLaw.map ?_ _
    exact (incr _ _ (monotone_ofFin' I)).hasGaussianLaw fun i ↦
      incr.indepFun_eval_sub bot_le
        (monotone_ofFin' I (Fin.castSucc_le_succ i)) h_bot
          |>.hasGaussianLaw_sub_of_sub (law _) (law _)

end Increments

section IsPreBrownian

variable (X : ℝ≥0 → Ω → ℝ)

/-- A stochastic process is called **pre-Brownian** if its finite-dimensional laws are those
of a Brownian motion, see `gaussianProjectiveFamily`. -/
class IsPreBrownian (P : Measure Ω := by volume_tac) : Prop where
  mk' ::
  hasLaw : ∀ I : Finset ℝ≥0, HasLaw (fun ω ↦ I.restrict (X · ω)) (gaussianProjectiveFamily I) P

variable {X} {P : Measure Ω}

lemma IsPreBrownian.congr {Y : ℝ≥0 → Ω → ℝ} [hX : IsPreBrownian X P] (h : ∀ t, X t =ᵐ[P] Y t) :
    IsPreBrownian Y P where
  hasLaw I := by
    refine (hX.hasLaw I).congr ?_
    have : ∀ᵐ ω ∂P, ∀ i : I, X i ω = Y i ω := ae_all_iff.2 fun _ ↦ h _
    filter_upwards [this] with ω hω using funext fun i ↦ (hω i).symm

lemma IsPreBrownian.isGaussianProcess [IsPreBrownian X P] : IsGaussianProcess X P where
  hasGaussianLaw I := (IsPreBrownian.hasLaw I).hasGaussianLaw

lemma IsPreBrownian.aemeasurable [hX : IsPreBrownian X P] (t : ℝ≥0) : AEMeasurable (X t) P :=
  HasGaussianLaw.aemeasurable (hX.isGaussianProcess.hasGaussianLaw_eval t)

lemma IsPreBrownian.hasLaw_eval [h : IsPreBrownian X P] (t : ℝ≥0) :
    HasLaw (X t) (gaussianReal 0 t) P :=
  (measurePreserving_eval_gaussianProjectiveFamily ⟨t, by simp⟩).hasLaw.comp (h.hasLaw {t})

lemma IsPreBrownian.hasLaw_sub [IsPreBrownian X P] (s t : ℝ≥0) :
    HasLaw (X s - X t) (gaussianReal 0 (max (s - t) (t - s))) P :=
  (measurePreserving_eval_sub_eval_gaussianProjectiveFamily
    {s, t} ⟨s, by simp⟩ ⟨t, by simp⟩).hasLaw.comp (IsPreBrownian.hasLaw _)

lemma IsPreBrownian.integral_eval [h : IsPreBrownian X P] (t : ℝ≥0) :
    P[X t] = 0 := by
  rw [(h.hasLaw_eval t).integral_eq, integral_id_gaussianReal]

lemma IsPreBrownian.integrable_eval [h : IsPreBrownian X P] (t : ℝ≥0) :
    Integrable (X t) P := (h.isGaussianProcess.hasGaussianLaw_eval t).integrable

lemma IsPreBrownian.covariance_eval [h : IsPreBrownian X P] (s t : ℝ≥0) :
    cov[X s, X t; P] = min s t := by
  convert (h.hasLaw {s, t}).covariance_comp
    (f := Function.eval ⟨s, by simp⟩) (g := Function.eval ⟨t, by simp⟩) ?_ ?_
  · rw [covariance_eval_gaussianProjectiveFamily]
  all_goals exact Measurable.aemeasurable (by fun_prop)

lemma IsPreBrownian.covariance_fun_eval [h : IsPreBrownian X P] (s t : ℝ≥0) :
    cov[fun ω ↦ X s ω, fun ω ↦ X t ω; P] = min s t :=
  h.covariance_eval s t

set_option backward.isDefEq.respectTransparency false in
lemma IsPreBrownian.hasIndepIncrements [h : IsPreBrownian X P] : HasIndepIncrements X P := by
  have : IsProbabilityMeasure P := h.isGaussianProcess.isProbabilityMeasure
  refine fun n t ht ↦ h.isGaussianProcess.hasGaussianLaw_increments.iIndepFun_of_covariance_eq_zero
    fun i j hij ↦ ?_
  rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right]
  · simp_rw [IsPreBrownian.covariance_fun_eval]
    wlog h' : i < j generalizing i j
    · simp_rw [← this j i hij.symm (by omega), min_comm]
      ring
    have h1 : i.succ ≤ j.succ := Fin.strictMono_succ h' |>.le
    have h2 : i.castSucc ≤ j.succ := Fin.le_of_lt h1
    have h3 : i.castSucc ≤ j.castSucc := Fin.le_castSucc_iff.mpr h1
    rw [min_eq_left (ht h1), min_eq_left (ht h'), min_eq_left (ht h2), min_eq_left (ht h3)]
    simp
  any_goals exact (h.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
  exact h.isGaussianProcess.hasGaussianLaw_sub.memLp_two

set_option backward.isDefEq.respectTransparency false in
lemma IsGaussianProcess.isPreBrownian_of_covariance (h1 : IsGaussianProcess X P)
    (h2 : ∀ t, P[X t] = 0) (h3 : ∀ s t, s ≤ t → cov[X s, X t; P] = s) :
    IsPreBrownian X P where
  hasLaw I := by
    refine ⟨aemeasurable_pi_lambda _ fun _ ↦ h1.aemeasurable _, ?_⟩
    apply (MeasurableEquiv.toLp 2 (_ → ℝ)).map_measurableEquiv_injective
    rw [MeasurableEquiv.coe_toLp, ← PiLp.coe_symm_continuousLinearEquiv 2 ℝ]
    have : IsGaussian
        (Measure.map (⇑(PiLp.continuousLinearEquiv 2 ℝ fun a ↦ ℝ).symm)
        (Measure.map (fun ω ↦ I.restrict fun x ↦ X x ω) P)) := by
      have := (h1.hasGaussianLaw I).isGaussian_map
      infer_instance
    apply IsGaussian.ext
    · rw [integral_map, integral_map, integral_map]
      · simp only [PiLp.continuousLinearEquiv_symm_apply, id_eq]
        simp_rw [← PiLp.continuousLinearEquiv_symm_apply 2 ℝ, ← ContinuousLinearEquiv.coe_coe]
        rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_gaussianProjectiveFamily,
          ContinuousLinearMap.integral_comp_comm]
        · simp only [ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply]
          congr with i
          rw [eval_integral]
          · simpa using h2 _
          · exact fun _ ↦ (h1.hasGaussianLaw_eval _).integrable
        · exact Integrable.of_eval fun _ ↦ (h1.hasGaussianLaw_eval _).integrable
        · exact IsGaussian.integrable_id
      any_goals fun_prop
      exact aemeasurable_pi_lambda _ fun _ ↦ h1.aemeasurable _
    · rw [← ContinuousLinearMap.toBilinForm_inj]
      refine LinearMap.BilinForm.ext_of_isSymm isPosSemidef_covarianceBilin.isSymm
        isPosSemidef_covarianceBilin.isSymm fun x ↦ ?_
      simp only [ContinuousLinearMap.toBilinForm_apply]
      have : IsFiniteMeasure (Measure.map (fun ω ↦ I.restrict fun x ↦ X x ω) P) := by
        have := (h1.hasGaussianLaw I).isGaussian_map
        infer_instance
      rw [PiLp.coe_symm_continuousLinearEquiv, covarianceBilin_apply_pi, covarianceBilin_apply_pi]
      · congrm ∑ i, ∑ j, _ * ?_
        rw [covariance_eval_gaussianProjectiveFamily, covariance_map]
        · wlog hij : i.1 ≤ j.1 generalizing i j
          · rw [covariance_comm, this j i (by grind), min_comm]
          rw [min_eq_left hij]
          exact h3 i j hij
        any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
        exact aemeasurable_pi_lambda _ (fun _ ↦ h1.aemeasurable _)
      · exact fun i ↦ (IsGaussian.hasGaussianLaw_id.eval i).memLp_two
      · exact fun i ↦ ((h1.hasGaussianLaw I).isGaussian_map.hasGaussianLaw_id.eval i).memLp_two

lemma HasIndepIncrements.isPreBrownian_of_hasLaw
    (law : ∀ t, HasLaw (X t) (gaussianReal 0 t) P) (incr : HasIndepIncrements X P) :
    IsPreBrownian X P := by
  apply IsGaussianProcess.isPreBrownian_of_covariance
  · exact incr.isGaussianProcess (fun t ↦ (law t).hasGaussianLaw)
      (law 0).ae_eq_const_of_gaussianReal
  · intro t
    rw [(law t).integral_eq, integral_id_gaussianReal]
  · intro s t hst
    have h1 := incr.indepFun_eval_sub (zero_le s) hst (law 0).ae_eq_const_of_gaussianReal
    have := (law 0).isProbabilityMeasure_iff.2 inferInstance
    have h2 : X t = X t - X s + X s := by simp
    rw [h2, covariance_add_right, h1.covariance_eq_zero, covariance_self, (law s).variance_eq,
      variance_id_gaussianReal]
    · simp
    · exact (law s).aemeasurable
    · exact (law s).hasGaussianLaw.memLp_two
    · exact (law t).hasGaussianLaw.memLp_two.sub (law s).hasGaussianLaw.memLp_two
    · exact (law s).hasGaussianLaw.memLp_two
    · exact (law t).hasGaussianLaw.memLp_two.sub (law s).hasGaussianLaw.memLp_two
    · exact (law s).hasGaussianLaw.memLp_two

lemma IsPreBrownian.neg [hX : IsPreBrownian X P] : IsPreBrownian (-X) P := by
  apply HasIndepIncrements.isPreBrownian_of_hasLaw _ _
  · exact fun t ↦ by simpa using gaussianReal_neg (hX.hasLaw_eval t)
  intro n s hs
  convert (hX.hasIndepIncrements n s hs).comp (fun _ x ↦ -x) (by measurability)
  simp; linarith

set_option backward.isDefEq.respectTransparency false in
lemma IsPreBrownian.smul [hX : IsPreBrownian X P] {c : ℝ≥0} (hc : c ≠ 0) :
    IsPreBrownian (fun t ω ↦ (X (c * t) ω) / √c) P := by
  refine IsGaussianProcess.isPreBrownian_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · have this t ω : X (c * t) ω / √c = (1 / √c) • ((X ∘ (c * ·)) t ω) := by
      simp [inv_mul_eq_div]
    simp_rw [this]
    exact (IsGaussianProcess.comp_right hX.isGaussianProcess _).smul _
  · rw [integral_div, IsPreBrownian.integral_eval, zero_div]
  · rw [covariance_fun_div_left, covariance_fun_div_right, IsPreBrownian.covariance_eval,
      min_eq_left]
    · simp [field]
    · exact mul_le_mul_right hst c

set_option backward.isDefEq.respectTransparency false in
/-- **Weak Markov property**: If `X` is a pre-Brownian motion, then
`X (t₀ + t) - X t₀` is a pre-Brownian motion which is independent from `(B t, t ≤ t₀)`.
This is the proof that it is pre-Brownian, see `IsPreBrownian.indepFun_shift` for independence. -/
lemma IsPreBrownian.shift [h : IsPreBrownian X P] (t₀ : ℝ≥0) :
    IsPreBrownian (fun t ω ↦ X (t₀ + t) ω - X t₀ ω) P := by
  refine (h.isGaussianProcess.shift t₀).isPreBrownian_of_covariance (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · rw [integral_sub, IsPreBrownian.integral_eval, IsPreBrownian.integral_eval, sub_zero]
    all_goals exact (h.isGaussianProcess.hasGaussianLaw_eval _).integrable
  · have := h.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right,
      h.covariance_eval, h.covariance_eval, h.covariance_eval, h.covariance_eval, ← add_min,
      min_eq_left hst, min_eq_right, min_eq_left, min_self]
    any_goals simp
    any_goals exact (h.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    exact h.isGaussianProcess.hasGaussianLaw_sub.memLp_two

set_option backward.isDefEq.respectTransparency false in
/-- **Weak Markov property**: If `X` is a pre-Brownian motion, then
`X (t₀ + t) - X t₀` is a pre-Brownian motion which is independent from `(B t, t ≤ t₀)`.
This is the proof that of independence, see `IsPreBrownian.shift` for the proof
that it is pre-Brownian. -/
lemma IsPreBrownian.indepFun_shift [h : IsPreBrownian X P] (hX : ∀ t, Measurable (X t)) (t₀ : ℝ≥0) :
    IndepFun (fun ω t ↦ X (t₀ + t) ω - X t₀ ω) (fun ω (t : Set.Iic t₀) ↦ X t ω) P := by
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
  · apply h.isGaussianProcess.of_isGaussianProcess
    rintro (t | ⟨t, ht⟩)
    · let L : (({t₀, t₀ + t} : Finset ℝ≥0) → ℝ) →L[ℝ] ℝ :=
        { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
          map_add' x y := by simp; abel
          map_smul' c x := by simp; ring }
      exact ⟨_, L, fun ω ↦ by simp [L]⟩
    · let L : (({t} : Finset ℝ≥0) → ℝ) →L[ℝ] ℝ :=
        { toFun x := x ⟨t, by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }
      exact ⟨_, L, fun ω ↦ by simp [L]⟩
  any_goals fun_prop
  · rintro s ⟨t, ht : t ≤ t₀⟩
    have := h.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left, h.covariance_eval, h.covariance_eval, min_eq_right, min_eq_right,
      sub_self]
    · grind
    · simp [ht, le_add_right]
    all_goals exact (h.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

set_option backward.isDefEq.respectTransparency false in
lemma IsPreBrownian.inv [h : IsPreBrownian X P] :
    IsPreBrownian (fun t ω ↦ t * (X (1 / t) ω)) P := by
  refine IsGaussianProcess.isPreBrownian_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · exact (IsGaussianProcess.comp_right h.isGaussianProcess _).smul _
  · rw [integral_const_mul, IsPreBrownian.integral_eval, mul_zero]
  · have := h.isGaussianProcess.isProbabilityMeasure
    rw [covariance_const_mul_left, covariance_const_mul_right, h.covariance_eval]
    obtain rfl | hs := eq_or_ne s 0
    · simp
    have : 0 < t := (pos_of_ne_zero hs).trans_le hst
    rw [min_eq_right]
    · norm_cast
      field_simp
    exact one_div_le_one_div_of_le (pos_of_ne_zero hs) hst

/-- A pre-Brownian motion `X` is **filtered** with respect to a filtration `𝓕` if it is adapted
to `𝓕` and the increments of `X` after time `t` are independent of `𝓕 t` -/
structure IsFilteredPreBrownian (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop
    extends IsPreBrownian X P where
  stronglyAdapted : StronglyAdapted 𝓕 X
  indep : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (X t - X s) inferInstance) (𝓕 s) P

instance IsPreBrownian.isFilteredPreBrownian [h : IsPreBrownian X P]
    (hX : ∀ t : ℝ≥0, Measurable (X t)) :
    IsFilteredPreBrownian X (natural X (fun t ↦ (hX t).stronglyMeasurable)) P where
  stronglyAdapted := stronglyAdapted_natural (fun t ↦ (hX t).stronglyMeasurable)
  indep s t hst := by
    have h := (IndepFun_iff_Indep _ _ _).1 (h.indepFun_shift hX s)
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
    · have hX : X t - X s = (fun f ↦ f (t - s)) ∘ (fun ω u ↦ (X (s + u) ω - X s ω)) := by
        funext; simp [add_tsub_cancel_of_le, hst]
      rw [hX, ←comap_comp]; apply comap_mono (Measurable.comap_le _); fun_prop
    · refine iSup_le fun u => iSup_le fun hu => ?_
      have hX : (X u) = ((fun f ↦ f ⟨u,hu⟩) ∘ (fun ω (t : Set.Iic s) ↦ X t ω)) := by
        funext; simp
      rw [hX, ←comap_comp]; apply comap_mono (Measurable.comap_le _); fun_prop

lemma IsPreBrownian.isMartingale (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    [IsProbabilityMeasure P] (hX : IsFilteredPreBrownian X 𝓕 P) : Martingale X 𝓕 P := by
  refine ⟨hX.stronglyAdapted, fun s t hst => ?_⟩
  have hM := fun t ↦ ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_no_cond : P[X t - X s | 𝓕 s] =ᵐ[P] fun _ ↦ P[X t - X s] := by
    refine condExp_indep_eq ?_ (𝓕.le s) ?_ (hX.indep s t hst)
    · exact Measurable.comap_le (Measurable.sub (hM t) (hM s))
    · exact (comap_measurable (X t - X s)).stronglyMeasurable
  have h_integral_zero : P[X t - X s] = 0 := calc
    P[X t - X s] = P[X t] - P[X s] := integral_sub (hX.integrable_eval t) (hX.integrable_eval s)
    _ = ↑0 := by simp [hX.integral_eval]
  calc
    _ = P[(X t - X s) + X s | 𝓕 s] := by simp
    _ =ᵐ[P] P[X t - X s | 𝓕 s] + P[X s | 𝓕 s] := condExp_add ((Integrable.sub
      (hX.integrable_eval t) (hX.integrable_eval s))) (hX.integrable_eval s) (𝓕 s)
    _ = P[X t - X s | 𝓕 s] + X s := by
      rw [condExp_of_stronglyMeasurable (𝓕.le s) (hX.stronglyAdapted s) (hX.integrable_eval s)]
    _ =ᵐ[P] (fun _ ↦ P[X t - X s]) + X s := by filter_upwards [h_no_cond] with ω hω; simp [hω]
    _ = X s := by aesop

end IsPreBrownian

section IsBrownian

variable (X : ℝ≥0 → Ω → ℝ)

/-- A stochastic process is called **Brownian** if its finite-dimensional laws are those
of a Brownian motion, see `IsPreBrownian`, and if it has almost-sure continuous paths. -/
class IsBrownian (X) (P : Measure Ω := by volume_tac) : Prop extends IsPreBrownian X P where
  cont : ∀ᵐ ω ∂P, Continuous (X · ω)

variable {X}

lemma IsBrownian.neg [h : IsBrownian X P] :
    IsBrownian (-X) P where
  toIsPreBrownian := h.toIsPreBrownian.neg
  cont := h.cont.mono (fun _ _ ↦ by simpa [← Pi.neg_def, continuous_neg_iff])

lemma IsBrownian.smul [h : IsBrownian X P] {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownian (fun t ω ↦ (X (c * t) ω) / √c) P where
  toIsPreBrownian := h.toIsPreBrownian.smul hc
  cont := by
    filter_upwards [h.cont] with ω h
    fun_prop

lemma IsBrownian.shift [h : IsBrownian X P] (t₀ : ℝ≥0) :
    IsBrownian (fun t ω ↦ X (t₀ + t) ω - X t₀ ω) P where
  toIsPreBrownian := h.toIsPreBrownian.shift t₀
  cont := by
    filter_upwards [h.cont] with ω h
    fun_prop

lemma IsBrownian.tendsto_nhds_zero [h : IsBrownian X P] :
    ∀ᵐ ω ∂P, Filter.Tendsto (X · ω) (𝓝 0) (𝓝 0) := by
  filter_upwards [h.cont, (h.hasLaw_eval 0).ae_eq_const_of_gaussianReal] with ω h1 h2
  convert h1.tendsto 0
  exact h2.symm

/-- **Blumenthal's zero-one law**: Let `𝓕` be the canonical filtration associated to a Brownian
motion. Then the `σ`-algebra `⨅ s > 0, 𝓕 s` is trivial. -/
lemma IsBrownian.indep_zero [h : IsBrownian X P] (hX : ∀ t, Measurable (X t))
    (hX' : ∀ ω, Continuous (X · ω)) {A : Set Ω}
    (hA : MeasurableSet[⨅ s > 0, natural X (fun t ↦ (hX t).stronglyMeasurable) s] A) :
    P A = 0 ∨ P A = 1 := by
  have := h.isGaussianProcess.isProbabilityMeasure
  -- We consider three different `σ`-algebras. `m1` is the one generated by the process `X`.
  let m1 : MeasurableSpace Ω := .comap (fun ω t ↦ X t ω) inferInstance
  -- `m2` is the one generated by the restriction of `X` to positive real numbers.
  let m2 : MeasurableSpace Ω := .comap (fun ω (t : Set.Ioi (0 : ℝ≥0)) ↦ X t ω) inferInstance
  -- `m3` is `⨅ s > 0, 𝓕 s`, which we want to show to be trivial.
  set m3 : MeasurableSpace Ω := ⨅ s > 0, natural X (fun t ↦ (hX t).stronglyMeasurable) s
-- We easily have that `m3 ≤ m1 ≤ mΩ`.
  have hm1 : m1 ≤ mΩ := by
    apply Measurable.comap_le
    apply @measurable_pi_lambda _ _ _ mΩ
    exact hX
  have hm3 : m3 ≤ m1 := by
    apply iInf₂_le_of_le 1 (by simp)
    rw [natural_eq_comap]
    exact comap_le_comap (fun x t ↦ x t.1) (by fun_prop) (by ext; simp)
  have hm3' := hm3.trans hm1
  -- Because `X` is continuous, `X t ⟶ X 0` as `t → 0⁺`, thus
  -- the random variable `X 0` is actually measurable with respect to `m2`, so `m1 ≤ m2`.
  have : m1 ≤ m2 := by
    simp_rw [m1, m2, comap_process]
    rw [iSup_split_single _ 0, sup_le_iff]
    constructor; swap
    · simp_rw [← pos_iff_ne_zero, iSup_subtype, Set.mem_Ioi]
      rfl
    rw [← measurable_iff_comap_le]
    have this : Filter.Tendsto (X ∘ ((↑) : Set.Ioi (0 : ℝ≥0) → ℝ≥0))
        ((𝓝[≠] 0).comap ((↑) : _ → ℝ≥0)) (𝓝 (X 0)) := by
      refine Filter.tendsto_comap'_iff ?_ |>.2
        (tendsto_pi_nhds.2 fun ω ↦ continuousAt_iff_punctured_nhds.1 (hX' ω).continuousAt)
      convert self_mem_nhdsWithin
      ext; simp [pos_iff_ne_zero]
    have l : NeBot ((𝓝[≠] (0 : ℝ≥0)).comap ((↑) : Set.Ioi (0 : ℝ≥0) → ℝ≥0)) := by
      refine comap_coe_neBot_of_le_principal <| le_principal_iff.2 ?_
      convert self_mem_nhdsWithin
      ext; simp [pos_iff_ne_zero]
    exact @measurable_of_tendsto_metrizable' _ _ (iSup _) _ _ _ _ _ _ _ _ l _
      (fun t ↦ (comap_measurable _).iSup' t) this
  -- We prove the result by showing that `m3` is independent of itself.
  refine measure_eq_zero_or_one_of_indep_self hm3' ?_ hA
  -- To do so, we show that for all `A ∈ m3`, all finite set `I ⊆ (0, +∞)` and all
  -- bounded continuous function `f : (I → ℝ) → ℝ`,
  -- `∫ ω in A, f (fun t ↦ X t) ∂P = P.real A * ∫ ω, f (fun t ↦ X t) ∂P`.
  refine indep_of_indep_of_le_right ?_ (hm3.trans this)
  refine indep_comap_process_of_bcf hm3' (fun _ ↦ (hX _).aemeasurable) fun A hA I f ↦ ?_
  -- If `I` is empty, there is nothing to do.
  obtain rfl | hI := I.eq_empty_or_nonempty
  · have : Subsingleton ((∅ : Finset (Set.Ioi (0 : ℝ≥0))) → ℝ) := inferInstance
    simp [this.eq_zero]
  -- We now assume `I` is not empty. We then prove that for all `ε > 0` such that `ε ≤ min I`,
  -- `∫ ω in A, f (fun t ↦ X t ω - X ε ω) ∂P = P.real A * ∫ ω, f (fun t ↦ X t ω - X ε ω) ∂P`.
  -- This follows from the fact that, because `A ∈ m3` in particular `A` is measurable
  -- with respect to `σ(X t | t ≤ ε)`. This `σ`-algebra is independent from
  -- `σ(X (ε + t) - X ε | t ≥ 0)` by the weak Markov property.
  have key (ε : ℝ≥0) (hε1 : 0 < ε) (hε2 : ε ≤ I.min' hI) :
      ∫ ω in A, f (fun t ↦ X t ω - X ε ω) ∂P = P.real A * ∫ ω, f (fun t ↦ X t ω - X ε ω) ∂P := by
    rw [IndepSets.setIntegral_eq_mul _ (by fun_prop) (hm3' A hA) (by fun_prop)]
    have := (IndepFun_iff_Indep _ _ _).1 <| h.indepFun_shift hX ε |>.symm
    refine indepSets_of_indepSets_of_le_right (Indep.singleton_indepSets this ?_) ?_
    · suffices m3 ≤ (.comap (fun ω (t : Set.Iic ε) ↦ X t ω) MeasurableSpace.pi) from this A hA
      apply iInf₂_le_of_le ε hε1
      rw [natural_eq_comap]
    simp only [Set.setOf_subset_setOf, ← measurableSpace_le_iff]
    apply comap_le_comap (fun x t ↦ x (t.1 - ε)) (by fun_prop)
    ext ω t
    simp only [Function.comp_apply, sub_left_inj]
    rw [add_tsub_cancel_of_le]
    exact hε2.trans (I.min'_le t.1 t.2)
  -- Because `f` is continuous and `X t ⟶ 0` almost surely as `t → 0`,
  -- we deduce that almost surely `f (fun t ↦ X t - X ε) ⟶ f (fun t ↦ X t)` as `t → 0`.
  have lol : ∀ᵐ ω ∂P, Tendsto (fun ε ↦ f (fun t ↦ X t ω - X ε ω)) (𝓝[>] 0)
      (𝓝 (f (fun t ↦ X t ω))) := by
    filter_upwards [h.tendsto_nhds_zero] with ω hω
    refine f.continuous.tendsto _ |>.comp (tendsto_pi_nhds.2 fun t ↦ ?_)
    convert (tendsto_nhdsWithin_of_tendsto_nhds hω).const_sub (X t ω)
    simp
  -- Because `f` is also bounded, we can apply the dominated convergence theorem to show that
  -- `∫ ω in A, f (fun t ↦ X t ω - X ε ω) ∂P ⟶ ∫ ω in A, f (fun t ↦ X t ω) ∂P`
  -- as `ε → 0⁺`.
  have h1 : Tendsto (fun ε ↦ ∫ ω in A, f (fun t ↦ X t ω - X ε ω) ∂P) (𝓝[>] 0)
      (𝓝 (∫ ω in A, f (fun t ↦ X t ω) ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖f‖) ?_ ?_
      (integrable_const _) (ae_restrict_of_ae lol)
    · exact Eventually.of_forall fun _ ↦ Measurable.aestronglyMeasurable (by fun_prop)
    · exact Eventually.of_forall fun _ ↦ ae_of_all _ fun _ ↦ f.norm_coe_le_norm _
  -- But similarly we have that
  -- `P.real A * ∫ ω, f (fun t ↦ X t ω - X ε ω) ∂P ⟶ P.real A * ∫ ω in A, f (fun t ↦ X t ω) ∂P`
  -- as `ε → 0⁺`, and we can conclude by uniqueness of the limit.
  refine tendsto_nhds_unique h1 ?_
  refine Tendsto.congr' (f₁ := fun ε ↦ P.real A * ∫ ω, f (fun t ↦ X t ω - X ε ω) ∂P) ?_ ?_
  · apply eventually_nhdsGT (I.min' hI |>.2)
    rintro ε ⟨h1, h2⟩
    exact (key ε h1 h2).symm
  refine Filter.Tendsto.const_mul (b := P.real A) ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖f‖) ?_ ?_
    (integrable_const _) lol
  · exact Eventually.of_forall fun _ ↦ Measurable.aestronglyMeasurable (by fun_prop)
  · exact Eventually.of_forall fun _ ↦ ae_of_all _ fun _ ↦ f.norm_coe_le_norm _

end IsBrownian

section Measure

section ContinuousMap.MeasurableSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

instance : MeasurableSpace C(X, Y) := borel _
instance : BorelSpace C(X, Y) where
  measurable_eq := rfl

lemma isClosed_sUnion_of_finite {X : Type*} [TopologicalSpace X] {s : Set (Set X)}
    (h1 : s.Finite) (h2 : ∀ t ∈ s, IsClosed t) : IsClosed (⋃₀ s) := by
  rw [Set.sUnion_eq_biUnion]
  exact h1.isClosed_biUnion h2

open TopologicalSpace in
lemma ContinuousMap.borel_eq_iSup_comap_eval [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y] :
    borel C(X, Y) = ⨆ a : X, (borel Y).comap fun b ↦ b a := by
  -- https://math.stackexchange.com/questions/4789531/when-does-the-borel-sigma-algebra-of-compact-convergence-coincide-with-the-pr
  apply le_antisymm
  swap
  · refine iSup_le fun x ↦ ?_
    simp_rw [← measurable_iff_comap_le]
    rw [← BorelSpace.measurable_eq, ← BorelSpace.measurable_eq]
    exact Continuous.measurable (by fun_prop)
  -- Denote by `M(K, U)` the set of functions `f` such that `Set.MapsTo f K U`. These form a
  -- basis for the compact-open topology when `K` is compact and `U` is open.
  -- Because `C(X, Y)` is second-countable, it suffices to prove that those sets are measurable.
  -- Let therefore `K` be a compact set of `X` and `U` an open set of `Y`.
  rw [borel_eq_generateFrom_of_subbasis ContinuousMap.compactOpen_eq]
  refine generateFrom_le fun s hs ↦ ?_
  obtain ⟨K, hK, U, hU, hs⟩ := hs
  rw [← hs]
  -- Consider `V` a countable basis of the topology on Y.
  let V := countableBasis Y
  have hV : IsTopologicalBasis V := isBasis_countableBasis Y
  have cV : V.Countable := countable_countableBasis Y
  let W₁ := {v | v ∈ V ∧ closure v ⊆ U}
  -- Consider `W` the set of `closure v`, where `v ∈ V` and `closure v ⊆ U`.
  let W := {v | ∃ u ∈ V, v ⊆ U ∧ v = closure u}
  -- Because `V` is countable, so is `W`.
  have cW : W.Countable := by
    apply (cV.image closure ).mono
    rintro - ⟨u, hu, -, rfl⟩
    exact ⟨u, hu, rfl⟩
  -- Because `Y` is regular, we can write that `U = ⋃_{v ∈ W} v`.
  have U_eq_sUnion_W : U = ⋃₀ W := by
    ext x
    rw [Set.mem_sUnion]
    constructor
    · intro hx
      obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := hV.nhds_basis_closure x |>.mem_iff.1 <| hU.mem_nhds hx
      exact ⟨closure v, ⟨v, hv2, hv3, rfl⟩, subset_closure hv1⟩
    · rintro ⟨-, ⟨t, ht1, ht2, rfl⟩, hx⟩
      exact ht2 hx
  -- Similarly, we can write that `U = ⋃_{v ∈ V, closure v ⊆ U} v`.
  have U_eq_sUnion_W₁ : U = ⋃₀ W₁ := by
    ext x
    rw [Set.mem_sUnion]
    refine ⟨fun hx ↦ ?_, fun ⟨t, ⟨ht1, ht2⟩, hx⟩ ↦ ht2 <| subset_closure hx⟩
    obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := hV.nhds_basis_closure x |>.mem_iff.1 <| hU.mem_nhds hx
    exact ⟨v, ⟨hv2, hv3⟩, hv1⟩
  -- For any continuous `f` such that `f '' K ⊆ U`, because `K` is compact, `f '' K` is compact.
  -- But we just proved that `U = ⋃_{v ∈ V, closure v ⊆ U} v`, and each `v ∈ V` is open,
  -- so there exists `J` a finite set of `v ∈ V` such that `closure v ⊆ U` and
  -- `f '' K ⊆ ⋃ v ∈ J, v`. We thus have `f '' K ⊆ ⋃ v ∈ J, closure v`. This is equivalent to
  -- having `I` a finite subset of `W` such that `f '' K ⊆ ⋃ v ∈ I, v`.
  have (f : C(X, Y)) (hf : K.MapsTo f U) : ∃ I, I.Finite ∧ I ⊆ W ∧ K.MapsTo f (⋃₀ I) := by
    simp_rw [Set.mapsTo_iff_image_subset] at hf ⊢
    rw [U_eq_sUnion_W₁, Set.sUnion_eq_biUnion] at hf
    have : ∀ i ∈ {v | v ∈ V ∧ closure v ⊆ U}, IsOpen i :=
      fun x ⟨hx, _⟩ ↦ hV.isOpen hx
    obtain ⟨b, hb1, hb2, hb3⟩ := (hK.image f.continuous).elim_finite_subcover_image this hf
    refine ⟨closure '' b, hb2.image _, ?_, ?_⟩
    · rintro - ⟨v, hv, rfl⟩
      exact ⟨v, (hb1 hv).1, (hb1 hv).2, rfl⟩
    rw [← Set.sUnion_eq_biUnion] at hb3
    exact hb3.trans <| Set.sUnion_mono_subsets fun _ ↦ subset_closure
  -- Therefore, we obtain that
  -- `M(K, U) = ⋃_{I ⊆ W, I finite}, M(K, ⋃ v ∈ I, v)`.
  have : {f : C(X, Y) | K.MapsTo f U} =
      ⋃₀ {v | ∃ I, I.Finite ∧ I ⊆ W ∧ v = {f : C(X, Y) | K.MapsTo f (⋃₀ I)}} := by
    ext f
    rw [Set.mem_sUnion]
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨I, hI1, hI2, hI3⟩ := this f h
      exact ⟨{f : C(X, Y) | K.MapsTo f (⋃₀ I)}, ⟨I, hI1, hI2, rfl⟩, hI3⟩
    · rintro ⟨-, ⟨I, hI1, hI2, rfl⟩, h⟩
      simp only [Set.mapsTo_iff_image_subset] at h ⊢
      rw [U_eq_sUnion_W]
      exact h.trans <| Set.sUnion_subset_sUnion hI2
  simp only
  rw [this]
  -- In particular, because `W` is countable, si this is a countable union.
  -- To show measurability it is therefore enough to show the measurability of each term.
  apply MeasurableSet.sUnion
  · let f : Set (Set Y) → Set C(X, Y) := fun I ↦ {f : C(X, Y) | Set.MapsTo (⇑f) K (⋃₀ I)}
    refine ((Set.countable_setOf_finite_subset cW).image f).mono ?_
    rintro - ⟨I, hI1, hI2, rfl⟩
    exact ⟨I, ⟨hI1, hI2⟩, rfl⟩
  -- Consider now `I` a finite subset of `W`.
  rintro - ⟨I, hI1, hI2, rfl⟩
  -- First, `⋃ v ∈ I, v` is closed as a finite union of closed sets.
  have hI : IsClosed (⋃₀ I) := by
    refine isClosed_sUnion_of_finite hI1 fun x hx ↦ ?_
    obtain ⟨u, -, -, rfl⟩ := hI2 hx
    exact isClosed_closure
  -- Consider `Q` a countable dense subset of `K`, which exists by second-countability assumption.
  obtain ⟨Q, cQ, dQ⟩ := TopologicalSpace.exists_countable_dense K
  have Q_sub_K : Subtype.val '' Q ⊆ K := Subtype.coe_image_subset K Q
  -- Because `f` is continuous and `⋃ v ∈ I, v` is closed and `Q` is dense in `K`, having
  -- `f '' K ⊆ ⋃ v ∈ I, v` is the same as `f '' Q ⊆ ⋃ v ∈ I, v`.
  have : {f : C(X, Y) | K.MapsTo f (⋃₀ I)} =
      {f : C(X, Y) | (Subtype.val '' Q).MapsTo f (⋃₀ I)} := by
    ext f
    refine ⟨fun h x hx ↦ h (Q_sub_K hx), fun h x hx ↦ ?_⟩
    obtain ⟨u, hu1, hu2⟩ := mem_closure_iff_seq_limit.1 <| Subtype.dense_iff.1 dQ hx
    exact hI.mem_of_tendsto ((f.continuous.tendsto x).comp hu2)
      (Filter.Eventually.of_forall fun n ↦ h (hu1 n))
  -- We can write `M(Q, ⋃ v ∈ I, v) = ⋂ q ∈ Q, (fun f ↦ f q) ⁻¹' (⋃ v ∈ I, v)`.
  have : {f : C(X, Y) | K.MapsTo f (⋃₀ I)} =
      ⋂ q ∈ Subtype.val '' Q, (fun f ↦ f q) ⁻¹' (⋃₀ I) := by
    rw [this]
    ext f
    rw [Set.mem_iInter₂]
    exact ⟨fun h x hx ↦ h hx, fun h x hx ↦ h x hx⟩
  rw [this]
  -- This is a countable intersection, so it suffices to prove that each term is measurable.
  -- Because `⋃ v ∈ I, v` is closed, it is measurable, so it suffices to prove that
  -- for any `q ∈ Q`, `fun f ↦ f q` is measurable for the product σ-algebra.
  -- The latter is the coarsest σ-algebra which makes the maps `fun f ↦ f x` measurable,
  -- so we are done.
  refine MeasurableSet.biInter (cQ.image _)
    fun q hq ↦ MeasurableSet.preimage hI.measurableSet (Measurable.le (le_iSup _ q) ?_)
  rw [BorelSpace.measurable_eq (α := Y)]
  exact comap_measurable _

lemma ContinuousMap.measurableSpace_eq_iSup_comap_eval
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y] :
    instMeasurableSpaceContinuousMap
      = ⨆ a : X, (inferInstance : MeasurableSpace Y).comap fun b ↦ b a := by
  simp_rw [BorelSpace.measurable_eq, borel_eq_iSup_comap_eval]

set_option backward.isDefEq.respectTransparency false in
lemma ContinuousMap.measurable_iff_eval {α : Type*} [MeasurableSpace α]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (g : α → C(X, Y)) :
    Measurable g ↔ ∀ (x : X), Measurable fun (a : α) ↦ g a x := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
  simp_rw [measurable_iff_comap_le,
    MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp, Function.comp_def]

end ContinuousMap.MeasurableSpace

def MeasurableEquiv.continuousMap : {f : ℝ≥0 → ℝ // Continuous f} ≃ᵐ C(ℝ≥0, ℝ) where
  toFun := fun f ↦ ContinuousMap.mk f.1 f.2
  invFun := fun f ↦ ⟨f, f.continuous⟩
  left_inv f := rfl
  right_inv f := rfl
  measurable_toFun := by
    simp only [Equiv.coe_fn_mk]
    rw [ContinuousMap.measurable_iff_eval]
    intro x
    simp only [ContinuousMap.coe_mk]
    revert x
    rw [← measurable_pi_iff]
    exact measurable_subtype_coe
  measurable_invFun := by
    simp only [Equiv.coe_fn_symm_mk]
    refine Measurable.subtype_mk ?_
    rw [measurable_pi_iff]
    exact fun _ ↦ Continuous.measurable (by fun_prop)

end Measure

end ProbabilityTheory
