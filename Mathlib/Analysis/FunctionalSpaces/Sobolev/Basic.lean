/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Michael Rothgang, Floris van Doorn
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Attempts for Sobolev Space definitions
-/

@[expose] public noncomputable section

open Function Seminorm SeminormFamily Set TopologicalSpace TestFunction MeasureTheory Distribution
  Filter Measure
open scoped BoundedContinuousFunction ENNReal Topology Distributions NNReal

variable {𝕜 𝕂 : Type*} [NontriviallyNormedField 𝕜] --[RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [MeasurableSpace E'] [BorelSpace E']
  /- probably `Ω` should have type `Set E` and moved after the argument `f` in declarations -/
  {Ω : Opens E} {Ω' : Opens E'}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [SMulCommClass ℝ 𝕜 F']
    -- [NormedSpace 𝕂 F]
  {f f' : E → F} {n : ℕ∞} {k : ℕ∞} {p : ℝ≥0∞} {μ ν : Measure E}
variable {T T' : 𝓓'(Ω, F)} {g g' : E → E →L[ℝ] F} {c : ℝ} {g g' : E → E →L[ℝ] F}
section move

omit [MeasurableSpace E] in
@[simp]
lemma TestFunction.eq_zero (f : 𝓓^{n}(Ω, F)) {x : E} (hx : x ∉ Ω) : f x = 0 :=
  image_eq_zero_of_notMem_tsupport <| mt (f.tsupport_subset ·) hx

lemma Finset.fin_univ_image {n : ℕ} :
    (Finset.univ (α := Fin n)).image Fin.val = Finset.range n := by
  ext
  simp [Fin.exists_iff]

@[simp]
lemma Finset.sup_fin_univ {α : Type*} [SemilatticeSup α] [OrderBot α] {n : ℕ} (f : ℕ → α) :
    (Finset.univ (α := Fin n)).sup (fun n ↦ f n) = (Finset.range n).sup f := by
  rw [← fin_univ_image, sup_image, Function.comp_def]

lemma MeasureTheory.aeEq_iff {α β : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → β} :
    f =ᵐ[μ] g ↔ μ {x | f x ≠ g x} = 0 := by
  rfl

-- we could probably do without this
lemma ae_of_forall₂ {α : Type*} [MeasurableSpace α] {p : α → Prop} {μ : Measure α} {s : Set α}
    (h : ∀ x ∈ s, p x) (h2 : μ sᶜ = 0) : ∀ᵐ x ∂μ, p x :=
  Eventually.mono h2 h

lemma Set.EqOn.aeEq {α β : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f g : α → β} (h : s.EqOn f g) (h2 : μ sᶜ = 0) : f =ᵐ[μ] g :=
  Filter.eventuallyEq_of_mem h2 h

lemma Set.EqOn.aeEq_restrict {α β : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f g : α → β} (h : s.EqOn f g) (hs : MeasurableSet s) : f =ᵐ[μ.restrict s] g :=
  ae_restrict_of_forall_mem hs h

instance [hμ : IsLocallyFiniteMeasure μ] : IsLocallyFiniteMeasure (μ.restrict Ω) where
  finiteAtNhds x := by
    obtain ⟨s, hs, hmus⟩ := hμ.finiteAtNhds x
    exact ⟨s, hs, lt_of_le_of_lt (Measure.restrict_apply_le Ω s) hmus⟩

/- to do: the Norm instance on PiLp also induces a non-defeq ENorm on PiLp,
we should disable the Norm → ENorm instance if we want to make this an instance. -/
-- /-- to remove, unused -/
-- @[reducible, simps -isSimp]
-- def PiLp.instENorm (p : ℝ≥0∞) {ι : Type*} [Fintype ι] (β : ι → Type*) [(i : ι) → ENorm (β i)] :
--     ENorm (PiLp p β) where
--   enorm f :=
--     if p = 0 then {i | ‖f i‖ₑ ≠ 0}.encard
--     else if p = ∞ then ⨆ i, ‖f i‖ₑ else (∑ i, ‖f i‖ₑ ^ p.toReal) ^ p.toReal⁻¹

attribute [fun_prop] TestFunction.contDiff
attribute [gcongr] ae_mono

-- lemma for fun_prop
@[fun_prop]
lemma TestFunction.contDiff_one {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : 𝓓(Ω, F)) : ContDiff ℝ 1 φ :=
  φ.contDiff.of_le (mod_cast le_top)

-- todo: protect HasFTaylorSeriesUpTo.fderiv

variable {p : E → FormalMultilinearSeries ℝ E F} in
omit [MeasurableSpace E] [BorelSpace E] in
lemma HasFTaylorSeriesUpTo.fderiv_eq {n : WithTop ℕ∞} (hf : HasFTaylorSeriesUpTo n f p)
    {m : ℕ} (h : m < n) (x : E) :
    _root_.fderiv ℝ (p · m) x = (p x m.succ).curryLeft :=
  hf.fderiv m h x |>.fderiv

variable {g : E → FormalMultilinearSeries ℝ E F} in
omit [MeasurableSpace E] [BorelSpace E] in
lemma HasFTaylorSeriesUpTo.tsupport_mono {m n : ℕ} (h : m ≤ n) (h2 : n ≤ k)
    (hf : HasFTaylorSeriesUpTo k f g) :
    tsupport (g · n) ⊆ tsupport (g · m) := by
  induction h with
  | refl => rfl
  | @step l h ih =>
    have hl : l < k := lt_of_lt_of_le (mod_cast lt_add_one l) h2
    refine subset_trans ?_ (ih hl.le)
    refine Eq.trans_subset ?_ (tsupport_fderiv_subset ℝ)
    rw [funext <| hf.fderiv_eq (mod_cast hl)]
    refine tsupport_comp_eq (g := ContinuousMultilinearMap.curryLeft) (fun {x} ↦ ?_) _ |>.symm
    exact (continuousMultilinearCurryLeftEquiv _ _ _).map_eq_zero_iff (x := x)


variable {g : E → FormalMultilinearSeries ℝ E F} in
omit [MeasurableSpace E] [BorelSpace E] in
lemma HasFTaylorSeriesUpTo.tsupport_subset {n : ℕ} (h : n ≤ k)
    (hf : HasFTaylorSeriesUpTo k f g) :
    tsupport (g · n) ⊆ tsupport f := by
  refine (hf.tsupport_mono (zero_le _) h).trans_eq ?_
  rw [← funext hf.zero_eq]
  refine tsupport_comp_eq (g := ContinuousMultilinearMap.curry0) (fun {x} ↦ ?_) _ |>.symm
  exact (continuousMultilinearCurryFin0 _ _ _).map_eq_zero_iff (x := x)


-- @[to_additive]
-- lemma ContinuousOn.exists_bound_of_mulTSupport_inter_subset
--     {α E : Type*} [SeminormedGroup E] [TopologicalSpace α] {s : Set α}
--     {f : α → E} (hf : ContinuousOn f s) (h2f : IsCompact (closure (mulTSupport f ∩ s)))
--     (h3f : closure (mulTSupport f ∩ s) ⊆ s) :
--     ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C := by
--   obtain ⟨C, hC⟩ := h2f.exists_bound_of_continuousOn' (hf.mono h3f)
--   refine ⟨max C 0, fun x hx ↦ ?_⟩
--   by_cases h2x : x ∈ mulTSupport f
--   · exact (hC x (subset_closure ⟨h2x, hx⟩)).trans <| le_max_left _ _
--   · simp [image_eq_one_of_notMem_mulTSupport h2x]

-- broken
-- /- is `hs` needed? (I think so). is `SecondCountableTopologyEither` needed? (I think not) -/
-- lemma ContinuousOn.MemLp_restrict_of_tsupport_subset {E X : Type*} {p : ℝ≥0∞}
--     [NormedAddCommGroup E]
--     [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
--     {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
--     {f : X → E} {s : Set X} (hs : MeasurableSet s)
--     (hf : ContinuousOn f s) (h2f : IsCompact (closure (tsupport f ∩ s)))
--     (h3f : closure (tsupport f ∩ s) ⊆ s) :
--     MemLp f p (μ.restrict s) := by
--   obtain ⟨C, hC⟩ := ContinuousOn.exists_bound_of_tsupport_inter_subset hf h2f h3f
--   have : MemLp f ∞ (μ.restrict s) := by
--     refine memLp_top_of_bound ?_ C (ae_restrict_of_forall_mem hs hC)
--     borelize E
--     rw [aestronglyMeasurable_iff_aemeasurable_separable]
--     refine ⟨hf.aemeasurable hs, f '' s, ?_, ?_⟩
--     · exact (hs.image_of_continuousOn hf).isSeparable
--     · exact mem_of_superset (self_mem_ae_restrict h's) (subset_preimage_image _ _)
--     exact hf.aestronglyMeasurable_of_isCompact sorry sorry
--   exact this.mono_exponent_of_measure_support_ne_top
--     (fun x ↦ image_eq_zero_of_notMem_tsupport) h2f.measure_ne_top le_top

lemma MeasureTheory.LocallyIntegrableOn.congr {X ε : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [TopologicalSpace ε] [ContinuousENorm ε] {f f' : X → ε} {s : Set X} {μ : Measure X}
    (h : f =ᵐ[μ.restrict s] f') (hf : LocallyIntegrableOn f s μ) : LocallyIntegrableOn f' s μ := by
  intro x hx
  obtain ⟨t, hxt, hft⟩ := hf x hx
  refine ⟨s ∩ t, inter_mem self_mem_nhdsWithin hxt, ?_⟩
  refine (hft.mono_set inter_subset_right).congr ?_
  refine h.filter_mono ?_
  gcongr
  exact inter_subset_left

lemma MeasureTheory.locallyIntegrableOn_congr {X ε : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [TopologicalSpace ε] [ContinuousENorm ε] [PseudoMetrizableSpace ε]
    {f f' : X → ε} {s : Set X} {μ : Measure X}
    (h : f =ᵐ[μ.restrict s] f') : LocallyIntegrableOn f s μ ↔ LocallyIntegrableOn f' s μ :=
  ⟨(·.congr h), (·.congr h.symm)⟩

@[simp]
lemma ENNReal.rpow_rpow_inv_iff {x : ℝ≥0∞} {y : ℝ} : (x ^ y) ^ y⁻¹ = x ↔ y ≠ 0 ∨ x = 1 := by
  constructor
  · rw [or_iff_not_imp_left, ne_eq, not_not]
    rintro h rfl
    simpa using h.symm
  · rintro (h|rfl)
    · apply ENNReal.rpow_rpow_inv h
    simp

@[simp]
theorem ContinuousMultilinearMap.fin0_apply_enorm {𝕜 G G' : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
    (f : ContinuousMultilinearMap 𝕜 (fun _ => G) G') {x : Fin 0 → G} :
    ‖f x‖ₑ = ‖f‖ₑ := by
  simp_rw [← ofReal_norm, fin0_apply_norm]

lemma Subsingleton.count_eq_dirac {ι : Type*} [MeasurableSpace ι] [Subsingleton ι] (i : ι) :
    count = dirac i := by
  calc count
      = count.restrict univ := by simp
    _ = count.restrict {i} := by congr; ext j; simp [Subsingleton.elim j i]
    _ = dirac i := by simp

lemma Unique.count_eq_dirac {ι : Type*} [MeasurableSpace ι] [Unique ι] :
    count = dirac (default : ι) :=
  Subsingleton.count_eq_dirac _

variable {X ε : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [TopologicalSpace ε] [ContinuousENorm ε] {f : X → ε} {μ ν : Measure X} {s : Set X} in
lemma LocallyIntegableOn.mono_measure (hf : LocallyIntegrableOn f s μ) (h : ν ≤ μ) :
    LocallyIntegrableOn f s ν := by
  sorry

section count
variable {ι α : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [TopologicalSpace α] [ContinuousENorm α] {f : ι → α} {p : ℝ≥0∞} {i : ι}

@[simp]
lemma eLpNorm_dirac (hp : p ≠ 0) :
    eLpNorm f p (dirac i) = ‖f i‖ₑ := by
  simp_rw [eLpNorm, if_neg hp]
  split_ifs
  · simp [eLpNormEssSup, essSup, limsup, limsSup, Ici_def]
  · simp [eLpNorm', ENNReal.toReal_eq_zero_iff, *]

lemma enorm_le_eLpNorm_count (f : ι → α) (i : ι) (hp : p ≠ 0) :
    ‖f i‖ₑ ≤ eLpNorm f p count := by
  calc
    ‖f i‖ₑ = eLpNorm f p (dirac i) := by rw [eLpNorm_dirac hp]
      _ = eLpNorm f p (count.restrict {i}) := by simp
      _ ≤ eLpNorm f p count := eLpNorm_restrict_le ..

lemma eLpNorm_count_lt_top_of_lt [Finite ι] (h : ∀ i, ‖f i‖ₑ < ∞) :
    eLpNorm f p .count < ∞ := by
  letI _ := Fintype.ofFinite ι
  simp_rw [eLpNorm]
  split_ifs with h2 h3
  · exact ENNReal.zero_lt_top
  · refine (essSup_le_of_ae_le (Finset.univ.sup (‖f ·‖ₑ)) ?_).trans_lt ?_
    · filter_upwards with x
      exact Finset.le_sup (f := (‖f ·‖ₑ)) (Finset.mem_univ _)
    · simp_rw [Finset.sup_lt_iff ENNReal.zero_lt_top, h, implies_true]
  · refine (ENNReal.rpow_lt_top_iff_of_pos ?_).mpr ?_
    · rw [one_div, inv_pos]
      exact ENNReal.toReal_pos h2 h3
    · simp_rw [lintegral_count, tsum_eq_sum (s := Finset.univ) (by simp), ENNReal.sum_lt_top,
        Finset.mem_univ, forall_const, ENNReal.rpow_lt_top_iff_of_pos (ENNReal.toReal_pos h2 h3), h,
        implies_true]

lemma eLpNorm_count_lt_top [Finite ι] (hp : p ≠ 0) :
    eLpNorm f p .count < ∞ ↔ ∀ i, ‖f i‖ₑ < ∞ :=
  ⟨fun h i ↦ (enorm_le_eLpNorm_count f i hp).trans_lt h, eLpNorm_count_lt_top_of_lt⟩

end count

end move

namespace Distribution

structure IsRepresentedBy (T : 𝓓'(Ω, F)) (f : E → F) (μ : Measure E) : Prop where
  locallyIntegrableOn : LocallyIntegrableOn f Ω μ
  eq_ofFun : T = ofFun Ω f μ

lemma IsRepresentedBy.congr {f f' : E → F} (h : f =ᵐ[μ.restrict Ω] f')
    (hf : IsRepresentedBy T f μ) : IsRepresentedBy T f' μ := by
  rcases hf with ⟨h1, h2⟩
  refine ⟨fun x hx ↦ ?_, by rwa [h2, ofFun_ae_congr]⟩
  obtain ⟨s, hs, hsf⟩ := h1 x hx
  refine ⟨s ∩ Ω, Filter.inter_mem hs self_mem_nhdsWithin, ?_⟩
  apply (hsf.mono_set inter_subset_left).congr_fun_ae
  have : ae (μ.restrict (s ∩ Ω)) ≤ ae (μ.restrict Ω) := by
    rw [Measure.ae_le_iff_absolutelyContinuous]
    exact (Measure.restrict_mono inter_subset_right (by rfl)).absolutelyContinuous
  exact h.filter_mono this

lemma isRepresentedBy_congr (hf : f =ᵐ[μ.restrict Ω] f') :
    IsRepresentedBy T f μ ↔ IsRepresentedBy T f' μ :=
  ⟨.congr hf, .congr hf.symm⟩

lemma isRepresentedBy_zero : IsRepresentedBy (0 : 𝓓'(Ω, F)) (0 : E → F) μ where
  locallyIntegrableOn := locallyIntegrable_zero.locallyIntegrableOn _
  eq_ofFun := by simp

namespace IsRepresentedBy

lemma unique_left (h : IsRepresentedBy T f μ) (h' : IsRepresentedBy T' f μ) : T = T' :=
  h.eq_ofFun.trans h'.eq_ofFun.symm

lemma unique_right (h : IsRepresentedBy T f μ) (h' : IsRepresentedBy T f' μ) :
    f =ᵐ[μ.restrict Ω] f' :=
  ofFun_inj <| h.eq_ofFun.symm.trans h'.eq_ofFun

lemma add (hT : IsRepresentedBy T f μ) (hT' : IsRepresentedBy T' f' μ) :
    IsRepresentedBy (T + T') (f + f') μ where
  locallyIntegrableOn := hT.locallyIntegrableOn.add hT'.locallyIntegrableOn
  eq_ofFun := by
    simp [hT.eq_ofFun, hT'.eq_ofFun, ofFun_add hT.locallyIntegrableOn hT'.locallyIntegrableOn]

lemma neg (hT : IsRepresentedBy T f μ) : IsRepresentedBy (-T) (-f) μ where
  locallyIntegrableOn := hT.locallyIntegrableOn.neg
  eq_ofFun := by simp [hT.eq_ofFun, ofFun_neg]

@[simp]
lemma _root_.isRepresentedBy_neg : IsRepresentedBy (-T) (-f) μ ↔ IsRepresentedBy T f μ :=
  ⟨fun h ↦ by simpa using h.neg, (·.neg)⟩

lemma sub (hT : IsRepresentedBy T f μ) (hT' : IsRepresentedBy T' f' μ) :
    IsRepresentedBy (T - T') (f - f') μ := by
  rw [sub_eq_add_neg T T', sub_eq_add_neg]
  exact hT.add hT'.neg

lemma smul (hT : IsRepresentedBy T f μ) : IsRepresentedBy (c • T) (c • f) μ where
  locallyIntegrableOn := hT.locallyIntegrableOn.smul c
  eq_ofFun := by simp [hT.eq_ofFun]

end IsRepresentedBy

end Distribution
open Distribution

section FinDim
variable [FiniteDimensional ℝ E]

/- maybe inline this definition when used -/
variable (Ω) in
/-- The weak or distributional derivative of a function:
this is 0 if the function is not locally integrable -/
def weakDeriv (f : E → F) (μ : Measure E) : 𝓓'(Ω, E →L[ℝ] F) :=
  fderivCLM (ofFun Ω f μ)

lemma weakDeriv_congr (h : f =ᵐ[μ.restrict Ω] f') : weakDeriv Ω f μ = weakDeriv Ω f' μ := by
  simp_rw [weakDeriv, ofFun_ae_congr h]

-- useful on its own?
lemma weakDeriv_of_not_locallyIntegrableOn (hf : ¬LocallyIntegrableOn f Ω μ) :
    weakDeriv Ω f μ = 0 := by
  simp [weakDeriv, ofFun_of_not_locallyIntegrable hf]

-- XXX: where should the minus sign go?
lemma weakDeriv_apply {f : E → F} (hf : LocallyIntegrableOn f Ω μ) (φ : 𝓓(Ω, ℝ)) (x : E) :
    weakDeriv Ω f μ φ x = ∫ (y : E), -(fderiv ℝ φ y) x • f y ∂μ := by
  simp only [weakDeriv, Distribution.fderivCLM]
  -- XXX: why do I need the dsimp step?
  dsimp
  simp [ofFun_apply hf, TestFunction.lineDerivCLM, TestFunction.fderivCLM]
  congr

@[simp]
lemma weakDeriv_add (hf : LocallyIntegrableOn f Ω μ) (hf' : LocallyIntegrableOn f' Ω μ) :
    weakDeriv Ω (f + f') μ = weakDeriv Ω f μ + weakDeriv Ω f' μ := by
  ext φ
  simp [weakDeriv, ofFun_add hf hf']

@[simp]
lemma weakDeriv_neg : weakDeriv Ω (-f) μ = -weakDeriv Ω f μ := by
  ext φ
  by_cases hf : LocallyIntegrableOn f Ω μ; swap
  · have hf' : ¬LocallyIntegrableOn (-f) Ω μ := by rwa [locallyIntegrableOn_neg_iff]
    simp [weakDeriv, *, ofFun_of_not_locallyIntegrable]
  simp [weakDeriv, ofFun_neg]

@[simp]
lemma weakDeriv_sub (hf : LocallyIntegrableOn f Ω μ) (hf' : LocallyIntegrableOn f' Ω μ) :
    weakDeriv Ω (f - f') μ = weakDeriv Ω f μ - weakDeriv Ω f' μ := by
  simp [sub_eq_add_neg, weakDeriv_add hf hf'.neg]

@[simp]
lemma weakDeriv_smul (c : ℝ) : weakDeriv Ω (c • f) μ = c • weakDeriv Ω f μ := by
  ext φ
  simp [weakDeriv]

lemma weakDeriv_zero : weakDeriv Ω (0 : E → F) μ = 0 := by simp [weakDeriv]

lemma weakDeriv_const [μ.IsAddHaarMeasure] [CompleteSpace F] (a : F) :
    weakDeriv Ω (fun _ : E ↦ a) μ = 0 := by
  by_cases hf : LocallyIntegrableOn (fun _ : E ↦ a) Ω μ; swap
  · exact weakDeriv_of_not_locallyIntegrableOn hf
  ext φ x
  simp_rw [weakDeriv_apply hf, UniformConvergenceCLM.coe_zero, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, neg_smul, integral_neg]
  rw [← integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (hg := differentiable_const _)]
  · simp
  · apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact (φ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) x).smul_right
  · apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact φ.hasCompactSupport.smul_right
  · apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact φ.hasCompactSupport.smul_right
  · exact φ.contDiff.differentiable (mod_cast le_top)

-- /-- `g` represents distribution `f` and is in `L^p`. -/
-- structure Distribution.MemLpWith (f : 𝓓'(Ω, F)) (g : E → F) (p : ℝ≥0∞) (μ : Measure E) :
--     Prop where
--   isRegular : IsRepresentedBy f g μ
--   memLp : MeasureTheory.MemLp g p μ

-- variable (Ω) in

-- /-- `f` is in `W^{1, p}` and has weak derivative represented by `g`. -/
-- structure MemSobolev1With (f : E → F) (g : E → E →L[ℝ] F) (p : ℝ≥0∞) (μ : Measure E) : Prop where
--   memLp : MemLp f p (μ.restrict Ω)
--   memLp_weakDeriv : (weakDeriv Ω f μ).MemLpWith g p μ

variable (Ω) in
/-- `f` has weak derivative represented by `g`. -/
@[mk_iff]
structure HasWeakDeriv (f : E → F) (g : E → E →L[ℝ] F) (μ : Measure E) : Prop where
  locallyIntegrableOn : LocallyIntegrableOn f Ω μ
  isRepresentedBy : IsRepresentedBy (weakDeriv Ω f μ) g μ

lemma hasWeakDeriv_congr (hf : f =ᵐ[μ.restrict Ω] f') (hg : g =ᵐ[μ.restrict Ω] g') :
    HasWeakDeriv Ω f g μ ↔ HasWeakDeriv Ω f' g' μ := by
  simp_rw [hasWeakDeriv_iff, weakDeriv_congr hf, locallyIntegrableOn_congr hf,
    isRepresentedBy_congr hg]

alias ⟨HasWeakDeriv.congr, _⟩ := hasWeakDeriv_congr

@[simp]
lemma hasWeakderiv_const [μ.IsAddHaarMeasure] [CompleteSpace F] {a : F} :
    HasWeakDeriv Ω (fun _ : E ↦ a) 0 μ := by
  simp_rw [hasWeakDeriv_iff, weakDeriv_const, isRepresentedBy_zero, and_true,
    locallyIntegrableOn_const]

@[simp]
lemma hasWeakDeriv_zero : HasWeakDeriv Ω (0 : E → F) 0 μ := by
  simp_rw [hasWeakDeriv_iff, weakDeriv_zero, isRepresentedBy_zero, and_true]
  apply locallyIntegrableOn_zero

namespace HasWeakDeriv

lemma locallyIntegrableOn_right (h : HasWeakDeriv Ω f g μ) : LocallyIntegrableOn g Ω μ :=
  h.isRepresentedBy.locallyIntegrableOn

nonrec lemma unique_right (h : HasWeakDeriv Ω f g μ) (h' : HasWeakDeriv Ω f' g' μ)
    (hf : f =ᵐ[μ.restrict Ω] f') : g =ᵐ[μ.restrict Ω] g' := by
  rw [hasWeakDeriv_iff, weakDeriv_congr hf] at h
  exact h.2.unique_right h'.2

lemma mono_measure (hf : HasWeakDeriv Ω f g μ) (hν : ν.restrict Ω ≤ μ.restrict Ω) :
    HasWeakDeriv Ω f g ν :=
  sorry

lemma add (hf : HasWeakDeriv Ω f g μ) (hf' : HasWeakDeriv Ω f' g' μ)
    (hfint : LocallyIntegrableOn f Ω μ) (hfint' : LocallyIntegrableOn f' Ω μ) :
    HasWeakDeriv Ω (f + f') (g + g') μ := by
  simp_rw [hasWeakDeriv_iff, weakDeriv_add hfint hfint', hf.1.add hf'.1, hf.2.add hf'.2, and_true]

lemma neg (hf : HasWeakDeriv Ω f g μ) : HasWeakDeriv Ω (-f) (-g) μ := by
  simp [hasWeakDeriv_iff, hf.1.neg, hf.2]

@[simp]
lemma _root_.hasWeakDeriv_neg : HasWeakDeriv Ω (-f) (-g) μ ↔ HasWeakDeriv Ω f g μ :=
  ⟨fun h ↦ by simpa using h.neg, (·.neg)⟩

lemma sub (hf : HasWeakDeriv Ω f g μ) (hg : HasWeakDeriv Ω f' g' μ)
    (hfint : LocallyIntegrableOn f Ω μ) (hfint' : LocallyIntegrableOn f' Ω μ) :
    HasWeakDeriv Ω (f - f') (g - g') μ := by
  simpa [sub_eq_add_neg] using hf.add hg.neg hfint hfint'.neg

lemma smul (hf : HasWeakDeriv Ω f g μ) : HasWeakDeriv Ω (c • f) (c • g) μ := by
  simp [hasWeakDeriv_iff, weakDeriv_smul, hf.2.smul, hf.1]

end HasWeakDeriv

lemma HasFDerivAt.hasWeakDeriv [μ.IsAddHaarMeasure] (hf : ∀ x ∈ Ω, HasFDerivAt f (g x) x)
    (hg : ContinuousOn g Ω) : HasWeakDeriv Ω f g μ := by
  have h0f : LocallyIntegrableOn f Ω μ := by
    have : DifferentiableOn ℝ f Ω := fun x hx ↦ (hf x hx).differentiableAt.differentiableWithinAt
    exact this.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have h0g : LocallyIntegrableOn g Ω μ :=
    hg.locallyIntegrableOn Ω.isOpen.measurableSet
  exact
  { locallyIntegrableOn := h0f
    isRepresentedBy.locallyIntegrableOn := h0g
    isRepresentedBy.eq_ofFun := by
      ext φ x
      have h y : φ y • fderiv ℝ f y x = φ y • g y x := by
        by_cases hy : y ∈ Ω
        · rw [(hf y hy).fderiv]
        · simp [hy]
      simp_rw [weakDeriv_apply h0f, ofFun_apply h0g, neg_smul, integral_neg,
        ContinuousLinearMap.integral_apply (φ.integrable_smul h0g),
        ContinuousLinearMap.coe_smul', Pi.smul_apply, ← h]
      rw [integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable]
      · exact (TestFunction.lineDerivCLM x φ).integrable_smul h0f
      · simp_rw [h]
        apply φ.integrable_smul
        exact (hg.clm_apply continuousOn_const).locallyIntegrableOn Ω.isOpen.measurableSet
      · exact φ.integrable_smul h0f
      · exact φ.differentiable
      · sorry
        -- This sorry is provable after merging with master (due to #35870).
    }

variable (Ω) in
open Classical in
/-- A choice of a weak derivative of `f` as a function, if it exists. 0 otherwise. -/
def wderiv (f : E → F) (μ : Measure E) : E → E →L[ℝ] F :=
  if h : ∃ g, HasWeakDeriv Ω f g μ then h.choose else 0

protected lemma HasWeakDeriv.wderiv (h : HasWeakDeriv Ω f g μ) :
    HasWeakDeriv Ω f (wderiv Ω f μ) μ := by
  rw [_root_.wderiv, dif_pos ⟨g, h⟩]
  generalize_proofs h2
  exact h2.choose_spec

lemma HasWeakDeriv.aeEq_wderiv (h : HasWeakDeriv Ω f g μ) (h2 : f =ᵐ[μ.restrict Ω] f') :
    g =ᵐ[μ.restrict Ω] wderiv Ω f' μ :=
  h.unique_right (h.congr h2 .rfl).wderiv h2

lemma wderiv_congr (h : f =ᵐ[μ.restrict Ω] f') : wderiv Ω f μ =ᵐ[μ.restrict Ω] wderiv Ω f' μ := by
  by_cases h2 : ∃ g, HasWeakDeriv Ω f g μ
  · obtain ⟨g, hg⟩ := h2
    exact hg.wderiv.aeEq_wderiv h
  · simp_rw [wderiv, dif_neg h2]
    rw [dif_neg]
    exact mt (fun ⟨g, hg⟩ ↦ ⟨g, hg.congr h.symm .rfl⟩) h2

variable (Ω) in
/-- A choice of a iterated weak derivative of `f`, if it exists. 0 otherwise.
  This is bundled in a `FormalMultilinearSeries`. -/
def iteratedWDeriv (f : E → F) (μ : Measure E) : E → FormalMultilinearSeries ℝ E F :=
  Function.swap <| Nat.rec (fun x ↦ .uncurry0 ℝ E (f x)) fun _ rec x ↦
    (wderiv Ω rec μ x).uncurryLeft

@[simp]
lemma iteratedWDeriv_zero {x : E} :
    iteratedWDeriv Ω f μ x 0 = .uncurry0 ℝ E (f x) :=
  rfl

@[simp]
lemma iteratedWDeriv_succ {x : E} {n : ℕ} :
    iteratedWDeriv Ω f μ x (n + 1) = (wderiv Ω (iteratedWDeriv Ω f μ · n) μ x).uncurryLeft :=
  rfl

variable (Ω) in
/-- `f` has "weak taylor series" g, which are all L^p
k currently can be `∞`. Do we want that? -/
structure HasWTaylorSeriesUpTo (f : E → F) (g : E → FormalMultilinearSeries ℝ E F)
    (k : ℕ∞) (p : ℝ≥0∞) (μ : Measure E) : Prop where
  zero_aeEq : (fun x ↦ (g x 0).curry0) =ᵐ[μ.restrict Ω] f
  hasWeakDeriv : ∀ m : ℕ, m < k → HasWeakDeriv Ω (g · m) (g · m.succ |>.curryLeft) μ
  memLp : ∀ m : ℕ, m ≤ k → MemLp (g · m) p (μ.restrict Ω)

namespace HasWTaylorSeriesUpTo

variable {g g' : E → FormalMultilinearSeries ℝ E F} {c : ℝ}

lemma zero_aeEq_uncurry0 (h : HasWTaylorSeriesUpTo Ω f g k p μ) :
    (g · 0) =ᵐ[μ.restrict Ω] (ContinuousMultilinearMap.uncurry0 ℝ E <| f ·) := by
  filter_upwards [h.zero_aeEq] with x hx using by simp [← hx]

lemma congr (hf : f =ᵐ[μ.restrict Ω] f')
    (hg : g =ᵐ[μ.restrict Ω] g') (k : ℕ∞) (h : HasWTaylorSeriesUpTo Ω f g k p μ) :
    HasWTaylorSeriesUpTo Ω f' g' k p μ where
  zero_aeEq := by
    filter_upwards [hf, hg, h.zero_aeEq] with x hfx hgx hx using by simp_rw [← hfx, ← hgx, ← hx]
  hasWeakDeriv m hm := by
    refine (h.hasWeakDeriv m hm).congr ?_ ?_
    all_goals { filter_upwards [hg] with x hx using by rw [hx] }
  memLp m hm := by
    refine (h.memLp m hm).ae_eq ?_
    filter_upwards [hg] with x hx using by rw [hx]

lemma _root_.hasWTaylorSeriesUpTo_congr (hf : f =ᵐ[μ.restrict Ω] f')
    (hg : g =ᵐ[μ.restrict Ω] g') (k : ℕ∞) :
    HasWTaylorSeriesUpTo Ω f g k p μ ↔ HasWTaylorSeriesUpTo Ω f' g' k p μ :=
  ⟨(·.congr hf hg), (·.congr hf.symm hg.symm)⟩

lemma unique (h : HasWTaylorSeriesUpTo Ω f g k p μ) (h' : HasWTaylorSeriesUpTo Ω f' g' k p μ)
    (hf : f =ᵐ[μ.restrict Ω] f') ⦃m : ℕ⦄ (hm : m ≤ k) : (g · m) =ᵐ[μ.restrict Ω] (g' · m) := by
  induction m with
  | zero =>
    filter_upwards [h.zero_aeEq, h'.zero_aeEq, hf] with x hgx hg'x hfx
    ext v
    simpa [Unique.eq_default v] using hgx.trans <| hfx.trans hg'x.symm
  | succ m ih =>
    have hm : m < k := lt_of_lt_of_le (mod_cast lt_add_one m) hm
    filter_upwards [(h.hasWeakDeriv m hm).unique_right (h'.hasWeakDeriv m hm) (ih hm.le)] with x hx
    exact (continuousMultilinearCurryLeftEquiv _ _ _).injective hx

lemma eLpNorm_zero (h : HasWTaylorSeriesUpTo Ω f g k p μ) :
    eLpNorm (g · 0) p (μ.restrict ↑Ω) = eLpNorm f p (μ.restrict ↑Ω) := by
  apply eLpNorm_congr_enorm_ae
  filter_upwards [h.zero_aeEq] with x hx using by simp [← hx]

lemma locallyIntegrableOn [IsLocallyFiniteMeasure (μ.restrict Ω)] [hp : Fact (1 ≤ p)]
    (hf : HasWTaylorSeriesUpTo Ω f g k p μ) {n : ℕ} (hn : n ≤ k) :
    LocallyIntegrableOn (fun x ↦ g x n) Ω μ :=
  locallyIntegrableOn_of_locallyIntegrable_restrict <| (hf.memLp n hn).locallyIntegrable hp.out

lemma mono {k' : ℕ∞} (hf : HasWTaylorSeriesUpTo Ω f g k p μ) (hk : k' ≤ k) :
    HasWTaylorSeriesUpTo Ω f g k' p μ where
  zero_aeEq := hf.zero_aeEq
  hasWeakDeriv m hm := hf.hasWeakDeriv m (lt_of_lt_of_le hm hk)
  memLp m hm := hf.memLp m (le_trans hm hk)

/- We could also prove this for `HasFTaylorSeriesUpTo`, but then we don't know anything about
`g` outside `Ω`. If we want to do this, we should define a new predicate
`HasCompactSupportIn f Ω` that states that `closure (tsupport f ∩ Ω)` is compact and a subset
of `Ω`. -/
lemma _root_.HasFTaylorSeriesUpTo.hasWTaylorSeriesUpTo [μ.IsAddHaarMeasure] (f : 𝓓^{k}(Ω, F))
    (hf : HasFTaylorSeriesUpTo k f g) :
    HasWTaylorSeriesUpTo Ω f g k p μ where
  zero_aeEq := Eventually.of_forall hf.zero_eq
  hasWeakDeriv m hm := by
    refine HasFDerivAt.hasWeakDeriv (fun x _ ↦ hf.fderiv m (mod_cast hm) x) ?_
    have := hf.cont (m + 1) (mod_cast (ENat.add_one_le_iff <| ENat.coe_ne_top m).mpr hm)
    exact ((continuousMultilinearCurryLeftEquiv _ _ _).continuous.comp this).continuousOn
  memLp m hm := by
    apply (hf.cont m (mod_cast hm)).memLp_of_hasCompactSupport
    apply f.hasCompactSupport.mono'
    exact (subset_tsupport _).trans (hf.tsupport_subset hm)

-- -- TODO: add doc-string!
-- def shrink_measure (hf : HasWTaylorSeriesUpTo Ω f g k p μ) {ν : Measure E}
--     (hν : ν.restrict Ω ≤ μ.restrict Ω) : E → FormalMultilinearSeries ℝ E F := by
--   intro x k
--   have aux := g x k
--   sorry -- define a new power series, which are the weak derivatives w.r.t. ν instead

lemma mono_measure (hf : HasWTaylorSeriesUpTo Ω f g k p μ) (hν : ν.restrict Ω ≤ μ.restrict Ω) :
    HasWTaylorSeriesUpTo Ω f g k p ν where
  zero_aeEq := hf.zero_aeEq.filter_mono (by gcongr)
  hasWeakDeriv m hm := by sorry
  memLp m hm := sorry

lemma mono_exponent [IsFiniteMeasure μ] (hf : HasWTaylorSeriesUpTo Ω f g k p μ)
    {p' : ℝ≥0∞} (hp' : p' ≤ p) : HasWTaylorSeriesUpTo Ω f g k p' μ where
  zero_aeEq := hf.zero_aeEq
  hasWeakDeriv := hf.hasWeakDeriv
  memLp m hm := (hf.memLp m hm).mono_exponent hp'

lemma add [IsLocallyFiniteMeasure (μ.restrict Ω)] [hp : Fact (1 ≤ p)]
    (hf : HasWTaylorSeriesUpTo Ω f g k p μ) (hf' : HasWTaylorSeriesUpTo Ω f' g' k p μ) :
    HasWTaylorSeriesUpTo Ω (f + f') (g + g') k p μ where
  zero_aeEq := by
    filter_upwards [hf.zero_aeEq, hf'.zero_aeEq] with x hfx hf'x
    simp [← hfx, ← hf'x]
  hasWeakDeriv m hm := (hf.hasWeakDeriv m hm).add (hf'.hasWeakDeriv m hm)
    (hf.locallyIntegrableOn hm.le) (hf'.locallyIntegrableOn hm.le)
  memLp m hm := (hf.memLp m hm).add (hf'.memLp m hm)

lemma neg (hf : HasWTaylorSeriesUpTo Ω f g k p μ) : HasWTaylorSeriesUpTo Ω (-f) (-g) k p μ where
  zero_aeEq := by
    filter_upwards [hf.zero_aeEq] with x hfx
    simp [← hfx]
  hasWeakDeriv m hm := (hf.hasWeakDeriv m hm).neg
  memLp m hm := (hf.memLp m hm).neg

@[simp]
lemma _root_.hasWTaylorSeriesUpTo_neg :
    HasWTaylorSeriesUpTo Ω (-f) (-g) k p μ ↔ HasWTaylorSeriesUpTo Ω f g k p μ :=
  ⟨fun h ↦ by simpa using h.neg, (·.neg)⟩

lemma sub [IsLocallyFiniteMeasure (μ.restrict Ω)] [hp : Fact (1 ≤ p)]
    (hf : HasWTaylorSeriesUpTo Ω f g k p μ) (hf' : HasWTaylorSeriesUpTo Ω f' g' k p μ) :
    HasWTaylorSeriesUpTo Ω (f - f') (g - g') k p μ := by
  rw [sub_eq_add_neg f f', sub_eq_add_neg g g']
  exact hf.add hf'.neg

lemma smul (hf : HasWTaylorSeriesUpTo Ω f g k p μ) :
    HasWTaylorSeriesUpTo Ω (c • f) (c • g) k p μ where
  zero_aeEq := by
    filter_upwards [hf.zero_aeEq] with x hfx
    simp [← hfx]
  hasWeakDeriv m hm := (hf.hasWeakDeriv m hm).smul
  memLp m hm := (hf.memLp m hm).const_smul c

@[simp]
lemma zero : HasWTaylorSeriesUpTo Ω 0 (0 : E → FormalMultilinearSeries ℝ E F) k p μ where
  zero_aeEq := by simp [funext Pi.zero_apply]
  hasWeakDeriv m hm := by simpa using hasWeakDeriv_zero
  memLp m hm := by simp

protected lemma iteratedWDeriv (hf : HasWTaylorSeriesUpTo Ω f g k p μ) :
    HasWTaylorSeriesUpTo Ω f (iteratedWDeriv Ω f μ) k p μ :=
  -- we don't make this a lemma, since this can be obtained from `h.unique h.iteratedWDeriv`
  have h : ∀ m : ℕ, m ≤ k → (g · m) =ᵐ[μ.restrict Ω] (iteratedWDeriv Ω f μ · m) := by
    intro m hm
    induction m with
    | zero => simp [hf.zero_aeEq_uncurry0]
    | succ n ih =>
      have : n < k := lt_of_lt_of_le (mod_cast lt_add_one n) hm
      filter_upwards [(hf.hasWeakDeriv n this).aeEq_wderiv (ih this.le)] with x hx
      simp [← hx]
  { zero_aeEq := by simp [iteratedWDeriv_zero]
    hasWeakDeriv m hm := (hf.hasWeakDeriv m hm).wderiv.congr (h m hm.le) (wderiv_congr (h m hm.le))
    memLp m hm := (hf.memLp m hm).ae_eq (h m hm) }

end HasWTaylorSeriesUpTo

variable (Ω) in
/--
A function `f` is in the Sobolev space `W^{k,p}(Ω; μ)` if it has a weak taylor series up to order
`k`.
`k` is called the *order* of the Sobolev space and `p` the *exponent*. We use this terminology in
lemma names (compare `MemSobolev.mono_order`, `MemSobolev.mono_exponent` and
`MemSobolev.mono_measure`).
-/
def MemSobolev (f : E → F) (k : ℕ∞) (p : ℝ≥0∞) (μ : Measure E) : Prop :=
  ∃ g : E → FormalMultilinearSeries ℝ E F, HasWTaylorSeriesUpTo Ω f g k p μ

namespace MemSobolev

lemma memLp (hf : MemSobolev Ω f n p μ) : MemLp f p (μ.restrict Ω) := by
  obtain ⟨g, hg⟩ := hf
  refine MemLp.ae_eq hg.zero_aeEq ?_
  exact hg.memLp 0 (zero_le _) |>.continuousLinearMap_comp
    (L := (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap)

-- check whether this is true. Do we need `n : ℕ`?
lemma memSobolev_succ : MemSobolev Ω f (n + 1) p μ ↔
    MemLp f p (μ.restrict Ω) ∧
    ∃ g : E → E →L[ℝ] F, HasWeakDeriv Ω f g μ ∧ MemSobolev Ω g n p μ := by
  sorry

lemma aestronglyMeasurable (hf : MemSobolev Ω f k p μ) :
    AEStronglyMeasurable f (μ.restrict Ω) :=
  hf.memLp.aestronglyMeasurable

@[simp]
lemma _root_.memSobolev_zero_order :
    MemSobolev Ω f 0 p μ ↔ MemLp f p (μ.restrict Ω) := by
  refine ⟨(·.memLp), fun hf ↦ ?_⟩
  use fun x ↦ Nat.rec (ContinuousMultilinearMap.uncurry0 _ _ (f x)) 0
  refine {
    zero_aeEq := by simp
    hasWeakDeriv m := by simp
    memLp m hm := ?_ }
  simp_rw [nonpos_iff_eq_zero, Nat.cast_eq_zero] at hm
  rw [hm]
  simp_rw [Nat.rec_zero]
  exact hf.continuousLinearMap_comp
    (L := (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- `MemSobolev Ω f k p μ` is monotone in `k`:
if `f ∈ W^{k,p}(Ω)` and `k' ≤ k`, then also `f ∈ W^{k',p}(Ω)`. -/
lemma mono_order {k' : ℕ∞} (hf : MemSobolev Ω f k p μ) (hk' : k' ≤ k) : MemSobolev Ω f k' p μ := by
  obtain ⟨g, hg⟩ := hf
  exact ⟨g, hg.mono hk'⟩

/-- `MemSobolev Ω f k p μ` is monotone in the measure `μ`:
if `ν ≤ μ` on `Ω`, then `MemSobolev Ω f k p μ` implies `MemSobolev Ω f k p ν`. -/
lemma mono_measure (hf : MemSobolev Ω f k p μ) (hν : ν.restrict Ω ≤ μ.restrict Ω) :
    MemSobolev Ω f k p ν := by
  obtain ⟨g, hg⟩ := hf
  exact ⟨_, hg.mono_measure hν⟩

/-- If `Ω` is bounded, `MemSobolev Ω f k p μ` is monotone in `p`:
`f ∈ W^{k,p}(Ω)` and `q ≤ p`, then also `f ∈ W^{k,q}(Ω)`. -/
lemma mono_exponent [IsFiniteMeasure μ] (hf : MemSobolev Ω f k p μ)
    {p' : ℝ≥0∞} (hp' : p' ≤ p) : MemSobolev Ω f k p' μ := by
  obtain ⟨g, hg⟩ := hf
  exact ⟨g, hg.mono_exponent hp'⟩

lemma add [IsLocallyFiniteMeasure (μ.restrict Ω)] [hp : Fact (1 ≤ p)]
    (hf : MemSobolev Ω f k p μ) (hf' : MemSobolev Ω f' k p μ) :
    MemSobolev Ω (f + f') k p μ := by
  obtain ⟨g, hg⟩ := hf
  obtain ⟨g', hg'⟩ := hf'
  exact ⟨g + g', hg.add hg'⟩

lemma neg (hf : MemSobolev Ω f k p μ) : MemSobolev Ω (-f) k p μ := by
  obtain ⟨g, hg⟩ := hf
  exact ⟨-g, hg.neg⟩

@[simp]
lemma _root_.memSobolev_neg : MemSobolev Ω (-f) k p μ ↔ MemSobolev Ω f k p μ :=
  ⟨fun h ↦ by simpa using h.neg, (·.neg)⟩

lemma sub [IsLocallyFiniteMeasure (μ.restrict Ω)] [hp : Fact (1 ≤ p)]
    (hf : MemSobolev Ω f k p μ) (hf' : MemSobolev Ω f' k p μ) : MemSobolev Ω (f - f') k p μ := by
  obtain ⟨g, hg⟩ := hf
  obtain ⟨g', hg'⟩ := hf'
  exact ⟨g - g', hg.sub hg'⟩

lemma smul (hf : MemSobolev Ω f k p μ) : MemSobolev Ω (c • f) k p μ := by
  obtain ⟨g, hg⟩ := hf
  exact ⟨c • g, hg.smul⟩

lemma _root_.TestFunction.memSobolev [μ.IsAddHaarMeasure] (f : 𝓓^{k}(Ω, F)) :
    MemSobolev Ω f k p μ := by
  obtain ⟨g, hg⟩ := f.contDiff
  exact ⟨g, hg.hasWTaylorSeriesUpTo⟩


@[simp]
lemma zero : MemSobolev Ω (0 : E → F) k p μ := ⟨0, by simp⟩

-- TODO: better test for MemSobolev: e.g. from being Lp and the weakderiv being nice
lemma const (a : F) (h : μ Ω ≠ ∞) : MemSobolev Ω (fun _ : E ↦ a) k p μ := by
  sorry

/- Add analogous lemmas for RepresentedBy and HasWeakDeriv-/
lemma _root_.memSobolev_congr (h : f =ᵐ[μ.restrict Ω] f') :
    MemSobolev Ω f k p μ ↔ MemSobolev Ω f' k p μ := by
  sorry

alias ⟨congr, _⟩ := memSobolev_congr

lemma aeEq (h : f =ᵐ[μ.restrict Ω] f') (hf : MemSobolev Ω f k p μ) :
    MemSobolev Ω f' k p μ :=
  memSobolev_congr h |>.mp hf

-- is this true?
lemma indicator {s : Set E} (hs : MeasurableSet s) (hf : MemSobolev Ω f k p μ) :
  MemSobolev Ω (s.indicator f) k p μ := sorry

-- is this true?
lemma restrict {s : Set E} (hs : MeasurableSet s) (hf : MemSobolev Ω f k p μ) :
  MemSobolev Ω f k p (μ.restrict s) := sorry

theorem aeeqFunMk (hf : MemSobolev Ω f k p μ) :
    MemSobolev Ω (AEEqFun.mk f hf.aestronglyMeasurable) k p μ :=
  hf.aeEq <| (AEEqFun.coeFn_mk f _).symm

end MemSobolev

section sobolevNorm

variable {g g' : E → FormalMultilinearSeries ℝ E F} {k : ℕ}

variable (Ω) in
open Finset in
/-- The seminorm of a `FormalMultiLinearSeries`. -/
def sobolevNormAux (g : E → FormalMultilinearSeries ℝ E F) (k : ℕ) (p : ℝ≥0∞) (μ : Measure E) :
    ℝ≥0∞ :=
  eLpNorm (fun i : Fin (k + 1) ↦ eLpNorm (g · i) p (μ.restrict Ω)) p .count
  -- ‖WithLp.toLp p fun i : Fin (k + 1) ↦ eLpNorm (g · i) p (μ.restrict Ω)‖ₑ

omit [BorelSpace E] [FiniteDimensional ℝ E] in
lemma sobolevNormAux_congr (h : ∀ (i : ℕ), i ≤ k → (g · i) =ᵐ[μ.restrict Ω] (g' · i)) :
    sobolevNormAux Ω g k p μ = sobolevNormAux Ω g' k p μ := by
  refine eLpNorm_congr_ae ?_
  filter_upwards with i
  refine eLpNorm_congr_ae (h i (mod_cast i.is_le))

lemma sobolevNormAux_lt_top (h : HasWTaylorSeriesUpTo Ω f g k p μ) :
    sobolevNormAux Ω g k p μ < ∞ := by
  refine eLpNorm_count_lt_top_of_lt (fun i ↦ ?_)
  simp_rw [enorm_eq_self, (h.memLp i (mod_cast i.is_le)).eLpNorm_lt_top]

open Classical Finset in
variable (Ω) in
/-- This definition is different than in (most) textbooks, since we use the `L^p`-norm of the total
derivative instead of the `L^p`-norm of partial derivatives. These definitions are equivalent
for finite dimensional `E` and `k < ∞` [argument todo].
Note that for `k = ∞` the space `W^{∞, p}` is not normable in general,
so we only define this for `k : ℕ`. -/
def sobolevNorm (f : E → F) (k : ℕ) (p : ℝ≥0∞) (μ : Measure E) : ℝ≥0∞ :=
  if h : MemSobolev Ω f k p μ then sobolevNormAux Ω h.choose k p μ else ∞

lemma HasWTaylorSeriesUpTo.sobolevNorm_eq (h : HasWTaylorSeriesUpTo Ω f g k p μ) :
    sobolevNorm Ω f k p μ = sobolevNormAux Ω g k p μ := by
  have : MemSobolev Ω f k p μ := ⟨g, h⟩
  rw [sobolevNorm, dif_pos this]
  exact sobolevNormAux_congr fun m hm ↦ this.choose_spec.unique h .rfl (mod_cast hm)

lemma sobolevNorm_lt_top_iff : sobolevNorm Ω f k p μ < ∞ ↔ MemSobolev Ω f k p μ := by
  refine ⟨fun h ↦ ?_, fun ⟨g, hg⟩ ↦ ?_⟩
  · simp [sobolevNorm] at h
    split_ifs at h with h'
    · exact h'
    · contradiction
  simp_rw [hg.sobolevNorm_eq, sobolevNormAux_lt_top hg]

alias ⟨_, MemSobolev.sobolevNorm_lt_top⟩ := sobolevNorm_lt_top_iff

lemma sobolevNorm_congr (h : f =ᵐ[μ.restrict Ω] f') :
    sobolevNorm Ω f k p μ = sobolevNorm Ω f' k p μ := by
  rw [sobolevNorm]
  split_ifs with h2
  · rw [sobolevNorm, dif_pos (h2.congr h)]
    refine sobolevNormAux_congr fun m hm ↦ ?_
    exact h2.choose_spec.unique (h2.congr h).choose_spec h (mod_cast hm)
  · rw [sobolevNorm, dif_neg]
    rwa [memSobolev_congr h.symm]

lemma sobolevNorm_zero : sobolevNorm Ω (0 : E → F) k p μ = 0 := by
  simp [HasWTaylorSeriesUpTo.zero.sobolevNorm_eq, sobolevNormAux]

lemma sobolevNorm_zero_measure : sobolevNorm Ω f k p 0 = 0 := by
  sorry

@[simp]
lemma sobolevNorm_neg :
    sobolevNorm Ω (-f) k p μ = sobolevNorm Ω f k p μ := by
  by_cases hf : MemSobolev Ω f k p μ
  · obtain ⟨g, hg⟩ := hf
    simp_rw [hg.sobolevNorm_eq, hg.neg.sobolevNorm_eq, sobolevNormAux,
      ← eLpNorm_neg (g · _), Pi.neg_def, FormalMultilinearSeries.neg_apply]
  · have h2f := hf
    rw [← memSobolev_neg] at h2f
    simp_rw [sobolevNorm, dif_neg hf, dif_neg h2f]

lemma sobolevNorm_add_le [IsLocallyFiniteMeasure (μ.restrict Ω)] [hp : Fact (1 ≤ p)] :
    sobolevNorm Ω (f + f') k p μ ≤ sobolevNorm Ω f k p μ + sobolevNorm Ω f' k p μ := by
  by_cases hf : MemSobolev Ω f k p μ
  case neg => simp [sobolevNorm, hf]
  by_cases hf' : MemSobolev Ω f' k p μ
  case neg => simp [sobolevNorm, hf']
  obtain ⟨g, hg⟩ := hf
  obtain ⟨g', hg'⟩ := hf'
  simp_rw [hg.sobolevNorm_eq, hg'.sobolevNorm_eq, (hg.add hg').sobolevNorm_eq, sobolevNormAux]
  refine (eLpNorm_mono_enorm fun i ↦ ?_).trans <| eLpNorm_add_le
    measurable_from_top.aestronglyMeasurable measurable_from_top.aestronglyMeasurable hp.out
  simp_rw [enorm_eq_self]
  exact eLpNorm_add_le (hg.memLp i (mod_cast i.is_le)).aestronglyMeasurable
    (hg'.memLp i (mod_cast i.is_le)).aestronglyMeasurable hp.out

lemma eLpNorm_le_sobolevNorm : eLpNorm f p (μ.restrict Ω) ≤ sobolevNorm Ω f k p μ := by
  by_cases hf : MemSobolev Ω f k p μ
  · obtain ⟨g, hg⟩ := hf
    simp_rw [hg.sobolevNorm_eq, sobolevNormAux]
    obtain rfl|hp := eq_or_ne p 0
    · simp
    exact hg.eLpNorm_zero.symm.trans_le (enorm_le_eLpNorm_count _ 0 hp)
  · simp_rw [sobolevNorm, dif_neg hf, le_top]

lemma sobolevNorm_zero_order (h : MemLp f p (μ.restrict Ω)) (hp : p ≠ 0) :
    sobolevNorm Ω f 0 p μ = eLpNorm f p (μ.restrict Ω) := by
  obtain ⟨g, hg⟩ := memSobolev_zero_order.mpr h
  simp_rw [hg.sobolevNorm_eq, sobolevNormAux, Subsingleton.count_eq_dirac (0 : Fin 1)]
  simp [hp, hg.eLpNorm_zero]

theorem sobolevNorm_eq_zero_iff (hf : AEStronglyMeasurable f μ) (hp : p ≠ 0) :
    sobolevNorm Ω f k p μ = 0 ↔ f =ᵐ[μ.restrict Ω] 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ (sobolevNorm_congr h).trans sobolevNorm_zero⟩
  simp_rw [← eLpNorm_eq_zero_iff hf.restrict hp, ← le_zero_iff, ← h, eLpNorm_le_sobolevNorm]

end sobolevNorm

end FinDim

/-! potential alternative definition (to delete) -/
namespace Distribution

def IsRegular (T : 𝓓'(Ω, F)) (μ : Measure E) : Prop :=
  ∃ (f : E → F), LocallyIntegrableOn f Ω μ ∧ T = ofFun Ω f μ

namespace IsRegular

variable {T T₁ T₂ : 𝓓'(Ω, F)}

lemma add (hT₁ : IsRegular T₁ μ) (hT₂ : IsRegular T₂ μ) : IsRegular (T₁ + T₂) μ := by
  obtain ⟨f, hf, rfl⟩ := hT₁
  obtain ⟨g, hg, rfl⟩ := hT₂
  exact ⟨f + g, hf.add hg, ofFun_add hf hg |>.symm⟩

lemma smul (hT : IsRegular T μ) (c : ℝ) : IsRegular (c • T) μ := by
  obtain ⟨f, hf, rfl⟩ := hT
  exact ⟨c • f, hf.smul c, ofFun_smul c |>.symm⟩

end IsRegular

open Classical in
/-- A representative of a regular distribution, chosen so that it is 0 outside `Ω`.
Has junk-value `0` for non-regular distributions. -/
def out (T : 𝓓'(Ω, F)) (μ : Measure E) : E → F :=
  if h : IsRegular T μ then Ω.1.indicator h.choose else 0

structure MemLp (T : 𝓓'(Ω, F)) (p : ℝ≥0∞) (μ : Measure E) : Prop where
  isRegular : IsRegular T μ
  memLp : MeasureTheory.MemLp (T.out μ) p μ

def MemSobolev (T : 𝓓'(Ω, F)) (k : ℕ∞) (p : ℝ≥0∞) (μ : Measure E) : Prop :=
  ∀ m : ℕ, m ≤ k → (iteratedFDerivCLM (E := E) (F := F) m T).MemLp p μ

open Classical Finset in
/-- This definition is different than in (most) textbooks, since we use the `L^p`-norm of the total
derivative instead of the `L^p`-norm of partial derivatives. These definitions are equivalent
for finite dimensional `E` and `k < ∞` [argument todo]. -/
def sobolevNorm (T : 𝓓'(Ω, F)) (k : ℕ) (p : ℝ≥0∞) (μ : Measure E) : ℝ≥0∞ :=
  if MemSobolev T k p μ then
    sobolevNormAux Ω (fun x i ↦ (iteratedFDerivCLM (E := E) (F := F) i T).out μ x) k p μ
  else ∞

end Distribution


variable [FiniteDimensional ℝ E]

variable (Ω F) in
def Sobolev (k : ℕ∞) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (μ : Measure E := by volume_tac)
    [IsLocallyFiniteMeasure (μ.restrict Ω)] :
    AddSubgroup (E →ₘ[μ.restrict Ω] F) where
  carrier := {f | MemSobolev Ω f k p μ}
  zero_mem' := by simp [memSobolev_congr AEEqFun.coeFn_zero, MemSobolev.zero]
  add_mem' {f g} hf hg := by simp [memSobolev_congr (AEEqFun.coeFn_add f g), hf.add hg]
  neg_mem' {f} hf := by simp [memSobolev_congr (AEEqFun.coeFn_neg f), hf.neg]

open AEEqFun

variable {g : E → F}
namespace MemSobolev

variable [IsLocallyFiniteMeasure (μ.restrict Ω)] [hp : Fact (1 ≤ p)]

-- AEStronglyMeasurable f (μ.restrict Ω)
/-- make an element of Lp from a function verifying `MemSobolev` -/
def toSobolev (f : E → F) (hf : MemSobolev Ω f k p μ) : Sobolev Ω F k p μ :=
  ⟨AEEqFun.mk f hf.aestronglyMeasurable, hf.aeEq (coeFn_mk f hf.aestronglyMeasurable).symm⟩

theorem toSobolev_val {f : E → F} (hf : MemSobolev Ω f k p μ) :
    (toSobolev f hf).1 = AEEqFun.mk f hf.aestronglyMeasurable := rfl

theorem coeFn_toSobolev {f : E → F} (hf : MemSobolev Ω f k p μ) :
    hf.toSobolev f =ᵐ[μ.restrict Ω] f :=
  coeFn_mk f hf.aestronglyMeasurable

theorem toSobolev_congr (hf : MemSobolev Ω f k p μ) (hg : MemSobolev Ω g k p μ)
    (hfg : f =ᵐ[μ.restrict Ω] g) : hf.toSobolev f = hg.toSobolev g := by
  simp [toSobolev, hfg]

@[simp]
theorem toSobolev_eq_toSobolev_iff
    (hf : MemSobolev Ω f k p μ) (hg : MemSobolev Ω g k p μ) :
    hf.toSobolev f = hg.toSobolev g ↔ f =ᵐ[μ.restrict Ω] g := by simp [toSobolev]

@[simp]
theorem toSobolev_zero (h : MemSobolev Ω (0 : E → F) k p μ) : h.toSobolev 0 = 0 :=
  rfl

theorem toSobolev_add {f g : E → F} (hf : MemSobolev Ω f k p μ) (hg : MemSobolev Ω g k p μ) :
    (hf.add hg).toSobolev (f + g) = hf.toSobolev f + hg.toSobolev g :=
  rfl

theorem toSobolev_neg {f : E → F} (hf : MemSobolev Ω f k p μ) :
    hf.neg.toSobolev (-f) = -hf.toSobolev f :=
  rfl

theorem toSobolev_sub {f g : E → F}
    (hf : MemSobolev Ω f k p μ) (hg : MemSobolev Ω g k p μ) :
    (hf.sub hg).toSobolev (f - g) = hf.toSobolev f - hg.toSobolev g :=
  rfl

end MemSobolev

namespace Sobolev

variable [IsLocallyFiniteMeasure (μ.restrict Ω)] [hp : Fact (1 ≤ p)]

instance instCoeFun : CoeFun (Sobolev Ω F k p μ) (fun _ => E → F) :=
  ⟨fun f => ((f : E →ₘ[μ.restrict Ω] F) : E → F)⟩

@[ext high]
theorem ext {f g : Sobolev Ω F k p μ} (h : f =ᵐ[μ.restrict Ω] g) : f = g := by
  ext
  exact h

theorem mem_sobolev_iff_memSobolev {f : E →ₘ[μ.restrict Ω] F} :
    f ∈ Sobolev Ω F k p μ ↔ MemSobolev Ω f k p μ := by rfl

alias ⟨_, _root_.MemSobolev.mem_sobolev ⟩ := mem_sobolev_iff_memSobolev

-- protected theorem antitone [IsFiniteMeasure μ] {p q : ℝ≥0∞} (hpq : p ≤ q) :
--     Sobolev Ω F k q μ ≤ Sobolev Ω F k p μ :=
--   fun f hf => (MemSobolev.mono_exponent ⟨f.aestronglyMeasurable, hf⟩ hpq).2

@[simp]
theorem coeFn_mk {f : E →ₘ[μ.restrict Ω] F} (hf : MemSobolev Ω f k p μ) :
    ((⟨f, hf⟩ : Sobolev Ω F k p μ) : E → F) = f := by
  rfl

-- not @[simp] because dsimp can prove this
theorem coe_mk {f : E →ₘ[μ.restrict Ω] F} (hf : MemSobolev Ω f k p μ) :
    ((⟨f, hf⟩ : Sobolev Ω F k p μ) : E →ₘ[μ.restrict Ω] F) = f := by
  rfl

@[simp]
theorem toSobolev_coeFn (f : Sobolev Ω F k p μ) (hf : MemSobolev Ω f k p μ) :
    hf.toSobolev f = f := by
  simp [MemSobolev.toSobolev]

theorem memSobolev (f : Sobolev Ω F k p μ) : MemSobolev Ω f k p μ :=
  f.prop

@[fun_prop]
protected theorem stronglyMeasurable (f : Sobolev Ω F k p μ) : StronglyMeasurable f :=
  f.val.stronglyMeasurable

@[fun_prop]
protected theorem aestronglyMeasurable (f : Sobolev Ω F k p μ) : AEStronglyMeasurable f ν :=
  (Sobolev.stronglyMeasurable f).aestronglyMeasurable

variable (E p μ) in
theorem coeFn_zero : ⇑(0 : Sobolev Ω F k p μ) =ᵐ[μ.restrict Ω] 0 :=
  AEEqFun.coeFn_zero

theorem coeFn_neg (f : Sobolev Ω F k p μ) : ⇑(-f) =ᵐ[μ.restrict Ω] -f :=
  AEEqFun.coeFn_neg _

theorem coeFn_add (f g : Sobolev Ω F k p μ) : ⇑(f + g) =ᵐ[μ.restrict Ω] f + g :=
  AEEqFun.coeFn_add _ _

theorem coeFn_sub (f g : Sobolev Ω F k p μ) : ⇑(f - g) =ᵐ[μ.restrict Ω] f - g :=
  AEEqFun.coeFn_sub _ _

theorem const_mem_sobolev (c : F) (h : μ Ω ≠ ∞) :
    AEEqFun.const E c ∈ Sobolev Ω F k p μ :=
  (MemSobolev.const c h).aeeqFunMk.mem_sobolev

section norm
/-! The Sobolev norm is only defined for `k < ∞`. -/
variable {k : ℕ}
theorem sobolevNorm_lt_top (f : Sobolev Ω F k p μ) : sobolevNorm Ω f k p μ < ∞ :=
  (memSobolev f).sobolevNorm_lt_top

@[aesop (rule_sets := [finiteness]) safe apply]
theorem sobolevNorm_ne_top (f : Sobolev Ω F k p μ) : sobolevNorm Ω f k p μ ≠ ∞ :=
  (sobolevNorm_lt_top f).ne

theorem mem_sobolev_iff_sobolevNorm_lt_top {f : E →ₘ[μ.restrict Ω] F} :
    f ∈ Sobolev Ω F k p μ ↔ sobolevNorm Ω f k p μ < ∞ := by
  rw [mem_sobolev_iff_memSobolev, sobolevNorm_lt_top_iff]

instance instNorm : Norm (Sobolev Ω F k p μ) where norm f := (sobolevNorm Ω f k p μ).toReal

-- note: we need this to be defeq to the instance from `SeminormedAddGroup.toNNNorm`, so
-- can't use `ENNReal.toNNReal (sobolevNorm Ω f k p μ)`
instance instNNNorm : NNNorm (Sobolev Ω F k p μ) where nnnorm f := ⟨‖f‖, ENNReal.toReal_nonneg⟩

instance instDist : Dist (Sobolev Ω F k p μ) where dist f g := ‖f - g‖

instance instEDist : EDist (Sobolev Ω F k p μ) where edist f g := sobolevNorm Ω (⇑f - ⇑g) k p μ

theorem norm_def (f : Sobolev Ω F k p μ) : ‖f‖ = (sobolevNorm Ω f k p μ).toReal :=
  rfl

theorem nnnorm_def (f : Sobolev Ω F k p μ) : ‖f‖₊ = (sobolevNorm Ω f k p μ).toNNReal :=
  rfl

@[simp, norm_cast]
protected theorem coe_nnnorm (f : Sobolev Ω F k p μ) : (‖f‖₊ : ℝ) = ‖f‖ :=
  rfl

@[simp]
theorem enorm_def (f : Sobolev Ω F k p μ) : ‖f‖ₑ = sobolevNorm Ω f k p μ :=
  ENNReal.coe_toNNReal <| Sobolev.sobolevNorm_ne_top f

@[simp]
lemma norm_toSobolev (f : E → F) (hf : MemSobolev Ω f k p μ) :
    ‖hf.toSobolev f‖ = (sobolevNorm Ω f k p μ).toReal := by
  rw [norm_def, sobolevNorm_congr hf.coeFn_toSobolev]

@[simp]
theorem nnnorm_toSobolev (f : E → F) (hf : MemSobolev Ω f k p μ) :
    ‖hf.toSobolev f‖₊ = ENNReal.toNNReal (sobolevNorm Ω f k p μ) :=
  NNReal.eq <| norm_toSobolev f hf

lemma enorm_toSobolev {f : E → F} (hf : MemSobolev Ω f k p μ) :
    ‖hf.toSobolev f‖ₑ = sobolevNorm Ω f k p μ := by
  simp_rw [enorm, nnnorm_toSobolev f hf, ENNReal.coe_toNNReal hf.sobolevNorm_lt_top.ne]

theorem dist_def (f g : Sobolev Ω F k p μ) : dist f g = (sobolevNorm Ω (⇑f - ⇑g) k p μ).toReal := by
  simp_rw [dist, norm_def]
  congr 1
  apply sobolevNorm_congr (coeFn_sub _ _)

theorem edist_def (f g : Sobolev Ω F k p μ) : edist f g = sobolevNorm Ω (⇑f - ⇑g) k p μ :=
  rfl

protected theorem edist_dist (f g : Sobolev Ω F k p μ) : edist f g = .ofReal (dist f g) := by
  rw [edist_def, dist_def, ← sobolevNorm_congr (coeFn_sub _ _),
    ENNReal.ofReal_toReal (sobolevNorm_ne_top (f - g))]

protected theorem dist_edist (f g : Sobolev Ω F k p μ) : dist f g = (edist f g).toReal :=
  Sobolev.dist_def ..

theorem dist_eq_norm (f g : Sobolev Ω F k p μ) : dist f g = ‖f - g‖ := rfl

@[simp]
theorem edist_toSobolev_toSobolev (hf : MemSobolev Ω f k p μ) (hg : MemSobolev Ω g k p μ) :
    edist (hf.toSobolev f) (hg.toSobolev g) = sobolevNorm Ω (f - g) k p μ := by
  rw [edist_def]
  exact sobolevNorm_congr (hf.coeFn_toSobolev.sub hg.coeFn_toSobolev)

@[simp]
theorem edist_toSobolev_zero (hf : MemSobolev Ω f k p μ) :
    edist (hf.toSobolev f) 0 = sobolevNorm Ω f k p μ := by
  simpa using edist_toSobolev_toSobolev hf .zero

@[simp]
theorem nnnorm_zero : ‖(0 : Sobolev Ω F k p μ)‖₊ = 0 := by
  rw [nnnorm_def, ZeroMemClass.coe_zero, sobolevNorm_congr AEEqFun.coeFn_zero, sobolevNorm_zero,
    ENNReal.toNNReal_zero]

@[simp]
theorem norm_zero : ‖(0 : Sobolev Ω F k p μ)‖ = 0 :=
  congr_arg ((↑) : ℝ≥0 → ℝ) nnnorm_zero

@[simp]
theorem norm_zero_measure (f : Sobolev Ω F k p 0) : ‖f‖ = 0 := by
  simp_rw [norm_def, sobolevNorm_zero_measure, ENNReal.toReal_zero]

theorem eq_zero_iff_aeEq_zero {f : Sobolev Ω F k p μ} : f = 0 ↔ f =ᵐ[μ.restrict Ω] 0 := by
  rw [Sobolev.ext_iff]
  exact EventuallyEq.congr_right AEEqFun.coeFn_zero

theorem norm_eq_zero_iff {f : Sobolev Ω F k p μ} : ‖f‖ = 0 ↔ f = 0 := by
  have h2p : p ≠ 0 := by rintro rfl; simpa using hp.out
  refine ⟨fun hf => ?_, fun hf => by simp [hf]⟩
  simp_rw [norm_def, ENNReal.toReal_eq_zero_iff, sobolevNorm_ne_top, or_false,
    sobolevNorm_eq_zero_iff (Sobolev.aestronglyMeasurable f) h2p] at hf
  ext
  exact hf.trans AEEqFun.coeFn_zero.symm

@[simp]
theorem norm_neg (f : Sobolev Ω F k p μ) : ‖-f‖ = ‖f‖ := by
  simp_rw [norm_def, sobolevNorm_congr (coeFn_neg _), sobolevNorm_neg]

@[simp]
theorem nnnorm_neg (f : Sobolev Ω F k p μ) : ‖-f‖₊ = ‖f‖₊ := by
  simp_rw [NNReal.eq_iff, Sobolev.coe_nnnorm, norm_neg]

instance instNormedAddCommGroup : NormedAddCommGroup (Sobolev Ω F k p μ) :=
  { AddGroupNorm.toNormedAddCommGroup
      { toFun := (norm : Sobolev Ω F k p μ → ℝ)
        map_zero' := norm_zero
        neg' := by simp only [norm_neg, implies_true]
        add_le' := fun f g => by
          suffices ‖f + g‖ₑ ≤ ‖f‖ₑ + ‖g‖ₑ by
            simpa only [ge_iff_le, enorm, ←ENNReal.coe_add, ENNReal.coe_le_coe] using this
          simp only [Sobolev.enorm_def]
          exact (sobolevNorm_congr (AEEqFun.coeFn_add _ _)).trans_le sobolevNorm_add_le
        eq_zero_of_map_eq_zero' _ := norm_eq_zero_iff.1 } with
    edist := edist
    edist_dist := Sobolev.edist_dist }

theorem smul_mem_sobolev (c : ℝ) (f : Sobolev Ω F k p μ) :
    c • (f : E →ₘ[μ.restrict Ω] F) ∈ Sobolev Ω F k p μ := by
  obtain ⟨f, hf⟩ := f
  rw [mem_sobolev_iff_memSobolev] at hf ⊢
  exact hf.smul.congr (AEEqFun.coeFn_smul _ _).symm

variable (Ω F k) in
/-- The `ℝ`-submodule of elements of `E →ₘ[μ.restrict Ω] F` whose Sobolev-norm is finite.
This is `Sobolev Ω F k p μ`, with extra structure. -/
def _root_.SobolevSubmodule (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure E := by volume_tac)
    [IsLocallyFiniteMeasure (μ.restrict Ω)] : Submodule ℝ (E →ₘ[μ.restrict Ω] F) :=
  { Sobolev Ω F k p μ with smul_mem' := fun c f hf => smul_mem_sobolev c ⟨f, hf⟩ }

theorem coe_LpSubmodule : (SobolevSubmodule Ω F k p μ).toAddSubgroup = Sobolev Ω F k p μ :=
  rfl

instance instNormedSpace : NormedSpace ℝ (Sobolev Ω F k p μ) :=
  { (SobolevSubmodule Ω F k p μ).module with
    norm_smul_le := sorry }

theorem coeFn_smul (c : ℝ) (f : Sobolev Ω F k p μ) : ⇑(c • f) =ᵐ[μ.restrict Ω] c • ⇑f :=
  AEEqFun.coeFn_smul _ _

instance : CompleteSpace (Sobolev Ω F k p μ) := sorry

theorem _root_.MemSobolev.toSobolev_smul {c : ℝ} {f : E → F} (hf : MemSobolev Ω f k p μ) :
    hf.smul.toSobolev (c • f) = c • hf.toSobolev f :=
  rfl

variable (Ω F k) in
/-- The inclusion from test functions into the Sobolev space. -/
def _root_.TestFunction.toSobolev (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure E := by volume_tac)
    [IsLocallyFiniteMeasure (μ.restrict Ω)] [IsAddHaarMeasure μ] :
    𝓓^{k}(Ω, F) →ₗ[ℝ] Sobolev Ω F k p μ where
  toFun f := f.memSobolev.toSobolev f
  map_add' _ _ := MemSobolev.toSobolev_add ..
  map_smul' _ _ := MemSobolev.toSobolev_smul ..

/- The compactly supported functions in the Sobolev space `Sobolev Ω F k p μ` is the closure
of the test functions inside the Sobolev space. -/
def compactlySupportedSobolev [IsAddHaarMeasure μ] : AddSubgroup (Sobolev Ω F k p μ) :=
  (TestFunction.toSobolev Ω F k p μ).toAddMonoidHom.range.topologicalClosure

end norm
end Sobolev

/-
To do:
0. Finish work on distributions and test functions              todo
1. Basic lemmas (closure under `+`, `•`, ...)                   done
2. define Sobolev spaces                                        done
2'. relate MemSobolev and finite Sobolev norm                   done
3. [Adams, Th 3.3] prove Banach space                           needs completeness
4. monotonicity in `k` and (if `Ω` is bounded) in `p`.          basically done
4'. relate W^{0,p} and L^p                                      done
5. [Adams, Cor 3.4] C^k functions are contained in W^{k, p}     done(?)
  -- we have it for test functions, and `MemSobolev.toSobolev` gives a way to show the inclusion.
  -- the precise statement where we close C^k functions w.r.t. the Sobolev norm is probably
  -- not immediately necessary
6. [Adams, Th 3.6] separable, uniform convexity
7. [Adams, Th 3.15-3.17] density of smooth functions in W^{k, p}
8. [Adams, Ch 4] Sobolev embedding theorem
-/
